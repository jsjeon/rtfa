(*
 * Copyright (c) 2006-2007,
 *  Jinseong Jeon <jinseong.jeon@arcs.kaist.ac.kr>
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 * this list of conditions and the following disclaimer in the documentation
 * and/or other materials provided with the distribution.
 *
 * 3. The names of the contributors may not be used to endorse or promote
 * products derived from this software without specific prior written
 * permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
 * LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 *)

module C = Cil
module T = Rtfa_types
module S = Struct

(*----------------------------------------------------------------------*)
(* CALLOC                                                              *)
(*----------------------------------------------------------------------*)

module StrKey =
struct
  type t = string
  let compare = Pervasives.compare
end

module CS = Set.Make(StrKey)

let wo_calloc = ref false

let calloced = ref CS.empty

let add_calloced (args: C.exp list) : unit =
  let extract_sname = function
    | C.SizeOf t ->
    (
      match C.unrollType t with
      | C.TComp (c,_) -> calloced := CS.add c.C.cname !calloced
      | _ -> ()
    )
    | C.SizeOfE (C.Lval lv) ->
    (
      match C.unrollType (C.typeOfLval lv) with
      | C.TComp (c,_) -> calloced := CS.add c.C.cname !calloced
      | _ -> ()
    )
    | _ -> ()
  in
  List.iter extract_sname args

(* is_calloced: string -> bool *)
let is_calloced (sn: string) : bool =
  if not !wo_calloc then CS.mem sn !calloced else false

module Make = functor (U: T.RE_SIG) ->
struct

(*----------------------------------------------------------------------*)
(* Basic Types for Deterministic Finite Automata                        *)
(*----------------------------------------------------------------------*)

module IntKey =
struct
  type t = int
  let compare = Pervasives.compare
end

module IS = Set.Make(IntKey)

module IM = Map.Make(IntKey)

type state = {
  s_id: int;
  mutable s_preds: IS.t;
  mutable s_succs: (U.t T.re) IM.t;
}

(*----------------------------------------------------------------------*)
(* Basic Elements                                                       *)
(*----------------------------------------------------------------------*)

let start = { (* start state *)
  s_id = 0;
  s_preds = IS.empty;
  s_succs = IM.empty;
} 

and final = { (* final state *)
  s_id = max_int;
  s_preds = IS.empty;
  s_succs = IM.empty;
} 

module IH = Inthash

let state_hash = IH.create 153

let find_state (s_id: int) : state =
  try IH.find state_hash s_id
  with Not_found -> raise (T.AP_Fatal ("find_state: "^(string_of_int s_id)))

(*----------------------------------------------------------------------*)
(* Additional type for Heap-allocation Analysis                         *)
(*----------------------------------------------------------------------*)

(* HA version 2.

(* info : have malloc call in closure or not *)
type info = HAVE | NORMAL

exception Already_have

HA version 2. end *)

(* HA version 3. *)

module TKey =
struct
  type t = U.t
  let compare = U.compare
end

module TS = Set.Make(TKey)

module N = Num

(* info: promotion cadidate set * promoted set *)
type info = TS.t * TS.t

(* HA version 3. end *)

(*----------------------------------------------------------------------*)
(* Mapping from Varinfo(funtion) to closure info.                       *)
(*----------------------------------------------------------------------*)

module VarInfoKey =
struct
  type t = C.varinfo
  let compare v1 v2 = Pervasives.compare v1.C.vid v2.C.vid
end

module VM = Map.Make(VarInfoKey)

let var_info_map = ref VM.empty

let fun_to_info (v: C.varinfo) (i: info) : unit =
  var_info_map := VM.add v i !var_info_map

(* HA version 1.

let find_re (v: C.varinfo) : U.t T.re =
  try VM.find v !var_re_map with Not_found -> T.Empty

HA version 1. end *)

let find_re (v: C.varinfo) : U.t T.re =
  try ignore (VM.find v !var_info_map); T.Func v
  with Not_found -> T.Empty

(* clear_info: unit -> unit *)
let clear_info () : unit =
  var_info_map := VM.empty

(*----------------------------------------------------------------------*)
(* Utilities for Automata Generation                                    *)
(*----------------------------------------------------------------------*)

let state_cnt = ref 0

let fresh_state () : state =
  incr state_cnt;
  let s = {
    s_id = !state_cnt;
    s_preds = IS.empty;
    s_succs = IM.empty;
  } in
  IH.add state_hash !state_cnt s; s

module SM = Map.Make(IntKey)

let sm = ref SM.empty (* mapping from stmt to s_id pair *)

let stmt_to_sid (sid: int) (head: int) (tail: int) : unit =
  sm := SM.add sid (head, tail) !sm

let find_head (sid: int) : state =
  find_state (fst (SM.find sid !sm))

let find_tail (sid: int) : state =
  find_state (snd (SM.find sid !sm))

let add_transition (src: state) (re: U.t T.re) (dst: state) : unit =
  let next_succs =
    if (IM.mem dst.s_id src.s_succs) then
      let re' = IM.find dst.s_id src.s_succs
      in IM.add dst.s_id (T.alter re re') src.s_succs
    else
      IM.add dst.s_id re src.s_succs
  in
  src.s_succs <- next_succs;
  dst.s_preds <- IS.add src.s_id dst.s_preds

(*----------------------------------------------------------------------*)
(* Automata Generation                                                  *)
(*----------------------------------------------------------------------*)

let current_fn = ref ""

let selective_make_state (sid: int) (re: U.t T.re) : unit =
  if (re = T.Empty) then
  (
    let st = fresh_state ()
    in stmt_to_sid sid st.s_id st.s_id
  )
  else
  (
    let head = fresh_state ()
    and tail = fresh_state ()
    in
    stmt_to_sid sid head.s_id tail.s_id;
    add_transition head re tail
  )

let rec make_state_block (b: C.block) : unit =
  List.iter make_state_stmt b.C.bstmts

and make_state_stmt (s: C.stmt) : unit =
  match s.C.skind with
  | C.Instr il ->
    (
      let head = fresh_state () in
      let tail = List.fold_left make_state_instr head il
      in
      stmt_to_sid s.C.sid head.s_id tail.s_id
    )
  | C.Return (eo,_) ->
    (
      match eo with
      | Some e -> selective_make_state s.C.sid (make_re_exp e)
      | None   -> selective_make_state s.C.sid T.Empty
    )
  | C.Goto     _
  | C.Break    _
  | C.Continue _ -> selective_make_state s.C.sid T.Empty
  | C.If (e,tb,fb,_) ->
    (
      selective_make_state s.C.sid (make_re_exp e);
      make_state_block tb;
      make_state_block fb
    )
  | C.Switch _ -> raise (T.AP_Fatal "Switch: CFG need to be made")
  | C.Loop (b,_,_,_)
  | C.Block b -> 
    (
      selective_make_state s.C.sid T.Empty;
      make_state_block b
    )
  | C.TryFinally _
  | C.TryExcept  _ -> raise (T.AP_Debug "Try stmt: not support")

and make_state_instr (acc: state) (i: C.instr) : state =
  let selective_link (acc: state) (re: U.t T.re) : state =
    if (re = T.Empty) then acc
    else
    (
      let st = fresh_state () in
      add_transition acc re st; st
    )
  in
  match i with
  | C.Set (lv,e,_) ->
    (
      let re1 = make_re_exp e
      and re2 = U.write_access lv 
      in 
      selective_link acc (T.conc re1 re2)
    )
  | C.Call (lvo,fn,args,_) ->
    (
      let re_folder (acc: U.t T.re) (e: C.exp) : U.t T.re =
        T.conc acc (make_re_exp e)
      in
      let re1 = List.fold_left re_folder T.Empty args
      and re3 =
        match lvo with
        | Some lv -> U.write_access lv
        | None    -> T.Empty
      in
      match fn with 
      | C.Lval (C.Var vi, C.NoOffset) ->
        (
          if !current_fn = vi.C.vname && !T.ap_inter then 
          (  (* self-recursive and inter-procedural *)
            let call_st   = selective_link acc re1
            and return_st = fresh_state ()
            in
            add_transition call_st T.Empty start;
            add_transition final T.Empty return_st;
            selective_link return_st re3
          )
          else
          (
            let re2 =
              if List.mem vi.C.vname S.alloc_names && (List.length args) >= 1
              then (* T.Func vi *)
              (
                let r1 =
                  if has_sizeof (List.hd args)
                  then U.read_access (extract_lv (List.hd args))
                  else T.Empty
                in
                if vi.C.vname = "calloc"
                then
                (
                  add_calloced args;
                  if has_sizeof (List.nth args 1)
                  then
                    let r2 = U.read_access (extract_lv (List.nth args 1)) in
                    T.star (T.conc r1 r2)
                  else
                    T.star r1
                )
                else r1
              )
              else find_re vi
              (* HA version 2
                try
                  let info = VM.find vi !var_info_map in
                  match info with
                  | NORMAL -> T.Func vi
                  | HAVE   -> raise Already_have
                with Not_found -> T.Empty
              *)
            in
            let st = selective_link acc (T.conc (T.conc re1 re2) re3) in
            if vi.C.vname = "exit" then (* special call *)
              add_transition st T.Empty final;
            st
          )
        )
      | C.Lval (C.Mem ex, C.NoOffset) ->
        (
          let fd_list = Ptranal.resolve_funptr ex in
          let fd_folder (acc: U.t T.re) (fd: C.fundec) : U.t T.re =
            let vi = fd.C.svar in
            let re =
              if List.mem vi.C.vname S.alloc_names && (List.length args) >= 1
              then (* T.Func vi *)
              (
                let r1 =
                  if has_sizeof (List.hd args)
                  then U.read_access (extract_lv (List.hd args))
                  else T.Empty
                in
                if vi.C.vname = "calloc"
                then
                (
                  add_calloced args;
                  if has_sizeof (List.nth args 1)
                  then
                    let r2 = U.read_access (extract_lv (List.nth args 1)) in
                    T.star (T.conc r1 r2)
                  else
                    T.star r1
                )
                else r1
              )
              else find_re vi
              (* HA version 2.
                try
                  let info = VM.find vi !var_info_map in
                  match info with
                  | NORMAL -> T.Func vi
                  | HAVE   -> raise Already_have
                with Not_found -> T.Empty
              *)
            in
            T.alter acc re
          in
          let re2 = List.fold_left fd_folder T.Empty fd_list
          in
          selective_link acc (T.conc (T.conc re1 re2) re3)
        )
      | _ -> raise (T.AP_Fatal "Call: other cases?")
    )
  | C.Asm _ -> acc (* actually, not support *)

and make_re_exp = function
  | C.Lval    lv
  | C.AddrOf  lv
  | C.StartOf lv -> (* U.read_access lv *)
    (* HA version 3. *) T.Empty
  | C.SizeOfE  e'
  | C.AlignOfE e'
  | C.CastE (_,e') 
  | C.UnOp  (_,e',_) -> make_re_exp e'
  | C.BinOp (_,e1,e2,_) -> T.conc (make_re_exp e1) (make_re_exp e2)
  | _ -> T.Empty

(* assume that S.set_target_struct was called *)
and has_sizeof = function
  | C.SizeOf t -> (* S.isTargetType t *)
    (* HA version 3. *)
    (
      match C.unrollType t with
      | C.TComp _ -> true
      | _ -> false
    )
  | C.SizeOfE (C.Lval lv) -> (* S.isTargetType (C.typeOfLval lv) *)
    (* HA version 3. *)
    (
       match C.unrollType (C.typeOfLval lv) with
       | C.TComp _ -> true
       | _ -> false
     )
  | _ -> false

(* HA version 3. *)
and extract_lv = function
  | C.SizeOf t -> (C.Var (C.makeVarinfo false "var_for_sizeof" t), C.NoOffset)
  | C.SizeOfE (C.Lval lv) -> lv
  | _ -> raise (T.AP_Fatal "has_sizeof and extract_lv dismatch.")
(* HA version 3. end *)

let rec restore_cfg_block (b: C.block) : unit =
  List.iter restore_cfg_stmt b.C.bstmts

and restore_cfg_stmt (s: C.stmt) : unit =
  let head = find_tail s.C.sid in
  let restore_cfg (succ: C.stmt) : unit =
    let tail = find_head succ.C.sid 
    in add_transition head T.Empty tail
  in
  List.iter restore_cfg s.C.succs;

  match s.C.skind with
  | C.If (_,tb,fb,_) -> (restore_cfg_block tb; restore_cfg_block fb)
  | C.Loop (b,_,_,_)
  | C.Block b -> restore_cfg_block b
  | C.Return (_,_) -> add_transition head T.Empty final
  | _ -> ()

let make_automata (fb: C.block) : unit =
  (* initialization *)
  state_cnt := 0;
  IH.clear state_hash;
  IH.add state_hash start.s_id start;
  IH.add state_hash final.s_id final;
  sm := SM.empty;
  start.s_preds <- IS.empty;
  start.s_succs <- IM.empty;
  final.s_preds <- IS.empty;
  final.s_succs <- IM.empty;

(* HA version 2.
  try (
HA version 2. end *)
    make_state_block fb;
    restore_cfg_block fb;
    try (
      let head = find_head (List.hd fb.C.bstmts).C.sid in
      add_transition start T.Empty head;
      if (IS.is_empty final.s_preds) then (* void function *)
      (
        let tail = find_tail (List.hd (List.rev fb.C.bstmts)).C.sid in
        add_transition tail T.Empty final
      );
      (* true *)
    )
    with Failure _ -> () (* empty body *)
(* HA version 2.
    with Failure _ -> true (* empty body *)
  )
  with Already_have -> false
HA version 2. end *)

(*----------------------------------------------------------------------*)
(* Automata Printer for Debugging                                       *)
(*----------------------------------------------------------------------*)

module P = Pretty

let automata_printer () : unit =
  let state_printer (sid: int) (s: state) : unit =
    ignore (P.printf "[%2d]: " sid);
    let pred_printer (pred: int) : unit =
      ignore (P.printf "%2d " pred)
    in
    print_string "{";
    IS.iter pred_printer s.s_preds;
    print_endline "}";
    let succ_printer (succ: int) (re: U.t T.re) : unit =
      ignore (P.printf " ->[%2d] %s\n" succ (T.str_of_re U.str_of_t re))
    in
    IM.iter succ_printer s.s_succs
  in
  IH.iter state_printer state_hash

(*----------------------------------------------------------------------*)
(* Automata Reduction by Eliminating States                             *)
(*----------------------------------------------------------------------*)

let self_edge (s: state) : U.t T.re =
  if not (IM.mem s.s_id s.s_succs) then T.Empty
  else IM.find s.s_id s.s_succs

let eliminate_state (s: state) : unit =
  let forwarding (pred: int) : unit =
    if pred = s.s_id then ()
    else (* exclude self-edge *)
    (
      let pred_s = find_state pred in
      let re = T.conc (IM.find s.s_id pred_s.s_succs) (T.star (self_edge s))
      in
      let targeting (succ: int) (re': U.t T.re) : unit =
        if succ = s.s_id then ()
        else (* exclude self-edge *)
        (
          let succ_s = find_state succ
          in add_transition pred_s (T.conc re re') succ_s
        )
      in
      IM.iter targeting s.s_succs;
      pred_s.s_succs <- IM.remove s.s_id pred_s.s_succs
    )
  in
  IS.iter forwarding s.s_preds;

  let remove_pred (succ: int) _ : unit =
    let succ_s = find_state succ
    in succ_s.s_preds <- IS.remove s.s_id succ_s.s_preds
  in
  IM.iter remove_pred s.s_succs;
  IH.remove state_hash s.s_id;

  if !T.ap_debug then (* debug *)
  (
    ignore (P.printf "= elminate %d =\n" s.s_id);
    automata_printer ()
  )

let has_empty_edge (s: state) : bool =
  let find_empty _ (re: U.t T.re) (acc: bool) : bool =
    if acc then acc else (re = T.Empty)
  in IM.fold find_empty s.s_succs false

let has_back_edge (s: state) : bool =
  let find_back (pred: int) (acc: bool) : bool =
    if acc then acc else s.s_id < pred (* exclude self *)
  in IS.fold find_back s.s_preds false

let state_compare (s1: state) (s2: state) : int =
  let bb1 = has_back_edge s1
  and bb2 = has_back_edge s2
  in
  if bb1 && (not bb2) then 1
  else if (not bb1) && bb2 then -1
  else if bb1 && bb2 then Pervasives.compare s2.s_id s1.s_id
  else (* not bb1 and not bb2 *)
    Pervasives.compare s1.s_id s2.s_id

module StateKey =
struct
  type t = state
  let compare = state_compare
end

module SS = Set.Make(StateKey)

let worklist = ref SS.empty

let push_worklist (n: int) : unit =
  if n <> start.s_id && n <> final.s_id then
    worklist := SS.add (find_state n) !worklist

let pop_worklist () : state =
  let next = SS.min_elt !worklist in
  worklist := SS.remove next !worklist; next

let compensate_worklist (n: int) _ : unit =
  let s = find_state n in
  if SS.mem s !worklist then 
    worklist := SS.remove s !worklist

let reduce () : unit =
try
  let workhorse (s: state) : unit =
    if (s.s_id = start.s_id) || (s.s_id = final.s_id) then ()
    else (* exclude start and final *)
    (
      let selective_push (succ: int) _ : unit =
        if succ <> s.s_id then push_worklist succ
      in
      IM.iter compensate_worklist s.s_succs; (* for reordering *)
      eliminate_state s;
      IM.iter selective_push s.s_succs
    )
  in
  let state_list = snd (List.split (IH.tolist state_hash)) in
  let empty_list = List.rev (List.filter has_empty_edge state_list) in
  let refined = List.filter (fun e -> not (has_back_edge e)) empty_list
  in
  List.iter workhorse refined;
  worklist := SS.empty; (* compensate during empty_list *)

  let remain_list = snd (List.split (IH.tolist state_hash))
  in
  List.iter (fun s -> push_worklist s.s_id) remain_list;
  while not (SS.is_empty !worklist) do
    workhorse (pop_worklist ())
  done
with Not_found -> raise (T.AP_Fatal "Inconsistent with pred-succ")

(*----------------------------------------------------------------------*)
(* Finding Local Closures                                               *)
(*----------------------------------------------------------------------*)

(* HA version 3. *)

let n_0 = N.num_of_int 0
let n_1 = N.num_of_int 1

let rec find_alloc (prev: TS.t) (promoted: TS.t) (d: N.num) = function
  | T.Empty -> (prev, promoted)
  | T.Cons elts ->
    (
      let folder (a1, a2) (elt: U.t) =
        if N.gt_num d n_0 (* in a closure *)
        then (TS.remove elt prev, TS.add elt promoted)
        else (TS.add elt prev, promoted)
      in
      List.fold_left folder (prev, promoted) elts
    )
  | T.Conc  rl
  | T.Alter rl -> List.fold_left
    (fun (a1, a2) r -> find_alloc a1 a2 d r) (prev, promoted) rl
  | T.Star re' -> find_alloc prev promoted (N.add_num d n_1) re'
  | T.Func  vi ->
    (
      let (prev', promoted') =
        try VM.find vi !var_info_map with Not_found -> (TS.empty, TS.empty)
      in
      if N.gt_num d n_0 (* in a closure *)
      then (prev, TS.union promoted (TS.union prev' promoted'))
      else (TS.union prev prev', TS.union promoted promoted')
    )

(* find_heap_allocated: C.fundec -> U.t list *)
let find_heap_allocated (f: C.fundec) : U.t list =
  current_fn := f.C.svar.C.vname;
  Stats.time "make_automata_m" make_automata f.C.sbody;

  if !T.ap_debug then (* debug *)
  (
    print_endline "= building automata =";
    automata_printer ()
  );
  Stats.time "reduce_m" reduce ();

  let ap =
    let r = self_edge start
    and u = self_edge final in
    try
    (
      let s = IM.find final.s_id start.s_succs in
      try
        let t = IM.find start.s_id final.s_succs in
        if not !T.ap_choice then
          let su_  = T.conc s (T.star u) in
          let su_t = T.conc su_ t
          in T.conc (T.star (T.alter r su_t)) su_
        else
          let r_s  = T.conc (T.star r) s in
          let tr_s = T.conc t r_s
          in T.conc r_s (T.star (T.alter u tr_s))
      with Not_found ->
        T.conc (T.star r) (T.conc s (T.star u))
    )
    with Not_found -> T.Empty
  in

  let local = Stats.time "find_alloc" (find_alloc TS.empty TS.empty n_0) ap
  in

(* debugging
  let set_printer (s: TS.t) : unit =
    let helper (elt: U.t) : unit =
      print_string (U.str_of_t elt); print_string " "
    in
    TS.iter helper s
  in
  print_endline !current_fn;
  print_string "ap: ";
  print_endline (T.str_of_re U.str_of_t ap);
  print_string "("; set_printer (fst local); print_string "), ";
  print_string "("; set_printer (snd local); print_endline ")";
*)

  if not (TS.is_empty (fst local)) || not (TS.is_empty (snd local)) then
    fun_to_info f.C.svar local;
  TS.elements (snd local)

(* HA verseion 3. end *)

(* HA version 2.

let rec find_alloc (flag: bool) = function
  | T.Empty
  | T.Cons _ -> false
  | T.Func _ -> flag
  | T.Conc  rl
  | T.Alter rl -> stop_true flag rl
  | T.Star re' -> find_alloc true re'
and stop_true (flag: bool) = function
  | [] -> false
  | hd :: tl -> if find_alloc flag hd then true else stop_true flag tl

(* is_heap_allocated: Cil.fundec -> bool *)
let is_heap_allocated (f: C.fundec) : bool =
  current_fn := f.C.svar.C.vname;

  let making = Stats.time "make_automata_m" make_automata f.C.sbody in
  if making then
  (
    if !T.ap_debug then (* debug *)
    (
      print_endline "= building automata =";
      automata_printer ()
    );
    Stats.time "reduce_m" reduce ();

    let ap =
      let r = self_edge start
      and u = self_edge final in
      try
      (
        let s = IM.find final.s_id start.s_succs in
        try
          let t = IM.find start.s_id final.s_succs in
          if not !T.ap_choice then
            let su_  = T.conc s (T.star u) in
            let su_t = T.conc su_ t
            in T.conc (T.star (T.alter r su_t)) su_
          else
            let r_s  = T.conc (T.star r) s in
            let tr_s = T.conc t r_s
            in T.conc r_s (T.star (T.alter u tr_s))
        with Not_found ->
          T.conc (T.star r) (T.conc s (T.star u))
      )
      with Not_found -> T.Empty
    in

(* HA version 1.

    fun_to_info f.C.svar ap;
    if f.C.svar.C.vname <> "main" then true
    else Stats.time "find_alloc" (find_alloc false) ap

HA version 1. end *)

    let have_closure = Stats.time "find_alloc" (find_alloc false) ap in
    (
      if have_closure then
        fun_to_info f.C.svar HAVE
      else if ap <> T.Empty then
        fun_to_info f.C.svar NORMAL
    );
    have_closure
  )
  else
  (
    fun_to_info f.C.svar HAVE;
    true
  )

HA version 2. end *)

end

