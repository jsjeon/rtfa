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

module T = Rtfa_types
module C = Cil

let loop_only = ref false

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
(* Additional type for Field Affinity                                   *)
(*----------------------------------------------------------------------*)

module TTKey =
struct
  type t = U.t * U.t
  let compare (a1,b1) (a2,b2) =
    let r = U.compare a1 a2 in
    if r = 0 then U.compare b1 b2 else r
end

module TTMap = Map.Make(TTKey)

module N = Num

let n_0 = N.num_of_int 0
let n_1 = N.num_of_int 1

(* info : start syms * end syms * (level * cnt) list Map.t *)
type info = U.t list * U.t list * (N.num * N.num) list TTMap.t

(* empty_info : unit -> info *)
let empty_info () = ([], [], TTMap.empty)

(* get_core: info -> (U.t * U.t * (N.num * N.num) list) list *)
let get_core ((_,_,m): info) : (U.t * U.t * (N.num * N.num) list) list =
  let folder (k1,k2) n acc = (k1,k2,n) :: acc
  in TTMap.fold folder m []

(*----------------------------------------------------------------------*)
(* Mapping from Varinfo(funtion) to affinity info.                      *)
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

let find_info (v: C.varinfo) : info =
  try VM.find v !var_info_map with Not_found -> ([], [], TTMap.empty)

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
              try ignore (VM.find vi !var_info_map); T.Func vi
              with Not_found -> T.Empty
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
              try ignore (VM.find vi !var_info_map); T.Func vi
              with Not_found -> T.Empty
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
  | C.StartOf lv -> U.read_access lv
  | C.SizeOfE  e'
  | C.AlignOfE e'
  | C.CastE (_,e') 
  | C.UnOp  (_,e',_) -> make_re_exp e'
  | C.BinOp (_,e1,e2,_) -> T.conc (make_re_exp e1) (make_re_exp e2)
  | _ -> T.Empty

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

  make_state_block fb;
  restore_cfg_block fb;
  try
    let head_of_func = find_head (List.hd fb.C.bstmts).C.sid in
    add_transition start T.Empty head_of_func;
    if (IS.is_empty final.s_preds) then (* void function *)
      let tail_of_func = find_tail (List.hd (List.rev fb.C.bstmts)).C.sid in
      add_transition tail_of_func T.Empty final
  with Failure _ -> () (* empty body *)

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
  else T.star (IM.find s.s_id s.s_succs)

let eliminate_state (s: state) : unit =
  let forwarding (pred: int) : unit =
    if pred = s.s_id then ()
    else (* exclude self-edge *)
    (
      let pred_s = find_state pred in
      let re = T.conc (IM.find s.s_id pred_s.s_succs) (self_edge s) 
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
(* Local Affinity Estimation                                            *)
(*----------------------------------------------------------------------*)

module TKey =
struct
  type t = U.t
  let compare = U.compare
end

module TS = Set.Make(TKey)

let local_map = ref TTMap.empty
let star_begins = ref TS.empty

let rec affine_re (first: bool) (d: N.num) (fs: TS.t) = function
  | T.Empty -> fs
  | T.Cons elts ->
    (
      if first && (List.length elts) <> 2 then (
        try star_begins := TS.add (List.hd elts) !star_begins
        with Failure _ -> raise (T.AP_Fatal "affine_re:cons")
      );
      let folder (acc: TS.t) (next: U.t) : TS.t =
        let set_iter (prev: U.t) : unit = 
          add_relation prev next d
        in
        TS.iter set_iter acc;
        TS.singleton next
      in
      List.fold_left folder fs elts
    )
  | T.Conc  rl ->
    (
      try 
        let fs' = affine_re first d fs (List.hd rl) in
        List.fold_left (fun a r -> affine_re false d a r) fs' (List.tl rl)
      with Failure _ -> raise (T.AP_Fatal "affine_re:conc")
    )
  | T.Alter rl -> List.fold_left
    (fun a r -> TS.union a (affine_re first d fs r)) TS.empty rl
  | T.Star re' ->
    (
      let d' = Num.add_num d n_1 in
      star_begins := TS.empty;
      let last_set = affine_re true d' TS.empty re' in
      let adder (start: U.t) : unit =
        let adder2 (last: U.t) : unit =
          add_relation last start d'
        in
        TS.iter adder2 last_set;
        let adder3 (prev: U.t) : unit =
          add_relation prev start d
        in
        TS.iter adder3 fs
      in
      TS.iter adder !star_begins; last_set
    )
  | T.Func  vi ->
    (
      let (begins, ends, m) = find_info vi in
      let set_iter (prev: U.t) : unit =
        let list_iter (func_start: U.t) : unit =
          add_relation prev func_start d
        in
        List.iter list_iter begins
      in
      TS.iter set_iter fs;

      let incr_d lst =
        let worker ((lv, cnt) : N.num * N.num) = (N.add_num lv d, cnt)
        in List.map worker lst
      in
      let m' = 
        if (N.gt_num d n_0) then TTMap.map incr_d m else m
      in
      local_map := merge_map !local_map m';

      let set_maker (acc: TS.t) (func_end: U.t) : TS.t =
        TS.add func_end acc
      in
      List.fold_left set_maker TS.empty ends
    )

and add_relation (a: U.t) (b: U.t) (depth: N.num) : unit =
  let tt = tt_refine a b in
  let prev_list = try TTMap.find tt !local_map with Not_found -> [] in
  let rec insert = function
    | [] -> (depth, n_1) :: []
    | hd :: tl ->
      if N.eq_num (fst hd) depth then
      (
        let prev = snd hd in
        let next = N.add_num prev n_1
        in
        (depth,next) :: tl
      )
      else hd :: (insert tl)
  in
  local_map := TTMap.add tt (insert prev_list) !local_map

and tt_refine (v1: U.t) (v2: U.t) : U.t * U.t =
  if (U.compare v1 v2) < 0 then (v1, v2) else (v2, v1)

and merge_map (m1: 'a) (m2: 'a) : 'a =
  let rec list_merger lst1 lst2 =
    match lst1, lst2 with
    | [], q  -> q
    |  p, [] -> p
    | hd1 :: tl1, hd2 :: tl2 ->
      (
        let lv1 = fst hd1
        and lv2 = fst hd2 in
        let lvc = N.compare_num lv1 lv2 in
        if lvc < 0 then (* lv1 < lv2 *)
          (hd1 :: (list_merger tl1 (hd2 :: tl2)))
        else if lvc > 0 then (* lv1 > lv2 *)
          (hd2 :: (list_merger (hd1 :: tl1) tl2))
        else (* lv1 = lv2 *)
        (
          let cnt1 = snd hd1
          and cnt2 = snd hd2 in
          ((lv1, N.add_num cnt1 cnt2) :: (list_merger tl1 tl2))
        )
      )
  in
  let nump_compare (lv1, cnt1) (lv2, cnt2) =
    let r = N.compare_num lv1 lv2 in
    if r = 0 then N.compare_num cnt1 cnt2 else r
  in
  let updater k prev_lst =
    try
    (
      let sorted_prev = List.stable_sort nump_compare prev_lst
      and sorted_call = List.stable_sort nump_compare (TTMap.find k m2)
      in
      list_merger sorted_prev sorted_call
    )
    with Not_found -> prev_lst
  in
  let result_map = ref TTMap.empty in
  let rest_adder k prev_list =
    if not (TTMap.mem k m1) then
      result_map := TTMap.add k prev_list !result_map
  in
  result_map := TTMap.mapi updater m1;
  TTMap.iter rest_adder m2;
  !result_map

let local_begins = ref TS.empty
let local_ends   = ref TS.empty

let rec grep_begins = function
  | T.Empty -> ()
  | T.Cons elts ->
    (
      try local_begins := TS.add (List.hd elts) !local_begins
      with Failure _ -> raise (T.AP_Fatal "grep_begins:cons")
    )
  | T.Conc  rl ->
    (
      try grep_begins (List.hd rl)
      with Failure _ -> raise (T.AP_Fatal "grep_begins:conc")
    )
  | T.Alter rl -> List.iter grep_begins rl
  | T.Star re' -> grep_begins re'
  | T.Func  vi ->
    (
      let (begins,_,_) = find_info vi in
      let adder (elt: U.t) : unit =
        local_begins := TS.add elt !local_begins
      in
      List.iter adder begins
    )

and grep_ends = function
  | T.Empty -> ()
  | T.Cons elts ->
    (
      try local_ends := TS.add (List.hd (List.rev elts)) !local_ends
      with Failure _ -> raise (T.AP_Fatal "grep_ends:cons")
    )
  | T.Conc  rl ->
    (
      try grep_ends (List.hd (List.rev rl))
      with Failure _ -> raise (T.AP_Fatal "grep_ends:conc")
    )
  | T.Alter rl -> List.iter grep_ends rl
  | T.Star re' -> grep_ends re'
  | T.Func  vi ->
    (
      let (_,ends,_) = find_info vi in
      let adder (elt: U.t) : unit =
        local_ends := TS.add elt !local_ends
      in
      List.iter adder ends
    )

(* remove_lv0: 'a -> 'a *)
let remove_lv0 (map: (N.num * N.num) list TTMap.t) =
  let remover k prev_lst =
    let rec except_lv0 = function
    | [] -> []
    | (lv, cnt) :: tl ->
      if (N.compare_num lv n_0) = 0 then except_lv0 tl
      else (lv, cnt) :: (except_lv0 tl)
    in
    except_lv0 prev_lst
  in
  TTMap.mapi remover map

(* for debugging *)
let map_printer (k1,k2) lst : unit =
  let rec lst_printer = function
    | [] -> ()
    | (lv, cnt) :: [] ->
      ignore (Pretty.printf "[lv: %s " (N.string_of_num lv));
      ignore (Pretty.printf "cnt: %s]\n" (N.string_of_num cnt))
    | (lv, cnt) :: tl ->
      ignore (Pretty.printf "[lv: %s " (N.string_of_num lv));
      ignore (Pretty.printf "cnt: %s] " (N.string_of_num cnt));
      lst_printer tl
  in
  ignore (Pretty.printf "(%s,%s)\n" (U.str_of_t k1) (U.str_of_t k2));
  lst_printer lst
  
(* local_affinity: ?bool -> Cil.fundec -> info *)
let local_affinity ?(entire = false) (f: C.fundec) : info =
  current_fn := f.C.svar.C.vname;
  Stats.time "make_automata" make_automata f.C.sbody;

  if !T.ap_debug then (* debug *)
  (
    print_endline "= building automata =";
    automata_printer ()
  );
  Stats.time "reduce" reduce ();

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

  local_map    := TTMap.empty;
  local_begins := TS.empty;
  local_ends   := TS.empty;

  if entire then
  ( (* FA version 3. - to be implemented differently *)
    ignore (Stats.time "affine_re" (affine_re false n_0 TS.empty) ap);
    Stats.time "grep_begins" grep_begins ap;
    Stats.time "grep_ends" grep_ends ap;
  )
  else
  (
    ignore (Stats.time "affine_re" (affine_re false n_0 TS.empty) ap);
    Stats.time "grep_begins" grep_begins ap;
    Stats.time "grep_ends" grep_ends ap;
  );

  let begins = if !loop_only then [] else TS.elements !local_begins
  and ends   = if !loop_only then [] else TS.elements !local_ends in
  if !loop_only then local_map := remove_lv0 !local_map;

(* debugging
  ignore (Pretty.printf "[%s]\n" f.C.svar.C.vname);
  print_string "ap: ";
  print_endline (T.str_of_re U.str_of_t ap);
  TTMap.iter map_printer !local_map;
*)

  let info = (begins, ends, !local_map) in
  if not (TTMap.is_empty !local_map) then fun_to_info f.C.svar info;
  info

end

