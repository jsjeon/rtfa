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

module C  = Cil
module S  = Struct
module T  = Rtfa_types
module CG = Rtfa_cg

module StructKey =
struct
  type t = C.compinfo
  let compare s1 s2 = Pervasives.compare s1.C.ckey s2.C.ckey
end

module SS = Set.Make(StructKey)

let selection = ref SS.empty

let add_choice (c: C.compinfo) : unit =
  if (List.length c.C.cfields) > 1 then 
    selection := SS.add c !selection

(* HA version 3. finding heap-allocated structure first *)

let find_heap_allocated (file: C.file) : unit =
  let module HA: T.RE_SIG with type t = C.compinfo =
    struct
      let struct_access lv =
        match C.unrollType (C.typeOfLval lv) with
        | C.TComp (c,_) -> T.Cons [c]
        | _ -> T.Empty

      type t = C.compinfo
      let compare c1 c2 = Pervasives.compare c1.C.cname c2.C.cname
      let str_of_t (f: t) = f.C.cname
      let read_access  = struct_access
      let write_access = fun _ -> T.Empty
    end
  in
    
  let module AP = M_automata.Make(HA) in
  let candidate = ref [] in
  let process_fd (fd: C.fundec) : unit =
    let cur = AP.find_heap_allocated fd in
    if fd.C.svar.C.vname = "main" then candidate := cur
  in
  List.iter process_fd (CG.get_ordered_fd ());
  AP.clear_info ();
  List.iter add_choice !candidate

(* HA version 3. end *)

(* PS version 4. 'structure access pattern' revisited with bottom-up manner *)

let find_repeatedly_used (file: C.file) : unit =
  let module PS : T.RE_SIG with type t = C.compinfo =
    struct
      let rec struct_access (lh, lo) =
        match lo with
        | C.Field (fi, off) ->
          if SS.mem fi.C.fcomp !selection
          then T.conc (T.Cons [fi.C.fcomp]) (struct_access (lh, off))
          else T.Empty
        | _ -> T.Empty
    
      type t = C.compinfo
      let compare c1 c2 = Pervasives.compare c1.C.ckey c2.C.ckey
      let str_of_t (c: t) = c.C.cname
      let read_access  = struct_access
      let write_access = struct_access
    end
  in 
  let module AP = P_automata.Make(PS) in
  let module CG = Rtfa_cg in
  let final = ref [] in
  let process_fd (fd: C.fundec) : unit =
    let cur = AP.find_closure fd in
    if fd.C.svar.C.vname = "main" then final := cur
  in
  CG.make_callgraph file;
  List.iter process_fd (CG.get_ordered_fd ());
  selection := SS.empty;
  List.iter add_choice !final

(* PS version 4. end *)

(* PS version 3.1.

let is_repeatedly_used (file: C.file) (c: C.compinfo) : bool =
  let module PS: T.RE_SIG with type t = C.fieldinfo =
    struct
      let rec field_access (c: C.compinfo) (lh, lo) =
        match lo with
        | C.Field (fi, off) ->
          if fi.C.fcomp.C.cname = c.C.cname then
            T.conc (T.Cons [fi]) (field_access c (lh, off))
          else T.Empty
        | _ -> T.Empty
      
      type t = C.fieldinfo
      let compare f1 f2 = Pervasives.compare f1.C.fname f2.C.fname
      let str_of_t (f: t) = f.C.fname
      let read_access  = (field_access c)
      let write_access = (field_access c)
    end
  in

  let module AP = P_automata.Make(PS) in
  let main_info = ref false in
  let process_fd (fd: C.fundec) : unit =
    let cur = AP.has_closure fd in
    if fd.C.svar.C.vname = "main" then main_info := cur
  in
  List.iter process_fd (CG.get_ordered_fd ());
  AP.clear_info ();
  !main_info

PS version 3.1. end *)

(* PS version 2. & 3.

let find_repeated (file: C.file) (c: C.compinfo) : unit =
  let module PS: T.RE_SIG with type t = C.fieldinfo =
    struct
      let rec field_access (c: C.compinfo) (lh, lo) =
        match lo with
        | C.Field (fi, off) ->
          if fi.C.fcomp.C.cname = c.C.cname then
            T.conc (T.Cons [fi]) (field_access c (lh, off))
          else T.Empty
        | _ -> T.Empty
      
      type t = C.fieldinfo
      let compare f1 f2 = Pervasives.compare f1.C.fname f2.C.fname
      let str_of_t (f: t) = f.C.fname
      let read_access  = (field_access c)
      let write_access = (field_access c)
    end
  in

(* PS version 2. using each 'field access pattern' of structure

  let module AP = Accesspattern.Make(PS)
  in
  AP.inter_pattern file;

  let g_ap = ref T.Empty in
  let find_main = function
    | C.GFun (fd, _) ->
      if fd.C.svar.C.vname = "main" then g_ap := AP.intra_pattern fd
    | _ -> ()
  in
  C.iterGlobals file find_main;

  let rec find_closure = function
    | T.Empty
    | T.Cons _ -> false
    | T.Conc  rl
    | T.Alter rl -> stop_true rl
    | T.Star _ -> true
  and stop_true = function
    | [] -> false
    | hd :: tl -> if find_closure hd then true else stop_true tl
  in
  if find_closure !g_ap then add_choice c

PS version 2. end *)

(* PS version 3. bottom-up approach (during building ap) *)

  let module AP = P_automata.Make(PS) in
  let main_info = ref false in
  let process_fd (fd: C.fundec) : unit =
    let cur = AP.has_closure fd in
    if fd.C.svar.C.vname = "main" then main_info := cur
  in
  List.iter process_fd (CG.get_ordered_fd ());
  AP.clear_info ();

  if !main_info then add_choice c

(* PS version 3. end *)

PS version 2. & 3. end *)

(* HA version 1 & 2.

(* to filter out which types are not heap-allocated *)
let is_heap_allocated (file: C.file) (c: C.compinfo) : bool =
(* HA version 2. find repeated alloc. call *)

  let module HA: T.RE_SIG with type t = C.fieldinfo =
    struct
      type t = C.fieldinfo
      let compare f1 f2 = Pervasives.compare f1.C.fname f2.C.fname
      let str_of_t (f: t) = f.C.fname
      let read_access  = fun _ -> T.Empty
      let write_access = fun _ -> T.Empty
    end
  in

  let module AP = M_automata.Make(HA) in
  let main_info = ref false in
  let process_fd (fd: C.fundec) : unit =
    let cur = AP.is_heap_allocated fd in
    if fd.C.svar.C.vname = "main" then main_info := cur
  in
  S.set_target_struct c;
  List.iter process_fd (CG.get_ordered_fd ());
  AP.clear_info ();
  !main_info

(* HA version 2. end *)

(* HA version 1. just find alloc. function

  let rec find_block (b: C.block) : bool =
    List.fold_left find_stmt false b.C.bstmts
  and find_stmt acc (s: C.stmt) : bool =
    if acc then acc else
    match s.C.skind with
    | C.Instr il -> List.fold_left find_instr false il
    | C.If (_,tb,fb,_) -> (find_block tb) || (find_block fb)
    | C.Switch _ -> raise (T.AP_Fatal "Switch: CFG need to be made")
    | C.Loop (b,_,_,_)
    | C.Block b -> find_block b
    | _ -> false
  and find_instr acc (i: C.instr) =
    if acc then acc else
    match i with
    | C.Call (_,fe,args,_) ->
      (
        match fe with
        | C.Lval (C.Var fn, C.NoOffset) ->
          (
            if List.mem fn.C.vname S.alloc_names then
            (
              if (List.length args) < 1 then false
              else find_exp (List.hd args)
            )
            else false
          )
        | _ -> false
      )
    | _ -> false
  and find_exp = function
    | C.SizeOf t -> is_target_type t
    | C.SizeOfE (C.Lval lv) -> is_target_type (C.typeOfLval lv)
    | _ -> false
  and is_target_type t =
    match C.unrollType t with
    | C.TComp (c',_) -> c'.C.ckey = c.C.ckey
    | _ -> false
  in

  let fold_func acc (g: C.global) : bool =
    if acc then acc else
    match g with
    | C.GFun (fd,_) -> find_block fd.C.sbody
    | _ -> false
  in
  C.foldGlobals file fold_func false

HA version 1. end *)

HA version 1 & 2. end *)

(*----------------------------------------------------------------------*)
(* Pool Selection Interface                                             *)
(*----------------------------------------------------------------------*)

(* select: C.file -> string *)
let rec select (file: C.file) : string =
(* PS version 3. bottom-up using 'field access pattern' of each structure

  let struct_cnt = ref (Num.num_of_int 0)
  and n_1 = Num.num_of_int 1 in

  let find_structure = function
    | C.GCompTag     (c,_)
    | C.GCompTagDecl (c,_) ->
      struct_cnt := Num.add_num !struct_cnt n_1;
      find_repeated file c
    | C.GType (ti,_) -> (* typedef *)
      (
        match C.unrollType ti.C.ttype with
        | C.TComp (c,_) -> find_repeated file c
        | _ -> ()
      )
    | _ -> ()
  in
  CG.make_callgraph file;
  C.iterGlobals file find_structure;
  if !S.info then
  (
    print_newline ();
    ignore (Pretty.printf "# struct: %d\n\n" (Num.int_of_num !struct_cnt));
  );

PS version 3. end *)

(* PS version 1. using 'structure access patterns' - scalability problem

  let module PS : T.RE_SIG with type t = C.compinfo =
    struct
      let rec struct_access (lh, lo) =
        match lo with
        | C.Field (fi, off) ->
          T.conc (T.Cons [fi.C.fcomp]) (struct_access (lh, off))
        | _ -> T.Empty
    
      type t = C.compinfo
      let str_of_t (c: t) = c.C.cname
      let read_access  = struct_access
      let write_access = struct_access
    end
  in 
  let module AP = Accesspattern.Make(PS)
  in
  AP.inter_pattern file;

  let g_ap = ref T.Empty in
  let find_main = function
    | C.GFun (fd,_) ->
      if fd.C.svar.C.vname = "main" then g_ap := AP.intra_pattern fd
    | _ -> ()
  in
  C.iterGlobals file find_main;

  let rec find_closure (flag: bool) = function
    | T.Empty -> ()
    | T.Cons elts -> if flag then List.iter add_choice elts
    | T.Conc  rl
    | T.Alter rl -> List.iter (find_closure flag) rl
    | T.Star re' -> find_closure true re'
  in
  find_closure false !g_ap;

PS version 1. end *)

(* HA version 3. & PS version 3.1. *)

  let struct_cnt = ref (Num.num_of_int 0)
  and n_1 = Num.num_of_int 1 in

  let find_structure = function
    | C.GCompTag     (c,_)
    | C.GCompTagDecl (c,_) -> struct_cnt := Num.add_num !struct_cnt n_1
    | _ -> ()
  in
  CG.make_callgraph file;
  C.iterGlobals file find_structure;
  if !S.info then
  (
    print_newline ();
    ignore (Pretty.printf "# struct: %d\n\n" (Num.int_of_num !struct_cnt));
  );

  find_heap_allocated file;

(* HA version 3. & PS version 3.1. end *)

  let c_lst     = SS.elements !selection in
  let c_cnt     = List.length c_lst
  and candidate = make_str c_lst in
  if !S.info then
  (
    ignore (Pretty.printf "candidate: %s (%d)\n\n" candidate c_cnt);
    flush stdout
  );

(* PS version 3. & HA version 2.

  selection := SS.filter (is_heap_allocated file) !selection;

PS version 3. & HA version 2. end *)

(* PS version 3.1.

  selection := SS.filter (is_repeatedly_used file) !selection;

PS version 3.1. end *)

  find_repeatedly_used file;

  let f_lst = SS.elements !selection in
  let f_cnt = List.length f_lst
  and final = make_str f_lst in
  if !S.info then
  (
    ignore (Pretty.printf "final: %s (%d)\n\n" final f_cnt);
    flush stdout
  );
  final

and make_str = function
  | [] -> ""
  | hd :: [] -> hd.C.cname
  | hd :: tl -> hd.C.cname ^ "/" ^ (make_str tl)

