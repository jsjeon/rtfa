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
module S = Struct
module C = Cil

(*----------------------------------------------------------------------*)
(* Basic Types for AP's own Call Graph                                  *)
(*----------------------------------------------------------------------*)

module StrKey =
struct
  type t = string
  let compare = Pervasives.compare
end

module SS = Set.Make(StrKey)

type visit = White | Gray | Black

type node = {
  n_fn: string;
  mutable n_visited: visit;
  mutable n_fd: C.fundec option;
  mutable n_preds: SS.t;
  mutable n_succs: SS.t;
}

(*----------------------------------------------------------------------*)
(* Basic Elements                                                       *)
(*----------------------------------------------------------------------*)

module H = Hashtbl

let node_hash : (string, node) H.t = H.create 31

let find_node (fn: string) : node =
  try H.find node_hash fn
  with Not_found -> raise (T.AP_Fatal "find_node")

(*----------------------------------------------------------------------*)
(* Utilities for Call Graph Generation                                  *)
(*----------------------------------------------------------------------*)

let new_node (fn: string) (fdo: C.fundec option) : unit =
  try 
    let node = find_node fn in
    if node.n_fd = None then node.n_fd <- fdo
  with T.AP_Fatal _ ->
  (
    let node = {
      n_fn = fn;
      n_visited = White;
      n_fd = fdo;
      n_preds = SS.empty;
      n_succs = SS.empty;
    } in
    H.add node_hash fn node
  )

let add_call (caller: string) (callee: string) : unit =
  try
  (
    let caller_n = find_node caller
    and callee_n = find_node callee
    in
    caller_n.n_succs <- SS.add callee caller_n.n_succs;
    callee_n.n_preds <- SS.add caller callee_n.n_preds
  )
  with T.AP_Fatal _ -> ()

(*----------------------------------------------------------------------*)
(* Call Graph Generation                                                *)
(*----------------------------------------------------------------------*)

let current_fn = ref ""

let rec make_cg_block (b: C.block) : unit =
  List.iter make_cg_stmt b.C.bstmts

and make_cg_stmt (s: C.stmt) : unit =
  match s.C.skind with
  | C.Instr il -> List.iter make_cg_instr il
  | C.If (_,tb,fb,_) -> (make_cg_block tb; make_cg_block fb)
  | C.Switch _ -> raise (T.AP_Fatal "Switch: CFG need to be made")
  | C.Loop (b,_,_,_)
  | C.Block b -> make_cg_block b
  | _ -> ()

and make_cg_instr (i: C.instr) : unit =
  match i with
  | C.Call (_,fn,_,_) ->
    (
      match fn with
      | C.Lval (C.Var vi, C.NoOffset) -> add_call !current_fn vi.C.vname
      | C.Lval (C.Mem ex, C.NoOffset) ->
        let fd_iter (fd: C.fundec) : unit =
          add_call !current_fn fd.C.svar.C.vname
        in
        List.iter fd_iter (Ptranal.resolve_funptr ex)
      | _ -> raise (T.AP_Fatal "Call: other cases?")
    )
  | _ -> ()

(* make_callgraph: Cil.file -> unit *)
let make_callgraph (file: C.file) : unit = 
  let make_node (g: C.global) : unit =
    match g with
    | C.GFun (fd,_) -> new_node fd.C.svar.C.vname (Some fd)
    | C.GVarDecl (vi,_) ->
      if C.isFunctionType vi.C.vtype then new_node vi.C.vname None
    | _ -> ()
  in
  H.clear node_hash;
  C.iterGlobals file make_node;

  let make_cg (g: C.global) : unit =
    match g with
    | C.GFun (fd,_) ->
      (
        current_fn := fd.C.svar.C.vname;
        make_cg_block fd.C.sbody
      )
    | _ -> ()
  in
  C.iterGlobals file make_cg

(*----------------------------------------------------------------------*)
(* Reverse Topological Ordering                                         *)
(*----------------------------------------------------------------------*)

let remove_call (caller: string) (callee: string) : unit =
  let caller_n = find_node caller
  and callee_n = find_node callee
  in
  caller_n.n_succs <- SS.remove callee caller_n.n_succs;
  callee_n.n_preds <- SS.remove caller callee_n.n_preds

let rec dfs (n: node) : unit =
  n.n_visited <- Gray;
  let find_back_edge (succ: string) : unit =
    let succ_n = find_node succ in
    if succ_n.n_visited = Gray then (* back-edge! *)
    (
      if !S.info then
      (
        if succ_n.n_fn = n.n_fn then
          ignore (Pretty.printf "self-edge: %s\n" n.n_fn)
        else
          ignore (Pretty.printf "back-edge: %s -> %s\n" n.n_fn succ_n.n_fn)
      );
      remove_call n.n_fn succ
    )
  in
  SS.iter find_back_edge n.n_succs;

  let bfs (succ: string) : unit =
    let succ_n = find_node succ in
    if succ_n.n_visited = White then dfs succ_n
  in
  SS.iter bfs n.n_succs;
  n.n_visited <- Black

let remove_back_edge () : unit =
  let find_root _ (n: node) : unit =
    if not (n.n_visited = White) then ()
    else if SS.is_empty n.n_preds then dfs n
  in
  H.iter find_root node_hash

module Q = Queue

let worklist : node Q.t = Q.create ()

let eliminate_node (n: node) : unit =
  let remove_succ (pred: string) : unit =
    let pred_n = find_node pred
    in pred_n.n_succs <- SS.remove n.n_fn pred_n.n_succs
  in
  SS.iter remove_succ n.n_preds;

  let next_eliminate (pred: string) : unit =
    let pred_n = find_node pred in
    if pred = n.n_fn then () (* exclude self-edge *)
    else if SS.is_empty pred_n.n_succs then Q.push pred_n worklist
  in
  SS.iter next_eliminate n.n_preds;

  H.remove node_hash n.n_fn;
  n.n_preds <- SS.empty

let ordered_list = ref ([] : C.fundec list)

let make_ordering () : unit =
  remove_back_edge ();

  let find_leaf _ (n: node) : unit =
    if SS.is_empty n.n_succs then Q.push n worklist
  in
  H.iter find_leaf node_hash;

  ordered_list := [];
  while not (Q.is_empty worklist) do
    let node = Q.pop worklist
    in
    eliminate_node node;
    match node.n_fd with
    | Some fd -> ordered_list := fd :: !ordered_list
    | None    -> ()
  done

(* get_ordered_fd: unit -> Cil.fundec list *)
let get_ordered_fd () : C.fundec list =
  if !ordered_list = [] then make_ordering ();

  let reversed = List.rev !ordered_list
  and fd_printer (fd: C.fundec) : unit =
    ignore (Pretty.printf "%s " fd.C.svar.C.vname)
  in
  if !T.ap_debug then 
  (
    print_endline "= reverse topological Call Order =";
    List.iter fd_printer reversed;
    print_newline ()
  );
  reversed

