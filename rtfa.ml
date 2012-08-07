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
module Rt = Rtfa_types
module P  = Poolselection
module A  = Affinity
module T  = Transformer
module Ma = M_automata
module Pa = P_automata
module Fa = F_automata

let t_struct_str = ref ""
let affinity_str = ref ""
let wrapper_str  = ref ""

module PTA = Ptranal

let main (file: C.file) =
  (* control-flow graphs *)
  if not !(Cilutil.makeCFG) then
  (
    ignore (Partial.calls_end_basic_blocks file);
    ignore (Partial.globally_unique_vids file);
    let gfun (g: C.global) : unit =
      match g with
      | C.GFun (fd,_) ->
        C.prepareCFG fd; ignore (C.computeCFGInfo fd true)
      | _ -> ()
    in
    C.iterGlobals file gfun;
  );
  (* points-to analysis *)
  if not !(PTA.feature.C.fd_enabled) then
    Stats.time "pointer analysis" (PTA.feature.C.fd_doit) file;

  (* turn on interprocedural access pattern *)
  Rt.ap_inter := true;
    
  if !t_struct_str = "" then
  (
    t_struct_str := Stats.time "pool selection" P.select file;
    if !t_struct_str = "" then (* no candidate *)
    (
      Stats.print stdout "";
      flush stdout;
      exit 0
    )
  ) else ignore (Stats.time "pool selection" P.select file);

  let s_list = ref ([]: string list)
  and tmp1 = ref "" in
  let iterator (l: string list ref) (s: string ref) (c: char) : unit =
    if c <> '/' then s := !s ^ (String.make 1 c)
    else ( l := !l @ [!s]; s := "" )
  in
  Stream.iter (iterator s_list tmp1) (Stream.of_string !t_struct_str);
  (* for last token *)
  s_list := !s_list @ [!tmp1];

  let count = ref 0 in
  String.iter (fun c -> if c = '/' then incr count) !t_struct_str;
  if !wrapper_str = "" then wrapper_str := String.make !count '/';

  let comp_finder (sname: string) : C.compinfo =
    let t_comp = ref (C.mkCompInfo true sname (fun _ -> []) []) in
    let rec finder acc = function
      | C.GCompTag     (c,_)
      | C.GCompTagDecl (c,_) ->
        if c.C.cname = sname then (t_comp := c; false) else acc
      | C.GType (ti,_) -> (* typedef *)
        (
          if ti.C.tname = sname then
          (
            match C.unrollType ti.C.ttype with
            | C.TComp (c,_) -> (t_comp := c; false)
            | _ -> acc
          ) else acc
        )
      | _ -> acc
    in
    if C.foldGlobals file finder true then
    (
      print_endline ("target struct is not defined: "^sname);
      raise S.UnknownStruct
    );
    !t_comp
  in
  if !affinity_str = "" then
  (
    let t_comp_lst = List.map comp_finder !s_list in
    affinity_str := Stats.time "field affinity" (A.analyze file) t_comp_lst
  );

  let a_list = ref ([]: string list)
  and w_list = ref ([]: string list)
  and tmp2 = ref "" and tmp3 = ref ""
  in
  Stream.iter (iterator a_list tmp2) (Stream.of_string !affinity_str);
  Stream.iter (iterator w_list tmp3) (Stream.of_string !wrapper_str);
  a_list := !a_list @ [!tmp2];
  w_list := !w_list @ [!tmp3];

  if (List.length !s_list) != (List.length !a_list) then
  (
    print_endline "# of struct != # of affinity";
    exit 0
  );

  let work (sname: string) (affinity: string) (wrapper: string) : unit =
    affinity_str := affinity;
    let t_comp = comp_finder sname in 

    let module PR = Pretty in
    if !affinity_str = "" then 
      affinity_str := Stats.time "field affinity" (A.analyze1 file) t_comp;
    if !S.info then
    (
      ignore (PR.printf "[FA] %s\n" t_comp.C.cname);
      ignore (PR.printf "<analyzed affinity> %s\n" !affinity_str);
    );
    S.set_target_struct t_comp;
    S.set_affinity_str !affinity_str;
    S.prepare ();
    try
    (
      ignore (S.get_max_obj_cnt ());
      let cm = Ma.is_calloced sname in
      Stats.time "transform" (T.transform file sname wrapper) cm;
      if !S.info then print_newline ()
    )
    with S.Inconsistent _ ->
    (
      ignore (PR.printf "\"%s\" is greater than pool\n" t_comp.C.cname);
      print_newline ()
    )
  in
  let rec iter3 (f: 'a -> 'a -> 'a -> unit) l1 l2 l3 =
    match l1, l2, l3 with
    | [], [], [] -> ()
    | h1::t1, h2::t2, h3::t3 -> (f h1 h2 h3); (iter3 f t1 t2 t3)
    | _ -> raise (Invalid_argument "struct, affinity, wrapper degree !=")
  in
  iter3 work !s_list !a_list !w_list;

  (* temporary expedient *)
  let temp_exp = "./test.rtfa.c" in
  let rtfa_out = open_out temp_exp
  in
  C.dumpFile C.defaultCilPrinter rtfa_out temp_exp file;

  Stats.print stdout "";
  flush stdout

let doRTFA = ref false

let feature : C.featureDescr =
{
  C.fd_name = "rtfa";
  C.fd_enabled = doRTFA;
  C.fd_description = "Remapping Transformer for Field Affinity";
  C.fd_extraopt =
  [
    ("--struct", Arg.String (fun str -> t_struct_str := str),
     "<target_struct>: name of target struct");
    ("--affinity", Arg.String (fun str -> affinity_str := str),
     "<affinity>: field affinity (e.g. key,next:data:dummy)");
    ("--wrapper", Arg.String (fun str -> wrapper_str := str),
     "<wrapper>: factory function (e.g. mymalloc)");
    ("--pool_size", Arg.Int (fun i -> S.pool_size := i),
     "<pool_size>: pool size (default: 2048)");
    ("--cache_line", Arg.Int (fun i -> A.cache_line_size := i),
     "<cache_line>: cache line size (default: 128)");
    ("--repeat", Arg.Int (fun i -> A.repeat := i),
     "<repeat>: for the RE's * feature (defaut: 1000)");
(*
    ("--simulate", Arg.Unit (fun _ -> A.simulate := true),
     "<simulate>: interpret re with a simulation method");
*)
    ("--pool_only", Arg.Unit (fun _ -> A.pool_only := true),
     "<pool_only>: pool only(no grouping), but reordering may be done");
    ("--no_reorder", Arg.Unit (fun _ -> A.no_reorder := true),
     "<no_reoreder>: pool only(no grouping), no reordering either");
    ("--one_pass_fa", Arg.Unit (fun _ -> A.one_pass := true),
     "<one_pass_fa>: one-pass field affinity calculation");
    ("--bin_packing", Arg.Unit (fun _ -> A.bin_packing := true),
     "<bin_packing>: enable bin packing algorithm");
    ("--no_compact", Arg.Unit (fun _ -> S.no_compact := true),
     "<no_compact>: no compaction, padding bits will be attached");
    ("--loop_only_pool", Arg.Unit (fun _ -> Pa.loop_only := true),
     "<loop_only_pool>: pool selection uses only loop-nest info");
    ("--loop_only_fa", Arg.Unit (fun _ -> Fa.loop_only := true),
     "<loop_only_fa>: field affinity uses only loop-nest info");
    ("--wo_calloc", Arg.Unit (fun _ -> Ma.wo_calloc := true),
     "<wo_calloc>: without calloc");
    ("--rtfa_info", Arg.Unit (fun _ -> S.info := true),
     "<rtfa_info>: basic info about pool selection and field affinity");
    ("--pattern_debug", Arg.Unit (fun _ -> Rt.ap_debug := true),
     "<pattern_debug>: debugging while access pattern generation");
    ("--affinity_debug", Arg.Unit (fun _ -> A.debug := true),
     "<affinity_debug>: debugging while affinity analysis");
  ];
  C.fd_doit = main;
  C.fd_post_check = true;
}

