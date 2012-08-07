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
module S = Struct
module T = Rtfa_types

(*----------------------------------------------------------------------*)
(* Basic Types for Temporal Relationship Graph                          *)
(*----------------------------------------------------------------------*)

module IntKey =
struct
  type t = int
  let compare = Pervasives.compare
end

module IM = Map.Make(IntKey)

module N = Num

let n_0 = N.num_of_int 0
let n_1 = N.num_of_int 1

type group = {
  g_id: int;
  mutable g_names: string list;
  mutable g_size: int;
  mutable g_edges: N.num IM.t;
  mutable g_placed: bool;
}

let graph_printer i group = (* for debugging *)
  ignore (Pretty.printf "[%d] " group.g_id);
  List.iter (fun fn -> ignore (Pretty.printf "%s " fn)) group.g_names;
  print_newline ();
  let edge_printer i' cnt =
    ignore (Pretty.printf "  to %d (%s)\n" i' (N.string_of_num cnt))
  in
  IM.iter edge_printer group.g_edges

(*----------------------------------------------------------------------*)
(* Temporal Relationship Graph with Self edge                           *)
(*----------------------------------------------------------------------*)

module IH = Inthash

let strg = IH.create 7

let find_group (g_id: int) : group =
  try IH.find strg g_id
  with Not_found -> raise (S.Inconsistent "STRG: find_group")

module StrKey =
struct
  type t = string
  let compare = Pervasives.compare
end

module SM = Map.Make(StrKey)

let fn_id_map = ref SM.empty

let fn_to_id (fn: string) (id: int) : unit =
  fn_id_map := SM.add fn id !fn_id_map

let id_cnt = ref 0

let fresh_id () =
  incr id_cnt; !id_cnt

let find_id ?(size=0) (fn: string) : int =
  try SM.find fn !fn_id_map
  with Not_found ->
  (
    let id = fresh_id () in
    let g = {
      g_id = id;
      g_names = [fn];
      g_size = size;
      g_edges = IM.empty;
      g_placed = false;
    } in
    IH.add strg id g;
    fn_to_id fn id; id
  )

let add_count (id1: int) (id2: int) (n: N.num) : unit =
  let g1 = find_group id1
  and g2 = find_group id2 in
  try
  (
    let p1 = IM.find id2 g1.g_edges
    and p2 = IM.find id1 g2.g_edges in
    if not (N.eq_num p1 p2) then raise (S.Inconsistent "add: diff. w");
    g1.g_edges <- IM.add id2 (N.add_num n p1) g1.g_edges;
    g2.g_edges <- IM.add id1 (N.add_num n p2) g2.g_edges
  )
  with Not_found ->
  (
    g1.g_edges <- IM.add id2 n g1.g_edges;
    g2.g_edges <- IM.add id1 n g2.g_edges
  )

(*----------------------------------------------------------------------*)
(* Sliding window (cache line)                                          *)
(*----------------------------------------------------------------------*)

type window = (int * string) list (* pivot, field name *)

let cache_line_size = ref 64

let push_field (n: N.num) (w: window) (f: C.fieldinfo) : window =
try
  let size = C.bitsSizeOf (C.unrollType f.C.ftype) in
  let shift = List.map (fun (b, fn) -> (b - size, fn)) w in
  let new_window =
    let added = shift @ [(!cache_line_size - size, f.C.fname)] in
    if (fst (List.hd added)) < 0 then List.tl added else added
  in
  let rec except_last (f: 'a -> unit) = function
    |      [] -> ()
    | _ :: [] -> ()
    | h :: tl -> (f h; except_last f tl)
  in
  let fid = find_id ~size:size f.C.fname in
  let adder (_,fn) =
    add_count fid (find_id fn) n
  in
  except_last adder new_window; new_window
with Failure _ -> raise (S.Inconsistent "push_field: List manipulation")

(*----------------------------------------------------------------------*)
(* STRG Generation with RE count memoization (old version)              *)
(*----------------------------------------------------------------------*)

module H = Hashtbl

let re_cnt : (C.fieldinfo T.re, N.num) H.t = H.create 1537 (* memoization *)

let rec cnt_of_re (re: C.fieldinfo T.re) : N.num =
try match re with
  | T.Empty
  | T.Cons   _ -> n_1
  | T.Star re' -> cnt_of_re re'
  | _ -> H.find re_cnt re
with Not_found ->
(
  let cnt =
    match re with
    | T.Conc  rl -> List.fold_left 
      (fun a r' -> N.mult_num a (cnt_of_re r')) n_1 rl
    | T.Alter rl -> List.fold_left 
      (fun a r' -> N.add_num a (cnt_of_re r')) n_0 rl
    | _ -> raise (S.Inconsistent "cnt_of_re")
  in
  H.add re_cnt re cnt; cnt
)

let cur_rand = ref 0

let my_rand () : int =
  cur_rand := !cur_rand * 25713 + 1345;
  if !cur_rand < 0 then cur_rand := 0 - !cur_rand;
  !cur_rand

let repeat = ref 1000 (* for the RE's * feature *)

let rec simulate_re (cnt: N.num) (w: window) = function
  | T.Empty -> [w]
  | T.Cons elts -> [List.fold_left (push_field cnt) w elts]
  | T.Conc  rl ->
    (
      let remain = ref cnt in
      let folder acc r =
        remain := N.div_num !remain (cnt_of_re r);
        List.flatten (List.map (fun w' -> simulate_re !remain w' r) acc)
      in List.fold_left folder [w] rl
    )
  | T.Alter rl ->
    (
      List.fold_left (fun acc r -> 
        acc @ (simulate_re (N.mult_num cnt (cnt_of_re r)) w r)) [] rl
    )
  | T.Star re' ->
    (
      let cnt = N.mult_num cnt (N.num_of_int 10)
      and repeat = !repeat / 10 (* loop unrolling *)
      in 
      let ww = ref w in
      if N.eq_num (cnt_of_re re') n_1 then
        let ww = ref w in
        for i = 0 to repeat do
          ww := List.hd (simulate_re cnt !ww re')
        done
      else (* Oh god, #case is re' to repeat! i.e. re' ^ repeat *)
        for i = 0 to repeat do
          let next = simulate_re cnt !ww re' in
          ww := List.nth next ((my_rand ()) mod (List.length next))
        done;
      [!ww]
    )
  | T.Func _ -> raise (S.Inconsistent "simulate_re: Func")

(*----------------------------------------------------------------------*)
(* STRG Generation with Affine Equations                                *)
(*----------------------------------------------------------------------*)

module IS = Set.Make(IntKey)

let start_set = ref IS.empty

let rec affine_re (first: bool) (d: N.num) (w: N.num) (fs: IS.t) = function
  | T.Empty -> fs
  | T.Cons elts ->
    (
      try
        let start = add_relation w fs (List.hd elts) in
        if (List.length elts) > 2 then
          if first then start_set := IS.union !start_set start;
        List.fold_left (add_relation w) start (List.tl elts)
      with Failure _ -> (start_set := IS.union !start_set fs; fs)
    )
  | T.Conc  rl ->
    (
      try
        let fs' = affine_re first d w fs (List.hd rl) 
        in List.fold_left 
        (fun a r -> affine_re false d w a r) fs' (List.tl rl)
      with Failure _ -> raise (S.Inconsistent "affine_re:conc")
    )
  | T.Alter rl -> List.fold_left
    (fun a r -> IS.union a (affine_re first d w fs r)) IS.empty rl
  | T.Star re' ->
    (
      let d' = N.add_num d n_1 in
      let w' = make_real_w d' w in
      start_set := IS.empty;
      let last_set = affine_re true d' w' IS.empty re' in
      let adder (start: int) : unit =
        let adder2 (last: int) : unit =
          add_count last start w'
        in
        IS.iter adder2 last_set;
        let adder3 (prev: int) : unit =
          add_count prev start w 
        in
        IS.iter adder3 fs
      in
      IS.iter adder !start_set; last_set
    )
  | T.Func _ -> raise (S.Inconsistent "affine_re: Func")

and make_real_w (depth: N.num) (w: N.num) : N.num =
  let r_to_d = N.power_num (N.num_of_int !repeat) depth
  in N.mult_num w r_to_d

and add_relation (cnt: N.num) (fs: IS.t) (f: C.fieldinfo) : IS.t =
  let size = C.bitsSizeOf (C.unrollType f.C.ftype) in
  let fid = find_id ~size:size f.C.fname in
  let adder (last: int) : unit =
    add_count fid last cnt
  in
  IS.iter adder fs; IS.singleton fid

let debug    = ref false
let simulate = ref false (* simulation based interpreting or not *)

let interpret_re (re: C.fieldinfo T.re) : unit =
  if !simulate then
  (
    let cnt = cnt_of_re re in
    if !debug then
    (
      ignore (Pretty.printf "#case: %s\n" (N.string_of_num cnt));
      flush stdout
    );
    match re with
    | T.Alter _ -> ignore (simulate_re n_1 [] re)
    | _ -> ignore (simulate_re cnt [] re)
  )
  else
    ignore (affine_re false n_0 n_1 IS.empty re)

(*----------------------------------------------------------------------*)
(* STRG Grouping                                                        *)
(*----------------------------------------------------------------------*)

let remove_count (id1: int) (id2: int) : unit =
  let g1 = find_group id1
  and g2 = find_group id2 in
  try
  (
    let p1 = IM.find id2 g1.g_edges
    and p2 = IM.find id1 g2.g_edges in
    if not (N.eq_num p1 p2) then raise (S.Inconsistent "rm: diff. w");
    g1.g_edges <- IM.remove id2 g1.g_edges;
    if id1 <> id2 then g2.g_edges <- IM.remove id1 g2.g_edges
  )
  with Not_found -> ()

let find_count (id1: int) (id2: int) : N.num =
  let g1 = find_group id1 in
  try IM.find id2 g1.g_edges with Not_found -> n_0

module Edge =
struct
  type t = N.num * int * int
  let compare (w1,s1,e1) (w2,s2,e2) =
    let r = N.compare_num w1 w2 in
    if r = 0 then Pervasives.compare (s1,e1) (s2,e2) else r
end

module ES = Set.Make(Edge)

let edge_set = ref ES.empty

let add_edge_set (w: N.num) (src: int) (dst: int) : unit =
  if src = dst then ()
  else if src < dst then 
    edge_set := ES.add (w,src,dst) !edge_set
  else 
    edge_set := ES.add (w,dst,src) !edge_set

let remove_edge_set (w: N.num) (src: int) (dst: int) : unit =
  if src < dst then 
    edge_set := ES.remove (w,src,dst) !edge_set
  else 
    edge_set := ES.remove (w,dst,src) !edge_set

let bin_packing = ref false

let grouping () : unit =
  let edge_set_maker (src: int) (g: group) : unit =
    let maker (dst: int) (w: N.num) : unit = add_edge_set w src dst
    in IM.iter maker g.g_edges
  in
  IH.iter edge_set_maker strg;

  let size_affected_w (wx, xs) (wy, ys) : N.num =
    let nxs = N.num_of_int xs
    and nys = N.num_of_int ys in
    let x_s = N.div_num nxs (N.add_num nxs nys)
    and y_s = N.div_num nys (N.add_num nxs nys) in
    N.add_num (N.mult_num wx x_s) (N.mult_num wy y_s)
  in
  let change = ref true in
  let fg = (* first group *)
    ref {
      g_id = 0;
      g_names = [];
      g_size = 0;
      g_edges = IM.empty;
      g_placed = false;
    }
  in
  let workhorse () : unit =
    let rec find_target_group = function
      | [] -> ()
      | (w,src,dst) :: tl ->
        (
          let change2 = ref false in

          let src_g = find_group src
          and dst_g = find_group dst
          and ws = find_count src src
          and wd = find_count dst dst in
          let ww = size_affected_w (ws,src_g.g_size) (wd,dst_g.g_size)
          in

          if N.le_num w ww then find_target_group tl
          else (* w > ws + wd grouping condition *)
          (
            let rec is_2_powered (k: int) : bool =
              if k < 0 then is_2_powered (0 - k)
              else if k <= 2 then true (* include an equal case *)
              else if (k mod 2) <> 0 then false
              else is_2_powered (k / 2)
            in

            if not !bin_packing then change2 := true
            else if (!fg).g_id = 0 then change2 := true (* exception *)
            else
            (
              (*
              if (!fg).g_id = src_g.g_id then change2 := true
              else if (!fg).g_id = dst_g.g_id then change2 := true
              else
              (
              *)
              let bin = (!fg).g_size
              and a = src_g.g_size
              and b = dst_g.g_size
              in
              if is_2_powered (a + b - bin) then change2 := true
              (*
              )
              *)
            );

            if !change2 then (* after size-effect considered *)
            (
              change := true;

              remove_count src src;
              remove_count dst dst;
              remove_count src dst;
              remove_edge_set w src dst;

              let head = if N.lt_num ws wd then dst else src
              and tail = if N.lt_num ws wd then src else dst
              and wn = N.add_num w ww
              in (* new weight for group : ws + w + wd *)
              add_count head head wn;

              let hg = find_group head
              and tg = find_group tail
              in
              let compensate (id: int) (g: group) : unit =
                if id = head || id = tail then () else
                (
                  let wh = find_count id head
                  and wt = find_count id tail in
                  let wn = size_affected_w (wh,hg.g_size) (wt,tg.g_size)
                  in (* new weight for others : wh + wt *)
                  remove_count id head;
                  remove_count id tail;
                  remove_edge_set wh id head;
                  remove_edge_set wt id tail;

                  if (N.sign_num wn) = 1 then
                  (
                    add_count id head wn;
                    add_edge_set wn id head
                  )
                )
              in 
              IH.iter compensate strg;
              hg.g_names <- hg.g_names @ tg.g_names;
              hg.g_size <- hg.g_size + tg.g_size;

              if (!fg).g_id = 0 then fg := hg (* not yet defined *)
              else if (!fg).g_id = hg.g_id || (!fg).g_id = tg.g_id then
                fg := hg; (* have been involved *)

              IH.remove strg tail
            )
          )
        )
    and edge_list = List.rev (ES.elements !edge_set)
    in
    find_target_group edge_list
  in
  while !change do
    change := false;
    workhorse ();
    if !debug then (IH.iter graph_printer strg; print_newline ())
  done

(*----------------------------------------------------------------------*)
(* Finding Affinity String                                              *)
(*----------------------------------------------------------------------*)

let pool_only  = ref false
let no_reorder = ref false

(* affinity: key,next:data:dummy *)
let affinity_str () : string =
  let max_self = ref n_0
  and max_self_id = ref min_int in
  let max_esum = ref n_0
  and max_esum_id = ref min_int in
  let max_finder (id: int) (g: group) : unit =
    let self = find_count id id in
    if N.gt_num self !max_self then
    (
      max_self := self;
      max_self_id := id
    );
    let esum = IM.fold (fun _ n acc -> N.add_num n acc) g.g_edges n_0 in
    if N.gt_num esum !max_esum then
    (
      max_esum := esum;
      max_esum_id := id
    )
  in
  IH.iter max_finder strg;

  let affinity = ref "" in
  let rec placing (id: int) : unit =
    let g = find_group id in
    let rec internal_group = function
      |       [] -> ""
      | hd :: [] -> hd
      | hd :: tl -> hd ^ "," ^ (internal_group tl)
    in
    affinity := !affinity ^ (internal_group g.g_names);
    g.g_placed <- true;

    let edge_list = IM.fold (fun i cnt acc -> (i,cnt)::acc) g.g_edges [] in
    let edge_compare (i1,cnt1) (i2,cnt2) =
      let self1 = find_count i1 i1
      and self2 = find_count i2 i2 in
      let r = N.compare_num self2 self1 in
      if r = 0 then N.compare_num cnt2 cnt1 else r
    in
    let sorted_edges = List.stable_sort edge_compare edge_list in
    
    let rec find_next = function
      | [] -> ()
      | (i,_) :: tl ->
        (
          let gi = find_group i in
          if gi.g_placed || i = id then find_next tl
          else
          (
            if (not !pool_only) then affinity := !affinity ^ ":"
            else affinity := !affinity ^ ",";
            placing i;
            find_next tl
          )
        )
    in
    find_next sorted_edges
  in
  if !max_self_id <> min_int then placing !max_self_id
  else if !max_esum_id <> min_int then placing !max_esum_id;

  let remove_remainder _ (g: group) : unit =
    if not g.g_placed then
    (
      let remover fn =
        fn_id_map := SM.remove fn !fn_id_map
      in
      List.iter remover g.g_names
    )
  in
  IH.iter remove_remainder strg;
  
  !affinity

(*----------------------------------------------------------------------*)
(* Affinity Interface                                                   *)
(*----------------------------------------------------------------------*)

let one_pass = ref false

(* analyze : Cil.file -> C.compinfo list -> string *)
let rec analyze (file: C.file) (cl: C.compinfo list) : string =
  if not !one_pass then
    String.make ((List.length cl) - 1) '/'
  else
  ( (* FA version 3. 1-pass bottom-up approach  *)

    (* initialization *)
    IH.clear strg;
    id_cnt := 0;
    fn_id_map := SM.empty;

    let module FA : T.RE_SIG with type t = C.compinfo * C.fieldinfo =
      struct
        let rec field_access (lh, lo) =
          match lo with
          | C.Field (fi, off) ->
            if List.mem fi.C.fcomp cl
            then T.conc (T.Cons [(fi.C.fcomp,fi)]) (field_access (lh, off))
            else T.Empty
          | _ -> T.Empty

        type t = C.compinfo * C.fieldinfo
        let compare (c1,f1) (c2,f2) =
          let r = Pervasives.compare c1.C.ckey c2.C.ckey in
          if r <> 0 then r else Pervasives.compare f1.C.fname f2.C.fname
        let str_of_t (c, f) = c.C.cname^"."^f.C.fname
        let read_access  = field_access
        let write_access = field_access
      end
    in

    let module AP = F_automata.Make(FA) in
    let module CG = Rtfa_cg in
    let main_info = ref (AP.empty_info ()) in
    let process_fd (fd: C.fundec) : unit =
      let cur = AP.local_affinity ~entire:true fd in
      if fd.C.svar.C.vname = "main" then main_info := cur
    in
    CG.make_callgraph file;
    List.iter process_fd (CG.get_ordered_fd ());
 
    let core = AP.get_core !main_info in
    let rec str_maker acc = function
      | [] -> acc
      | c :: tl ->
        (
          IH.clear strg;
          id_cnt := 0;
          fn_id_map := SM.empty;
      
          let selective_concretize ((c1,f1), (c2,f2), w_lst) =
            if c1.C.cname = c.C.cname && c2.C.cname = c.C.cname then
              concretize_core (f1,f2,w_lst)
          in
          if (not !pool_only) || (not !no_reorder) then
            List.iter selective_concretize core;
        
          if acc <> "" then str_maker (acc^"/"^(make_affinity_str c)) tl
          else str_maker (make_affinity_str c) tl
        )
    in
    let final_affinity = str_maker "" cl in
    AP.clear_info ();
    final_affinity
  ) (* FA version 3. end *)

(* analyze1 : Cil.file -> C.compinfo -> string *)
and analyze1 (file: C.file) (c: C.compinfo) : string =
  (* initialization *)
  IH.clear strg;
  id_cnt := 0;
  fn_id_map := SM.empty;

  let module FA : T.RE_SIG with type t = C.fieldinfo =
    struct
      let rec field_access (lh, lo) =
        match lo with
        | C.Field (fi, off) -> 
          if fi.C.fcomp.C.cname = c.C.cname then
            T.conc (T.Cons [fi]) (field_access (lh, off))
          else T.Empty
        | _ -> T.Empty

      type t = C.fieldinfo
      let compare f1 f2 = Pervasives.compare f1.C.fname f2.C.fname
      let str_of_t (f: t) = f.C.fname
      let read_access  = field_access
      let write_access = field_access
    end
  in

(* FA version 1. top-down approach (using full ap) - scalability problem

  let module AP = Accesspattern.Make(FA)
  in
  AP.inter_pattern file;

  let g_ap = ref T.Empty in
  let find_main = function
    | C.GFun (fd, _) ->
      if fd.C.svar.C.vname = "main" then g_ap := AP.intra_pattern fd
    | _ -> ()
  in
  C.iterGlobals file find_main;

  cur_rand := int_of_float (Unix.gettimeofday ());
  if (not !pool_only) || (not !no_reorder) then interpret_re !g_ap;

FA version 1. end *)

(* FA version 2. bottom-up approach (during building ap) *)

  let module AP = F_automata.Make(FA) in
  let module CG = Rtfa_cg in
  let main_info = ref (AP.empty_info ()) in
  let process_fd (fd: C.fundec) : unit =
    let cur = AP.local_affinity fd in
    if fd.C.svar.C.vname = "main" then main_info := cur
  in
  CG.make_callgraph file;
  List.iter process_fd (CG.get_ordered_fd ());

  if (not !pool_only) || (not !no_reorder) then
    List.iter concretize_core (AP.get_core !main_info);
  AP.clear_info ();
  make_affinity_str c

(* FA version 2. end *)
 
(* FA version 2. & 3. *)

and concretize_core (f1, f2, w_lst) : unit =
  let f1_sz = C.bitsSizeOf (C.unrollType f1.C.ftype) in
  let f1_id = find_id ~size:f1_sz f1.C.fname in
  let f1_s  = IS.singleton f1_id in
  let each_lv (lv, cnt) : unit =
    let cnt' = make_real_w lv cnt
    in ignore (add_relation cnt' f1_s f2)
  in
  List.iter each_lv w_lst

and make_affinity_str (c: C.compinfo) : string =
  edge_set := ES.empty;
  if !debug then (IH.iter graph_printer strg; print_newline ());
  if (not !pool_only) then grouping ();

  let affinity = affinity_str () in

  let dont_appear = ref "" in
  let all_appear (f: C.fieldinfo) = 
    try ignore (SM.find f.C.fname !fn_id_map)
    with Not_found ->
    (
      if !dont_appear = "" then dont_appear := f.C.fname
      else dont_appear := !dont_appear ^ "," ^ f.C.fname
    )
  in 
  List.iter all_appear c.C.cfields;

  if affinity <> "" then
  (
    if !dont_appear <> "" then
    (
      if (not !pool_only) then affinity ^ ":" ^ !dont_appear
      else affinity ^ "," ^ !dont_appear
    )
    else affinity
  )
  else (* empty access *)
  (
    let rec fn_gather = function
      | [] -> ""
      | hd :: [] -> hd.C.fname
      | hd :: tl -> hd.C.fname ^ "," ^ (fn_gather tl)
    in
    fn_gather c.C.cfields
  )

