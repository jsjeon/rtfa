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

exception UnknownStruct
exception Inconsistent of string
exception UnknownField of string

(* referred from ptranal module (src/ext/pta/ptranal.ml) *)
let alloc_names = ["malloc";"calloc";"realloc";"xmalloc";
  "__builtin_alloca";"alloca";"kmalloc"]

let dummy = "@@dummy"
(* compinfo of target struct *)
let t_struct  = ref (C.mkCompInfo true dummy (fun _ -> []) [])
let set_target_struct (c: C.compinfo) : unit = t_struct := c

let affinity = ref ""
let set_affinity_str (s: string) : unit = affinity := s

module StrKey =
  struct
    type t = string
    let compare = Pervasives.compare
  end

module SM = Map.Make(StrKey)

let field_add (s: string) (data: 'a) (map: 'a SM.t) : 'a SM.t =
  if SM.mem s map then raise (Inconsistent ("affinity overlap: "^s))
  else SM.add s data map

let no_compact  = ref false
let info        = ref false
let pool_size   = ref 2048
let max_obj_cnt = ref 0
let first_group = ref 0
let struct_size = ref 0
let field_info  = ref SM.empty

(* calc each struct size *)
let rec prepare () : unit =
  (* initialization *)
  max_obj_cnt := 0;
  first_group := 0;
  field_info  := SM.empty;

  if (!t_struct).C.cname = dummy then
    raise (Inconsistent "target struct is not given");

  let field_finder (s: string) : int =
    let fs = ref 0 in
    let fieldinfo_iter (f: C.fieldinfo) =
      if f.C.fname = s then
        fs := (C.bitsSizeOf (C.unrollType f.C.ftype)) lsr 3
    in
    List.iter fieldinfo_iter (!t_struct).C.cfields;
    if !fs = 0 then raise (UnknownField s);
    !fs
  in
  let fname  = ref ""
  and gsizes = ref ([]: (string * int) list)
  and prev_g = ref 0
  in
  let fieldInfoAdder (gsizes: (string * int) list) : int =
    let gsize = List.fold_left (fun acc (_,fs) -> acc + fs) 0 gsizes
    in
    let helper (acc: int) (fname,fsize) =
      field_info := field_add fname (!prev_g,gsize,acc) !field_info;
      acc + fsize
    in (List.fold_left helper 0 gsizes)
  in
  let iterator (c: char) : unit =
    if c <> ':' && c <> ',' then
      fname := !fname ^ (String.make 1 c)
    else (* ':' or ',' *)
    (
      gsizes := !gsizes @ [(!fname,(field_finder !fname))];
      fname  := "";
      if c = ':' then (* new group *)
      (
        prev_g := !prev_g + (fieldInfoAdder !gsizes);
        if !first_group = 0 then first_group := !prev_g;
        gsizes := []
      )
    )
  in
  Stream.iter iterator (Stream.of_string !affinity);
  (* for last field *)
  gsizes := !gsizes @ [(!fname,(field_finder !fname))];
  prev_g := !prev_g + (fieldInfoAdder !gsizes);
  if !first_group = 0 then first_group := !prev_g;

  (* affinity check *)
  let affinity_checker (f: C.fieldinfo) : unit =
    try ignore (SM.find f.C.fname !field_info)
    with Not_found -> raise (Inconsistent ("affinity absense: "^f.C.fname))
  in
  List.iter affinity_checker (!t_struct).C.cfields;

  (* here, prev_g is total struct size *)
  struct_size := !prev_g;

  (* no_compact option *)
  if !no_compact then
  (
    let field_list = ref ([]: (string * int) list)
    and max_gs     = ref 0
    in
    let field_info_collector fname (prev_g,gsize,_) (acc: int) : int =
      field_list := (fname,prev_g) :: !field_list;
      if acc < gsize then gsize else acc
    in
    max_gs := SM.fold field_info_collector !field_info 0;
    let sorted_field_list = 
      List.sort (fun (_,i) (_,j) -> Pervasives.compare i j) !field_list
    in
    let update (acc: int) (fname,_) : int =
      let (_,_,prev_f) = get_args fname
      in
      field_info := SM.add fname (acc,!max_gs,prev_f) !field_info;
      acc + !max_gs
    in
    struct_size := List.fold_left update 0 sorted_field_list
  );

  max_obj_cnt := !pool_size / !struct_size

(* type confirmation *)
and isTargetType (t: C.typ) : bool =
  if (!t_struct).C.cname = dummy then
    raise (Inconsistent "target struct is not given");
  match C.unrollType t with
  | C.TComp (c,_) -> (!t_struct).C.cname = c.C.cname
  | _ -> false

and isTargetPtrType (t: C.typ) : bool =
  match C.unrollType t with
  | C.TPtr (t,_) -> isTargetType t
  | _ -> false

(* field confirmation *)
and isTargetField (f: C.fieldinfo) : bool =
  if SM.is_empty !field_info then
    raise (Inconsistent "field info is not constructed");
  (SM.mem f.C.fname !field_info) && (!t_struct).C.cname = f.C.fcomp.C.cname

(*
 * 'get' interfaces
 *)

(* field_name -> prev_group_sizes, group_size, prev_field_size *)
and get_args (fname: string) : int * int * int =
  SM.find fname !field_info

let get_max_obj_cnt () : int = 
  if !max_obj_cnt = 0 then
    raise (Inconsistent "max_obj_cnt is not calculated");
  !max_obj_cnt

let get_first_group_size () : int =
  if !first_group = 0 then
    raise (Inconsistent "first_group is not calculated");
  !first_group

let get_struct_size () : int =
  if !struct_size = 0 then
    raise (Inconsistent "struct size is not calculated");
  !struct_size
