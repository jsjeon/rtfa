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

(*----------------------------------------------------------------------*)
(* Exceptions and Flags                                                 *)
(*----------------------------------------------------------------------*)

exception AP_Fatal of string
exception AP_Debug of string

let ap_inter  = ref false
let ap_choice = ref false
let ap_debug  = ref false

(*----------------------------------------------------------------------*)
(* Parameterized Regular Expression                                     *)
(*----------------------------------------------------------------------*)

type 't re =
    Empty
  | Cons  of 't list
  | Conc  of 't re list
  | Alter of 't re list
  | Star  of 't re
  | Func  of C.varinfo (* for bottom-up approach *)

(* str_of_re: ('t -> string) -> 't re -> string *)
let rec str_of_re (f: 't -> string) (exp: 't re) : string =
  match exp with
  | Empty -> "@"
  | Cons  el -> List.fold_left (fun ac e -> ac^(f e)) "" el
  | Conc  rl -> List.fold_left (fun ac r -> ac^(str_of_re f r)) "" rl
  | Alter rl ->
    let rec alter_printer (elts: 't re list) : string =
      match elts with
      | [] -> ""
      | hd :: [] -> str_of_re f hd
      | hd :: tl -> (str_of_re f hd)^" + "^(alter_printer tl)
    in
    "("^(alter_printer rl)^")"
  | Star  re -> "("^(str_of_re f re)^")*"
  | Func   v -> "\""^(v.C.vname)^"\""

(*----------------------------------------------------------------------*)
(* Utilities for RE Generation                                          *)
(*----------------------------------------------------------------------*)

module REKey =
struct
  type 't t = 't re
  let compare r1 r2 =
    if (r1 == r2) then 0 else Pervasives.compare r1 r2
end

module RS = Setp.Make(REKey)

let make_set (rl: 't re list) : 't RS.t =
  let rs = ref RS.empty in
  List.iter (fun r -> rs := RS.add r !rs) rl;
  !rs

(* alter: 't re -> 't re -> 't re *)
let rec alter (x: 't re) (y: 't re) : 't re =
  if x == y then x (* or y *) else
  match x, y with
  | Alter xl, Alter yl ->
    (
      let xs = make_set xl
      and ys = make_set yl in
      let xy = RS.elements (RS.union xs ys)
      in
      if (List.length xy) = 1 then List.hd xy else Alter xy
    )
  | Alter xl, _ -> Alter (xl @ [y])
  | _, Alter yl -> Alter (x :: yl)
  | Star xs, Star ys -> Star (alter xs ys)
  | Star _, Empty -> x
  | Empty, Star _ -> y
  | Star xs, _ -> if xs == y then x else Alter [x; y]
  | _, Star ys -> if y == ys then y else Alter [x; y]
  | _, _ -> Alter [x; y]

(* conc: 't re -> 't re -> 't re *)
let conc (x: 't re) (y: 't re) : 't re =
  match x, y with
  | Empty, _ -> y
  | _, Empty -> x
  | Cons xl, Cons yl -> Cons (xl @ yl)
  | Conc xl, Conc yl -> Conc (xl @ yl)
  | Conc xl, _ -> Conc (xl @ [y])
  | _, Conc yl -> Conc (x :: yl)
  | Star xs, _ -> if xs == y then x else Conc [x; y]
  | _, Star ys -> if x == ys then y else Conc [x; y]
  | _, _ -> Conc [x; y]

(* star: 't re -> 't re *)
let star (x: 't re) : 't re =
  match x with
  | Empty
  | Star _ -> x
  | _ -> Star x

(*----------------------------------------------------------------------*)
(* Signature for User-Specific Access and Type                          *)
(*----------------------------------------------------------------------*)

module type RE_SIG =
sig
  type t (* lval, field, and so on *)
  val str_of_t     : t -> string
  val compare      : t -> t -> int
  val read_access  : Cil.lval -> t re
  val write_access : Cil.lval -> t re
end

