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

open Cil

module C = Cil
module S = Struct

(* Objective
 * 1. lval transformation to accurate formula,
          which is involved in target structure
 * 1'. pointer arithmetic transformation
 * 2. void* _rtfa_alloc_(void) func for allocation of target structure
 * 3. void _rtfa_free_(void* ) func for release of target structure
 *)

let free_names  = ["free"]
let wrapper     = ref ""
let in_wrapper  = ref false
let is_calloced = ref false
let pool_size   = ref C.zero
let max_obj_cnt = ref C.zero
let g1_size     = ref C.zero
let pool_head   = ref C.zero

let rec two_power (n: int) : int =
  if n = 1 then 0
  else if (n mod 2) = 1 || n = 0 then -1
  else
  (
    let r = two_power (n / 2) in
    if r = -1 then -1 else (1 + r)
  )

let rec lv_transform (lh: lhost) (fi: fieldinfo) (off: offset) : lval =
try
(
  let mask2 = C.kinteger64 C.ILong (Int64.of_int (!S.pool_size - 1))
  and (prev_g,gsize,prev_f) = S.get_args fi.C.fname
  and host = CastE (C.intType, (* p->f: (int)p *)
    match lh with 
    | Mem e -> e 
    | Var _ -> raise (S.Inconsistent "lv_transform: variable access"))
  in
  let rank =
    if !is_calloced then
      BinOp (Div, (* ((int)p - pool_head) / g1_size *)
        (BinOp (MinusA, host, !pool_head, C.intType)), !g1_size, C.intType)
    else
      let exponent = two_power (S.get_first_group_size ()) in
      if exponent = -1
      then
        BinOp (Div, (* ((int)p & 0x00000fff) / g1_size *)
          (BinOp (BAnd, host, mask2, C.voidPtrType)), !g1_size, C.intType)
      else
        BinOp (Shiftrt, (* ((int)p & 0x00000fff) >> exponent *)
          (BinOp (BAnd, host, mask2, C.voidPtrType)),
            (C.integer exponent), C.intType)
  in
  let offset = (* prev_g*max_obj_cnt + (gsize-g1_size)*rank + prev_f *)
    let term1 = 
      BinOp (Mult, C.integer prev_g, !max_obj_cnt, C.intType)
    and term2 =
      BinOp (Mult, rank, (BinOp (MinusA,
        C.integer gsize, !g1_size, C.intType)), C.intType)
    and term3 = C.integer prev_f 
    in
    BinOp (PlusA,(BinOp (PlusA,term1,term2,C.intType)),term3,C.intType)
  in
  let addr = BinOp (PlusPI, host, offset, C.voidPtrType) in
  let casted_addr = C.mkCast addr (TPtr (fi.C.ftype,[]))
  in
  match off with
  | Field (fi',off') ->
    if S.isTargetField fi' then lv_transform (Mem addr) fi' off'
    else C.mkMem ~addr:casted_addr ~off:off
  | _ -> C.mkMem ~addr:casted_addr ~off:off
)
with Not_found -> 
  raise (S.Inconsistent "lv_transform: field confirmation is needed")

let hasTargetType = function
  | SizeOf t -> S.isTargetType t
  | SizeOfE (Lval lv) -> S.isTargetType (C.typeOfLval lv)
  | _ -> false

let rec hasTargetPtrType = function
  | Lval lv -> S.isTargetPtrType (C.typeOfLval lv)
  | UnOp (_,e,_) -> hasTargetPtrType e
  | BinOp (_,e1,e2,_) -> (hasTargetPtrType e1) <> (hasTargetPtrType e2)
  | _ -> false

let id = fun x -> x

class paVisitor =
object inherit nopCilVisitor

(* transform original pointer arithmetic to appropriate access formula *)
(* p + i => (t ptr)((int)p + i * g1_size) *)
method vexpr (e: C.exp) : C.exp C.visitAction =
  match e with
  | BinOp (op, e1, e2, t) ->
    (
      match op with
      | PlusPI
      | IndexPI ->
        (
          if hasTargetPtrType e1 then
            let p' = C.mkCast e1 C.intType
            and m_g1 = BinOp (Mult, e2, !g1_size, C.typeOf e2) in
            let t = C.mkCast (BinOp (PlusA, p', m_g1, C.intType)) (C.typeOf e1)
            in ChangeDoChildrenPost (t, id)
          else if hasTargetPtrType e2 then
            let p' = C.mkCast e2 C.intType
            and m_g1 = BinOp (Mult, e1, !g1_size, C.typeOf e1) in
            let t = C.mkCast (BinOp (PlusA, m_g1, p', C.intType)) (C.typeOf e2)
            in ChangeDoChildrenPost (t, id)
          else DoChildren
        )
      | MinusPI ->
        (
          if hasTargetPtrType e1 then
            let p' = C.mkCast e1 C.intType
            and m_g1 = BinOp (Mult, e2, !g1_size, C.typeOf e2) in
            let t = C.mkCast (BinOp (MinusA, p', m_g1, C.intType)) (C.typeOf e1)
            in ChangeDoChildrenPost (t, id)
          else if hasTargetPtrType e2 then
            let p' = C.mkCast e2 C.intType
            and m_g1 = BinOp (Mult, e1, !g1_size, C.typeOf e1) in
            let t = C.mkCast (BinOp (MinusA, m_g1, p', C.intType)) (C.typeOf e2)
            in ChangeDoChildrenPost (t, id)
          else DoChildren
        )
      | _ -> DoChildren
    )
  | _ -> DoChildren

end

class tVisitor (rtfa_alloc: C.varinfo) (rtfa_free: C.varinfo) =
object inherit nopCilVisitor

method vfunc (f: C.fundec) : C.fundec C.visitAction =
  if f.svar.vname = !wrapper then in_wrapper := true
  else in_wrapper := false;
  DoChildren

(* transform original field access to accurate access formula *)
method vlval (lh,loff) : C.lval C.visitAction =
  match lh, loff with
  | C.Mem _, C.Field (fi,off) -> 
    (
      if S.isTargetField fi then 
        ChangeDoChildrenPost ((lv_transform lh fi off), id)
      else DoChildren
    )
  | _ -> DoChildren

(* transform original allocation for target struct to _rtfa_alloc_ *)
method vinst (instr: C.instr) : C.instr list C.visitAction =
  match instr with
  | Call (r,Lval(Var vi, NoOffset),args,l) ->
    if List.mem vi.vname S.alloc_names && vi.vname <> "calloc" then
    (
      if !in_wrapper then
        ChangeDoChildrenPost ([(Call (r,Lval(Var rtfa_alloc,NoOffset),[],l))], id)
      else if List.length args = 1 && hasTargetType (List.hd args) then
        ChangeDoChildrenPost ([(Call (r, Lval(Var rtfa_alloc,NoOffset),[],l))], id)
      else DoChildren
    )
    else if List.mem vi.vname free_names && not !is_calloced then
    (
      if List.length args = 1 then
      (
        match List.hd args with
        | CastE (t,e) ->
          (
            if t = C.voidPtrType then
            (
              if S.isTargetPtrType (C.typeOf e) then
                ChangeDoChildrenPost ([(Call (r,Lval(Var rtfa_free,NoOffset),args,l))], id)
              else DoChildren
            )
            else DoChildren
          )
        | _ ->
          (
            if S.isTargetPtrType (C.typeOf (List.hd args)) then
              ChangeDoChildrenPost ([(Call (r,Lval(Var rtfa_free,NoOffset),args,l))], id)
            else DoChildren
          )
      )
      else DoChildren
    )
    else DoChildren
  | _ -> DoChildren

end

let comment = GText("/* Generated by RTFA */")

class callocVisitor (g_ps: C.lval) (g_oc: C.lval) (g_ph: C.lval) =
object inherit nopCilVisitor

method vinst (instr: C.instr) : C.instr list C.visitAction =
  match instr with
  | Call (Some r,Lval(Var vi, NoOffset),args,l) ->
    if vi.vname = "calloc" && List.length args >= 2 &&
      (hasTargetType (List.nth args 0) || hasTargetType (List.nth args 1))
    then
      let obj  =
        let exponent = two_power (S.get_struct_size ()) in
          if exponent = -1
          then BinOp (Div, !pool_size, C.integer (S.get_struct_size ()), C.intType)
          else BinOp (Shiftrt, !pool_size, C.integer exponent, C.intType)
      and size = BinOp (Mult, (List.nth args 0), (List.nth args 1), C.intType)
      in
      let s1 = Set (g_ps, size, l)
      and s2 = Set (g_oc, obj, l)
      and s3 = Set (g_ph, C.mkCast (Lval r) C.intType, l)
      in ChangeDoChildrenPost ([instr; s1; s2; s3], id)
    else DoChildren
  | _ -> DoChildren

end

let loc = C.locUnknown
let bank_descr_place = ref false

(* transform: Cil.file -> string -> string -> bool -> unit *)
let transform (f: C.file) (s: string) (w: string) (c: bool) : unit =
  let rtfa_alloc_str = "_"^s^"_alloc_"
  and rtfa_alloc_typ = (TFun (voidPtrType,Some [],false,[])) in
  let rtfa_alloc = C.makeVarinfo true rtfa_alloc_str rtfa_alloc_typ in

  let rtfa_free_str = "_"^s^"_free_"
  and rtfa_free_typ = 
    (TFun (voidType,Some [("free_p",C.voidPtrType,[])],false,[])) in
  let rtfa_free = C.makeVarinfo true rtfa_free_str rtfa_free_typ in

  (* task 1: lval and allocation transformation *)
  wrapper     := w;
  is_calloced := c;
  pool_size   := C.integer !S.pool_size;
  max_obj_cnt := C.integer (S.get_max_obj_cnt ());
  g1_size     := C.integer (S.get_first_group_size ());
  if !is_calloced then
  (
    let v_ph = C.makeGlobalVar (s^"_pool_head") C.intType in
    let g_ph = GVar (v_ph, {init = Some (SingleInit C.zero)}, loc) in
    f.globals <- comment :: g_ph :: f.globals;
    let v_oc = C.makeGlobalVar (s^"_max_obj_cnt") C.intType in
    let g_oc = GVar (v_oc, {init = Some (SingleInit C.zero)}, loc) in
    f.globals <- comment :: g_oc :: f.globals;
    let v_ps = C.makeGlobalVar (s^"_pool_size") C.longType in
    let g_ps = GVar (v_ps, {init = Some (SingleInit C.zero)}, loc) in
    f.globals <- comment :: g_ps :: f.globals;
    pool_size := Lval (C.var v_ps);
    max_obj_cnt := Lval (C.var v_oc);
    pool_head := Lval (C.var v_ph);
    let callocFinder = new callocVisitor (C.var v_ps) (C.var v_oc) (C.var v_ph)
    in C.visitCilFile callocFinder f
  );
  let visitor = new paVisitor
  in C.visitCilFile visitor f;
  let visitor = new tVisitor rtfa_alloc rtfa_free
  in C.visitCilFile visitor f;
  
  (* task 2: insert _rtfa_alloc_ and _rtfa_free_ function *)
  let my_alloc = C.emptyFunction rtfa_alloc_str
  and my_free  = C.emptyFunction rtfa_free_str in
  let free_p = C.makeFormalVar my_free "free_p" C.voidPtrType in
 
  (* set function return type *)
  C.setFunctionType my_alloc rtfa_alloc_typ;
  C.setFunctionType my_free  rtfa_free_typ;

  (* basic information *)
  let mask1 = C.kinteger64 ILong (Int64.of_int (0 - !S.pool_size))
  and malloc = 
    C.makeVarinfo true "malloc" 
    (TFun (C.voidPtrType,Some [("sz",C.intType,[])],false,[]))
  and free =
    C.makeVarinfo true "free"
    (TFun (C.voidType,Some [("ptr",C.voidPtrType,[])],false,[]))
  and pn = 1000
  in

  (* define bank_descr type and global bank_list var *)
  let bank_descr_comp = C.mkCompInfo true "bank_descr"
    (fun c ->
      [
        ("free_pool",C.intType,None,[],loc);
        ("current_pool",C.intType,None,[],loc);
        ("base_addr",C.charPtrType,None,[],loc);
        ("base_aligned",C.charPtrType,None,[],loc);
        ("active_structure",
          TArray(C.intType,Some (C.integer pn),[]),None,[],loc);
        ("next",TPtr (TComp (c,[]),[]),None,[],loc);
      ]
    ) [] in
  let bank_descr = TComp (bank_descr_comp, []) in
  let bank_descr_ptr = TPtr (bank_descr, []) in
  let bank_list = C.makeGlobalVar (s^"_bank_list") bank_descr_ptr in

  (* define global bank_full var *)
  let bank_full = C.makeGlobalVar (s^"_bank_full") C.intType in

  (* each fieldinfo of bank_descr *)
  let mkOffset fn ft =
    Field ({
      fcomp = bank_descr_comp;
      fname = fn;
      ftype = ft;
      fbitfield = None;
      fattr = [];
      floc = loc;
    }, NoOffset)
  in
  let free_pool = mkOffset "free_pool" C.intType
  and cur_pool = mkOffset "current_pool" C.intType
  and base_addr = mkOffset "base_addr" C.charPtrType
  and base_aligned = mkOffset "base_aligned" C.charPtrType
  and active = 
    mkOffset "active_structure" (TArray (C.intType,Some (C.integer pn),[]))
  and next = mkOffset "next" (TPtr (TComp (bank_descr_comp,[]), []))
  in

  (* set local varibales for my_alloc *)
  let addr = C.makeLocalVar my_alloc (s^"_addr") C.charPtrType
  and target = C.makeLocalVar my_alloc s bank_descr_ptr
  and old_bank_list = 
    C.makeLocalVar my_alloc ("old_"^s^"_bank_list") bank_descr_ptr
  and i = C.makeLocalVar my_alloc "i" C.intType in

  let addr = C.var addr
  and target = C.var target
  and old_bank_list = C.var old_bank_list in

  let nc   = C.mkMem ~addr:(Lval target) ~off:cur_pool in
  let off  = C.addOffset (Index (Lval nc,NoOffset)) active in
  let nanc = C.mkMem ~addr:(Lval target) ~off:off
  and nf   = C.mkMem ~addr:(Lval target) ~off:free_pool
  and nb   = C.mkMem ~addr:(Lval target) ~off:base_addr
  and nba  = C.mkMem ~addr:(Lval target) ~off:base_aligned
  and nn   = C.mkMem ~addr:(Lval target) ~off:next in

  (* add local body of my_alloc *)
  my_alloc.sbody <-
  C.mkBlock
  ([
    C.mkStmt (Instr
    [
      (* old_node_bank_list = node_bank_list; *)
      (Set (old_bank_list, Lval (C.var bank_list), loc));
      (* node = node_bank_list; *)
      (Set (target, Lval (C.var bank_list),loc));
    ]);
    (* if (node == NULL || node_bank_full) *)
    C.mkStmt (If (BinOp (LOr,
      (BinOp (Eq, (Lval target), C.zero, C.intType)),
      (Lval (C.var bank_full)), C.intType),
      C.mkBlock (* then part *)
      ([
        (* node = malloc(sizeof(struct bank_descr)); *)
        C.mkStmtOneInstr (Call (Some target,
          Lval (C.var malloc),[SizeOf bank_descr],loc));
        (* node->base_addr = malloc(2048*1001); *)
        C.mkStmtOneInstr (Call 
          (Some nb, Lval (C.var malloc),
           [BinOp (Mult, !pool_size, C.integer (pn+1), C.intType)],
           loc));
        C.mkStmt (Instr
        [
          (* node->base_aligned = (((int)node->base_addr+2047) & -2048); *)
          (Set (nba, (BinOp (BAnd,
            (BinOp (PlusA, (C.mkCast (Lval nb) C.intType),
                   BinOp (MinusA, !pool_size, C.one, C.intType), C.intType)),
            mask1, C.intType)),loc));
          (* node->free_pool = 1000; *)
          (Set (nf, C.integer pn, loc));
          (* node->current_pool = 0; *)
          (Set (nc, C.zero, loc));
        ])
      ] @
      (* for (i=0; i<1000; i++) *)
      C.mkForIncr ~iter:i ~incr:C.one
        ~first:C.zero ~stopat:(C.integer pn)
        ~body:(
        [
          (* node->active_structure[i] = 0; *)
          C.mkStmtOneInstr (Set
            (C.mkMem ~addr:(Lval target)
             ~off:(C.addOffset (Index (Lval (C.var i), NoOffset)) active),
            C.zero, loc))
        ]) @
      [
        C.mkStmt (Instr
        [
          (* node->next = old_node_bank_list; *)
          (Set (nn, Lval old_bank_list, loc));
          (* node_bank_list = node; *)
          (Set (C.var bank_list, Lval target, loc));
          (* node_bank_full = 0; *)
          (Set (C.var bank_full, C.zero, loc))
        ]);
      ]), C.mkBlock [], loc))
  ] @
  (C.mkWhile ~guard:(Lval target)
   ~body:[
    (* if (node->free_pool || *)
    C.mkStmt (If (BinOp (LOr, Lval nf,
      (* node->free_pool == 0 && *)
      BinOp (LAnd, BinOp (Eq, Lval nf, C.zero, C.intType),
      (* node->active_structure[node->current_pool] < max_obj_cnt) *)
        BinOp (Lt, Lval nanc, !max_obj_cnt, C.intType),
        C.intType), C.intType),
      C.mkBlock (* then part *)
      [
        (* if (node->active_structure[node->current_pool] == max_obj_cnt) *)
        C.mkStmt (If (BinOp (Eq, Lval nanc, !max_obj_cnt, C.intType),
          C.mkBlock (* then part *)
          [
            (* node->current_pool++; *)
            C.mkStmtOneInstr (Set (nc,
              BinOp (PlusA, Lval nc, C.one, C.intType),loc));
            (* if ((node->current_pool == 1000) || *)
            C.mkStmt (If (BinOp (LOr,
              (BinOp (Eq, Lval nc, C.integer pn, C.intType)),
              (* node->active_structure[node->current_pool]==max_obj_cnt *)
              (BinOp (Eq, Lval nanc, !max_obj_cnt, C.intType)),
              C.intType),
              C.mkBlock (* then part *)
              (
                (* for (i=0; i<1000; i++) *)
                C.mkForIncr ~iter:i ~incr:C.one
                ~first:C.zero ~stopat:(C.integer pn)
                ~body:(
                [
                  (* if (node->active_structure[i] == 0) *)
                  C.mkStmt (If (BinOp (Eq,
                    Lval (C.mkMem ~addr:(Lval target)
                      ~off:(C.addOffset (Index (Lval (C.var i),NoOffset)) 
                      active)), C.zero, C.intType),
                    C.mkBlock (* then part *)
                    [
                      (* node->current_pool = i; *)
                      C.mkStmtOneInstr (Set (nc,Lval (C.var i),loc));
                      C.mkStmt (Break loc)
                    ], C.mkBlock [], loc))
                ])
              ), C.mkBlock [], loc));
          ], C.mkBlock [], loc));
        (* node_addr = node->base_aligned + 2048*node->current_pool +
          node->active_structure[node->current_pool]*g1_size; *)
        C.mkStmtOneInstr (Set (addr,
          BinOp (PlusA, Lval nba, BinOp (PlusA,
            BinOp (Mult, Lval nc, !pool_size, C.intType),
            BinOp (Mult, Lval nanc, !g1_size, C.intType),
            C.intType), C.intType), loc));
        (* if (node->active_structure[node->current_pool] == 0) *)
        C.mkStmt (If (BinOp (Eq, Lval nanc, C.zero, C.intType),
          C.mkBlock
          [
            (* node->free_pool--; *)
            C.mkStmtOneInstr (Set (nf,
              BinOp (MinusA, Lval nf, C.one, C.intType), loc))
          ], C.mkBlock [], loc));
        (* node->active_structure[node->current_pool]++; *)
        C.mkStmtOneInstr (Set (nanc,
          BinOp (PlusA, Lval nanc, C.one, C.intType), loc));
        (* return node_addr; *)
        C.mkStmt (Return (Some (Lval addr), loc))
      ], C.mkBlock [], loc));
    (* node = node->next; *)
    C.mkStmtOneInstr (Set (target, Lval nn, loc))
  ]) @
  [
    C.mkStmt (Instr
    [
      (* node_bank_full = 1; *)
      (Set (C.var bank_full, C.one, loc));
      (* _my_alloc_ (); *)
      (Call (None, Lval (C.var rtfa_alloc),[],loc));
    ])
  ]);

  (* set local variables for my_free *)
  let target = C.makeLocalVar my_free s bank_descr_ptr
  and prev = C.makeLocalVar my_free (s^"_prev") bank_descr_ptr
  and cp = C.makeLocalVar my_free "current_pool" C.intType in

  let target = C.var target
  and prev = C.var prev
  and cp = C.var cp
  and free_p = C.var free_p in

  let off = C.addOffset (Index (Lval cp, NoOffset)) active in
  let nac = C.mkMem ~addr:(Lval target) ~off:off
  and nc  = C.mkMem ~addr:(Lval target) ~off:cur_pool
  and nf  = C.mkMem ~addr:(Lval target) ~off:free_pool
  and nb  = C.mkMem ~addr:(Lval target) ~off:base_addr
  and nba = C.mkMem ~addr:(Lval target) ~off:base_aligned
  and nn  = C.mkMem ~addr:(Lval target) ~off:next in

  (* add local body of my_free *)
  my_free.sbody <-
  C.mkBlock
  ((
    C.mkStmt (Instr
    [
      (* node = node_bank_list; *)
      (Set (target,Lval (C.var bank_list),loc));
      (* node_prev = NULL; *)
      (Set (prev, C.zero, loc))
    ])
  ) ::
  (C.mkWhile ~guard:(Lval target)
   ~body:[
    (* if (node->base_addr <= free_p && *)
    (C.mkStmt (If (BinOp (LAnd, 
      (BinOp (Le, (Lval nb), (Lval free_p), C.intType)),
      (* (int)node->base_addr+2048*1001 > (int)free_p) *)
      (BinOp (Gt,
        (BinOp (PlusA, 
          (C.mkCast (Lval nb) C.intType),
          (BinOp (Mult, !pool_size, (C.integer (pn+1)), C.intType)),
          C.intType)),
        (C.mkCast (Lval free_p) C.intType), C.intType)), C.intType),
      C.mkBlock (* then part *)
      [
        (* currnt_pool = ((int)free_p - (int)node->base_aligned)/2048; *)
        C.mkStmtOneInstr (Set (cp, (BinOp (Div,
          (BinOp (MinusA, (C.mkCast (Lval free_p) C.intType),
            (C.mkCast (Lval nba) C.intType), C.intType)),
          !pool_size, C.intType)), loc));
        (* if (current_pool != node->current_pool) *)
        C.mkStmt (If (BinOp (Ne, (Lval cp), (Lval nc), C.intType),
          C.mkBlock (* then part *)
          [
            (* node->active_structure[current_pool]--; *)
            C.mkStmtOneInstr (Set (nac, (BinOp (MinusA, 
            (Lval nac), C.one, C.intType)),loc))
          ], C.mkBlock [], loc));
        (* if (node->active_structure[current_pool] == 0) *)
        (C.mkStmt (If (BinOp (Eq, (Lval nac), C.zero, C.intType),
          C.mkBlock (* then part *)
          [
            (* node->free_pool++; *)
            (C.mkStmtOneInstr (Set (nf,
               (BinOp (PlusA, (Lval nf), C.one, C.intType)), loc)));
            (* if (node->free_pool == 1000) *)
            (C.mkStmt (If (BinOp 
              (Eq, (Lval nf), (C.integer pn), C.intType),
              C.mkBlock (* then part *)
              [
                (* free(node->base_addr); *)
                C.mkStmtOneInstr (Call (None, Lval (C.var free),
                [Lval nb], loc));
                (* if (prev) *)
                C.mkStmt (If (Lval prev,
                  (* prev->next = node->next; *)
                  C.mkBlock [
                    C.mkStmtOneInstr (Set
                      ((C.mkMem ~addr:(Lval prev) ~off:next),
                      (Lval nn), loc))
                  ],
                  (* node_bank_list = node->next; *)
                  C.mkBlock [
                    C.mkStmtOneInstr (Set (C.var bank_list, Lval nn, loc))
                  ], loc));
                (* free(node); *)
                C.mkStmtOneInstr (Call (None, 
                  Lval (C.var free),[(Lval target)],loc));
                (* return; *)
                C.mkStmt (Return (None, loc));
              ], C.mkBlock [], loc)))
          ], C.mkBlock [], loc)))
      ], C.mkBlock [], loc)));
    C.mkStmt (Instr
    [
      (* node_prev = node; *)
      (Set (prev,Lval target,loc));
      (* node = node->next; *)
      (Set (target, Lval nn,loc))
    ])
  ]));

  if not !is_calloced then
  (
    (* add bank_descr type and bank_list var *)
    if not !bank_descr_place then
    (
      f.globals <- comment :: GCompTag (bank_descr_comp,loc) :: f.globals;
      bank_descr_place := true
    );

    (* add my_alloc func and my_free to original source *)
    f.globals <- comment :: GVarDecl(rtfa_free,loc) :: f.globals;
    f.globals <- comment :: GVarDecl(rtfa_alloc,loc) :: f.globals;

    let glist = GVar (bank_list,{init = Some (SingleInit C.zero)},loc)
    and gfull = GVar (bank_full,{init = Some (SingleInit C.zero)},loc)
    in
    f.globals <- f.globals @ [comment; glist; gfull; GFun(my_alloc,loc)];
    f.globals <- f.globals @ [comment; GFun(my_free,loc)]
  )

