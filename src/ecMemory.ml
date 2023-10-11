(* -------------------------------------------------------------------- *)
open EcIdent
open EcSymbols
open EcUtils
open EcTypes

module Msym = EcSymbols.Msym

(* -------------------------------------------------------------------- *)
type memory = EcIdent.t

let mem_equal = EcIdent.id_equal

(* -------------------------------------------------------------------- *)
type proj_arg = {
  arg_quantum : quantum;    (* classical/quantum *)
  arg_ty      : ty;         (* type of the procedure argument "arg" *)
  arg_pos     : int;        (* projection *)
}

type local_memtype_ = {
  mt_name : symbol option;      (* provides access to the full local memory *)
  mt_decl : ovariable list;
  mt_proj : (int * ty) Msym.t;  (* where to find the symbol in mt_decl and its type *)
  mt_ty   : ty;                 (* ttuple (List.map v_type mt_decl) *)
  mt_n    : int;                (* List.length mt_decl *)
}

let mk_lmt
      (mt_name : symbol option)
      (mt_decl : ovariable list)
      (mt_proj : (int * ty) Msym.t)
  =

  let mt_ty = ttuple (List.map ov_type mt_decl) in
  let mt_n  = List.length mt_decl in

  { mt_name; mt_decl; mt_proj; mt_ty; mt_n; }

let lmem_hash_ (lmem : local_memtype_) : int =
  let mt_name_hash = Why3.Hashcons.combine_option Hashtbl.hash lmem.mt_name in
  let mt_decl_hash = Why3.Hashcons.combine_list EcTypes.ov_hash 0 lmem.mt_decl in

  let mt_proj_hash =
    let el_hash (s, (i, ty)) =
      Why3.Hashcons.combine2 (Hashtbl.hash s) i (EcTypes.ty_hash ty) in
    Why3.Hashcons.combine_list el_hash 0 (Msym.bindings lmem.mt_proj) in

  Why3.Hashcons.combine_list
    (fun i -> i)
    (EcTypes.ty_hash lmem.mt_ty)
    [lmem.mt_n; mt_name_hash; mt_decl_hash; mt_proj_hash]

let lmt_equal_
    (ty_equal : ty -> ty -> bool)
    (lmt1     : local_memtype_)
    (lmt2     : local_memtype_)
  =

  match lmt1.mt_name, lmt2.mt_name with
  | None, None ->
      Msym.equal (fun (_, ty1) (_, ty2) ->
        ty_equal ty1 ty2
      ) lmt1.mt_proj lmt2.mt_proj

  | Some name1, Some name2 when name1 = name2->
      List.all2 ov_equal lmt1.mt_decl lmt2.mt_decl

  | _, _ ->
     false

let lmt_fv_ (lmt : local_memtype_) (fv : int Mid.t) =
  List.fold_left (fun fv v ->
    EcIdent.fv_union fv v.ov_type.ty_fv
  ) fv lmt.mt_decl

let lmt_iter_ty_ (f : ty -> unit) (lmt : local_memtype_) =
  List.iter (fun v -> f v.ov_type) lmt.mt_decl

(* -------------------------------------------------------------------- *)
type local_memtype = {
  classical_lmt : local_memtype_;
  quantum_lmt   : local_memtype_;
}

let lmt_hash (lmem : local_memtype) =
  Why3.Hashcons.combine (lmem_hash_ lmem.classical_lmt) (lmem_hash_ lmem.quantum_lmt)

let lmt_fv (lmem : local_memtype) =
  EcIdent.Mid.empty
  |> lmt_fv_ lmem.classical_lmt
  |> lmt_fv_ lmem.quantum_lmt

let lmt_equal
    (ty_equal : ty -> ty -> bool)
    (mt1      : local_memtype)
    (mt2      : local_memtype)
  =
     lmt_equal_ ty_equal mt1.classical_lmt mt2.classical_lmt
  && lmt_equal_ ty_equal mt1.quantum_lmt mt2.quantum_lmt

let lmt_iter_ty (f : ty -> unit) (lmem : local_memtype) =
  lmt_iter_ty_ f lmem.classical_lmt;
  lmt_iter_ty_ f lmem.quantum_lmt

(* -------------------------------------------------------------------- *)

(* [Lmt_schema] if for an axiom schema, and is instantiated to a        *
 * concrete memory type when the axiom schema is.                       *)
type memtype =
  | Lmt_concrete of local_memtype option
  | Lmt_schema

let is_schema = function Lmt_schema -> true | _ -> false

let mt_fv (mt : memtype) =
  match mt with
  | Lmt_schema
  | Lmt_concrete None -> EcIdent.Mid.empty
  | Lmt_concrete (Some lmem) -> lmt_fv lmem

let mt_equal_gen
    (ty_equal : ty -> ty -> bool)
    (mt1      : memtype)
    (mt2      : memtype)
  =
  match mt1, mt2 with
  | Lmt_schema, Lmt_schema ->
     true

  | Lmt_concrete mt1, Lmt_concrete mt2 ->
     oeq (lmt_equal ty_equal) mt1 mt2

  | Lmt_schema,     Lmt_concrete _
  | Lmt_concrete _, Lmt_schema -> false

let mt_equal (mt1 : memtype) (mt2 : memtype) =
  mt_equal_gen ty_equal mt1 mt2

let mt_iter_ty (f : ty -> unit) (mt : memtype) =
  match mt with
  | Lmt_schema ->
     ()

  | Lmt_concrete lmem ->
     oiter (lmt_iter_ty f) lmem

(* -------------------------------------------------------------------- *)
type memenv = memory * memtype

let mem_hash ((mem, mt) : memenv) =
  let base = EcIdent.id_hash mem in

  match mt with
  | Lmt_schema ->
     base

  | Lmt_concrete mt ->
      Why3.Hashcons.combine
        base
        (Why3.Hashcons.combine_option lmt_hash mt)

let me_equal_gen
    (ty_equal  : ty -> ty -> bool)
    ((m1, mt1) : memenv)
    ((m2, mt2) : memenv)
  =
    mem_equal m1 m2 && mt_equal_gen ty_equal mt1 mt2

let me_equal : memenv -> memenv -> bool =
  me_equal_gen ty_equal

(* -------------------------------------------------------------------- *)
let memory   ((m, _ ) : memenv) = m
let memtype  ((_, mt) : memenv) = mt

(* -------------------------------------------------------------------- *)
exception DuplicatedMemoryBinding of symbol
exception NoQuantumMemory

(* -------------------------------------------------------------------- *)
let empty_local_mt ~(witharg : bool) =
  let empty (argname : symbol) =
    let name = if witharg then Some argname else None in
    mk_lmt name [] Msym.empty in

  let classical_lmt = empty arg_symbol in
  let quantum_lmt = empty qarg_symbol in

  Lmt_concrete (Some { classical_lmt; quantum_lmt; })

let empty_local ~(witharg : bool) (me : memory) =
  me, empty_local_mt ~witharg

(* -------------------------------------------------------------------- *)
let schema_mt =
  Lmt_schema

let schema (me : memory) : memenv =
  (me, schema_mt)

(* -------------------------------------------------------------------- *)
let abstract_mt =
  Lmt_concrete None

let abstract (me : memory) : memenv =
  (me, abstract_mt)

(* -------------------------------------------------------------------- *)
let is_bound_lmt_ (lmt : local_memtype_) (x : symbol) =
  Some x = lmt.mt_name || Msym.mem x lmt.mt_proj

let is_bound_lmt (lmem : local_memtype) (x : symbol) =
     is_bound_lmt_ lmem.classical_lmt x
  || is_bound_lmt_ lmem.quantum_lmt x

let is_bound (x : symbol) (mt : memtype) =
  match mt with
  | Lmt_schema -> false
  | Lmt_concrete None -> false
  | Lmt_concrete (Some lmem) -> is_bound_lmt lmem x

let is_bound_pv (pv : prog_var) (mt : memtype) =
  match pv with
  | PVglob _ -> false
  | PVloc id -> is_bound id mt

(* -------------------------------------------------------------------- *)
type lookup = (variable * proj_arg option * int option) option

let lmt_lookup_ (lmt : local_memtype_) (q : quantum) (x : symbol) =
  let mk (v_name : symbol) (v_type : ty) =
    { v_quantum = q; v_name; v_type; } in

  if lmt.mt_name = Some x then
    Some (mk x lmt.mt_ty, None, None)
  else
    match Msym.find_opt x lmt.mt_proj with
    | Some (i, xty) ->
      if lmt.mt_n = 1 then
        Some (mk (odfl x lmt.mt_name) xty, None, None)
      else
        let pa =
          if   is_none lmt.mt_name
          then None
          else Some { arg_quantum = q; arg_ty = lmt.mt_ty; arg_pos = i; } in
        Some (mk x xty, pa, Some i)

    | None -> None

let lmt_lookup (lmem : local_memtype) (x : symbol) : lookup =
  match lmt_lookup_ lmem.classical_lmt `Classical  x with
  | Some _ as aout -> aout
  | None -> lmt_lookup_ lmem.quantum_lmt `Quantum x

let lookup (x : symbol) (mt : memtype) : lookup =
  match mt with
  | Lmt_schema ->
     None

  | Lmt_concrete None ->
     None

  | Lmt_concrete (Some lmem) ->
     lmt_lookup lmem x

let lookup_me (x : symbol) (me : memenv) =
  lookup x (snd me)

(* -------------------------------------------------------------------- *)

let lmt_bind_ (lmt : local_memtype_) (v : ovariable) =
  let mt_decl = lmt.mt_decl @ [v] in
  let mt_proj =
    match v.ov_name with
    | None -> lmt.mt_proj
    | Some x -> Msym.add x (lmt.mt_n, v.ov_type) lmt.mt_proj
  in
  mk_lmt lmt.mt_name mt_decl mt_proj


let lmt_bind (lmt : local_memtype) (v : ovariable) =
  let _ =
    match v.ov_name with
    | None -> ()
    | Some x -> if is_bound_lmt lmt x then raise (DuplicatedMemoryBinding x)
  in
  match v.ov_quantum with
  | `Classical -> { lmt with classical_lmt = lmt_bind_ lmt.classical_lmt v }
  | `Quantum   -> { lmt with quantum_lmt   = lmt_bind_ lmt.quantum_lmt   v }

let lmt_bindall (vs : ovariable list) (lmt : local_memtype) =
  List.fold_left lmt_bind lmt vs

(* -------------------------------------------------------------------- *)
let mt_bindall (vs : ovariable list) (mt : memtype) : memtype =
  match mt with
  | Lmt_schema | Lmt_concrete None -> assert false
  | Lmt_concrete (Some lmt) -> Lmt_concrete (Some (lmt_bindall vs lmt))

let bindall_mt = mt_bindall      (* FIXME *)

(* -------------------------------------------------------------------- *)
let bindall (vs : ovariable list) ((m, mt) : memenv) : memenv =
  (m, mt_bindall vs mt)

(* -------------------------------------------------------------------- *)
let bind_fresh (v : ovariable) ((m, mt) : memenv) =
  let v =
    match v.ov_name with
    | None -> v
    | Some x ->
        if is_bound x mt then
          let rec for_idx idx =
            let x' = Printf.sprintf "%s%d" x idx in
              if is_bound x' mt then for_idx (idx+1)
              else x' in
          let x' = for_idx 0 in
          {v with ov_name = Some x' }
        else
          v
  in
  bindall [v] (m,mt), v

let bindall_fresh (vs : ovariable list) (me : memenv) =
  List.map_fold (fun me v -> bind_fresh v me) me vs

(* -------------------------------------------------------------------- *)
let lmt_subst_ (st : ty -> ty) (lmt : local_memtype_) =
  let decl =
    if st == identity then
      lmt.mt_decl
    else
      List.Smart.map (fun vty ->
        let ty' = st vty.ov_type in
        if ty_equal vty.ov_type ty' then vty else { vty with ov_type = ty'; }
      ) lmt.mt_decl
  in

  if   decl ==(*phy*) lmt.mt_decl
  then lmt
  else mk_lmt lmt.mt_name decl (Msym.map (fun (i, ty) -> i, st ty) lmt.mt_proj)

(* -------------------------------------------------------------------- *)
let lmt_subst (st : ty -> ty) (lmem : local_memtype) =
  let classical_lmt = lmt_subst_ st lmem.classical_lmt in
  let quantum_lmt   = lmt_subst_ st lmem.quantum_lmt in

    if classical_lmt == lmem.classical_lmt && quantum_lmt == lmem.quantum_lmt
    then lmem
    else { classical_lmt; quantum_lmt; }

(* -------------------------------------------------------------------- *)
let mt_subst (st : ty -> ty) (mt : memtype) =
  match mt with
  | Lmt_schema ->
     mt

  | Lmt_concrete None ->
     mt

  | Lmt_concrete (Some lmt) ->
     let lmt' = lmt_subst st lmt in
     if lmt' == lmt then mt else Lmt_concrete (Some lmt')

(* -------------------------------------------------------------------- *)
let me_subst (sm : memory Mid.t) (st : ty -> ty) ((m, mt) as me : memenv) =
  let m'  = EcIdent.Mid.find_def m m sm in
  let mt' = mt_subst st mt in

  if m' == m && mt' == mt then me else (m', mt')

(* -------------------------------------------------------------------- *)
let lmt_get_name_ (lmt : local_memtype_) (s : symbol) (p : int option) =
  match p with
  | None ->
     Some s

  | Some i when Some s = lmt.mt_name ->
     omap fst
       (List.find_opt
          (fun (_, (i', _)) -> i = i')
          (Msym.bindings lmt.mt_proj))

  | Some _ ->
      None

(* -------------------------------------------------------------------- *)
let lmt_get_name
    (lmem : local_memtype)
    (s    : symbol)
    (p    : int option)
  =
  match lmt_get_name_ lmem.classical_lmt s p with
  | Some _ as s -> s
  | None -> lmt_get_name_ lmem.quantum_lmt s p

(* -------------------------------------------------------------------- *)
let mt_get_name
    (mt : memtype)
    (s  : symbol)
    (p  : int option)
  =
  match mt with
  | Lmt_schema ->
     None

  | Lmt_concrete None ->
     None

  | Lmt_concrete (Some mt) ->
     lmt_get_name mt s p

(* -------------------------------------------------------------------- *)
let get_name (s : symbol) (p : int option) ((_, mt) : memenv)  =
  mt_get_name mt s p

(* -------------------------------------------------------------------- *)
let lmt_local_type_ (lmt : local_memtype_) =
  ttuple (List.map ov_type lmt.mt_decl)

let lmt_local_type (lmem : local_memtype) =
  let cl = lmt_local_type_ lmem.classical_lmt in
  let ql = lmt_local_type_ lmem.quantum_lmt in
  (cl, ql)

let mt_local_type (mt : memtype) =
  match mt with
  | Lmt_schema ->
     assert false

  | Lmt_concrete lmem ->
     omap lmt_local_type lmem

let local_type = mt_local_type  (* FIXME *)

(* -------------------------------------------------------------------- *)
let has_locals mt = match mt with
  | Lmt_schema -> assert false
  | Lmt_concrete lmem -> Option.is_some lmem

(* -------------------------------------------------------------------- *)
type lmt_printing = symbol option * ovariable list
type mt_printing  = lmt_printing * lmt_printing

let for_printing (mt : memtype) : mt_printing option =
  match mt with
  | Lmt_schema ->
     None

  | Lmt_concrete None ->
     None

  | Lmt_concrete (Some mt) ->
     let doit mt = mt.mt_name, mt.mt_decl in
     Some (doit mt.classical_lmt, doit mt.quantum_lmt)
