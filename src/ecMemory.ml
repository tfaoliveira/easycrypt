(* -------------------------------------------------------------------- *)
open EcIdent
open EcSymbols
open EcUtils
open EcAst
open EcTypes

module Msym = EcSymbols.Msym

(* -------------------------------------------------------------------- *)
type memory = EcAst.memory

let mem_equal = EcAst.mem_equal

(* -------------------------------------------------------------------- *)
type proj_arg = EcAst.proj_arg

let mk_lmt lmt_name lmt_decl lmt_proj =
  { lmt_name;
    lmt_decl;
    lmt_proj;
    lmt_ty = ttuple (List.map ov_type lmt_decl);
    lmt_n  = List.length lmt_decl;
  }

type memtype = EcAst.memtype

let lmt_hash = EcAst.lmt_hash

let mt_fv = EcAst.mt_fv

let lmt_equal = EcAst.lmt_equal

let mt_equal_gen = EcAst.mt_equal_gen

let mt_equal = EcAst.mt_equal

(* -------------------------------------------------------------------- *)
type memenv = EcAst.memenv

let me_equal_gen = EcAst.me_equal_gen
let me_equal = EcAst.me_equal

(* -------------------------------------------------------------------- *)
let memory   ((m, _ ) : memenv) = m
let memtype  ((_, mt) : memenv) = mt

(* -------------------------------------------------------------------- *)
exception DuplicatedMemoryBinding of symbol

(* -------------------------------------------------------------------- *)
type wa = [`All | `Classical | `Quantum | `None]

let empty_local_mt ~(witharg : wa) =
  let empty (q : quantum) (argname : symbol) =
    let name =
      if witharg = `All || witharg = (q :> wa) then
        Some argname
      else None in
    mk_lmt name [] Msym.empty in

  let classical_lmt = empty `Classical arg_symbol  in
  let quantum_lmt   = empty `Quantum   qarg_symbol in

  Lmt_concrete (Some { classical_lmt; quantum_lmt; })

let empty_local ~(witharg : wa) (me : memory) =
  me, empty_local_mt ~witharg

(* -------------------------------------------------------------------- *)
let abstract_mt = Lmt_concrete None

let abstract (me : memory) : memenv = (me, abstract_mt)

(* -------------------------------------------------------------------- *)
let is_bound_lmt_ (lmt : local_memtype_) (x : symbol) =
  Some x = lmt.lmt_name || Msym.mem x lmt.lmt_proj

let is_bound_lmt (lmem : local_memtype) (x : symbol) =
     is_bound_lmt_ lmem.classical_lmt x
  || is_bound_lmt_ lmem.quantum_lmt x

let is_bound (x : symbol) (mt : memtype) =
  match mt with
  | Lmt_concrete None -> false
  | Lmt_concrete (Some lmem) -> is_bound_lmt lmem x

let is_bound_pv (pv : prog_var) (mt : memtype) =
  match pv with
  | PVglob _ -> false
  | PVloc (_,id) -> is_bound id mt

(* -------------------------------------------------------------------- *)
type lookup = (variable * proj_arg option * int option) option

let lmt_lookup_ (lmt : local_memtype_) (q : quantum) (x : symbol) =
  let mk (v_name : symbol) (v_type : ty) =
    { v_quantum = q; v_name; v_type; } in

  if lmt.lmt_name = Some x then
    Some (mk x lmt.lmt_ty, None, None)
  else
    match Msym.find_opt x lmt.lmt_proj with
    | Some (i, xty) ->
      if lmt.lmt_n = 1 then
        Some (mk (odfl x lmt.lmt_name) xty, None, None)
      else
        let pa =
          if   is_none lmt.lmt_name
          then None
          else Some { arg_quantum = q; arg_ty = lmt.lmt_ty; arg_pos = i; } in
        Some (mk x xty, pa, Some i)

    | None -> None

let lmt_lookup (lmem : local_memtype) (x : symbol) : lookup =
  match lmt_lookup_ lmem.classical_lmt `Classical  x with
  | Some _ as aout -> aout
  | None -> lmt_lookup_ lmem.quantum_lmt `Quantum x

let lookup (x : symbol) (mt : memtype) : lookup =
  match mt with
  | Lmt_concrete None ->
     None

  | Lmt_concrete (Some lmem) ->
     lmt_lookup lmem x

let lookup_me (x : symbol) (me : memenv) =
  lookup x (snd me)

(* -------------------------------------------------------------------- *)
let lmt_bind_ (lmt : local_memtype_) (v : ovariable) =
  let mt_decl = lmt.lmt_decl @ [v] in
  let mt_proj =
    match v.ov_name with
    | None -> lmt.lmt_proj
    | Some x -> Msym.add x (lmt.lmt_n, v.ov_type) lmt.lmt_proj
  in
  mk_lmt lmt.lmt_name mt_decl mt_proj

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
  | Lmt_concrete None -> assert false
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
      lmt.lmt_decl
    else
      List.Smart.map (fun vty ->
        let ty' = st vty.ov_type in
        if ty_equal vty.ov_type ty' then vty else { vty with ov_type = ty'; }
      ) lmt.lmt_decl
  in

  if   decl ==(*phy*) lmt.lmt_decl
  then lmt
  else mk_lmt lmt.lmt_name decl (Msym.map (fun (i, ty) -> i, st ty) lmt.lmt_proj)

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

  | Some i when Some s = lmt.lmt_name ->
     omap fst
       (List.find_opt
          (fun (_, (i', _)) -> i = i')
          (Msym.bindings lmt.lmt_proj))

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
  | Lmt_concrete None ->
     None

  | Lmt_concrete (Some mt) ->
     lmt_get_name mt s p

(* -------------------------------------------------------------------- *)
let get_name (s : symbol) (p : int option) ((_, mt) : memenv)  =
  mt_get_name mt s p

(* -------------------------------------------------------------------- *)
let lmt_local_type_ (lmt : local_memtype_) =
  ttuple (List.map ov_type lmt.lmt_decl)

let lmt_local_type (lmem : local_memtype) =
  let cl = lmt_local_type_ lmem.classical_lmt in
  let ql = lmt_local_type_ lmem.quantum_lmt in
  (cl, ql)

let mt_local_type ( Lmt_concrete lmem : memtype) =
   omap lmt_local_type lmem

let local_type = mt_local_type  (* FIXME *)

(* -------------------------------------------------------------------- *)
let has_quantum (mt : memtype) =
  match mt with
  | Lmt_concrete None ->
     false

  | Lmt_concrete (Some lmem) ->
     lmem.quantum_lmt.lmt_ty <> tunit

(* -------------------------------------------------------------------- *)
let has_locals (Lmt_concrete mt) =
  Option.is_some mt

(* -------------------------------------------------------------------- *)
type lmt_printing = symbol option * ovariable list
type mt_printing  = lmt_printing * lmt_printing

let for_printing (mt : memtype) : mt_printing option =
  match mt with
  | Lmt_concrete None ->
     None

  | Lmt_concrete (Some mt) ->
     let doit mt = mt.lmt_name, mt.lmt_decl in
     Some (doit mt.classical_lmt, doit mt.quantum_lmt)
