(* -------------------------------------------------------------------- *)
(*open EcSymbols *)
open EcUtils
open EcTypes


module Msym = EcSymbols.Msym

(* -------------------------------------------------------------------- *)
type memory = EcIdent.t

let mem_equal = EcIdent.id_equal

(* -------------------------------------------------------------------- *)

type local_memtype = EcTypes.local_memtype

type memtype = EcTypes.memtype

let lmt_equal ty_equal mt1 mt2 =
  Msym.equal (fun (o1, ty1) (o2,ty2) ->
      ty_equal ty1 ty2 &&
      opt_equal (fun (s1, ty1, i1) (s2, ty2, i2) ->
          i1 == i2 && ty_equal ty1 ty2 && s1 = s2) o1 o2) mt1.lmt_symb mt2.lmt_symb

(* -------------------------------------------------------------------- *)
type memenv = memory * memtype

let me_equal (m1,mt1) (m2, mt2) =
  EcIdent.id_equal m1 m2 && EcTypes.mt_equal mt1 mt2

let me_hash (mem,mt) =
  Why3.Hashcons.combine
      (EcIdent.id_hash mem)
      (mt_hash mt)

(*
let mem_hash (mem,mt) = match mt with
  | Lmt_schema -> 0
  | Lmt_concrete mt ->
    Why3.Hashcons.combine
      (EcIdent.id_hash mem)
      (Why3.Hashcons.combine_option lmem_hash mt)

let me_equal_gen ty_equal (m1,mt1) (m2,mt2) =
  mem_equal m1 m2 && mt_equal_gen ty_equal mt1 mt2

let me_equal = me_equal_gen ty_equal
*)

(* -------------------------------------------------------------------- *)
let memory   (m,_) = m
let memtype  (_,mt) = mt

let me_lookup (_, mt) x = EcTypes.mt_lookup mt x
(* -------------------------------------------------------------------- *)
(*exception DuplicatedMemoryBinding of symbol

(* -------------------------------------------------------------------- *)
let empty_local_mt ~witharg =
  let lmt = mk_lmt (if witharg then Some arg_symbol else None) [] Msym.empty in
  Lmt_concrete (Some lmt)

let empty_local ~witharg (me : memory) =
  me, empty_local_mt ~witharg

let schema_mt = Lmt_schema
let schema (me:memory) = me, schema_mt

let abstract_mt = Lmt_concrete None
let abstract (me:memory) = me, abstract_mt

let is_schema = function Lmt_schema -> true | _ -> false

(* -------------------------------------------------------------------- *)

let is_bound_lmt x lmt =
  Some x = lmt.mt_name || Msym.mem x lmt.mt_proj

let is_bound x mt =
  match mt with
  | Lmt_schema -> false
  | Lmt_concrete None -> false
  | Lmt_concrete (Some lmt) -> is_bound_lmt x lmt

let lookup (x : symbol) (mt : memtype) : (variable * proj_arg option * int option) option =
  match mt with
  | Lmt_schema        -> None
  | Lmt_concrete None -> None
  | Lmt_concrete (Some lmt) ->
    if lmt.mt_name = Some x then
      Some ({v_name = x; v_type = lmt.mt_ty}, None, None)
    else
      match Msym.find_opt x lmt.mt_proj with
      | Some (i,xty) ->
        if lmt.mt_n = 1 then
          Some ({ v_name = odfl x lmt.mt_name; v_type = xty}, None, None)
        else
          let v = { v_name = x; v_type = xty } in
          let pa =
            if lmt.mt_name = None then None
            else Some { arg_ty = lmt.mt_ty; arg_pos = i; } in
          Some(v, pa, Some i)
      | None -> None

let lookup_me x me = lookup x (snd me)

let is_bound_pv pv me = match pv with
  | PVglob _ -> false
  | PVloc id -> is_bound id me

(* -------------------------------------------------------------------- *)
let bindall_lmt (vs : ovariable list) lmt =
  let n = List.length lmt.mt_decl in
  let add_proj mt_proj i v =
    match v.ov_name with
    | None -> mt_proj
    | Some x ->
        if lmt.mt_name = Some x then raise (DuplicatedMemoryBinding x);
        let merger = function
          | Some _ -> raise (DuplicatedMemoryBinding x)
          | None   -> Some (n + i,v.ov_type)
        in Msym.change merger x mt_proj
  in
  let mt_decl = lmt.mt_decl @ vs in
  let mt_proj = List.fold_lefti add_proj lmt.mt_proj vs in
  mk_lmt lmt.mt_name mt_decl mt_proj

let bindall_mt (vs : ovariable list) (mt : memtype) : memtype =
  match mt with
  | Lmt_schema | Lmt_concrete None -> assert false
  | Lmt_concrete (Some lmt) -> Lmt_concrete (Some (bindall_lmt vs lmt))

let bindall (vs : ovariable list) ((m,mt) : memenv) : memenv =
  m, bindall_mt vs mt

let bindall_fresh (vs : ovariable list) ((m,mt) : memenv) =
  match mt with
  | Lmt_schema | Lmt_concrete None -> assert false
  | Lmt_concrete (Some lmt) ->
    let is_bound x m = Some x = lmt.mt_name || Msym.mem x m in
    let fresh_pv m v =
      match v.ov_name with
      | None   -> m, v
      | Some name ->
          let name =
            if not(is_bound name m) then name
            else
              let rec for_idx idx =
                let x = Printf.sprintf "%s%d" name idx in
                if is_bound x m then for_idx (idx+1)
                else x in
              for_idx 0 in
          Msym.add name (-1,v.ov_type) m, { v with ov_name = Some name } in
    let _, vs = List.map_fold fresh_pv lmt.mt_proj vs in
    let lmt = bindall_lmt vs lmt in
    (m, Lmt_concrete (Some lmt)), vs

let bind_fresh v me =
  let me, vs = bindall_fresh [v] me in
  me, as_seq1 vs

(* -------------------------------------------------------------------- *)

let mt_subst st o =
  match o with
  | Lmt_schema -> o
  | Lmt_concrete None -> o
  | Lmt_concrete (Some mt) ->
    let decl = mt.mt_decl in
    let decl' =
      if st == identity then decl
      else
        List.Smart.map (fun vty ->
            let ty' = st vty.ov_type in
            if ty_equal vty.ov_type ty' then vty else {vty with ov_type = ty'}) decl in
    if decl == decl' then o
    else
      let lmt = mk_lmt
          mt.mt_name decl' (Msym.map (fun (i,ty) -> i, st ty) mt.mt_proj) in
      Lmt_concrete (Some lmt)

let me_subst sm st (m,mt as me) =
  let m' = EcIdent.Mid.find_def m m sm in
  let mt' = EcTypes.mt_subst st mt in
  if m' == m && mt' == mt then me else
    (m', mt')

(* -------------------------------------------------------------------- *)
let for_printing mt =
  match mt with
  | Lmt_schema -> None
  | Lmt_concrete None -> None
  | Lmt_concrete (Some mt) -> Some (mt.mt_name, mt.mt_decl)

(* -------------------------------------------------------------------- *)
let rec pp_list sep pp fmt xs =
  let pp_list = pp_list sep pp in
    match xs with
    | []      -> ()
    | [x]     -> Format.fprintf fmt "%a" pp x
    | x :: xs -> Format.fprintf fmt "%a%(%)%a" pp x sep pp_list xs

(* -------------------------------------------------------------------- *)
let get_name s p (_,mt) =
  match mt with
  | Lmt_schema        -> None
  | Lmt_concrete None -> None
  | Lmt_concrete (Some mt) ->
    match p with
    | None -> Some s
    | Some i ->
      if Some s = mt.mt_name then
        omap fst (List.find_opt (fun (_,(i',_)) -> i = i') (Msym.bindings mt.mt_proj))
      else
        None

(* -------------------------------------------------------------------- *)

let local_type mt =
  match mt with
  | Lmt_schema -> assert false
  | Lmt_concrete None -> None
  | Lmt_concrete (Some mt) -> Some (ttuple (List.map ov_type mt.mt_decl))

let has_locals mt = match mt with
  | Lmt_concrete (Some _) -> true
  | Lmt_concrete None -> false
  | Lmt_schema -> assert false
*)
