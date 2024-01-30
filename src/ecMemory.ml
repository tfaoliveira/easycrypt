(* -------------------------------------------------------------------- *)
open EcSymbols
open EcUtils
open EcAst
open EcTypes

module Msym = EcSymbols.Msym

(* -------------------------------------------------------------------- *)
type memory = EcAst.memory

let mem_equal = EcAst.mem_equal

(* -------------------------------------------------------------------- *)

type memtype = EcAst.memtype

let mt_fv = EcAst.mt_fv

let lmt_equal = EcAst.lmt_equal

let mt_equal = EcAst.mt_equal

(* -------------------------------------------------------------------- *)
type memenv = EcAst.memenv

let me_equal = EcAst.me_equal

(* -------------------------------------------------------------------- *)
let memory   (m,_) = m
let memtype  (_,mt) = mt

(* -------------------------------------------------------------------- *)
exception DuplicatedMemoryBinding of symbol

(* -------------------------------------------------------------------- *)
let lmt_empty =
  mk_lmt Msym.empty Msym.empty

let mt_global =
  mk_mt (Some lmt_empty) gvs_all

let lmt_add_params lmt arg params =
  let lmt_symb = lmt.lmt_symb in
  let ty = ttuple (List.map ov_type params) in
  (* Add arg *)
  let lmt_symb = Msym.add arg (None, ty) lmt_symb in


  (* Add projs *)
  let lmt_symb, lmt_proj =
    match params with
    | [{ov_name = Some s}] ->
      let lmt_symb =
        let change o =
          if o <> None then raise (DuplicatedMemoryBinding s);
          Some (Some(arg, ty, None), ty) in
        Msym.change change s lmt_symb in
      let lmt_proj = Msym.add arg (Ptbl_direct s) lmt.lmt_proj in
      lmt_symb, lmt_proj
    | _ ->
      let add_proj lmt_symb i ov =
        ofold (fun s m ->
            let change o =
              if o <> None then raise (DuplicatedMemoryBinding s);
              Some (Some(arg, ty, Some i), ov_type ov) in
            Msym.change change s m) lmt_symb ov.ov_name in
      let lmt_symb =
        List.fold_lefti add_proj lmt_symb params in
      let add_proji ma i ov =
        ofold (fun s m -> EcMaps.Mint.add i s m) ma ov.ov_name in
      let projs = List.fold_lefti add_proji EcMaps.Mint.empty params in
      let lmt_proj = Msym.add arg (Ptbl_proj projs) lmt.lmt_proj in
      lmt_symb, lmt_proj
  in
  (* Build the result *)
  mk_lmt lmt_symb lmt_proj

let mt_add_params mt arg params =
  mk_mt (Some (lmt_add_params (oget mt.mt_lmt) arg params)) mt.mt_gvs

let mt_init_params params =
  mt_add_params mt_global arg_symbol params

let mt_init_res ty =
  mt_add_params mt_global res_symbol [{ ov_name = None; ov_type = ty }]

let lmt_add_ovars lmt vs =
  let add lmt_symb ov =
    ofold
      (fun s m ->
        let change o =
          if o <> None then raise (DuplicatedMemoryBinding s);
          Some (None, ov_type ov)
        in
        Msym.change change s m)
      lmt_symb ov.ov_name
  in
  let lmt_symb =
    List.fold_left add lmt.lmt_symb vs in
  mk_lmt lmt_symb lmt.lmt_proj

let mt_add_ovars mt vs =
  mk_mt (Some (lmt_add_ovars (oget mt.mt_lmt) vs)) mt.mt_gvs

let mt_add_vars mt vs =
  mt_add_ovars mt (List.map ovar_of_var vs)

let lmt_lookup x lmt =
  Msym.find_opt x lmt.lmt_symb

let lmt_lookup_pp lmt x i =
  match Msym.find_opt x lmt.lmt_proj, i with
  | Some (Ptbl_direct z), None -> Some z
  | Some (Ptbl_proj m), Some i -> EcMaps.Mint.find_opt i m
  | _, None -> Some x
  | _, Some _ -> None

let mt_lookup mt x =
  omap_dfl (lmt_lookup x) None mt.mt_lmt

let mt_lookup_pp mt x i =
  match mt.mt_lmt with
  | None -> if i = None then Some x else None
  | Some lmt -> lmt_lookup_pp lmt x i

let me_lookup (_,mt) x = mt_lookup mt x

let me_lookup_pp (_, mt) x i = mt_lookup_pp mt x i

let is_bound mt x = mt_lookup mt x <> None





(*
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
  Some x = lmt.lmt_name || Msym.mem x lmt.lmt_proj

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
    if lmt.lmt_name = Some x then
      Some ({v_name = x; v_type = lmt.lmt_ty}, None, None)
    else
      match Msym.find_opt x lmt.lmt_proj with
      | Some (i,xty) ->
        if lmt.lmt_n = 1 then
          Some ({ v_name = odfl x lmt.lmt_name; v_type = xty}, None, None)
        else
          let v = { v_name = x; v_type = xty } in
          let pa =
            if lmt.lmt_name = None then None
            else Some { arg_ty = lmt.lmt_ty; arg_pos = i; } in
          Some(v, pa, Some i)
      | None -> None

let lookup_me x me = lookup x (snd me)

let is_bound_pv pv me = match pv with
  | PVglob _ -> false
  | PVloc id -> is_bound id me

(* -------------------------------------------------------------------- *)
let bindall_lmt (vs : ovariable list) lmt =
  let n = List.length lmt.lmt_decl in
  let add_proj mt_proj i v =
    match v.ov_name with
    | None -> mt_proj
    | Some x ->
        if lmt.lmt_name = Some x then raise (DuplicatedMemoryBinding x);
        let merger = function
          | Some _ -> raise (DuplicatedMemoryBinding x)
          | None   -> Some (n + i,v.ov_type)
        in Msym.change merger x mt_proj
  in
  let mt_decl = lmt.lmt_decl @ vs in
  let mt_proj = List.fold_lefti add_proj lmt.lmt_proj vs in
  mk_lmt lmt.lmt_name mt_decl mt_proj

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
    let is_bound x m = Some x = lmt.lmt_name || Msym.mem x m in
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
    let _, vs = List.map_fold fresh_pv lmt.lmt_proj vs in
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
    let decl = mt.lmt_decl in
    let decl' =
      if st == identity then decl
      else
        List.Smart.map (fun vty ->
            let ty' = st vty.ov_type in
            if ty_equal vty.ov_type ty' then vty else {vty with ov_type = ty'}) decl in
    if decl == decl' then o
    else
      let lmt = mk_lmt
          mt.lmt_name decl' (Msym.map (fun (i,ty) -> i, st ty) mt.lmt_proj) in
      Lmt_concrete (Some lmt)

let me_subst sm st (m,mt as me) =
  let m' = EcIdent.Mid.find_def m m sm in
  let mt' = mt_subst st mt in
  if m' == m && mt' == mt then me else
    (m', mt')

(* -------------------------------------------------------------------- *)
let for_printing mt =
  match mt with
  | Lmt_schema -> None
  | Lmt_concrete None -> None
  | Lmt_concrete (Some mt) -> Some (mt.lmt_name, mt.lmt_decl)

(* -------------------------------------------------------------------- *)
let rec pp_list sep pp fmt xs =
  let pp_list = pp_list sep pp in
    match xs with
    | []      -> ()
    | [x]     -> Format.fprintf fmt "%a" pp x
    | x :: xs -> Format.fprintf fmt "%a%(%)%a" pp x sep pp_list xs

let dump_memtype mt =
  match mt with
  | Lmt_schema        -> "schema"
  | Lmt_concrete None -> "abstract"
  | Lmt_concrete (Some mt) ->
    let pp_vd fmt v =
      Format.fprintf fmt "@[%s: %s@]"
        (odfl "_" v.ov_name)
        (EcTypes.dump_ty v.ov_type)
    in
    Format.asprintf "@[{@[%a@]}@]" (pp_list ",@ " pp_vd) mt.lmt_decl

(* -------------------------------------------------------------------- *)
let get_name s p (_,mt) =
  match mt with
  | Lmt_schema        -> None
  | Lmt_concrete None -> None
  | Lmt_concrete (Some mt) ->
    match p with
    | None -> Some s
    | Some i ->
      if Some s = mt.lmt_name then
        omap fst (List.find_opt (fun (_,(i',_)) -> i = i') (Msym.bindings mt.lmt_proj))
      else
        None

(* -------------------------------------------------------------------- *)

let local_type mt =
  match mt with
  | Lmt_schema -> assert false
  | Lmt_concrete None -> None
  | Lmt_concrete (Some mt) -> Some (ttuple (List.map ov_type mt.lmt_decl))

let has_locals mt = match mt with
  | Lmt_concrete (Some _) -> true
  | Lmt_concrete None -> false
  | Lmt_schema -> assert false
*)
