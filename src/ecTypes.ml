(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open EcIdent
open EcPath
open EcUid

module BI = EcBigInt

(* -------------------------------------------------------------------- *)
type locality  = [`Local | `Declare | `Global]
type is_local  = [`Local | `Global]

let local_of_locality = function
  | `Local   -> `Local
  | `Global  -> `Global
  | `Declare -> `Local

(* -------------------------------------------------------------------- *)
type pvar_kind =
  | PVKglob
  | PVKloc

type prog_var =
  | PVglob of EcPath.xpath
  | PVloc of EcSymbols.symbol

(* FIXME: this function should always returns empty *)
let pv_fv = function
  | PVglob x -> EcPath.x_fv Mid.empty x
  | PVloc _ -> Mid.empty

let pv_equal v1 v2 = match v1, v2 with
  | PVglob x1, PVglob x2 ->
    EcPath.x_equal x1 x2
  | PVloc i1, PVloc i2 -> EcSymbols.sym_equal i1 i2
  | PVloc _, PVglob _ | PVglob _, PVloc _ -> false

let pv_kind = function
  | PVglob _ -> PVKglob
  | PVloc _ -> PVKloc

let pv_hash v =
  let h = match v with
    | PVglob x -> EcPath.x_hash x
    | PVloc i -> Hashtbl.hash i in

  Why3.Hashcons.combine
    h (if pv_kind v = PVKglob then 1 else 0)

let pv_compare v1 v2 =
  match v1, v2 with
  | PVloc i1,  PVloc i2  -> EcSymbols.sym_compare i1 i2
  | PVglob x1, PVglob x2 -> EcPath.x_compare x1 x2
  | _, _ -> Stdlib.compare (pv_kind v1) (pv_kind v2)

let pv_compare_p v1 v2 =
  match v1, v2 with
  | PVloc i1,  PVloc i2  -> EcSymbols.sym_compare i1 i2
  | PVglob x1, PVglob x2 -> EcPath.x_compare_na x1 x2
  | _, _ -> Stdlib.compare (pv_kind v1) (pv_kind v2)

let pv_ntr_compare v1 v2 =
  match v1, v2 with
  | PVloc i1,  PVloc i2  -> EcSymbols.sym_compare i1 i2
  | PVglob x1, PVglob x2 -> EcPath.x_ntr_compare x1 x2
  | _, _ -> Stdlib.compare (pv_kind v1) (pv_kind v2)

let is_loc  = function PVloc _ -> true  | PVglob _ -> false
let is_glob = function PVloc _ -> false | PVglob _ -> true

let get_loc = function PVloc id -> id | PVglob _ -> assert false
let get_glob = function PVloc _ -> assert false | PVglob xp -> xp

let symbol_of_pv = function
  | PVglob x -> x.EcPath.x_sub
  | PVloc id -> id

let string_of_pvar_kind = function
  | PVKglob -> "PVKglob"
  | PVKloc  -> "PVKloc"

let string_of_pvar (p : prog_var) =
  let sp = match p with
    | PVglob x -> EcPath.x_tostring x
    | PVloc id -> id in

  Printf.sprintf "%s[%s]"
    sp (string_of_pvar_kind (pv_kind p))

let name_of_pvar pv =
  match pv with
  | PVloc x -> x
  | PVglob xp -> EcPath.xbasename xp

let pv_loc id = PVloc id

let arg_symbol = "arg"
let res_symbol = "res"
let pv_arg = PVloc arg_symbol
let pv_res =  PVloc res_symbol

let xp_glob x =
  let top = x.EcPath.x_top in
  if top.EcPath.m_args = [] then x else
    (* remove the functor argument *)
    let ntop = EcPath.mpath top.m_top [] in
    EcPath.xpath ntop x.EcPath.x_sub

let pv_glob x = PVglob (xp_glob x)

let pv_subst m_subst px = match px with
  | PVglob x ->
    let mp' = m_subst x in
    if x == mp' then px else pv_glob mp'
  | PVloc _ -> px

(* -------------------------------------------------------------------- *)

(*
type functor_fun = {
  ff_params : Sid.t;
  ff_fun : xpath;
   (* The xpath is fully applied, argument can be abstract module in Sid.t; *)
}
*)

type gvar_set_node =
  | Empty                              (* The empty memory                           *)
  | All                                (* The memory of All global                   *)
  | Set       of Sx.t                  (* The memory restricted to the variable in s *)
  | GlobFun   of xpath                 (* The global memory used by the function     *)
  | Union     of gvar_set * gvar_set   (* Union                                      *)
  | Diff      of gvar_set * gvar_set   (* Difference                                 *)
  | Inter     of gvar_set * gvar_set   (* Intersection                               *)

and gvar_set =
  { gvs_node : gvar_set_node;
    gvs_tag  : int;
    gvs_fv   : int EcIdent.Mid.t;
  }

let gvs_equal : gvar_set -> gvar_set -> bool = (==)
let gvs_hash gvs = gvs.gvs_tag
let gvs_fv gvs = gvs.gvs_fv
(*
let ff_equal ff1 ff2 =
  x_equal ff1.ff_fun ff2.ff_fun && Sid.equal ff1.ff_params ff2.ff_params
*)

module Hsgvs = Why3.Hashcons.Make (struct
  type t = gvar_set

  let equal gvs1 gvs2 =
    match gvs1.gvs_node, gvs2.gvs_node with
    | Empty, Empty -> true
    | All  , All   -> true
    | Set x, Set y -> Sx.equal x y
    | GlobFun f1, GlobFun f2 -> x_equal f1 f2
    | Union(s11,s12), Union(s21,s22)
    | Diff (s11,s12), Diff (s21,s22)
    | Inter(s11,s12), Inter(s21,s22) -> gvs_equal s11 s21 && gvs_equal s12 s22
    | _, _ -> false

  let hash gvs =
    match gvs.gvs_node with
    | Empty        -> 0
    | All          -> 1
    | Set s        -> Sx.fold (fun x h -> Why3.Hashcons.combine (x_hash x) h) s 2
    | GlobFun f    -> x_hash f
    | Union(s1,s2) -> Why3.Hashcons.combine_list gvs_hash 3 [s1; s2]
    | Diff (s1,s2) -> Why3.Hashcons.combine_list gvs_hash 4 [s1; s2]
    | Inter(s1,s2) -> Why3.Hashcons.combine_list gvs_hash 5 [s1; s2]

  let fv gvs =
    match gvs with
    | Empty | All  -> Mid.empty
    | Set x        -> Mid.empty (* global variable path has not ident *)
    | GlobFun f    -> x_fv Mid.empty f
    | Union(s1,s2) | Diff (s1,s2) | Inter(s1,s2) ->
        fv_union (gvs_fv s1) (gvs_fv s2)

  let tag n gvs = { gvs with gvs_tag = n; gvs_fv = fv gvs.gvs_node; }
end)

let mk_gvs node =
  Hsgvs.hashcons { gvs_node = node; gvs_tag = -1; gvs_fv = Mid.empty }

let gvs_empty = mk_gvs Empty
let gvs_all = mk_gvs All
let gvs_set s = mk_gvs (Set s)
let gvs_fun f = mk_gvs (GlobFun f)

let gvs_union s1 s2 =
  match s1.gvs_node, s2.gvs_node with
  | All, _ | _, All -> gvs_all
  | Empty, _ -> s2
  | _, Empty -> s1
  | Set s1, Set s2 -> gvs_set (Sx.union s1 s2)
  | _, _ -> mk_gvs (Union(s1,s2))

let gvs_diff s1 s2 =
  match s1.gvs_node, s2.gvs_node with
  | Empty, _ | _, All -> gvs_empty
  | _, Empty -> s1
  | Set s1, Set s2 -> gvs_set (Sx.diff s1 s2)
  | _, _ -> mk_gvs  (Diff (s1,s2))

let gvs_inter s1 s2 =
  match s1.gvs_node, s2.gvs_node with
  | All, _ -> s2
  | _, All -> s1
  | Empty, _ | _, Empty -> gvs_empty
  | Set s1, Set s2 -> gvs_set (Sx.inter s1 s2)
  | _, _ -> mk_gvs (Inter(s1,s2))

(* -------------------------------------------------------------------- *)

type var_set = {
  lvs : Ssym.t;
  gvs : gvar_set;
}

let vs_hash vs = gvs_hash vs.gvs
let vs_equal vs1 vs2 = gvs_equal vs1.gvs vs2.gvs && Ssym.equal vs1.lvs vs2.lvs
let vs_fv vs = vs.gvs.gvs_fv

let vs_empty = { lvs = Ssym.empty; gvs = gvs_empty }
let vs_all lvs = { lvs; gvs = gvs_all }

let vs_globfun f = { lvs = Ssym.empty; gvs = gvs_fun f }

let vs_union s1 s2 =
  { lvs = Ssym.union s1.lvs s2.lvs; gvs = gvs_union s1.gvs s2.gvs }

let vs_diff s1 s2 =
  { lvs = Ssym.diff s1.lvs s2.lvs; gvs = gvs_diff s1.gvs s2.gvs }

let vs_inter s1 s2 =
  { lvs = Ssym.inter s1.lvs s2.lvs; gvs = gvs_inter s1.gvs s2.gvs }


(* -------------------------------------------------------------------- *)
type ty = {
  ty_node : ty_node;
  ty_fv   : int EcIdent.Mid.t; (* only ident appearing in path *)
  ty_tag  : int;
}

and ty_node =
  | Tmem    of memtype
  | Tunivar of EcUid.uid
  | Tvar    of EcIdent.t
  | Ttuple  of ty list
  | Tconstr of EcPath.path * ty list
  | Tfun    of ty * ty

and local_memtype =
  { lmt_symb : ((EcSymbols.symbol * ty * int) option * ty) Msym.t;
    lmt_proj : EcSymbols.symbol EcMaps.Mint.t Msym.t;
    lmt_fv   : int EcIdent.Mid.t;
    lmt_tag  : int;
  }

(* The type of memory restricted to a gvar_set *)
(* [lmt = None] is for an axiom schema, and is instantiated to a concrete
   memory type when the axiom schema is.  *)
and memtype = {
  lmt : local_memtype option;
  gvs : gvar_set;
  mt_fv : int EcIdent.Mid.t;
  mt_tag : int;
}

let is_schema mt = mt.lmt = None

type dom = ty list

let ty_equal : ty -> ty -> bool = (==)
let ty_hash ty = ty.ty_tag
let ty_fv ty = ty.ty_fv

let lmt_equal : local_memtype -> local_memtype -> bool = (==)
let lmt_hash lmt = lmt.lmt_tag
let lmt_fv lmt = lmt.lmt_fv

let mt_equal : memtype -> memtype -> bool = (==)
let mt_hash mt = mt.mt_tag
let mt_fv mt = mt.mt_fv

module Hsty = Why3.Hashcons.Make (struct
  type t = ty

  let equal ty1 ty2 =
    match ty1.ty_node, ty2.ty_node with
    | Tmem mt1, Tmem mt2 ->
        mt_equal mt1 mt2

    | Tunivar u1, Tunivar u2 ->
        uid_equal u1 u2

    | Tvar v1, Tvar v2 ->
        id_equal v1 v2

    | Ttuple lt1, Ttuple lt2 ->
        List.all2 ty_equal lt1 lt2

    | Tconstr (p1, lt1), Tconstr (p2, lt2) ->
        EcPath.p_equal p1 p2 && List.all2 ty_equal lt1 lt2

    | Tfun (d1, c1), Tfun (d2, c2)->
        ty_equal d1 d2 && ty_equal c1 c2

    | _, _ -> false

  let hash ty =
    match ty.ty_node with
    | Tmem mt          -> mt_hash mt
    | Tunivar u        -> u
    | Tvar    id       -> EcIdent.tag id
    | Ttuple  tl       -> Why3.Hashcons.combine_list ty_hash 0 tl
    | Tconstr (p, tl)  -> Why3.Hashcons.combine_list ty_hash p.p_tag tl
    | Tfun    (t1, t2) -> Why3.Hashcons.combine (ty_hash t1) (ty_hash t2)

  let fv ty =
    let union ex =
      List.fold_left (fun s a -> fv_union s (ex a)) Mid.empty in

    match ty with
    | Tmem mt          -> mt.mt_fv
    | Tunivar _        -> Mid.empty
    | Tvar    _        -> Mid.empty (* FIXME: section *)
    | Ttuple  tys      -> union (fun a -> a.ty_fv) tys
    | Tconstr (_, tys) -> union (fun a -> a.ty_fv) tys
    | Tfun    (t1, t2) -> union (fun a -> a.ty_fv) [t1; t2]

  let tag n ty = { ty with ty_tag = n; ty_fv = fv ty.ty_node; }
end)

let mk_ty node =
  Hsty.hashcons { ty_node = node; ty_tag = -1; ty_fv = Mid.empty }

module MSHty = EcMaps.MakeMSH(struct
  type t = ty
  let tag t = t.ty_tag
end)

module Mty = MSHty.M
module Sty = MSHty.S
module Hty = MSHty.H

(* -------------------------------------------------------------------- *)
module Hslmt = Why3.Hashcons.Make (struct

  type t = local_memtype
  (*
  { lmt_symb : ((EcSymbols.symbol * ty * int) option * ty) EcSymbols.Msym.t;
    lmt_proj : EcSymbols.symbol EcMaps.Mint.t EcSymbols.Msym.t;
    lmt_fv   : int EcIdent.Mid.t;
    lmt_tag  : int;
  } *)

  let equal lmt1 lmt2 =
    Msym.equal
       (fun (o1, ty1) (o2, ty2) ->
         ty_equal ty1 ty2 &&
         opt_equal (fun (s1,ty1,i1) (s2,ty2, i2) ->
             i1 == i2 && ty_equal ty1 ty2 && sym_equal s1 s2) o1 o2)
       lmt1.lmt_symb lmt2.lmt_symb

  let hash lmt =
    Msym.fold
      (fun s (_,ty) hash -> Why3.Hashcons.combine2 (Hashtbl.hash s) (ty_hash ty) hash)
      lmt.lmt_symb 0

  let fv lmt =
    (* Remark no need to take the type in the first componant since the variable is declared *)
    Msym.fold (fun _ (_, ty) fv -> fv_union fv (ty.ty_fv))
      lmt.lmt_symb Mid.empty

  let tag n lmt =
    { lmt with
      lmt_tag = n; lmt_fv = fv lmt }
end)

let mk_lmt lmt_symb lmt_proj =
  Hslmt.hashcons { lmt_symb; lmt_proj; lmt_tag = -1; lmt_fv = Mid.empty}

let lmt_map_ty (f:ty -> ty) lmt =
  let lmt_sym =
    Msym.map (fun (o, ty) -> omap (fun (s,ty,i) -> s, f ty, i) o, f ty) lmt.lmt_symb in
  mk_lmt lmt_sym lmt.lmt_proj

let lmt_iter_ty (f:ty -> unit) lmt =
  (* We do not do o since the variable occurs in another declaration *)
  Msym.iter (fun _ (o,ty) -> f ty) lmt.lmt_symb

let lmt_fold_ty (f:'a -> ty -> 'a) a lmt =
  Msym.fold (fun _ (_, ty) a -> f a ty) lmt.lmt_symb a

let lmt_sub_exists_ty f lmt =
  Msym.exists (fun _ (_, ty) -> f ty) lmt.lmt_symb

(* -------------------------------------------------------------------- *)
module Hsmt = Why3.Hashcons.Make (struct

  type t = memtype
  (*
  {
    lmt : local_memtype;
    gvs : gvar_set;
    mt_fv : int EcIdent.Mid.t;
    mt_tag : int;
  }
  *)

  let equal mt1 mt2 =
    opt_equal lmt_equal mt1.lmt mt2.lmt && gvs_equal mt1.gvs mt2.gvs

  let hash mt =
    Why3.Hashcons.combine (ohash lmt_hash mt.lmt) (gvs_hash mt.gvs)

  let tag n mt =
    { mt with
      mt_tag = n; mt_fv = fv_union (omap_dfl lmt_fv Mid.empty mt.lmt) (gvs_fv mt.gvs) }
end)

let mk_mto lmt gvs =
  Hsmt.hashcons { lmt; gvs; mt_tag = -1; mt_fv = Mid.empty}

let mt_map_ty (f:ty -> ty) mt =
  mk_mto (omap (lmt_map_ty f) mt.lmt) mt.gvs

let mt_iter_ty (f:ty -> unit) mt = oiter (lmt_iter_ty f) mt.lmt

let mt_fold_ty (f:'a -> ty -> 'a) a mt =
  ofold (fun lmt a -> lmt_fold_ty f a lmt) a mt.lmt

let mt_sub_exists_ty f mt = oexists (lmt_sub_exists_ty f) mt.lmt

let lmt_concrete (mt:memtype) = ofdfl (fun _ -> assert false) mt.lmt

let mt_schema = mk_mto None gvs_all

let mk_mt lmt gvs = mk_mto (Some lmt) gvs

(* -------------------------------------------------------------------- *)
let tuni uid     = mk_ty (Tunivar uid)
let tvar id      = mk_ty (Tvar id)
let tconstr p lt = mk_ty (Tconstr (p, lt))
let tfun t1 t2   = mk_ty (Tfun (t1, t2))
let tmem mt      = mk_ty (Tmem mt)

let tmrestr (mt:memtype) (s:var_set) =
  let lmt = lmt_concrete mt in
  let lmt_symb = ref (Msym.set_diff lmt.lmt_symb s.lvs) in
  let lmt_proj =
    Msym.diff (fun x mp _ ->
        let sp = EcMaps.Mint.fold (fun _ x sp -> Ssym.add x sp) mp Ssym.empty in
        lmt_symb := Msym.set_diff !lmt_symb sp;
        None) lmt.lmt_proj s.lvs in
  let lmt = mk_lmt !lmt_symb lmt_proj in
  tmem (mk_mt lmt (gvs_inter mt.gvs s.gvs))

(* -------------------------------------------------------------------- *)
let tunit      = tconstr EcCoreLib.CI_Unit .p_unit    []
let tbool      = tconstr EcCoreLib.CI_Bool .p_bool    []
let tint       = tconstr EcCoreLib.CI_Int  .p_int     []
let txint      = tconstr EcCoreLib.CI_xint .p_xint    []

let tdistr ty  = tconstr EcCoreLib.CI_Distr.p_distr   [ty]
let toption ty = tconstr EcCoreLib.CI_Option.p_option [ty]
let treal      = tconstr EcCoreLib.CI_Real .p_real    []
let tcpred ty  = tfun ty tbool

let trealp    = tconstr EcCoreLib.CI_Xreal.p_realp []
let txreal    = tconstr EcCoreLib.CI_Xreal.p_xreal []

let ttuple lt    =
  match lt with
  | []  -> tunit
  | [t] -> t
  | _ -> mk_ty (Ttuple lt)

let toarrow dom ty =
  List.fold_right tfun dom ty

let tpred t = tfun t tbool

(* -------------------------------------------------------------------- *)
let tytuple_flat (ty : ty) =
  match ty.ty_node with Ttuple tys -> tys | _ -> [ty]

let rec tyfun_flat (ty : ty) =
  match ty.ty_node with
  | Tfun (t1, t2) ->
      let dom, codom = tyfun_flat t2 in (t1 :: dom, codom)
  | _ ->
      ([], ty)

(* -------------------------------------------------------------------- *)
let as_tdistr (ty : ty) =
  match ty.ty_node with
  | Tconstr (p, [sty])
      when EcPath.p_equal p EcCoreLib.CI_Distr.p_distr
    -> Some sty

  | _ -> None

let is_tdistr (ty : ty) = as_tdistr ty <> None

(* -------------------------------------------------------------------- *)
let ty_map f t =
  match t.ty_node with
  | Tmem mt ->
      tmem (mt_map_ty f mt)

  | Tunivar _ | Tvar _ -> t

  | Ttuple lty ->
     ttuple (List.Smart.map f lty)

  | Tconstr (p, lty) ->
     let lty = List.Smart.map f lty in
     tconstr p lty

  | Tfun (t1, t2) ->
      tfun (f t1) (f t2)

let ty_fold f s ty =
  match ty.ty_node with
  | Tmem mt -> mt_fold_ty f s mt
  | Tunivar _ | Tvar _ -> s
  | Ttuple lty -> List.fold_left f s lty
  | Tconstr(_, lty) -> List.fold_left f s lty
  | Tfun(t1,t2) -> f (f s t1) t2

let ty_sub_exists f t =
  match t.ty_node with
  | Tmem mt -> mt_sub_exists_ty f mt
  | Tunivar _ | Tvar _ -> false
  | Ttuple lty -> List.exists f lty
  | Tconstr (_, lty) -> List.exists f lty
  | Tfun (t1, t2) -> f t1 || f t2

let ty_iter f t =
  match t.ty_node with
  | Tmem mt -> mt_iter_ty f mt
  | Tunivar _ | Tvar _ -> ()
  | Ttuple lty -> List.iter f lty
  | Tconstr (_, lty) -> List.iter f lty
  | Tfun (t1,t2) -> f t1; f t2

exception FoundUnivar

let rec ty_check_uni t =
  match t.ty_node with
  | Tunivar _ -> raise FoundUnivar
  | _ -> ty_iter ty_check_uni t

(* -------------------------------------------------------------------- *)
let symbol_of_ty (ty : ty) =
  match ty.ty_node with
  | Tmem   _      -> "g"
  | Tunivar _      -> "u"
  | Tvar    _      -> "x"
  | Ttuple  _      -> "x"
  | Tfun    _      -> "f"
  | Tconstr (p, _) ->
      let x = EcPath.basename p in
      let rec doit i =
        if   i >= String.length x
        then "x"
        else match Char.lowercase_ascii x.[i] with
             | 'a' .. 'z' -> String.make 1 x.[i]
             | _ -> doit (i+1)
      in
        doit 0

let fresh_id_of_ty (ty : ty) =
  EcIdent.create (symbol_of_ty ty)

(* -------------------------------------------------------------------- *)
type ty_subst = {
  ts_mod       : EcPath.mpath Mid.t;
  ts_u         : ty Muid.t;
  ts_v         : ty Mid.t;
  ts_memtype   : local_memtype option;
}

let ty_subst_id =
  { ts_mod = Mid.empty;
    ts_u  = Muid.empty;
    ts_v  = Mid.empty;
    ts_memtype = None;
  }

let is_ty_subst_id s =
  Mid.is_empty s.ts_mod
  && Muid.is_empty s.ts_u
  && Mid.is_empty s.ts_v
  && is_none s.ts_memtype


module type SubstXp = sig
  type t
  val bind : t -> EcIdent.ident -> EcIdent.ident * t
  val subst : t -> xpath -> xpath
end

module SubstGvs(X:SubstXp) = struct
(*  let ff_subst s ff =
    let s = ref s in
    let ff_params =
      Sid.map (fun x ->
        let x', s' = X.bind !s x in
        s := s';
        x') ff.ff_params in
    { ff_params; ff_fun = X.subst !s ff.ff_fun } *)

  let rec gvs_subst s gvs =
    match gvs.gvs_node with
    | Empty | All  -> gvs
    | Set x        -> gvs_set   (Sx.map (X.subst s) x)
    | GlobFun f    -> gvs_fun   (X.subst s f)
    | Union(s1,s2) -> gvs_union (gvs_subst s s1) (gvs_subst s s2)
    | Diff (s1,s2) -> gvs_diff  (gvs_subst s s1) (gvs_subst s s2)
    | Inter(s1,s2) -> gvs_inter (gvs_subst s s1) (gvs_subst s s2)

end

module SubstXp :
  SubstXp with type t = ty_subst
= struct
  type t = ty_subst
  let bind s x = x, {s with ts_mod = Mid.remove x s.ts_mod }
  let subst s xp = x_subst_abs s.ts_mod xp
end

module SGvs = SubstGvs(SubstXp)

let rec gvs_subst (s:ty_subst) gvs =
  match gvs.gvs_node with
  | Empty | All  -> gvs
  | Set x        -> gvs       (* no mod_ident in x *)
  | GlobFun f    -> gvs_fun   (SubstXp.subst s f)
  | Union(s1,s2) -> gvs_union (gvs_subst s s1) (gvs_subst s s2)
  | Diff (s1,s2) -> gvs_diff  (gvs_subst s s1) (gvs_subst s s2)
  | Inter(s1,s2) -> gvs_inter (gvs_subst s s1) (gvs_subst s s2)

let gvs_subst s gvs =
  if Mid.is_empty s.ts_mod then gvs
  else gvs_subst s gvs

let vs_subst s vs =
  if Mid.is_empty s.ts_mod then vs
  else { lvs = vs.lvs; gvs = gvs_subst s vs.gvs }

let rec ty_subst s ty =
  match ty.ty_node with
  | Tmem mt    -> tmem (mt_subst s mt)
  | Tunivar id -> Muid.find_def ty id s.ts_u
  | Tvar id    -> Mid.find_def ty id s.ts_v
  | _          -> ty_map (ty_subst s) ty

and mt_subst s (mt:memtype) =
  mk_mto
    (omap_dfl (fun lmt -> Some (lmt_subst s lmt)) s.ts_memtype mt.lmt)
    (gvs_subst s mt.gvs)

and lmt_subst s (lmt:local_memtype) =
  lmt_map_ty (ty_subst s) lmt

let restr_subst s fv =
  { s with ts_mod = Mid.set_diff s.ts_mod fv}

let mk_restr_subst fv subst s x =
  let s = restr_subst s (fv x) in
  if is_ty_subst_id s then x
  else subst s x

let ty_subst = mk_restr_subst ty_fv ty_subst
let mt_subst = mk_restr_subst mt_fv mt_subst
let lmt_subst = mk_restr_subst lmt_fv lmt_subst

(* -------------------------------------------------------------------- *)
module Tuni = struct

  let subst (uidmap : ty Muid.t) =
    { ty_subst_id with ts_u = uidmap }

  let subst1 ((id, t) : uid * ty) =
    subst (Muid.singleton id t)

  let subst_dom uidmap dom =
    List.map (ty_subst (subst uidmap)) dom

  let occurs u =
    let rec aux t =
      match t.ty_node with
      | Tunivar u' -> uid_equal u u'
      | _ -> ty_sub_exists aux t in
    aux

  let univars =
    let rec doit univars t =
      match t.ty_node with
      | Tunivar uid -> Suid.add uid univars
      | _ -> ty_fold doit univars t

    in fun t -> doit Suid.empty t

  let rec fv_rec fv t =
    match t.ty_node with
    | Tunivar id -> Suid.add id fv
    | _ -> ty_fold fv_rec fv t

  let fv = fv_rec Suid.empty
end

(* -------------------------------------------------------------------- *)
module Tvar = struct
  let subst (s : ty Mid.t) =
    ty_subst { ty_subst_id with ts_v = s}

  let subst1 (id,t) =
    subst (Mid.singleton id t)

  let init lv lt =
    assert (List.length lv = List.length lt);
    List.fold_left2 (fun s v t -> Mid.add v t s) Mid.empty lv lt

  let rec fv_rec fv t =
    match t.ty_node with
    | Tvar id -> Sid.add id fv
    | _ -> ty_fold fv_rec fv t

  let fv = fv_rec Sid.empty
end

(* -------------------------------------------------------------------- *)
type ovariable = {
  ov_name : EcSymbols.symbol option;
  ov_type : ty;
}

let ov_name { ov_name = x } = x
let ov_type { ov_type = x } = x

let ov_hash v =
  Why3.Hashcons.combine
    (Hashtbl.hash v.ov_name)
    (ty_hash v.ov_type)

let ov_equal vd1 vd2 =
  EcUtils.opt_equal (=) vd1.ov_name vd2.ov_name &&
  ty_equal vd1.ov_type vd2.ov_type

type variable = {
  v_name : EcSymbols.symbol;   (* can be "_" *)
  v_type : ty;
}

let v_name { v_name = x } = x
let v_type { v_type = x } = x

let v_hash v =
  Why3.Hashcons.combine
    (Hashtbl.hash v.v_name)
    (ty_hash v.v_type)

let v_equal vd1 vd2 =
  vd1.v_name = vd2.v_name &&
  ty_equal vd1.v_type vd2.v_type

let ovar_of_var { v_name = n; v_type = t } =
  { ov_name = Some n; ov_type = t }

let ty_fv_and_tvar (ty : ty) =
  EcIdent.fv_union ty.ty_fv (Mid.map (fun () -> 1) (Tvar.fv ty))

(* -------------------------------------------------------------------- *)
(* Basic operations on local_memtype                                    *)

let lmt_init = mk_lmt Msym.empty Msym.empty

let lmt_lookup lmt x =
  Msym.find_opt x lmt.lmt_symb

let lmt_lookup_proj lmt x i =
  obind (fun mp -> EcMaps.Mint.find_opt i mp)
    (Msym.find_opt x lmt.lmt_proj)

let mt_lookup mt x =
  obind (fun lmt -> lmt_lookup lmt x) mt.lmt

let mt_lookup_proj mt x i =
  obind (fun lmt -> lmt_lookup_proj lmt x i) mt.lmt

exception DuplicatedMemoryBinding of symbol

let lmt_symb_add lmt_symb v =
  let merger o =
    if o <> None then raise (DuplicatedMemoryBinding v.v_name);
    Some (None, v.v_type) in
  Msym.change merger v.v_name lmt_symb

let lmt_adds lmt (xs : variable list) =
  let lmt_symb =
    List.fold_left lmt_symb_add lmt.lmt_symb xs in
  mk_lmt lmt_symb lmt.lmt_proj

let lmt_add lmt x ty =
  mk_lmt (lmt_symb_add lmt.lmt_symb {v_name = x; v_type = ty} ) (lmt.lmt_proj)

let lmt_oadds lmt (xs : ovariable list) =
  let lmt_symb =
    List.fold_left (fun lmt_symb ov ->
        omap_dfl (fun v -> lmt_symb_add lmt_symb {v_name = v; v_type = ov.ov_type})
                 lmt_symb ov.ov_name) lmt.lmt_symb xs in
  mk_lmt lmt_symb lmt.lmt_proj

let lmt_add_proj lmt x (l: ovariable list) =
  let ty = ttuple (List.map ov_type l) in
  let lmt_symb = ref (lmt_symb_add lmt.lmt_symb { v_name = x; v_type = ty}) in
  let x_proj = ref EcMaps.Mint.empty in
  let doit i ov =
    oiter (fun p ->
      let merger o =
         if o <> None then raise (DuplicatedMemoryBinding p);
         Some (Some(x,ty,i), ov.ov_type) in
      lmt_symb := Msym.change merger p !lmt_symb;
      x_proj := EcMaps.Mint.add i p !x_proj) ov.ov_name in
  List.iteri doit l;
  let lmt_proj = Msym.add x !x_proj lmt.lmt_proj in
  mk_lmt !lmt_symb lmt_proj

let mt_all lmt = mk_mt lmt gvs_all
let mt_glob = mt_all lmt_init

(* -------------------------------------------------------------------- *)
type lpattern =
  | LSymbol of (EcIdent.t * ty)
  | LTuple  of (EcIdent.t * ty) list
  | LRecord of EcPath.path * (EcIdent.t option * ty) list

let idty_equal (x1,t1) (x2,t2) =
  EcIdent.id_equal x1 x2 && ty_equal t1 t2

let lp_equal p1 p2 =
  match p1, p2 with
  | LSymbol xt1, LSymbol xt2 -> idty_equal xt1 xt2
  | LTuple lx1, LTuple lx2 -> List.all2 idty_equal lx1 lx2
  | _ -> false

let idty_hash (x,t) = Why3.Hashcons.combine (EcIdent.id_hash x) (ty_hash t)

let lp_hash = function
  | LSymbol  x -> idty_hash x
  | LTuple  lx -> Why3.Hashcons.combine_list idty_hash 0 lx

  | LRecord (p, lx) ->
      let for1 (x, ty) =
        Why3.Hashcons.combine (ty_hash ty)
          (Why3.Hashcons.combine_option EcIdent.id_hash x)
      in
        Why3.Hashcons.combine_list for1 (p_hash p) lx

let lp_ids = function
  | LSymbol (id,_)  -> [id]
  | LTuple  ids     -> List.map fst ids
  | LRecord (_,ids) -> List.pmap fst ids

let lp_bind = function
  | LSymbol b     -> [b]
  | LTuple  b     -> b
  | LRecord (_,b) ->
      List.pmap (fun (x, ty) -> omap (fun x -> (x, ty)) x) b

(* -------------------------------------------------------------------- *)
type expr = {
  e_node : expr_node;
  e_ty   : ty;
  e_fv   : int Mid.t;
  e_tag  : int;
}

and expr_node =
  | Eint   of BI.zint                      (* int. literal          *)
  | Elocal of EcIdent.t                    (* let-variables         *)
  | Evar   of prog_var                     (* module variable       *)
  | Eop    of EcPath.path * ty list        (* op apply to type args *)
  | Eapp   of expr * expr list             (* op. application       *)
  | Equant of equantif * ebindings * expr  (* fun/forall/exists     *)
  | Elet   of lpattern * expr * expr       (* let binding           *)
  | Etuple of expr list                    (* tuple constructor     *)
  | Eif    of expr * expr * expr           (* _ ? _ : _             *)
  | Ematch of expr * expr list * ty        (* match _ with _        *)
  | Eproj  of expr * int                   (* projection of a tuple *)

and equantif  = [ `ELambda | `EForall | `EExists ]
and ebinding  = EcIdent.t * ty
and ebindings = ebinding list

type closure = (EcIdent.t * ty) list * expr

(* -------------------------------------------------------------------- *)
let e_equal   = ((==) : expr -> expr -> bool)
let e_hash    = fun e -> e.e_tag
let e_compare = fun e1 e2 -> e_hash e1 - e_hash e2
let e_fv e    = e.e_fv
let e_ty e    = e.e_ty

(* -------------------------------------------------------------------- *)
let lp_fv = function
  | LSymbol (id, _) ->
      Sid.singleton id

  | LTuple ids ->
      List.fold_left (fun s (id, _) -> Sid.add id s) Sid.empty ids

  | LRecord (_, ids) ->
      List.fold_left
        (fun s (id, _) -> ofold Sid.add s id)
        Sid.empty ids

let fv_node e =
  let union ex =
    List.fold_left (fun s e -> fv_union s (ex e)) Mid.empty
  in

  match e with
  | Eint _            -> Mid.empty
  | Eop (_, tys)      -> union (fun a -> a.ty_fv) tys
  | Evar v            -> pv_fv v
  | Elocal id         -> fv_singleton id
  | Eapp (e, es)      -> union e_fv (e :: es)
  | Elet (lp, e1, e2) -> fv_union (e_fv e1) (fv_diff (e_fv e2) (lp_fv lp))
  | Etuple es         -> union e_fv es
  | Eif (e1, e2, e3)  -> union e_fv [e1; e2; e3]
  | Ematch (e, es, _) -> union e_fv (e :: es)
  | Equant (_, b, e)  -> List.fold_left (fun s (id, _) -> Mid.remove id s) (e_fv e) b
  | Eproj (e, _)      -> e_fv e

(* -------------------------------------------------------------------- *)
let qt_equal : equantif -> equantif -> bool = (==)
let qt_hash  : equantif -> int = Hashtbl.hash

(* -------------------------------------------------------------------- *)
module Hexpr = Why3.Hashcons.Make (struct
  type t = expr

  let b_equal b1 b2 =
    let b1_equal (x1, ty1) (x2, ty2) =
      EcIdent.id_equal x1 x2 && ty_equal ty1 ty2 in
    List.all2 b1_equal b1 b2

  let equal_node e1 e2 =
    match e1, e2 with
    | Eint   i1, Eint   i2 -> BI.equal i1 i2
    | Elocal x1, Elocal x2 -> EcIdent.id_equal x1 x2
    | Evar   x1, Evar   x2 -> pv_equal x1 x2

    | Eop (p1, tys1), Eop (p2, tys2) ->
           (EcPath.p_equal p1 p2)
        && (List.all2 ty_equal tys1 tys2)

    | Eapp (e1, es1), Eapp (e2, es2) ->
           (e_equal e1 e2)
        && (List.all2 e_equal es1 es2)

    | Elet (lp1, e1, f1), Elet (lp2, e2, f2) ->
        (lp_equal lp1 lp2) && (e_equal e1 e2) && (e_equal f1 f2)

    | Etuple es1, Etuple es2 ->
        List.all2 e_equal es1 es2

    | Eif (c1, e1, f1), Eif (c2, e2, f2) ->
        (e_equal c1 c2) && (e_equal e1 e2) && (e_equal f1 f2)

    | Ematch (e1, es1, ty1), Ematch (e2, es2, ty2) ->
           List.all2 e_equal (e1 :: es1) (e2 :: es2)
        && ty_equal ty1 ty2

    | Equant (q1, b1, e1), Equant (q2, b2, e2) ->
        qt_equal q1 q2 && e_equal e1 e2 && b_equal b1 b2

    | Eproj(e1, i1), Eproj(e2, i2) ->
        i1 = i2 && e_equal e1 e2

    | _, _ -> false

  let equal e1 e2 =
    equal_node e1.e_node e2.e_node &&
    ty_equal e1.e_ty e2.e_ty

  let b_hash bs =
    let b1_hash (x, ty) =
      Why3.Hashcons.combine (EcIdent.tag x) (ty_hash ty)
    in
    Why3.Hashcons.combine_list b1_hash 0 bs

  let hash e =
    match e.e_node with
    | Eint   i -> BI.hash i
    | Elocal x -> Hashtbl.hash x
    | Evar   x -> pv_hash x

    | Eop (p, tys) ->
        Why3.Hashcons.combine_list ty_hash
          (EcPath.p_hash p) tys

    | Eapp (e, es) ->
        Why3.Hashcons.combine_list e_hash (e_hash e) es

    | Elet (p, e1, e2) ->
        Why3.Hashcons.combine2
          (lp_hash p) (e_hash e1) (e_hash e2)

    | Etuple es ->
        Why3.Hashcons.combine_list e_hash 0 es

    | Eif (c, e1, e2) ->
        Why3.Hashcons.combine2
          (e_hash c) (e_hash e1) (e_hash e2)

    | Ematch (e, es, ty) ->
        Why3.Hashcons.combine_list e_hash
          (Why3.Hashcons.combine (e_hash e) (ty_hash ty))
          es

    | Equant (q, b, e) ->
        Why3.Hashcons.combine2 (qt_hash q) (e_hash e) (b_hash b)

    | Eproj (e, i) ->
        Why3.Hashcons.combine (e_hash e) i

  let tag n e =
    let fv = fv_union (fv_node e.e_node) e.e_ty.ty_fv in
      { e with e_tag = n; e_fv = fv; }
end)

(* -------------------------------------------------------------------- *)
let mk_expr e ty =
  Hexpr.hashcons { e_node = e; e_tag = -1; e_fv = Mid.empty; e_ty = ty }

let e_tt    = mk_expr (Eop (EcCoreLib.CI_Unit.p_tt, [])) tunit
let e_int   = fun i -> mk_expr (Eint i) tint
let e_local = fun x ty -> mk_expr (Elocal x) ty
let e_var   = fun x ty -> mk_expr (Evar x) ty
let e_op    = fun x targs ty -> mk_expr (Eop (x, targs)) ty
let e_let   = fun pt e1 e2 -> mk_expr (Elet (pt, e1, e2)) e2.e_ty
let e_tuple = fun es ->
  match es with
  | []  -> e_tt
  | [x] -> x
  | _   -> mk_expr (Etuple es) (ttuple (List.map e_ty es))

let e_if    = fun c e1 e2 -> mk_expr (Eif (c, e1, e2)) e2.e_ty
let e_match = fun e es ty -> mk_expr (Ematch (e, es, ty)) ty
let e_proj  = fun e i ty -> mk_expr (Eproj(e,i)) ty

let e_proj_simpl e i ty =
  match e.e_node with
  | Etuple es -> List.nth es i
  | _ -> e_proj e i ty

let e_quantif q b e =
  if List.is_empty b then e else

  let b, e =
    match e.e_node with
    | Equant (q', b', e) when qt_equal q q' -> (b@b', e)
    | _ -> b, e in

  let ty =
    match q with
    | `ELambda -> toarrow (List.map snd b) e.e_ty
    | `EForall | `EExists -> tbool

  in mk_expr (Equant (q, b, e)) ty

let e_forall b e = e_quantif `EForall b e
let e_exists b e = e_quantif `EExists b e
let e_lam    b e = e_quantif `ELambda b e

let e_app x args ty =
  if args = [] then x
  else
    match x.e_node with
    | Eapp(x', args') -> mk_expr (Eapp (x', (args'@args))) ty
    | _ -> mk_expr (Eapp (x, args)) ty

let e_app_op ?(tyargs=[]) op args ty =
  e_app (e_op op tyargs (toarrow (List.map e_ty args) ty)) args ty

(* -------------------------------------------------------------------- *)
module Reals : sig
  val of_lit : EcBigInt.zint -> expr
  val of_int : expr -> expr
  val add    : expr -> expr -> expr
  val opp    : expr -> expr
  val sub    : expr -> expr -> expr
  val mul    : expr -> expr -> expr
  val inv    : expr -> expr
  val div    : expr -> expr -> expr
end = struct
  module CIR = EcCoreLib.CI_Real

  let of_int f = e_app_op CIR.p_real_of_int [f] treal
  let of_lit n = of_int (e_int n)

  let add f1 f2 = e_app_op CIR.p_real_add [f1; f2] treal
  let opp f     = e_app_op CIR.p_real_opp [f] treal
  let sub f1 f2 = add f1 (opp f2)
  let mul f1 f2 = e_app_op CIR.p_real_mul [f1; f2] treal
  let inv f     = e_app_op CIR.p_real_inv [f] treal
  let div f1 f2 = mul f1 (inv f2)
end

(* -------------------------------------------------------------------- *)
let e_decimal (n, (l, f)) =
  if EcBigInt.equal f EcBigInt.zero then Reals.of_lit n else

  let d   = EcBigInt.pow (EcBigInt.of_int 10) l in
  let gcd = EcBigInt.gcd f d in
  let f   = EcBigInt.div f gcd in
  let d   = EcBigInt.div d gcd in
  let fct = Reals.div (Reals.of_lit f) (Reals.of_lit d) in

  if   EcBigInt.equal n EcBigInt.zero
  then fct
  else Reals.add (Reals.of_lit n) fct

(* -------------------------------------------------------------------- *)
let e_none (ty : ty) : expr =
  e_op EcCoreLib.CI_Option.p_none [ty] (toption ty)

let e_some ({ e_ty = ty } as e : expr) : expr =
  let op = e_op EcCoreLib.CI_Option.p_some [ty] (tfun ty (toption ty)) in
  e_app op [e] (toption ty)

let e_oget (e : expr) (ty : ty) : expr =
  let op = e_op EcCoreLib.CI_Option.p_oget [ty] (tfun (toption ty) ty) in
  e_app op [e] ty

(* -------------------------------------------------------------------- *)
let e_map fty fe e =
  match e.e_node with
  | Eint _ | Elocal _ | Evar _ -> e

  | Eop (p, tys) ->
      let tys' = List.Smart.map fty tys in
      let ty'  = fty e.e_ty in
        e_op p tys' ty'

  | Eapp (e1, args) ->
      let e1'   = fe e1 in
      let args' = List.Smart.map fe args in
      let ty'   = fty e.e_ty in
        e_app e1' args' ty'

  | Elet (lp, e1, e2) ->
      let e1' = fe e1 in
      let e2' = fe e2 in
        e_let lp e1' e2'

  | Etuple le ->
      let le' = List.Smart.map fe le in
        e_tuple le'

  | Eproj (e1, i) ->
      let e' = fe e1 in
      let ty = fty e.e_ty in
      e_proj e' i ty

  | Eif (e1, e2, e3) ->
      let e1' = fe e1 in
      let e2' = fe e2 in
      let e3' = fe e3 in
      e_if e1' e2' e3'

  | Ematch (b, es, ty) ->
      let ty' = fty ty in
      let b'  = fe b in
      let es' = List.Smart.map fe es in
      e_match b' es' ty'

  | Equant (q, b, bd) ->
      let dop (x, ty as xty) =
        let ty' = fty ty in
          if ty == ty' then xty else (x, ty') in
      let b'  = List.Smart.map dop b in
      let bd' = fe bd in
      e_quantif q b' bd'

let e_fold (fe : 'a -> expr -> 'a) (state : 'a) (e : expr) =
  match e.e_node with
  | Eint _                -> state
  | Elocal _              -> state
  | Evar _                -> state
  | Eop _                 -> state
  | Eapp (e, args)        -> List.fold_left fe (fe state e) args
  | Elet (_, e1, e2)      -> List.fold_left fe state [e1; e2]
  | Etuple es             -> List.fold_left fe state es
  | Eproj(e,_)            -> fe state e
  | Eif (e1, e2, e3)      -> List.fold_left fe state [e1; e2; e3]
  | Ematch (e, es, _)     -> List.fold_left fe state (e :: es)
  | Equant (_, _, e1)     -> fe state e1

let e_iter (fe : expr -> unit) (e : expr) =
  e_fold (fun () e -> fe e) () e

module MSHe = EcMaps.MakeMSH(struct type t = expr let tag e = e.e_tag end)
module Me = MSHe.M
module Se = MSHe.S
module He = MSHe.H

(* -------------------------------------------------------------------- *)
type e_subst = {
    es_freshen : bool; (* true means realloc local *)
    es_ty      : ty_subst;
    es_loc     : expr Mid.t;
}

let e_subst_id = {
    es_freshen = false;
    es_ty     = ty_subst_id;
    es_loc     = Mid.empty;
}

(* -------------------------------------------------------------------- *)
let is_e_subst_id s =
     not s.es_freshen
  && is_ty_subst_id s.es_ty
  && Mid.is_empty s.es_loc

(* -------------------------------------------------------------------- *)
let e_subst_init freshen on_ty esloc =
  { es_freshen = freshen;
    es_ty      = on_ty;
    es_loc     = esloc; }

(* -------------------------------------------------------------------- *)
let add_local s ((x, t) as xt) =
  let x' = if s.es_freshen then EcIdent.fresh x else x in
  let t' = ty_subst s.es_ty t in

    if   x == x' && t == t'
    then (s, xt)
    else
      let merger o = assert (o = None); Some (e_local x' t') in
        ({ s with es_loc = Mid.change merger x s.es_loc }, (x', t'))

(* -------------------------------------------------------------------- *)
let add_locals = List.Smart.map_fold add_local

(* -------------------------------------------------------------------- *)
let subst_lpattern (s: e_subst) (lp:lpattern) =
  match lp with
  | LSymbol x ->
      let (s, x') = add_local s x in
        (s, LSymbol x')

  | LTuple xs ->
      let (s, xs') = add_locals s xs in
        (s, LTuple xs')

  | LRecord (p, xs) ->
      let (s, xs') =
        List.Smart.map_fold
          (fun s ((x, t) as xt) ->
            match x with
            | None ->
                let t' = ty_subst s.es_ty t in
                  if t == t' then (s, xt) else (s, (x, t'))
            | Some x ->
                let (s, (x', t')) = add_local s (x, t) in
                  if   x == x' && t == t'
                  then (s, xt)
                  else (s, (Some x', t')))
          s xs
      in
        (s, LRecord (p, xs'))

(* -------------------------------------------------------------------- *)
let rec e_subst (s: e_subst) e =
  match e.e_node with
  | Elocal id -> begin
      match Mid.find_opt id s.es_loc with
      | Some e' -> e'
      | None    ->
(* FIXME schema *)
(*        assert (not s.es_freshen); *)
        e_local id (ty_subst s.es_ty e.e_ty)
  end

  | Evar pv ->
      let pv' = pv_subst (x_subst_abs s.es_ty.ts_mod) pv in
      let ty' = ty_subst s.es_ty e.e_ty in
        e_var pv' ty'

  | Eop (p, tys) ->
      let tys' = List.Smart.map (ty_subst s.es_ty) tys in
      let ty'  = ty_subst s.es_ty e.e_ty in
        e_op p tys' ty'

  | Elet (lp, e1, e2) ->
      let e1' = e_subst s e1 in
      let s, lp' = subst_lpattern s lp in
      let e2' = e_subst s e2 in
        e_let lp' e1' e2'

  | Equant (q, b, e1) ->
      let s, b' = add_locals s b in
      let e1' = e_subst s e1 in
        e_quantif q b' e1'

  | _ -> e_map (ty_subst s.es_ty) (e_subst s) e

(* -------------------------------------------------------------------- *)
let e_subst_closure s (args, e) =
  let (s, args) = add_locals s args in
    (args, e_subst s e)

(* -------------------------------------------------------------------- *)
let e_subst s =
  if is_e_subst_id s then identity
  else
    if s.es_freshen then e_subst s
    else He.memo 107 (e_subst s)

(* -------------------------------------------------------------------- *)
let is_local e =
  match e.e_node with
  | Elocal _ -> true
  | _ -> false

(* -------------------------------------------------------------------- *)
let destr_local e =
   match e.e_node with
  | Elocal id -> id
  | _ -> assert false

(* -------------------------------------------------------------------- *)
let is_var e =
  match e.e_node with
  | Evar _ -> true
  | _ -> false

(* -------------------------------------------------------------------- *)
let destr_var e =
   match e.e_node with
  | Evar pv -> pv
  | _ -> assert false

(* -------------------------------------------------------------------- *)
let is_tuple_var e =
  match e.e_node with
  | Etuple es -> List.for_all is_var es
  | _ -> false

(* -------------------------------------------------------------------- *)
let destr_tuple_var e =
   match e.e_node with
  | Etuple es -> List.map destr_var es
  | _ -> assert false

(* -------------------------------------------------------------------- *)
let destr_app = function
    { e_node = Eapp (e, es) } -> (e, es) | e -> (e, [])

(* -------------------------------------------------------------------- *)
let split_args e =
  match e.e_node with
  | Eapp (e, args) -> (e, args)
  | _ -> (e, [])



(* -------------------------------------------------------------------- *)
