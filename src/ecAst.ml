open EcIdent
open EcSymbols
open EcUtils
open EcMaps

module rec PATH :
sig

  type path = private {
    p_node : path_node;
    p_tag  : int
  }

  and path_node =
    | Psymbol of symbol
    | Pqname  of path * symbol

  val p_equal       : path -> path -> bool
  val p_hash        : path -> int
  val p_compare     : path -> path -> int
  val p_ntr_compare : path -> path -> int

  val mk_path : path_node -> path

  module Mp : Map.S with type key = path
  module Hp : EcMaps.EHashtbl.S with type key = path

  module Sp : sig
    include Set.S with module M = Map.MakeBase(Mp)
    val ntr_elements : t -> elt list
  end

  type mpath = {
    m_top   : mpath_top;
(*    m_targs : TYPES.ty list; *)
    m_args  : mpath list;
    m_tag   : int;
  }

  and mpath_top =
    [ | `Local of ident
      | `Concrete of path * path option ]

  val m_equal       : mpath -> mpath -> bool
  val mt_equal      : mpath_top -> mpath_top -> bool
  val m_hash        : mpath -> int
  val m_compare     : mpath -> mpath -> int
  val m_ntr_compare : mpath -> mpath -> int

  val mpath : mpath_top -> mpath list -> mpath

  module Mm : Map.S with type key = mpath
  module Hm : EcMaps.EHashtbl.S with type key = mpath

  module Sm : sig
    include Set.S with module M = Map.MakeBase(Mm)
    val ntr_elements : t -> elt list
  end

  val m_fv  : int EcIdent.Mid.t -> mpath -> int EcIdent.Mid.t

end
=
struct
  (* ------------------------------------------------------------------------- *)
  (* path                                                                      *)
  type path = {
    p_node : path_node;
    p_tag  : int
  }

  and path_node =
    | Psymbol of symbol
    | Pqname  of path * symbol

  let p_equal   = ((==) : path -> path -> bool)
  let p_hash    = fun p -> p.p_tag
  let p_compare = fun p1 p2 -> p_hash p1 - p_hash p2

  module Hspath = Why3.Hashcons.Make(
    struct
      type t = path

      let equal_node p1 p2 =
        match p1, p2 with
        | Psymbol id1, Psymbol id2 ->
          sym_equal id1 id2
        | Pqname (p1, id1), Pqname(p2, id2) ->
          sym_equal id1 id2 && p_equal p1 p2
        | _ -> false

      let equal p1 p2 = equal_node p1.p_node p2.p_node

      let hash p =
        match p.p_node with
        | Psymbol id    -> Hashtbl.hash id
        | Pqname (p,id) -> Why3.Hashcons.combine p.p_tag (Hashtbl.hash id)

      let tag n p = { p with p_tag = n }
    end)

  let mk_path node =
    Hspath.hashcons { p_node = node; p_tag = -1; }


  (* -------------------------------------------------------------------- *)
  module Path = MakeMSH (
    struct
      type t  = path
      let tag = p_hash
    end)

  let rec p_ntr_compare (p1 : path) (p2 : path) =
    match p1.p_node, p2.p_node with
    | Psymbol _, Pqname  _ -> -1
    | Pqname  _, Psymbol _ -> +1

    | Psymbol x1, Psymbol x2 ->
      String.compare x1 x2

    | Pqname (p1, x1), Pqname (p2, x2) -> begin
        match p_ntr_compare p1 p2 with
        | 0 -> String.compare x1 x2
        | n -> n
      end

  module Mp = Path.M
  module Hp = Path.H

  module Sp = struct
    include Path.S

    let ntr_elements s =
      List.ksort ~key:identity ~cmp:p_ntr_compare (elements s)
  end


  (* ------------------------------------------------------------------------- *)
  (* mpath                                                                     *)

  type mpath = {
      m_top  : mpath_top;
      m_args : mpath list;
      m_tag  : int;
    }

  and mpath_top =
    [ | `Local of ident
      | `Concrete of path * path option ]

  let m_equal   = ((==) : mpath -> mpath -> bool)
  let m_hash    = fun p -> p.m_tag
  let m_compare = fun p1 p2 -> m_hash p1 - m_hash p2

  let rec m_fv fv mp =
    let fv =
      match mp.m_top with
      | `Local id -> EcIdent.fv_add id fv
      | `Concrete _  -> fv in
    List.fold_left m_fv fv mp.m_args


  let mt_equal mt1 mt2 =
    match mt1, mt2 with
    | `Local id1, `Local id2 -> EcIdent.id_equal id1 id2
    | `Concrete(p1, o1), `Concrete(p2, o2) ->
      p_equal p1 p2 && oall2 p_equal o1 o2
    | _, _ -> false

  module Hsmpath = Why3.Hashcons.Make (struct
    type t = mpath

    let equal m1 m2 =
      mt_equal m1.m_top m2.m_top  && List.all2 m_equal m1.m_args m2.m_args

    let hash m =
      let hash =
        match m.m_top with
        | `Local id -> EcIdent.id_hash id
        | `Concrete(p, o) ->
          o |> ofold
                 (fun s h -> Why3.Hashcons.combine h (p_hash s))
                 (p_hash p)
      in
      Why3.Hashcons.combine_list m_hash hash m.m_args

    let tag n p = { p with m_tag = n }
  end)

  let mpath p args =
    Hsmpath.hashcons { m_top = p; m_args = args; m_tag = -1; }

  (* -------------------------------------------------------------------- *)
  module MPath = MakeMSH (struct
    type t  = mpath
    let tag = m_hash
  end)

  let m_top_ntr_compare (mt1 : mpath_top) (mt2 : mpath_top) =
    match mt1, mt2 with
    | `Local    _, `Concrete _ -> -1
    | `Concrete _, `Local    _ -> +1

    | `Local id1, `Local id2 ->
      id_ntr_compare id1 id2

    | `Concrete (p1, op1), `Concrete (p2, op2) -> begin
        match p_ntr_compare p1 p2 with
        | 0 -> ocompare p_ntr_compare op1 op2
        | n -> n
      end

  let rec m_ntr_compare (m1 : mpath) (m2 : mpath) =
    match m_top_ntr_compare m1.m_top m2.m_top with
    | 0 -> List.compare m_ntr_compare m1.m_args m2.m_args
    | n -> n

  module Mm = MPath.M
  module Hm = MPath.H

  module Sm = struct
    include MPath.S
    let ntr_elements s =
      List.ksort ~key:identity ~cmp:m_ntr_compare (elements s)
  end

end

and TYPES : sig

  type ty = {
    ty_node : ty_node;
    ty_fv   : int Mid.t;
    ty_tag  : int;
  }

  and ty_node =
    | Tglob   of PATH.mpath (* The tuple of global variable of the module *)
    | Tunivar of EcUid.uid
    | Tvar    of EcIdent.t
    | Ttuple  of ty list
    | Tconstr of PATH.path * ty list
    | Tfun    of ty * ty

  val ty_equal : ty -> ty -> bool
  val ty_hash  : ty -> int

  val mk_ty : ty_node -> ty

  module Mty : Map.S with type key = ty
  module Sty : Set.S with module M = Map.MakeBase(Mty)
  module Hty : EcMaps.EHashtbl.S with type key = ty

end
=
struct

  type ty = {
    ty_node : ty_node;
    ty_fv   : int Mid.t;
    ty_tag  : int;
  }

  and ty_node =
    | Tglob   of PATH.mpath (* The tuple of global variable of the module *)
    | Tunivar of EcUid.uid
    | Tvar    of EcIdent.t
    | Ttuple  of ty list
    | Tconstr of PATH.path * ty list
    | Tfun    of ty * ty

  let ty_equal : ty -> ty -> bool = (==)
  let ty_hash ty = ty.ty_tag

  module Hsty = Why3.Hashcons.Make (struct
    type t = ty

    let equal ty1 ty2 =
      match ty1.ty_node, ty2.ty_node with
      | Tglob m1, Tglob m2 ->
        PATH.m_equal m1 m2

      | Tunivar u1, Tunivar u2 ->
        EcUid.uid_equal u1 u2

      | Tvar v1, Tvar v2 ->
        id_equal v1 v2

      | Ttuple lt1, Ttuple lt2 ->
        List.all2 ty_equal lt1 lt2

      | Tconstr (p1, lt1), Tconstr (p2, lt2) ->
        PATH.p_equal p1 p2 && List.all2 ty_equal lt1 lt2

      | Tfun (d1, c1), Tfun (d2, c2)->
        ty_equal d1 d2 && ty_equal c1 c2

      | _, _ -> false

    let hash ty =
      match ty.ty_node with
      | Tglob m          -> PATH.m_hash m
      | Tunivar u        -> u
      | Tvar    id       -> EcIdent.tag id
      | Ttuple  tl       -> Why3.Hashcons.combine_list ty_hash 0 tl
      | Tconstr (p, tl)  -> Why3.Hashcons.combine_list ty_hash p.p_tag tl
      | Tfun    (t1, t2) -> Why3.Hashcons.combine (ty_hash t1) (ty_hash t2)

    let fv ty =
      let union ex =
        List.fold_left (fun s a -> fv_union s (ex a)) Mid.empty in

      match ty with
      | Tglob m          -> PATH.m_fv Mid.empty m
      | Tunivar _        -> Mid.empty
      | Tvar    _        -> Mid.empty
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

end
