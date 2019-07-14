open EcIdent
open EcSymbols
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
