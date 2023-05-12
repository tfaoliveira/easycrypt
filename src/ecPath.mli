(* -------------------------------------------------------------------- *)
open EcIdent
open EcMaps
open EcSymbols

(* -------------------------------------------------------------------- *)
(** {2 Path} *)

type path = private {
  p_node : path_node;
  p_tag  : int
}

and path_node =
| Psymbol of symbol
| Pqname  of path * symbol

(* -------------------------------------------------------------------- *)
val psymbol : symbol -> path
val pqname  : path -> symbol -> path
val pqoname : path option -> symbol -> path
val pappend : path -> path -> path

val p_equal       : path -> path -> bool
val p_compare     : path -> path -> int
val p_ntr_compare : path -> path -> int
val p_hash        : path -> int

(* -------------------------------------------------------------------- *)
val tostring    : path -> string
val toqsymbol   : path -> qsymbol
val fromqsymbol : qsymbol -> path
val basename    : path -> symbol
val extend      : path -> symbol list -> path
val prefix      : path -> path option
val getprefix   : path -> path -> symbol list option
val isprefix    : path -> path -> bool
val rootname    : path -> symbol
val tolist      : path -> symbol list
val p_size      : path -> int

(* -------------------------------------------------------------------- *)
module Mp : Map.S with type key = path
module Hp : EcMaps.EHashtbl.S with type key = path

module Sp : sig
  include Set.S with module M = Map.MakeBase(Mp)

  val ntr_elements : t -> elt list
end

(* -------------------------------------------------------------------- *)
(** {2 Module path} *)

(* -------------------------------------------------------------------- *)
(** module wrapper kind *)
type wrap_k = [`Ext | `Cb]

(** agent with an attached module wrapper kind *)
type agk  = ident * wrap_k

type agks = agk list

(* -------------------------------------------------------------------- *)
(** a module path *)
type mpath

(** resolved top-level module path *)
type mpath_top_r =
  [ | `Local    of ident
    | `Concrete of path * path option ]

(* -------------------------------------------------------------------- *)
(** {3 Module resolution} *)

(** [resolve m] resolves [m] and returns:
    - [(agks, `Local    m            , args')] which is [$agks( m(args')     )]
    - [(agks, `Concrete (p, None    ), args')] which is [$agks( p(args')     )]
    - [(agks, `Concrete (p, Some sub), args')] which is [$agks( p(args').sub )] *)
val resolve : mpath -> (ident * wrap_k) list * mpath_top_r * mpath list

(** [margs m = fst(resolve m)] *)
val margs : mpath -> mpath list

(** [mtop m = snd(resolve m)] *)
val mtop : mpath -> mpath_top_r

(* -------------------------------------------------------------------- *)
(** {3 Smart constructors for modules} *)

(** [mpath agks m args] builds the module path [$agks( m(args) )] *)
val mpath : agks -> mpath_top_r -> mpath list -> mpath

(** [mpath_abs] is similar to [mpath], but only for abstract modules *)
val mpath_abs : agks -> ident -> mpath list -> mpath

(** [mpath_crt agks p args sub] returns [$agks( p(args).sub )]  *)
val mpath_crt : agks -> path -> mpath list -> path option -> mpath

(* -------------------------------------------------------------------- *)
(** [mqname mp x] adds [x] to [mp]'s sub-path (only for concrete modules) *)
val mqname : mpath -> symbol -> mpath

(** strips arguments of a module path (below the sub-path), i.e.
    [mastrip ( $agks( p(args).sub ) ) = $agks( p.sub )] *)
val mastrip : mpath -> mpath

(** build an abstract path from an ident *)
val mident : ident -> mpath

(** strip arguments and sub-path of a [mpath], i.e.
    [m_functor ( p(args).sub ) = p] *)
(* TODO: cost: what should this do? *)
val m_functor : mpath -> mpath

(** applies [args] to [mp], possibly below [mp]'s sub-path, i.e.
    [m_apply p.sub args = (p(args)).sub )] *)
val m_apply : mpath -> mpath list -> mpath

(* -------------------------------------------------------------------- *)
(** {3 Utilities for modules} *)

val m_equal       : mpath -> mpath -> bool
val mtop_equal    : mpath_top_r -> mpath_top_r -> bool
val m_compare     : mpath -> mpath -> int
val m_ntr_compare : mpath -> mpath -> int
val m_hash        : mpath -> int
val m_fv          : int EcIdent.Mid.t -> mpath -> int EcIdent.Mid.t

val m_is_local    : mpath -> bool
val m_is_concrete : mpath -> bool

val mget_ident : mpath -> ident

val pp_m : Format.formatter -> mpath -> unit

(* -------------------------------------------------------------------- *)
(** {2 Variable and procedure path} *)

type xpath = private {
  x_top : mpath;
  x_sub : symbol;
  x_tag : int;
}

val xpath     : mpath -> symbol -> xpath
val xastrip   : xpath -> xpath

val x_equal       : xpath -> xpath -> bool
val x_compare     : xpath -> xpath -> int
val x_ntr_compare : xpath -> xpath -> int
val x_hash        : xpath -> int

(* These functions expect xpath representing program variables
 * with a normalized [x_top] field. *)
val x_compare_na : xpath -> xpath -> int

val x_fv : int EcIdent.Mid.t -> xpath -> int EcIdent.Mid.t

val xbasename   : xpath -> symbol

val pp_x : Format.formatter -> xpath -> unit

(* -------------------------------------------------------------------- *)
val m_tostring : mpath -> string
val x_tostring : xpath -> string

(* -------------------------------------------------------------------- *)
module Mm : Map.S with type key = mpath
module Hm : EcMaps.EHashtbl.S with type key = mpath

module Sm : sig
  include Set.S with module M = Map.MakeBase(Mm)

  val ntr_elements : t -> elt list
end

(* -------------------------------------------------------------------- *)
module Mx : Map.S with type key = xpath
module Hx : EcMaps.EHashtbl.S with type key = xpath

module Sx : sig
  include Set.S with module M = Map.MakeBase(Mx)

  val ntr_elements : t -> elt list
end

(* -------------------------------------------------------------------- *)
type smsubst = {
  sms_crt : path Mp.t;
  sms_id  : mpath Mid.t;
  sms_ag  : ident Mid.t;        (** agent substitution *)
}

val sms_identity : smsubst
val sms_is_identity : smsubst -> bool

val sms_bind_abs   : ident -> mpath -> smsubst -> smsubst
val sms_bind_agent : ident -> ident -> smsubst -> smsubst

val p_subst : path Mp.t -> path -> path
val m_subst : smsubst -> mpath -> mpath
val x_subst : smsubst -> xpath -> xpath
