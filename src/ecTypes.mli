(* -------------------------------------------------------------------- *)
open EcBigInt
open EcMaps
open EcSymbols
open EcUid
open EcIdent

(* -------------------------------------------------------------------- *)
(* FIXME: section: move me *)

type locality  = [`Declare | `Local | `Global ]
type is_local  =           [ `Local | `Global ]

val local_of_locality : locality -> is_local

(* -------------------------------------------------------------------- *)
type pvar_kind =
  | PVKglob
  | PVKloc

type prog_var = private
  | PVglob of EcPath.xpath
  | PVloc of EcSymbols.symbol

val pv_equal       : prog_var -> prog_var -> bool
val pv_compare     : prog_var -> prog_var -> int
val pv_ntr_compare : prog_var -> prog_var -> int

val pv_kind : prog_var -> pvar_kind

(* work only if the prog_var has been normalized *)
val pv_compare_p : prog_var -> prog_var -> int
val pv_hash    : prog_var -> int
val pv_fv      : prog_var -> int EcIdent.Mid.t
val is_loc     : prog_var -> bool
val is_glob    : prog_var -> bool

val get_loc     : prog_var -> EcSymbols.symbol
val get_glob    : prog_var -> EcPath.xpath

val symbol_of_pv   : prog_var -> symbol
val string_of_pvar : prog_var -> string
val name_of_pvar   : prog_var -> string

val pv_subst : (EcPath.xpath -> EcPath.xpath) -> prog_var -> prog_var

val pv_loc  : EcSymbols.symbol -> prog_var
val pv_glob : EcPath.xpath -> prog_var
val xp_glob : EcPath.xpath -> EcPath.xpath

val arg_symbol : symbol
val res_symbol : symbol
val pv_res  : prog_var
val pv_arg  : prog_var

(* -------------------------------------------------------------------- *)
(*
type functor_fun = {
  ff_params : Sid.t;
  ff_fun : EcPath.xpath;
   (* The xpath is fully applied, argument can be abstract module in Sid.t; *)
}
*)

type gvar_set_node =
  | Empty                             (* The empty memory                           *)
  | All                               (* The memory of all globals                  *)
  | Set       of EcPath.Sx.t          (* The memory restricted to the variable in s *)
  | GlobFun   of EcPath.xpath         (* The global memory used by the function     *)
  | Union     of gvar_set * gvar_set  (* Union                                      *)
  | Diff      of gvar_set * gvar_set  (* Difference                                 *)
  | Inter     of gvar_set * gvar_set  (* Intersection                               *)

and gvar_set = private {
  gvs_node : gvar_set_node;
  gvs_tag  : int;
  gvs_fv   : int EcIdent.Mid.t;
}

val gvs_equal : gvar_set -> gvar_set -> bool
val gvs_hash  : gvar_set -> int
val gvs_fv    : gvar_set -> int EcIdent.Mid.t

val gvs_empty : gvar_set
val gvs_all   : gvar_set
val gvs_set   : EcPath.Sx.t -> gvar_set
val gvs_fun   : EcPath.xpath -> gvar_set
val gvs_union : gvar_set -> gvar_set -> gvar_set
val gvs_diff  : gvar_set -> gvar_set -> gvar_set
val gvs_inter : gvar_set -> gvar_set -> gvar_set


type var_set = {
  lvs : EcSymbols.Ssym.t;
  gvs : gvar_set;
}

val vs_equal : var_set -> var_set -> bool
val vs_hash  : var_set -> int
val vs_fv    : var_set -> int EcIdent.Mid.t

val vs_empty : var_set
val vs_all   : EcSymbols.Ssym.t -> var_set
val vs_globfun  : EcPath.xpath -> var_set
val vs_union : var_set -> var_set -> var_set
val vs_diff  : var_set -> var_set -> var_set
val vs_inter : var_set -> var_set -> var_set


(* -------------------------------------------------------------------- *)
type ty = private {
  ty_node : ty_node;
  ty_fv   : int Mid.t;
  ty_tag  : int;
}

and ty_node =
  | Tmem    of memtype
  | Tunivar of EcUid.uid
  | Tvar    of EcIdent.t
  | Ttuple  of ty list
  | Tconstr of EcPath.path * ty list
  | Tfun    of ty * ty

and local_memtype = private {
  lmt_symb : ((EcSymbols.symbol * ty * int) option * ty) Msym.t;
  lmt_proj : EcSymbols.symbol EcMaps.Mint.t Msym.t;
  lmt_fv   : int EcIdent.Mid.t;
  lmt_tag  : int;
}

(* The type of memory restricted to the var_set *)
(* [lmt = None] is for an axiom schema, and is instantiated to a concrete
   memory type when the axiom schema is.  *)
and memtype = private {
  lmt : local_memtype option;
  gvs : gvar_set;
  mt_fv : int EcIdent.Mid.t;
  mt_tag : int;
}

val is_schema : memtype -> bool

module Mty : Map.S with type key = ty
module Sty : Set.S with module M = Map.MakeBase(Mty)
module Hty : EcMaps.EHashtbl.S with type key = ty

type dom = ty list

val ty_equal : ty -> ty -> bool
val ty_hash  : ty -> int

val lmt_equal : local_memtype -> local_memtype -> bool
val lmt_hash  : local_memtype -> int
val lmt_fv    : local_memtype -> int EcIdent.Mid.t
val lmt_map_ty : (ty -> ty) -> local_memtype -> local_memtype

val mt_equal : memtype -> memtype -> bool
val mt_hash  : memtype -> int
val mt_fv    : memtype -> int EcIdent.Mid.t

val tuni    : EcUid.uid -> ty
val tvar    : EcIdent.t -> ty
val ttuple  : ty list -> ty
val tconstr : EcPath.path -> ty list -> ty
val tfun    : ty -> ty -> ty

val mk_mto  : local_memtype option -> gvar_set -> memtype
val mk_mt   : local_memtype -> gvar_set -> memtype

val tmem    : memtype -> ty
val tmrestr : memtype -> var_set -> ty

val tpred   : ty -> ty

val ty_fv_and_tvar : ty -> int Mid.t

(* -------------------------------------------------------------------- *)
val tunit   : ty
val tbool   : ty
val tint    : ty
val txint   : ty
val treal   : ty
val tdistr  : ty -> ty
val toption : ty -> ty
val tcpred  : ty -> ty
val toarrow : ty list -> ty -> ty

val trealp : ty
val txreal : ty

val tytuple_flat : ty -> ty list
val tyfun_flat   : ty -> (dom * ty)

(* -------------------------------------------------------------------- *)
val is_tdistr : ty -> bool
val as_tdistr : ty -> ty option

(* -------------------------------------------------------------------- *)
exception FoundUnivar

val ty_check_uni : ty -> unit

(* -------------------------------------------------------------------- *)
type ty_subst = {
  ts_mod : EcPath.mpath Mid.t;
  ts_u   : ty Muid.t;
  ts_v   : ty Mid.t;
  ts_memtype : local_memtype option;
}

val ty_subst_id    : ty_subst
val is_ty_subst_id : ty_subst -> bool

module type SubstXp = sig
  type t
  val bind : t -> EcIdent.ident -> EcIdent.ident * t
  val subst : t -> EcPath.xpath -> EcPath.xpath
end

module SubstGvs(X:SubstXp) : sig
  val gvs_subst : X.t -> gvar_set -> gvar_set
end

val gvs_subst : ty_subst -> gvar_set -> gvar_set
val vs_subst : ty_subst -> var_set -> var_set

val ty_subst : ty_subst -> ty -> ty
val mt_subst : ty_subst -> memtype -> memtype
val lmt_subst : ty_subst -> local_memtype -> local_memtype

module Tuni : sig
  val univars : ty -> Suid.t

  val subst1    : (uid * ty) -> ty_subst
  val subst     : ty Muid.t -> ty_subst
  val subst_dom : ty Muid.t -> dom -> dom
  val occurs    : uid -> ty -> bool
  val fv        : ty -> Suid.t
end

module Tvar : sig
  val subst1  : (EcIdent.t * ty) -> ty -> ty
  val subst   : ty Mid.t -> ty -> ty
  val init    : EcIdent.t list -> ty list -> ty Mid.t
  val fv      : ty -> Sid.t
end

val mt_map_ty        : (ty -> ty) -> memtype -> memtype
val mt_iter_ty       : (ty -> unit) -> memtype -> unit
val mt_fold_ty       : ('a -> ty -> 'a) -> 'a -> memtype -> 'a
val mt_sub_exists_ty : (ty -> bool) -> memtype -> bool

(* -------------------------------------------------------------------- *)
(* [map f t] applies [f] on strict subterms of [t] (not recursive) *)
val ty_map : (ty -> ty) -> ty -> ty

(* [sub_exists f t] true if one of the strict-subterm of [t] valid [f] *)
val ty_sub_exists : (ty -> bool) -> ty -> bool

val ty_fold : ('a -> ty -> 'a) -> 'a -> ty -> 'a
val ty_iter : (ty -> unit) -> ty -> unit

(* -------------------------------------------------------------------- *)
val symbol_of_ty   : ty -> string
val fresh_id_of_ty : ty -> EcIdent.t

(* -------------------------------------------------------------------- *)
type lpattern =
  | LSymbol of (EcIdent.t * ty)
  | LTuple  of (EcIdent.t * ty) list
  | LRecord of EcPath.path * (EcIdent.t option * ty) list

val lp_equal : lpattern -> lpattern -> bool
val lp_hash  : lpattern -> int
val lp_bind  : lpattern -> (EcIdent.t * ty) list
val lp_ids   : lpattern -> EcIdent.t list
val lp_fv    : lpattern -> EcIdent.Sid.t

(* -------------------------------------------------------------------- *)
type ovariable = {
  ov_name : symbol option;
  ov_type : ty;
}
val ov_name  : ovariable -> symbol option
val ov_type  : ovariable -> ty
val ov_hash  : ovariable -> int
val ov_equal : ovariable -> ovariable -> bool

type variable = {
  v_name : symbol;   (* can be "_" *)
  v_type : ty;
}

val v_name  : variable -> symbol
val v_type  : variable -> ty
val v_hash  : variable -> int
val v_equal : variable -> variable -> bool

val ovar_of_var: variable -> ovariable

(* -------------------------------------------------------------------- *)
(* lmt without any binding *)
val lmt_init     : local_memtype
val lmt_adds     : local_memtype -> variable list -> local_memtype
val lmt_add      : local_memtype -> symbol -> ty -> local_memtype
val lmt_oadds    : local_memtype -> ovariable list -> local_memtype
val lmt_add_proj : local_memtype -> symbol -> ovariable list -> local_memtype

(* This is equivalent to [mk_mt lmt gvs_all] *)
val mt_all : local_memtype -> memtype
(* This is equivalent to [mt_all lmt_init], ie only global variable are accessible *)
val mt_glob : memtype

val lmt_lookup :
  local_memtype -> symbol -> ((EcSymbols.symbol * ty * int) option * ty) option

val lmt_lookup_proj :
  local_memtype -> symbol -> int -> symbol option

val mt_lookup :
  memtype -> symbol -> ((EcSymbols.symbol * ty * int) option * ty) option

val mt_lookup_proj :
  memtype -> symbol -> int -> symbol option

(* -------------------------------------------------------------------- *)
type expr = private {
  e_node : expr_node;
  e_ty   : ty;
  e_fv   : int Mid.t;    (* module idents, locals *)
  e_tag  : int;
}

and expr_node =
  | Eint   of zint                         (* int. literal          *)
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
val qt_equal : equantif -> equantif -> bool

(* -------------------------------------------------------------------- *)
val e_equal   : expr -> expr -> bool
val e_compare : expr -> expr -> int
val e_hash    : expr -> int
val e_fv      : expr -> int EcIdent.Mid.t
val e_ty      : expr -> ty

(* -------------------------------------------------------------------- *)
val e_tt       : expr
val e_int      : zint -> expr
val e_decimal  : zint * (int * zint) -> expr
val e_local    : EcIdent.t -> ty -> expr
val e_var      : prog_var -> ty -> expr
val e_op       : EcPath.path -> ty list -> ty -> expr
val e_app      : expr -> expr list -> ty -> expr
val e_let      : lpattern -> expr -> expr -> expr
val e_tuple    : expr list -> expr
val e_if       : expr -> expr -> expr -> expr
val e_match    : expr -> expr list -> ty -> expr
val e_lam      : (EcIdent.t * ty) list -> expr -> expr
val e_quantif  : equantif -> ebindings -> expr -> expr
val e_forall   : ebindings -> expr -> expr
val e_exists   : ebindings -> expr -> expr
val e_proj     : expr -> int -> ty -> expr
val e_none     : ty -> expr
val e_some     : expr -> expr
val e_oget     : expr -> ty -> expr

val e_proj_simpl : expr -> int -> ty -> expr

(* -------------------------------------------------------------------- *)
val is_local     : expr -> bool
val is_var       : expr -> bool
val is_tuple_var : expr -> bool

val destr_local     : expr -> EcIdent.t
val destr_var       : expr -> prog_var
val destr_app       : expr -> expr * expr list
val destr_tuple_var : expr -> prog_var list

(* -------------------------------------------------------------------- *)
val split_args : expr -> expr * expr list

(* -------------------------------------------------------------------- *)
val e_map :
     (ty   -> ty  ) (* 1-subtype op. *)
  -> (expr -> expr) (* 1-subexpr op. *)
  -> expr
  -> expr

val e_fold :
  ('state -> expr -> 'state) -> 'state -> expr -> 'state

val e_iter : (expr -> unit) -> expr -> unit

(* -------------------------------------------------------------------- *)
type e_subst = {
  es_freshen : bool; (* true means realloc local *)
  es_ty      : ty_subst;
  es_loc     : expr Mid.t;
}

val e_subst_id : e_subst

val is_e_subst_id : e_subst -> bool

val e_subst_init :
     bool
  -> ty_subst
  -> expr Mid.t
  -> e_subst

val add_local  : e_subst -> EcIdent.t * ty -> e_subst * (EcIdent.t * ty)
val add_locals : e_subst -> (EcIdent.t * ty) list -> e_subst * (EcIdent.t * ty) list

val e_subst_closure : e_subst -> closure -> closure
val e_subst : e_subst -> expr -> expr

(* val e_mapty : (ty -> ty) -> expr -> expr *)

(* val e_uni   : (uid -> ty option) -> expr -> expr *)
