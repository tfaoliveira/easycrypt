open EcIdent
open EcUid
open EcPath
open EcAst
open EcTypes
open EcCoreFol
open EcCoreModules

type mod_extra =
  { mex_tglob : ty;
    mex_glob  : memory -> form;
    mex_fv    : int Mid.t
  }

type sc_instanciate =
  { sc_memtype : memtype;
    sc_mempred : mem_pr Mid.t;
    sc_expr    : expr Mid.t;
  }

type f_subst

type 'a substitute = f_subst -> 'a -> 'a
(* form before subst -> form after -> resulting form *)
type tx = form -> form -> form
type 'a tx_substitute = ?tx:tx -> 'a substitute
type 'a subst_bind = f_subst -> 'a -> f_subst * 'a

module Fsubst : sig

val subst_init : ?freshen:bool ->
                 ?suid: ty Muid.t ->
                 ?sty: ty Mid.t ->
                 ?esloc: expr Mid.t ->
                 ?schema: sc_instanciate ->
                 unit -> f_subst

val subst_id : f_subst

val is_subst_id : f_subst -> bool

val bind_local  : f_subst -> EcIdent.ident -> form -> f_subst
val bind_elocal : f_subst -> EcIdent.ident -> expr -> f_subst
val bind_mod    : f_subst -> EcIdent.ident -> mpath -> mod_extra -> f_subst
val bind_absmod : f_subst -> EcIdent.ident -> EcIdent.ident -> f_subst
val bind_mem    : f_subst -> memory -> memory -> f_subst

val bind_rename  : f_subst -> EcIdent.ident -> EcIdent.ident -> ty -> f_subst

val bind_locals  :
  f_subst -> (EcIdent.ident * 'a) list -> form list -> f_subst
val bind_olocals :
  f_subst -> (EcIdent.ident option * 'a) list -> form list -> f_subst

val remove_predef_mem : f_subst -> memory -> f_subst

(* Apply the substitution in the type first *)
val add_binding  : binding  subst_bind
val add_bindings : bindings subst_bind
val add_memenv   : memenv   subst_bind
val add_lpattern : where:[`Expr | `Form] -> lpattern subst_bind
val add_elocals : (EcIdent.ident * ty) list subst_bind

val m_subst   : mpath    substitute
val x_subst   : xpath    substitute
val pv_subst  : prog_var substitute
val ty_subst  : ty       substitute
val mt_subst  : memtype  substitute
val e_subst   : expr     substitute
val i_subst   : instr    substitute
val s_subst   : stmt     substitute
val mem_subst : memory   substitute


val gty_subst : gty         substitute
val mr_subst  : mod_restr   substitute
val mty_subst : module_type substitute
val oi_subst  : oracle_info substitute

val f_subst   : form tx_substitute

val f_subst_local : EcIdent.t -> form -> form -> form
val f_subst_mem   : EcIdent.t -> EcIdent.t -> form -> form


end

module Tuni : sig
  val univars : ty -> Suid.t
  val subst1    : (uid * ty) -> f_subst
  val subst     : ty Muid.t -> f_subst
  val subst_dom : ty Muid.t -> dom -> dom
  val occurs    : uid -> ty -> bool
  val fv        : ty -> Suid.t
end

module Tvar : sig
  val init     : EcIdent.t list -> ty list -> ty Mid.t
  val subst1   : (EcIdent.t * ty) -> ty -> ty
  val ty_subst : ty Mid.t -> ty -> ty
  val f_subst  : ty Mid.t -> form -> form
end
