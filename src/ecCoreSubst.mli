(* -------------------------------------------------------------------- *)
open EcUid
open EcIdent
open EcPath
open EcTypes
open EcCoreModules
open EcCoreFol

(* -------------------------------------------------------------------- *)
type f_subst

(* -------------------------------------------------------------------- *)
val f_subst_init :
       ?freshen:bool
    -> ?tu:ty Muid.t
    -> ?tv:ty Mid.t
    -> ?esloc:expr Mid.t
    -> ?mt:EcMemory.memtype
    -> ?mempred:(mem_pr Mid.t)
    -> unit -> f_subst

val ty_subst : f_subst -> ty -> ty

module Tuni : sig
  val univars : ty -> Suid.t

  val subst1    : (uid * ty) -> f_subst
  val subst     : ty Muid.t -> f_subst
  val subst_dom : ty Muid.t -> dom -> dom
  val occurs    : uid -> ty -> bool
  val fv        : ty -> Suid.t
end

module Tvar : sig
  val subst1  : (EcIdent.t * ty) -> ty -> ty
  val subst   : ty Mid.t -> ty -> ty
  val init    : EcIdent.t list -> ty list -> ty Mid.t
end


(* -------------------------------------------------------------------- *)

val add_elocal  : f_subst -> EcIdent.t * ty -> f_subst * (EcIdent.t * ty)
val add_elocals : f_subst -> (EcIdent.t * ty) list -> f_subst * (EcIdent.t * ty) list

val bind_elocal : f_subst -> EcIdent.t -> expr -> f_subst

val e_subst_closure : f_subst -> closure -> closure
val e_subst : f_subst -> expr -> expr

(* -------------------------------------------------------------------- *)
val s_subst   : f_subst -> stmt -> stmt


(* -------------------------------------------------------------------- *)
module Fsubst : sig
  val f_subst_id  : f_subst
  val is_subst_id : f_subst -> bool

  val f_subst_init :
       ?freshen:bool
    -> ?tu:ty Muid.t
    -> ?tv:ty Mid.t
    -> ?esloc:expr Mid.t
    -> ?mt:EcMemory.memtype
    -> ?mempred:(mem_pr Mid.t)
    -> unit -> f_subst

  val f_bind_local  : f_subst -> EcIdent.t -> form -> f_subst
  val f_bind_mem    : f_subst -> EcIdent.t -> EcIdent.t -> f_subst
  val f_bind_absmod : f_subst -> EcIdent.t -> EcIdent.t -> f_subst
  val f_bind_mod    : f_subst -> EcIdent.t -> EcPath.mpath -> (EcIdent.t -> form) -> f_subst
  val f_bind_rename : f_subst -> EcIdent.t -> EcIdent.t -> ty -> f_subst

  val has_mem : f_subst -> EcAst.memory -> bool

  val f_subst   : ?tx:(form -> form -> form) -> f_subst -> form -> form

  val f_subst_local : EcIdent.t -> form -> form -> form
  val f_subst_mem   : EcIdent.t -> EcIdent.t -> form -> form

  (* val uni_subst : (EcUid.uid -> ty option) -> f_subst *)
  (* val uni : (EcUid.uid -> ty option) -> form -> form *)
  val subst_tvar :
    ?es_loc:(EcTypes.expr EcIdent.Mid.t) ->
    EcTypes.ty EcIdent.Mid.t ->
    form -> form

  val add_binding  : f_subst -> binding  -> f_subst * binding
  val add_bindings : f_subst -> bindings -> f_subst * bindings

  val lp_subst : f_subst -> lpattern -> f_subst * lpattern
  val subst_xpath    : f_subst -> xpath -> xpath
  val s_subst        : f_subst -> stmt  -> stmt
  val e_subst        : f_subst -> expr  -> expr
  val subst_me       : f_subst -> EcMemory.memenv -> EcMemory.memenv
  val m_subst        : f_subst -> EcIdent.t -> EcIdent.t
  val subst_ty       : f_subst -> ty -> ty
  val subst_mty      : f_subst -> module_type -> module_type
  val subst_oi       : f_subst -> PreOI.t -> PreOI.t
  val subst_gty      : f_subst -> gty -> gty
end
