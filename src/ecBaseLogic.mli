(* -------------------------------------------------------------------- *)
open EcTypes
open EcCoreFol

(* -------------------------------------------------------------------- *)
module Epoch : sig
  type t

  val init : t

  val lt  : t -> t -> bool
  val leq : t -> t -> bool

  val next : t -> t
  val max : t -> t -> t
  val min : t -> t -> t
end

(* -------------------------------------------------------------------- *)
type local_kind =
| LD_var    of ty * form option
| LD_mem    of EcMemory.memtype
| LD_modty  of mod_info * EcModules.module_type
| LD_hyp    of form
| LD_abs_st of EcModules.abs_uses

(* -------------------------------------------------------------------- *)
type l_local = {
  l_id    : EcIdent.t;
  l_epoch : Epoch.t;
  l_kind  : local_kind;
}

type l_locals = l_local list

val l_id    : l_local -> EcIdent.t
val l_epoch : l_local -> Epoch.t

(* -------------------------------------------------------------------- *)
type hyps = {
  h_tvar   : EcDecl.ty_params;
  h_local  : l_local list;
  h_agents : EcIdent.t list;    (* (disjoint) local agent names *)
}

val hyps_epoch : hyps -> Epoch.t

val by_id_opt : EcIdent.t -> hyps -> l_local option
