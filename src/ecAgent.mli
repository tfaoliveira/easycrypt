(** Stateless API to handle agent constraints *)

open EcUtils

(* -------------------------------------------------------------------- *)
type error =
  | NotDisjoint of EcIdent.t list

val pp_error : error pp

exception InstantiationFailure of error

(* -------------------------------------------------------------------- *)
(** agent substitution *)
type agent_map = EcIdent.t EcIdent.Mid.t

(* -------------------------------------------------------------------- *)
(** records the instantiation constraints on agent names *)
type constraints

val pp_constrs : constraints pp

(* -------------------------------------------------------------------- *)
val empty : constraints

val is_empty : constraints -> bool

val closed : constraints -> agent_map -> bool

(** [open_constraints Δ {a1,...,an}] returns the substitution refreshing the
    agent names [{a1,...,an}], and add to [Δ] the constraints that these
    agent names must be distincts. *)
val open_constraints : constraints -> EcIdent.t list -> agent_map * constraints

val no_duplicates : EcIdent.t list -> bool
