(* -------------------------------------------------------------------- *)
open EcPath
open EcFol
open EcEnv
open EcProvers

(* -------------------------------------------------------------------- *)
val check : ?notify:notify -> prover_infos -> LDecl.hyps -> form -> bool
val dump_why3 : env -> string -> unit

type tenv

val tenv_task : tenv -> Why3.Task.task

val init : EcEnv.LDecl.hyps ->
  EcFol.form ->
  EcEnv.env * EcBaseLogic.hyps * tenv * Why3.Decl.decl

val trans_axiom : tenv -> EcPath.path * EcDecl.axiom -> unit

module Frequency : sig

  (* -------------------------------------------------------------------- *)
  type relevant = Sp.t * Sx.t

  val r_empty : relevant
  val r_inter : relevant -> relevant -> relevant
  val r_diff  : relevant -> relevant -> relevant
  val r_card  : relevant -> int

  type all_rel = [ `OP of path | `PROC of xpath]

  val r_fold : (all_rel -> 'a -> 'a) -> relevant -> 'a -> 'a

  type frequency

  val create : Sp.t -> frequency
  val frequency : frequency -> all_rel -> int
  val f_ops : Sp.t -> form -> relevant

  val add : frequency -> EcFol.form -> unit

end
