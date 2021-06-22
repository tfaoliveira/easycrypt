open EcFol

(* -------------------------------------------------------------------- *)
val check_loaded : EcEnv.env -> unit

(* -------------------------------------------------------------------- *)
val oget_c_bnd : c_bnd option -> bool -> c_bnd

(* [xint] from a [c_bnd] of type [mode] *)
val xi_of_c_bnd : mode:[`Xint | `Int] -> c_bnd -> form

(* -------------------------------------------------------------------- *)
(* [cost_sub_self c a]: [a] must be of type [xint] *)
val cost_sub_self : cost -> form -> form * cost

(* [cost_add_self c a]: [a] must be of type [xint] *)
val cost_add_self : cost -> form -> cost

(* -------------------------------------------------------------------- *)
(* Result of a backward reasoning on cost: given [c1] and [c2], we try to solve
   the equation [c1 = x + c2] over [x].
*)
type cost_backward_res = [
  | `Ok of form * cost          (* [`Ok (c,x)] means that [x] is a solution
                                   whenever [c] holds. *)
  | `XError of EcPath.xpath          (* error with oracle call [x] *)
  | `FullError                  (* full minus not full *)
]

(* Backward reasoning on cost.
   [cost_sub c1 c2] looks for a solution [x] of [c1 = x + c2]. *)
val cost_sub : cost -> cost -> cost_backward_res

(* -------------------------------------------------------------------- *)
val cost_app : cost -> form list -> cost

val choare_sum : cost -> (form * form) -> cost

(* -------------------------------------------------------------------- *)
val free_expr : EcTypes.expr -> bool

(* The cost of an expression evaluation in any memory of type [menv]
   satisfying [pre].
   Type [xint]. *)
val cost_of_expr : EcFol.form -> EcMemory.memenv -> EcTypes.expr -> EcFol.form

(* The cost of an expression evaluation in any memory of type [menv].
   Type [xint]. *)
val cost_of_expr_any : EcMemory.memenv -> EcTypes.expr -> EcFol.form
