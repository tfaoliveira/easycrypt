open EcFol
open EcPath
open EcSymbols

(* -------------------------------------------------------------------- *)
val check_loaded : EcEnv.env -> unit

(* -------------------------------------------------------------------- *)
val oget_c_bnd : form option -> bool -> form

val cost_orcl : symbol -> xpath -> form -> form

(* -------------------------------------------------------------------- *)
type csub_res = { cond : form; res : form; }

(* [c] of type [tcost], [sub] of type [xint].
   Return: cond, res *)
val cost_sub_self : c:form -> sub:form -> csub_res

(* [c] of type [tcost], [a] of type [xint] *)
val cost_add_self : c:form -> a:form -> form

(* -------------------------------------------------------------------- *)
(* Result of a backward reasoning on cost: given [c1] and [c2], we try to solve
   the equation [c1 = x + c2] over [x]. *)
type cost_backward_res = [
  | `Ok of form * cost          (* [`Ok (c,x)] means that [x] is a solution
                                   whenever [c] holds. *)
  | `FullError                  (* full minus not full *)
]

(* Backward reasoning on cost.
   [cost_sub c1 c2] looks for a solution [x] of [c1 = x + c2]. *)
val cost_sub : cost -> cost -> cost_backward_res

(* -------------------------------------------------------------------- *)
val cost_app : cost -> form list -> cost

val choare_sum : cost -> (form * form) -> cost

(* [choare_xsum cost (m,n)]:
   [cost] of type [tcost], [m] of type [tint], [n] of type [txint].

   [n] must be finite, i.e. [n = f_N n_fin]. Then this is a sum of integers:
      [choare_xsum cost (m,n) = choare_sum cost (m,n_fin)]. *)
val choare_xsum : form -> (form * form) -> form

(* -------------------------------------------------------------------- *)
val free_expr : EcTypes.expr -> bool

(* The cost of an expression evaluation in any memory of type [menv]
   satisfying [pre].
   Type [xint]. *)
val cost_of_expr : EcFol.form -> EcMemory.memenv -> EcTypes.expr -> EcFol.form

(* The cost of an expression evaluation in any memory of type [menv].
   Type [xint]. *)
val cost_of_expr_any : EcMemory.memenv -> EcTypes.expr -> EcFol.form
