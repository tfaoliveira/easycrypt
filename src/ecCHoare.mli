
(* -------------------------------------------------------------------- *)
val check_loaded : EcEnv.env -> unit

(* -------------------------------------------------------------------- *)
val free_expr : EcTypes.expr -> bool

(* The cost of an expression evaluation in any memory of type [menv]
   satisfying [pre]. *)
val cost_of_expr : EcFol.form -> EcMemory.memenv -> EcTypes.expr -> EcFol.form

(* The cost of an expression evaluation in any memory of type [menv]. *)
val cost_of_expr_any : EcMemory.memenv -> EcTypes.expr -> EcFol.form
