open EcFol

(* -------------------------------------------------------------------- *)
val check_loaded : EcEnv.env -> unit

(* -------------------------------------------------------------------- *)
val c_bnd_of_opt : cost_bnd option -> cost_bnd

val xi_of_c_bnd : cost_bnd -> form

(* -------------------------------------------------------------------- *)
val free_expr : EcTypes.expr -> bool

(* The cost of an expression evaluation in any memory of type [menv]
   satisfying [pre]. *)
val cost_of_expr : EcFol.form -> EcMemory.memenv -> EcTypes.expr -> EcFol.form

(* The cost of an expression evaluation in any memory of type [menv]. *)
val cost_of_expr_any : EcMemory.memenv -> EcTypes.expr -> EcFol.form
