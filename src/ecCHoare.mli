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

(* Backward reasoning on cost.
   Looks for a solution [x] of [c = x + sub]. *)
val cost_sub : c:form -> sub:form -> csub_res

(* Same as [cost_sub], but only for the concrete cost.
   [c] of type [tcost], [sub] of type [xint]. *)
val cost_sub_self : c:form -> sub:form -> csub_res

(* -------------------------------------------------------------------- *)
(* [c] of type [tcost], [a] of type [xint] *)
val cost_add_self : c:form -> a:form -> form

(* -------------------------------------------------------------------- *)
(* [choare_xsum cost (m,n)]:
   [cost] of type [tcost], [m] of type [tint], [n] of type [txint].

   [n] must be finite, i.e. [n = f_N n_fin]. *)
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
