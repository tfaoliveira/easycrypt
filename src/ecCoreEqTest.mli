(* -------------------------------------------------------------------- *)
open EcTypes
open EcEnv

(* -------------------------------------------------------------------- *)
type 'a eqtest  = env -> 'a -> 'a -> bool

val for_type : ty eqtest
val for_etyarg : etyarg eqtest
