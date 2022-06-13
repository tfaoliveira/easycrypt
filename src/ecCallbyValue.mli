(* -------------------------------------------------------------------- *)
open EcFol
open EcEnv
open EcReduction

(* -------------------------------------------------------------------- *)
(** used by `/=` *)
val norm_cbv : reduction_info -> LDecl.hyps -> form -> form
