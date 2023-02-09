(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal.FApi

(* -------------------------------------------------------------------- *)
module Low : sig
  val t_equiv_label_clean : side -> backward
  val t_equiv_label : backward
end

(* -------------------------------------------------------------------- *)
val t_label : oside -> backward
