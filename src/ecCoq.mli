open EcFol
open EcEnv
open EcProvers

type mode =
  | Check (* Check scripts *)
  | Edit  (* Edit then check scripts *)
  | Fix   (* Try to check script, then edit script on non-success *)

val check: loc:EcLocation.t -> name:string -> ?notify:notify ->
  ?coqmode:mode-> LDecl.hyps -> form -> bool
