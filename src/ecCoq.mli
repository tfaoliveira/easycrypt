open EcFol
open EcEnv
open EcProvers

type mode =
  | Batch (* Only check scripts *)
  | Update (* Check and update scripts *)
  | Edit  (* Edit then check scripts *)
  | Fix   (* Try to check script, then edit script on non-success *)
  | FixUpdate (* Update and fix *)


val check: loc:EcLocation.t -> ?notify:notify -> ?coqmode:mode-> LDecl.hyps -> form -> bool
