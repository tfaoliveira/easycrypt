(* -------------------------------------------------------------------- *)
open EcParsetree
open EcEnv
open EcTypes

(* -------------------------------------------------------------------- *)
val bind_bitstring : env -> pqsymbol -> int -> env

(* -------------------------------------------------------------------- *)
val bind_circuit : env -> psymbol -> string -> env 

(* -------------------------------------------------------------------- *)
val bdep : env -> pgamepath -> psymbol -> int -> int-> string list -> psymbol -> unit
