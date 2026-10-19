(* -------------------------------------------------------------------- *)
(* Evaluation of closed expressions and of concrete procedures, for the *)
(* [eval] and [check] commands. See ecEval.ml for the trusted base.     *)
(* -------------------------------------------------------------------- *)
open EcPath
open EcFol

(* -------------------------------------------------------------------- *)
exception EvalError of string

type value =
  | VInt   of Z.t
  | VBool  of bool
  | VBits  of int * Z.t                  (* size, unsigned value *)
  | VCtor  of path * int * value list    (* constructor, index, fields *)
  | VTuple of value list
  | VFun   of (value -> value)
  | VNeu   of path * value list * int    (* stuck application of an abstract op, *)
                                         (* with a unique identifier             *)
  | VWitness

val pp_value : Format.formatter -> value -> unit

(* Structural equality; raises [EvalError] when it cannot be decided. *)
val value_eq : value -> value -> bool

val as_bool : value -> bool

(* -------------------------------------------------------------------- *)
val eval_form : EcEnv.env -> form -> value
val run_proc  : EcEnv.env -> xpath -> form list -> value

(* Equality at the given type, using the [eval] rules on [=] (e.g. for  *)
(* arrays); raises [EvalError] when it cannot be decided.               *)
val check_eq  : EcEnv.env -> EcTypes.ty -> value -> value -> bool
