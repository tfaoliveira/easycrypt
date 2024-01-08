(* ==================================================================== *)
open Aig

(* ==================================================================== *)
val explode : size:int -> 'a list -> 'a list list

(* ==================================================================== *)
val sint_of_bools : bool list -> int

val uint_of_bools : bool list -> int

val bytes_of_bools : bool list -> bytes

(* ==================================================================== *)
val of_int : size:int -> int -> reg

val of_bigint : size:int -> Z.t -> reg

val of_int32s : int32 list -> reg

(* ==================================================================== *)
val w8 : int -> reg

val w16 : int -> reg

val w32 : int32 -> reg

val w64 : int64 -> reg

val w128 : string -> reg

val w256 : string -> reg

(* ==================================================================== *)
val mux2 : node -> node -> node -> node

val mux2_reg : reg -> reg -> node -> reg

val mux_reg : (node * reg) list -> reg -> reg

(* ==================================================================== *)
val reg : size:int -> name:int -> reg

(* ==================================================================== *)
val uextend : size:int -> reg -> reg

val sextend : size:int -> reg -> reg

(* ==================================================================== *)
val lnot_ : reg -> reg

val lor_ : reg -> reg -> reg

val land_ : reg -> reg -> reg

val ors : node list -> node

val ands : node list -> node

(* ==================================================================== *)
val arshift : offset:int -> reg -> reg

val lsl_ : reg -> reg -> reg

val lsr_ : reg -> reg -> reg

val asl_ : reg -> reg -> reg

val asr_ : reg -> reg -> reg

val shift : side:[`L | `R] -> sign:[`U | `S] -> reg -> reg -> reg

(* ==================================================================== *)
val incr : reg -> node * reg

val incr_dropc : reg -> reg

val incrc : reg -> reg

(* ==================================================================== *)
val add : reg -> reg -> node * reg

val addc : reg -> reg -> reg

val add_dropc : reg -> reg -> reg

(* ==================================================================== *)
val opp : reg -> reg

val sub : reg -> reg -> node * reg

val sub_dropc : reg -> reg -> reg

(* ==================================================================== *)
val umul : reg -> reg -> reg

val umull : reg -> reg -> reg

val umulh : reg -> reg -> reg

val smul : reg -> reg -> reg

val smull : reg -> reg -> reg

(* ==================================================================== *)
val sat : signed:bool -> size:int -> reg -> reg
