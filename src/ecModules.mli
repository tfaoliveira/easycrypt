(* -------------------------------------------------------------------- *)
open EcPath

(* -------------------------------------------------------------------- *)
include module type of struct include EcCoreModules end

(* -------------------------------------------------------------------- *)
(* Instantiation of EcCoreModules.PreOI on EcCoreFol.form. *)
module OI : sig
  type t = PreOI.t

  val hash : t -> int

  val equal : t -> t -> bool

  val allowed : t -> xpath list

  val allowed_s : t -> Sx.t

  val mk : xpath list -> t

  val filter : (xpath -> bool) -> t -> t
end

(* -------------------------------------------------------------------- *)

val add_oinfo :
  mod_restr -> string -> OI.t -> mod_restr

val change_oicalls :
  mod_restr -> string -> xpath list -> mod_restr

val oicalls_filter :
  mod_restr -> EcSymbols.Msym.key -> (EcPath.xpath -> bool) -> mod_restr
