(* -------------------------------------------------------------------- *)
open EcMaps

module Json = Yojson

(* -------------------------------------------------------------------- *)
module Version : sig
  val current : int
end

(* -------------------------------------------------------------------- *)
type digest = Digest.t

type ecoroot = {
  eco_kind   : EcLoader.kind;
  eco_digest : digest;
}

type eco = {
  eco_root    : ecoroot;
  eco_depends : ecoroot Mstr.t;
}

(* -------------------------------------------------------------------- *)
val get_eco_filename : string -> string

(* -------------------------------------------------------------------- *)
exception InvalidEco

val of_json : Json.t -> eco
val pp : Format.formatter -> eco -> unit

(* -------------------------------------------------------------------- *)
type loader = string ->
  (EcLoader.namespace option * string * EcLoader.kind) option

val check_eco : loader -> string -> bool
