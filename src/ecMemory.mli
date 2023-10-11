(* -------------------------------------------------------------------- *)
open EcSymbols
open EcTypes
(* -------------------------------------------------------------------- *)
type memory = EcIdent.t

val mem_equal : memory -> memory -> bool

(* -------------------------------------------------------------------- *)

type proj_arg = {
  arg_quantum : quantum;    (* classical/quantum *)
  arg_ty      : ty;         (* type of the procedure argument "arg" *)
  arg_pos     : int;        (* projection *)
}

type memtype

val mt_equal_gen : (ty -> ty -> bool) -> memtype -> memtype -> bool
val mt_equal     : memtype -> memtype -> bool
val mt_fv        : memtype -> int EcIdent.Mid.t

val mt_iter_ty : (ty -> unit) -> memtype -> unit

(* -------------------------------------------------------------------- *)
type memenv = memory * memtype

val mem_hash : memenv -> int
val me_equal_gen : (ty -> ty -> bool) -> memenv -> memenv -> bool
val me_equal : memenv -> memenv -> bool

(* -------------------------------------------------------------------- *)
val memory   : memenv -> memory
val memtype  : memenv -> memtype

(* -------------------------------------------------------------------- *)
val empty_local    : witharg:bool -> memory -> memenv
val empty_local_mt : witharg:bool -> memtype

val schema    : memory -> memenv
val schema_mt : memtype

val abstract    : memory -> memenv
val abstract_mt : memtype

val is_schema : memtype -> bool

exception DuplicatedMemoryBinding of symbol

val bindall    : ovariable list -> memenv -> memenv
val bindall_mt : ovariable list -> memtype -> memtype

val bind_fresh : ovariable -> memenv -> memenv * ovariable
val bindall_fresh : ovariable list -> memenv -> memenv * ovariable list

(* -------------------------------------------------------------------- *)
type lookup = (variable * proj_arg option * int option) option

val lookup : symbol -> memtype -> lookup

val lookup_me : symbol -> memenv -> lookup

(* -------------------------------------------------------------------- *)
val get_name : symbol -> int option -> memenv -> symbol option

(* -------------------------------------------------------------------- *)
val is_bound : symbol -> memtype -> bool
val is_bound_pv : EcTypes.prog_var -> memtype -> bool

(* -------------------------------------------------------------------- *)
val mt_subst : (ty -> ty) -> memtype -> memtype
val me_subst : memory EcIdent.Mid.t -> (ty -> ty) -> memenv -> memenv

(* -------------------------------------------------------------------- *)
type lmt_printing = symbol option * ovariable list
type mt_printing  = lmt_printing * lmt_printing

(* -------------------------------------------------------------------- *)
val local_type : memtype -> (ty * ty) option
val has_locals : memtype -> bool

(* -------------------------------------------------------------------- *)
val for_printing : memtype -> mt_printing option
