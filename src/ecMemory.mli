(* -------------------------------------------------------------------- *)
open EcSymbols
open EcTypes
(* -------------------------------------------------------------------- *)
type memory = EcAst.memory

val mem_equal : memory -> memory -> bool

(* -------------------------------------------------------------------- *)
type proj_arg = EcAst.proj_arg
type memtype = EcAst.memtype

val mt_equal_gen : (ty -> ty -> bool) -> memtype -> memtype -> bool
val mt_equal     : memtype -> memtype -> bool
val mt_fv        : memtype -> int EcIdent.Mid.t

(* -------------------------------------------------------------------- *)
type memenv = EcAst.memenv

val me_equal_gen : (ty -> ty -> bool) -> memenv -> memenv -> bool
val me_equal : memenv -> memenv -> bool

val has_quantum : memenv -> bool

(* -------------------------------------------------------------------- *)
val memory   : memenv -> memory
val memtype  : memenv -> memtype

(* -------------------------------------------------------------------- *)
type wa = [`All | `Classical | `Quantum | `None]

val empty_local    : witharg:wa -> memory -> memenv
val empty_local_mt : witharg:wa -> memtype

val abstract    : memory -> memenv
val abstract_mt : memtype

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
val has_quantum : memtype -> bool

(* -------------------------------------------------------------------- *)
val for_printing : memtype -> mt_printing option
