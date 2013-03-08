(* -------------------------------------------------------------------- *)
open EcIdent
open EcTypes
open EcModules
open EcMemory

(* -------------------------------------------------------------------- *)
val mstd   : memory
val mpre   : memory
val mpost  : memory
val mhr    : memory
val mleft  : memory
val mright : memory

type gty =
  | GTty    of EcTypes.ty
  | GTmodty of module_type
  | GTmem

type quantif = 
  | Lforall
  | Lexists

type binding =  (EcIdent.t * gty) list

type form = private { 
  f_node : f_node;
  f_ty   : ty; 
  f_fv   : EcIdent.Sid.t;
  f_tag  : int;
}

and f_node = 
  | Fquant  of quantif * binding * form
  | Fif     of form * form * form
  | Flet    of lpattern * form * form
  | Fint    of int
  | Flocal  of EcIdent.t
  | Fpvar   of EcTypes.prog_var * memory
  | Fop     of EcPath.path * ty list
  | Fapp    of form * form list
  | Ftuple  of form list

  | FhoareF of form * EcPath.mpath * form  (* $pre / $post *)
  | FhoareS of memenv * form * stmt * form (* $hr  / $hr   *)

  | FequivF of form * (EcPath.mpath * EcPath.mpath) * form  (* $left,$right / $left,$right *)
  | FequivS of form * (memenv * stmt) EcUtils.double * form (* $left,$right / $left,$right *)

  | Fpr     of memory * EcPath.mpath * form list * (EcIdent.t * ty) * form 

val f_equal : form -> form -> bool

(* -------------------------------------------------------------------- *)
(* val fv : form -> EcIdent.Sid.t *)
val ty : form -> EcTypes.ty
val fv_node : f_node -> EcIdent.Sid.t
val mk_form : f_node -> EcTypes.ty -> form

val f_local : EcIdent.t -> EcTypes.ty -> form
val f_pvar : EcTypes.prog_var -> EcTypes.ty -> memory -> form

val f_true : form
val f_false : form
val f_bool : bool -> form

val f_int : int -> form

val f_op : EcPath.path -> EcTypes.ty list -> EcTypes.ty -> form
val f_app : form -> form list -> EcTypes.ty -> form

val f_tuple : form list -> form
val f_if : form -> form -> form -> form
val f_let : EcTypes.lpattern -> form -> form -> form
val f_quant : quantif -> binding -> form -> form
val f_exists : binding -> form -> form
val f_forall : binding -> form -> form

val f_hoare   : memenv -> form -> EcModules.stmt -> form -> form 
val f_hoareF  : form -> EcPath.mpath -> form -> form 
val f_equivF  : form -> EcPath.mpath -> EcPath.mpath -> form -> form 
val f_pr      : 
    memory -> EcPath.mpath -> form list -> 
      EcIdent.t * EcTypes.ty -> form -> form

val fop_not : form
val f_not : form -> form

val fop_and : form
val f_and : form -> form -> form

val fop_anda : form
val f_anda : form -> form -> form

val fop_or : form
val f_or : form -> form -> form

val fop_ora : form
val f_ora : form -> form -> form

val fop_imp : form
val f_imp : form -> form -> form

val fop_iff : form
val f_iff : form -> form -> form

val fop_eq : EcTypes.ty -> form
val f_eq : form -> form -> form

val f_int_leq : form -> form -> form

val f_int_lt  : form -> form -> form


(* -------------------------------------------------------------------- *)
type destr_error =
    Destr_and
  | Destr_or
  | Destr_imp
  | Destr_forall
  | Destr_exists

exception DestrError of destr_error

val destr_and : form -> form * form
val destr_or : form -> form * form
val destr_imp : form -> form * form
val destr_forall1 : form -> EcIdent.t * gty * form
val destr_exists1 : form -> EcIdent.t * gty * form
val is_and : form -> bool
val is_or : form -> bool
val is_imp : form -> bool
val is_forall : form -> bool
val is_exists : form -> bool

val map : (EcTypes.ty -> EcTypes.ty) -> (form -> form) -> form -> form

(* -------------------------------------------------------------------- *)
module Fsubst :
  sig
    val mapty : (EcTypes.ty -> EcTypes.ty) -> form -> form
    val uni : EcTypes.ty EcUidgen.Muid.t -> form -> form
    val idty : 'a -> 'a
    val subst_local : EcIdent.t -> form -> form -> form
    val subst_tvar : EcTypes.ty EcIdent.Mid.t -> form -> form
  end

type local_kind = 
  | LD_var of EcTypes.ty * form option
  | LD_mem
  | LD_modty of EcModules.module_type
  | LD_hyp of form

type l_local = EcIdent.t * local_kind

type hyps = { 
    h_tvar : EcIdent.t list; 
    h_local : l_local list; }

type l_decl = hyps * form

type prover_info = unit (* FIXME *)

type rule_name =
    RN_admit
  | RN_clear of EcIdent.t
  | RN_prover of prover_info
  | RN_local of EcIdent.t
  | RN_global of EcPath.path * EcTypes.ty list
  | RN_exc_midle
  | RN_eq of EcIdent.t * form
  | RN_and_I
  | RN_or_I of bool
  | RN_imp_I
  | RN_forall_I
  | RN_exists_I of form
  | RN_and_E
  | RN_or_E
  | RN_imp_E
  | RN_forall_E of form
  | RN_exists_E
  | RN_cut of form

  | RN_app of (int * form)
  | RN_wp of int
  | RN_skip
  | RN_while of form * form * form

type rule     = (rule_name, l_decl) EcBaseLogic.rule
type judgment = (rule_name, l_decl) EcBaseLogic.judgment

(* -------------------------------------------------------------------- *)
module LDecl :
sig
  type error =
    | UnknownSymbol of EcSymbols.symbol
    | UnknownIdent of EcIdent.t
    | NotAVariable of EcIdent.t
    | NotAHypothesis of EcIdent.t
    | CanNotClear of EcIdent.t * EcIdent.t
    | CannotClearMem
    | CannotClearModTy
    | DuplicateIdent of EcIdent.t
    | DuplicateSymbol of EcSymbols.symbol

  exception Ldecl_error of error

  val pp_error : Format.formatter -> error -> unit
  val error : error -> 'a
  val lookup : EcSymbols.symbol -> hyps -> l_local
  val lookup_by_id : EcIdent.t -> hyps -> local_kind
  val get_hyp : EcIdent.t * local_kind -> EcIdent.t * form
  val get_var : EcIdent.t * local_kind -> EcIdent.t * EcTypes.ty
  val lookup_hyp : EcSymbols.symbol -> hyps -> EcIdent.t * form
  val has_hyp : EcSymbols.symbol -> hyps -> bool
  val lookup_hyp_by_id : EcIdent.t -> hyps -> form
  val lookup_var : EcSymbols.symbol -> hyps -> EcIdent.t * EcTypes.ty
  val lookup_var_by_id : EcIdent.t -> hyps -> EcTypes.ty
  val has_symbol : EcSymbols.symbol -> hyps -> bool
  val has_ident : EcIdent.t -> hyps -> bool
  val check_id : EcIdent.t -> hyps -> unit
  val add_local : EcIdent.t -> local_kind -> hyps -> hyps
  val clear : EcIdent.t -> hyps -> hyps
end

(* -------------------------------------------------------------------- *)
module Lvar :
sig
  type t

  val mk_pvar :  EcTypes.prog_var -> EcMemory.memory -> t    
end

(* -------------------------------------------------------------------- *)
module LVmap : Map.S with type key =  Lvar.t
module LVset : 
  sig
    include Set.S with type elt =  Lvar.t
    val pvars : t -> (EcTypes.prog_var * EcMemory.memory) list
  end

(* -------------------------------------------------------------------- *)

module Pvar : sig 
  type t = EcTypes.prog_var * EcMemory.memory * ty
end
module PVset : Set.S with type elt = Pvar.t

module Subst :
  sig
    type t
    val single_subst :  Lvar.t -> form -> t
    val subst_form :  t -> form -> form
    val add_subst : LVmap.key -> form -> t -> t
    val empty_subst : t
    val fpvar_form : form -> LVset.t
  end


val free_pvar : form -> PVset.t 

val form_of_exp : EcMemory.memory -> EcTypes.tyexpr -> form

val let_form : (Lvar.t*ty) list -> form -> form -> form 
