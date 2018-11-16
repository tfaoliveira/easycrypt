open EcFol
open EcTypes
open EcPath
open EcMemory
open EcIdent
open EcModules

module Name = EcIdent

module MName = Mid

(* -------------------------------------------------------------------------- *)

type meta_name = Name.t

type axiom =
  | Axiom_Form     of form
  | Axiom_Memory   of memory
  | Axiom_MemEnv   of memenv
  | Axiom_Prog_Var of prog_var
  | Axiom_Op       of path * ty list
  | Axiom_Module   of mpath_top
  | Axiom_Mpath    of mpath
  | Axiom_Instr    of instr
  | Axiom_Stmt     of stmt
  | Axiom_Lvalue   of lvalue
  | Axiom_Xpath    of xpath
  | Axiom_Hoarecmp of hoarecmp
  | Axiom_Local    of ident * ty

type fun_symbol =
  (* from type form *)
  | Sym_Form_If
  | Sym_Form_App          of ty
  | Sym_Form_Tuple
  | Sym_Form_Proj         of int
  | Sym_Form_Match        of ty
  | Sym_Form_Quant        of quantif * bindings
  | Sym_Form_Let          of lpattern
  | Sym_Form_Pvar         of ty
  | Sym_Form_Prog_var     of pvar_kind
  | Sym_Form_Glob
  | Sym_Form_Hoare_F
  | Sym_Form_Hoare_S
  | Sym_Form_bd_Hoare_F
  | Sym_Form_bd_Hoare_S
  | Sym_Form_Equiv_F
  | Sym_Form_Equiv_S
  | Sym_Form_Eager_F
  | Sym_Form_Pr
  (* form type stmt*)
  | Sym_Stmt_Seq
  (* from type instr *)
  | Sym_Instr_Assign
  | Sym_Instr_Sample
  | Sym_Instr_Call
  | Sym_Instr_Call_Lv
  | Sym_Instr_If
  | Sym_Instr_While
  | Sym_Instr_Assert
  (* from type xpath *)
  | Sym_Xpath
  (* from type mpath *)
  | Sym_Mpath
  (* generalized *)
  | Sym_App
  | Sym_Quant             of quantif * ((ident * (gty option)) list)

(* invariant of pattern : if the form is not Pat_Axiom, then there is
     at least one of the first set of patterns *)
type pattern =
  | Pat_Anything
  | Pat_Meta_Name  of pattern * meta_name
  | Pat_Sub        of pattern
  | Pat_Or         of pattern list
  | Pat_Instance   of pattern option * meta_name * path * pattern list
  | Pat_Red_Strat  of pattern * reduction_strategy

  | Pat_Fun_Symbol of fun_symbol * pattern list
  | Pat_Axiom      of axiom
  | Pat_Type       of pattern * gty

and reduction_strategy = pattern -> axiom -> (pattern * axiom) option

type map = pattern MName.t

val pat_fv : pattern -> int Mid.t

(* -------------------------------------------------------------------------- *)

val pat_axiom : axiom -> pattern

val pat_form      : form            -> pattern
val pat_mpath     : mpath           -> pattern
val pat_mpath_top : mpath_top       -> pattern
val pat_xpath     : xpath           -> pattern
val pat_op        : path -> ty list -> pattern
val pat_lvalue    : lvalue          -> pattern
val pat_instr     : instr           -> pattern
val pat_stmt      : stmt            -> pattern
val pat_local     : ident -> ty     -> pattern

(* -------------------------------------------------------------------------- *)

val p_true    : pattern
val p_false   : pattern

(* -------------------------------------------------------------------------- *)
val p_mpath        : pattern -> pattern list -> pattern
val p_xpath        : pattern -> pattern -> pattern
val p_prog_var     : pattern -> pvar_kind -> pattern
val p_lvalue_var   : pattern -> ty -> pattern
val p_lvalue_tuple : pattern list -> pattern

val p_let      : lpattern -> pattern -> pattern -> pattern
val p_if       : pattern -> pattern -> pattern -> pattern
val p_proj     : pattern -> int -> ty -> pattern
val p_app      : pattern -> pattern list -> ty option -> pattern
val p_f_quant  : quantif -> bindings -> pattern -> pattern
val p_quant    : quantif -> (EcIdent.t * EcFol.gty option) list -> pattern -> pattern
val p_pvar     : prog_var -> ty -> memory -> pattern

val p_assign   : pattern -> pattern -> pattern
val p_sample   : pattern -> pattern -> pattern
val p_call     : pattern option -> pattern -> pattern list -> pattern
val p_instr_if : pattern -> pattern -> pattern -> pattern
val p_while    : pattern -> pattern -> pattern
val p_assert   : pattern -> pattern

(* -------------------------------------------------------------------------- *)
val p_destr_app : pattern -> pattern * pattern list

(* -------------------------------------------------------------------------- *)
val p_if_simpl      : pattern -> pattern -> pattern -> pattern
val p_proj_simpl    : pattern -> int -> ty -> pattern
val p_app_simpl_opt : pattern option -> pattern list -> ty -> pattern option
val p_forall_simpl  : bindings -> pattern -> pattern
val p_exists_simpl  : bindings -> pattern -> pattern

(* -------------------------------------------------------------------------- *)
module Psubst : sig
  type p_subst

  val p_subst_id   : p_subst
  val p_bind_local : p_subst -> EcIdent.t -> pattern -> p_subst

  val p_subst      : p_subst -> pattern -> pattern
end

(* -------------------------------------------------------------------- *)
val default_start_name : string
val default_end_name   : string
val default_name       : string
