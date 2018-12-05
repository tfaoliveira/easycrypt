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

type pbindings = (ident * gty option) list

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
  | Sym_Form_Proj         of int * ty
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
  | Sym_Quant             of quantif * pbindings


(* invariant of pattern : if the form is not Pat_Axiom, then there is
     at least one of the first set of patterns *)
type pattern =
  | Pat_Anything
  | Pat_Meta_Name  of pattern * meta_name * pbindings option
  | Pat_Sub        of pattern
  | Pat_Or         of pattern list
  | Pat_Instance   of pattern option * meta_name * path * pattern list
  | Pat_Red_Strat  of pattern * reduction_strategy

  | Pat_Fun_Symbol of fun_symbol * pattern list
  | Pat_Axiom      of axiom
  | Pat_Type       of pattern * gty

and reduction_strategy =
  EcReduction.reduction_info -> EcReduction.reduction_info ->
  EcReduction.reduction_info * EcReduction.reduction_info

type map = pattern MName.t

val pat_fv : pattern -> int Mid.t

(* -------------------------------------------------------------------------- *)
val p_equal    : pattern -> pattern -> bool
val p_map_fold : ('a -> pattern -> 'a * pattern) -> 'a -> pattern -> 'a * pattern
(* -------------------------------------------------------------------------- *)

val pat_axiom : axiom -> pattern

val axiom_form    : form -> axiom
val axiom_mpath   : mpath -> axiom

val pat_form      : form            -> pattern
val pat_mpath     : mpath           -> pattern
val pat_mpath_top : mpath_top       -> pattern
val pat_xpath     : xpath           -> pattern
val pat_op        : path -> ty list -> pattern
val pat_lvalue    : lvalue          -> pattern
val pat_instr     : instr           -> pattern
val pat_stmt      : stmt            -> pattern
val pat_local     : ident -> ty     -> pattern
val pat_pv        : prog_var        -> pattern
val pat_memory    : EcMemory.memory -> pattern
val pat_memenv    : EcMemory.memenv -> pattern
val pat_cmp       : hoarecmp        -> pattern

(* -------------------------------------------------------------------------- *)
exception Invalid_Type of string

val form_of_pattern      : EcEnv.env -> pattern -> form
val memory_of_pattern    : pattern -> memory
val memenv_of_pattern    : pattern -> memenv
val prog_var_of_pattern  : EcEnv.env -> pattern -> prog_var
val xpath_of_pattern     : EcEnv.env -> pattern -> xpath
val mpath_of_pattern     : EcEnv.env -> pattern -> mpath
val mpath_top_of_pattern : EcEnv.env -> pattern -> mpath_top
val path_of_pattern      : pattern -> path
val stmt_of_pattern      : EcEnv.env -> pattern -> stmt
val instr_of_pattern     : EcEnv.env -> pattern -> instr list
val lvalue_of_pattern    : EcEnv.env -> pattern -> lvalue
val expr_of_pattern      : EcEnv.env -> pattern -> expr
val cmp_of_pattern       : pattern -> hoarecmp

(* -------------------------------------------------------------------------- *)

val p_true    : pattern
val p_false   : pattern

(* -------------------------------------------------------------------------- *)
val p_mpath        : pattern -> pattern list -> pattern
val p_xpath        : pattern -> pattern -> pattern
val p_prog_var     : pattern -> pvar_kind -> pattern
val p_lvalue_var   : pattern -> ty -> pattern
val p_lvalue_tuple : pattern list -> pattern

val p_type     : pattern -> gty -> pattern

val p_let      : lpattern -> pattern -> pattern -> pattern
val p_if       : pattern -> pattern -> pattern -> pattern
val p_proj     : pattern -> int -> ty -> pattern
val p_tuple    : pattern list -> pattern
val p_app      : pattern -> pattern list -> ty option -> pattern
val p_f_quant  : quantif -> bindings -> pattern -> pattern
val p_quant    : quantif -> (EcIdent.t * EcFol.gty option) list -> pattern -> pattern
val p_pvar     : pattern -> ty -> pattern -> pattern
val p_glob     : pattern -> pattern -> pattern
val p_match    : pattern -> ty -> pattern list -> pattern

val p_hoareF   : pattern -> pattern -> pattern -> pattern
val p_hoareS   : pattern -> pattern -> pattern -> pattern -> pattern
val p_bdHoareF : pattern -> pattern -> pattern -> pattern -> pattern -> pattern
val p_bdHoareS : pattern -> pattern -> pattern -> pattern -> pattern -> pattern -> pattern
val p_equivF   : pattern -> pattern -> pattern -> pattern -> pattern
val p_equivS   : pattern -> pattern -> pattern -> pattern -> pattern -> pattern -> pattern
val p_eagerF   : pattern -> pattern -> pattern -> pattern -> pattern -> pattern -> pattern
val p_pr       : pattern -> pattern -> pattern -> pattern -> pattern

val p_assign   : pattern -> pattern -> pattern
val p_sample   : pattern -> pattern -> pattern
val p_call     : pattern option -> pattern -> pattern list -> pattern
val p_instr_if : pattern -> pattern -> pattern -> pattern
val p_while    : pattern -> pattern -> pattern
val p_assert   : pattern -> pattern

val p_stmt     : pattern list -> pattern

(* -------------------------------------------------------------------------- *)
val p_destr_app : pattern -> pattern * pattern list

(* -------------------------------------------------------------------------- *)
val p_eq    : pattern -> pattern -> pattern
val p_and   : pattern -> pattern -> pattern
val p_ands  : pattern list -> pattern

(* -------------------------------------------------------------------------- *)
val p_if_simpl      : pattern -> pattern -> pattern -> pattern
val p_proj_simpl    : pattern -> int -> ty -> pattern
val p_app_simpl_opt : pattern option -> pattern list -> ty option -> pattern option
val p_forall_simpl  : bindings -> pattern -> pattern
val p_exists_simpl  : bindings -> pattern -> pattern
val p_eq_simpl      : pattern -> pattern -> pattern

(* -------------------------------------------------------------------------- *)
val p_not_simpl      : pattern -> pattern
val p_imp_simpl      : pattern -> pattern -> pattern
val p_anda_simpl     : pattern -> pattern -> pattern
val p_ora_simpl      : pattern -> pattern -> pattern
val p_iff_simpl      : pattern -> pattern -> pattern
val p_and_simpl      : pattern -> pattern -> pattern
val p_or_simpl       : pattern -> pattern -> pattern
val p_int_le_simpl   : pattern -> pattern -> pattern
val p_int_lt_simpl   : pattern -> pattern -> pattern
val p_int_add_simpl  : pattern -> pattern -> pattern
val p_int_mul_simpl  : pattern -> pattern -> pattern
val p_int_opp_simpl  : pattern -> pattern
val p_real_le_simpl  : pattern -> pattern -> pattern
val p_real_lt_simpl  : pattern -> pattern -> pattern
val p_real_add_simpl : pattern -> pattern -> pattern
val p_real_mul_simpl : pattern -> pattern -> pattern
val p_real_opp_simpl : pattern -> pattern
val p_real_inv_simpl : pattern -> pattern

(* -------------------------------------------------------------------------- *)
val p_destr_app     : pattern -> pattern * pattern list
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
module Psubst : sig
  type p_subst = {
      ps_freshen : bool;
      ps_patloc  : pattern             Mid.t;
      ps_opdef   : (ident list * expr) Mp.t;
      ps_pddef   : (ident list * form) Mp.t;
      ps_exloc   : expr                Mid.t;
      ps_sty     : ty_subst;
    }

  val p_subst_id   : p_subst

  val is_subst_id  : p_subst -> bool
  val p_subst_init : ?sty:EcTypes.ty_subst ->
                     ?opdef:(EcIdent.ident list * EcTypes.expr) EcPath.Mp.t ->
                     ?prdef:(EcIdent.ident list * EcFol.form) EcPath.Mp.t ->
                     unit -> p_subst

  val p_bind_local  : p_subst -> ident -> pattern -> p_subst
  val p_bind_mem    : p_subst -> memory -> memory -> p_subst
  val p_bind_mod    : p_subst -> ident -> mpath -> p_subst
  val p_bind_rename : p_subst -> ident -> ident -> ty -> p_subst
  val p_bind_gty    : p_subst -> ident -> ident -> gty -> p_subst

  val p_rem_local   : p_subst -> ident -> p_subst
  val p_rem_mem     : p_subst -> memory -> p_subst
  val p_rem_mod     : p_subst -> ident -> p_subst

  val add_local     : p_subst -> ident * ty -> p_subst * (t * ty)
  val add_locals    : p_subst -> (t * ty) list ->
                      p_subst * (t * ty) list

  val add_binding   : p_subst -> binding -> p_subst * binding
  val add_bindings  : p_subst -> bindings -> p_subst * bindings

  val add_pbinding  : p_subst -> ident * gty option -> p_subst * (ident * gty option)
  val add_pbindings : p_subst -> (ident * gty option) list -> p_subst * ((ident * gty option) list)

  val p_subst       : p_subst -> pattern -> pattern
end

(* -------------------------------------------------------------------- *)

val p_betared_opt : pattern -> pattern option


(* -------------------------------------------------------------------- *)
val default_start_name : string
val default_end_name   : string
val default_name       : string


(* -------------------------------------------------------------------------- *)

module PReduction : sig

  val reduce_local_opt  : EcEnv.LDecl.hyps -> EcReduction.reduction_info ->
                          Psubst.p_subst -> Name.t -> pattern option

  val h_red_pattern_opt : EcEnv.LDecl.hyps -> EcReduction.reduction_info ->
                          Psubst.p_subst -> pattern -> pattern option
  val h_red_axiom_opt : EcEnv.LDecl.hyps -> EcReduction.reduction_info ->
                          Psubst.p_subst -> axiom -> pattern option
  val h_red_form_opt : EcEnv.LDecl.hyps -> EcReduction.reduction_info ->
                          Psubst.p_subst -> form -> pattern option
end
