open EcFol
open EcTypes
open EcIdent
open EcPath
open EcEnv

(* ---------------------------------------------------------------------- *)
exception Matches
exception NoMatches
exception CannotUnify
exception NoNext


module Name = EcIdent

module MName = Mid

(* -------------------------------------------------------------------------- *)

type meta_name = Name.t

type axiom =
  | Axiom_Form     of form
  | Axiom_Memory   of EcMemory.memory
  | Axiom_MemEnv   of EcMemory.memenv
  | Axiom_Prog_Var of prog_var
  | Axiom_Op       of EcPath.path * EcTypes.ty list
  | Axiom_Module   of mpath_top
  | Axiom_Mpath    of mpath
  | Axiom_Instr    of EcModules.instr
  | Axiom_Stmt     of EcModules.stmt
  | Axiom_Lvalue   of EcModules.lvalue
  | Axiom_Xpath    of EcPath.xpath
  | Axiom_Hoarecmp of EcFol.hoarecmp

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
  | Sym_Form_Prog_var     of EcTypes.pvar_kind
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
  | Pat_Instance   of pattern option * meta_name * EcPath.path * pattern list
  | Pat_Red_Strat  of pattern * reduction_strategy

  | Pat_Fun_Symbol of fun_symbol * pattern list
  | Pat_Axiom      of axiom
  | Pat_Type       of pattern * gty

and reduction_strategy = pattern -> axiom -> (pattern * axiom) option


type environnement = {
    env_hyps           : EcEnv.LDecl.hyps;
    env_unienv         : EcUnify.unienv;
    env_red_strat      : reduction_strategy;
    env_red_info       : EcReduction.reduction_info;
    env_restore_unienv : EcUnify.unienv option;
    (* FIXME : ajouter ici les stratégies *)
  }

type map = (pattern * binding Mid.t) MName.t


type pat_continuation =
  | ZTop
  | Znamed     of pattern * meta_name * pat_continuation

  (* Zor (cont, e_list, ne) :
       - cont   : the continuation if the matching is correct
       - e_list : if not, the sorted list of next engines to try matching with
       - ne     : if no match at all, then take the nengine to go up
   *)
  | Zor        of pat_continuation * engine list * nengine

  (* Zand (before, after, cont) :
       - before : list of couples (form, pattern) that has already been checked
       - after  : list of couples (form, pattern) to check in the following
       - cont   : continuation if all the matches succeed
   *)
  | Zand       of (axiom * pattern) list
                  * (axiom * pattern) list
                  * pat_continuation

  | Zbinds     of pat_continuation * binding Mid.t

and engine = {
    e_head         : axiom;
    e_pattern      : pattern;
    e_binds        : binding Mid.t;
    e_continuation : pat_continuation;
    e_map          : map;
    e_env          : environnement;
  }

and nengine = {
    ne_continuation : pat_continuation;
    ne_map          : map;
    ne_binds        : binding Mid.t;
    ne_env          : environnement;
  }

val search          : form -> pattern -> LDecl.hyps -> reduction_strategy ->
                      EcReduction.reduction_info ->
                      (map * environnement) option

val search_eng      : engine -> nengine option

val red_make_strat_from_info : EcReduction.reduction_info -> LDecl.hyps ->
                               pattern -> axiom -> (pattern * axiom) option

val mkengine        : form -> pattern -> LDecl.hyps -> reduction_strategy ->
                      EcReduction.reduction_info ->
                      engine

val pattern_of_form : bindings -> form -> pattern

val rewrite_term    : map -> EcFol.form -> environnement -> EcFol.form

val pat_fv          : pattern -> int Mid.t
