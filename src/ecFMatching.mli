open EcFol
open EcIdent
open EcEnv
open EcPattern

(* ---------------------------------------------------------------------- *)
exception Matches
exception NoMatches
exception CannotUnify
exception NoNext

type match_env = {
    me_unienv    : EcUnify.unienv;
    me_meta_vars : ogty Mid.t;
    me_matches   : pattern Mid.t;
  }

type verbose

type environment = {
    env_hyps               : EcEnv.LDecl.hyps;
    env_match              : match_env;
    env_red_info_match     : EcReduction.reduction_info;
    env_red_info_same_meta : EcReduction.reduction_info;
    env_meta_restr_binds   : pbindings Mid.t;
    env_verbose            : verbose;
  }

val no_verbose    : verbose
val full_verbose  : verbose
val debug_verbose : verbose

type pat_continuation
type engine
type nengine

val get_matches     : engine -> match_env
val get_n_matches   : nengine -> match_env

val menv_copy       : match_env -> match_env

val menv_of_hyps    : LDecl.hyps -> match_env

val menv_add_form   : ident -> EcTypes.ty -> match_env -> match_env

val menv_add_mem    : ident -> match_env -> match_env

val menv_get_form   : ident -> env -> match_env -> form option

val menv_has_form   : ident -> match_env -> bool

val menv_has_memory : ident -> match_env -> bool

val init_match_env  : ?mtch:pattern Mid.t -> ?unienv:EcUnify.unienv ->
                      ?metas:ogty Mid.t -> unit -> match_env

val search_eng      : engine -> nengine option

val mk_engine       : ?mtch:match_env -> pattern -> pattern ->
                      LDecl.hyps -> EcReduction.reduction_info ->
                      EcReduction.reduction_info -> engine

val pattern_of_form : match_env -> form -> pattern
val pattern_of_memory : match_env -> EcMemory.memory -> pattern

val rewrite_term    : engine -> EcFol.form -> pattern

val menv_is_full    : match_env -> LDecl.hyps -> bool

(* -------------------------------------------------------------------------- *)
module Translate : sig
  exception Invalid_Type of string

  val form_of_pattern      : EcEnv.env -> pattern -> form
  val memory_of_pattern    : pattern -> EcMemory.memory
  val memenv_of_pattern    : pattern -> EcMemory.memenv
  val prog_var_of_pattern  : EcEnv.env -> pattern -> EcTypes.prog_var
  val xpath_of_pattern     : EcEnv.env -> pattern -> EcPath.xpath
  val mpath_of_pattern     : EcEnv.env -> pattern -> EcPath.mpath
  val mpath_top_of_pattern : EcEnv.env -> pattern -> EcPath.mpath_top
  val path_of_pattern      : pattern -> EcPath.path
  val stmt_of_pattern      : EcEnv.env -> pattern -> EcModules.stmt
  val instr_of_pattern     : EcEnv.env -> pattern -> EcModules.instr list
  val lvalue_of_pattern    : EcEnv.env -> pattern -> EcModules.lvalue
  val expr_of_pattern      : EcEnv.env -> pattern -> EcTypes.expr
  val cmp_of_pattern       : pattern -> hoarecmp
end

val psubst_of_menv  : match_env -> Psubst.p_subst
val fsubst_of_menv  : match_env -> env -> f_subst
