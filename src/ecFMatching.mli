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

type verbose = {
    verbose_match           : bool;
    verbose_rule            : bool;
    verbose_type            : bool;
    verbose_bind_restr      : bool;
    verbose_add_meta        : bool;
    verbose_abstract        : bool;
    verbose_reduce          : bool;
    verbose_show_ignored_or : bool;
    verbose_show_or         : bool;
  }

type environment = {
    env_hyps               : EcEnv.LDecl.hyps;
    env_match              : match_env;
    env_red_info_match     : EcReduction.reduction_info;
    env_red_info_same_meta : EcReduction.reduction_info;
    env_restore_unienv     : EcUnify.unienv option ref;
    env_current_binds      : pbindings;
    env_meta_restr_binds   : pbindings Mid.t;
    env_verbose            : verbose;
  }

val no_verbose    : verbose
val full_verbose  : verbose
val debug_verbose : verbose

type pat_continuation =
  | ZTop
  | Znamed     of pattern * meta_name * pbindings option * pat_continuation

  (* Zor (cont, e_list, ne) :
       - cont   : the continuation if the matching is correct
       - e_list : if not, the sorted list of next engines to try matching with
       - ne     : if no match at all, then take the nengine to go up *)
  | Zor        of pat_continuation * engine list * nengine

  (* Zand (before, after, cont) :
       - before : list of couples (form, pattern) that has already been checked
       - after  : list of couples (form, pattern) to check in the following
       - cont   : continuation if all the matches succeed *)
  | Zand       of (axiom * pattern) list
                  * (axiom * pattern) list
                  * pat_continuation

  | ZReduce    of pat_continuation * engine * nengine


and engine = {
    e_head         : axiom;
    e_pattern      : pattern;
    e_continuation : pat_continuation;
    e_env          : environment;
  }

and nengine = {
    ne_continuation : pat_continuation;
    ne_env          : environment;
  }

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

val mk_engine       : ?verbose:bool -> ?mtch:match_env -> form -> pattern ->
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

val restore_environment : environment -> unit
val copy_environment    : environment -> environment
