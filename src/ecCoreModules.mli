(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcSymbols
open EcPath
open EcTypes

(* -------------------------------------------------------------------- *)
type lvalue =
  | LvVar   of (prog_var * ty)
  | LvTuple of (prog_var * ty) list

val lv_equal     : lvalue -> lvalue -> bool
val symbol_of_lv : lvalue -> symbol
val ty_of_lv     : lvalue -> EcTypes.ty
val lv_of_list   : (prog_var * ty) list -> lvalue option

(* --------------------------------------------------------------------- *)
type instr = private {
  i_node : instr_node;
  i_fv   : int EcIdent.Mid.t;
  i_tag  : int;
}

and instr_node =
  | Sasgn     of lvalue * expr
  | Srnd      of lvalue * expr
  | Scall     of lvalue option * xpath * expr list
  | Sif       of expr * stmt * stmt
  | Swhile    of expr * stmt
  | Smatch    of expr * ((EcIdent.t * EcTypes.ty) list * stmt) list
  | Sassert   of expr
  | Sabstract of EcIdent.t

and stmt = private {
  s_node : instr list;
  s_fv   : int EcIdent.Mid.t;
  s_tag  : int;
}

(* -------------------------------------------------------------------- *)
val i_equal   : instr -> instr -> bool
val i_compare : instr -> instr -> int
val i_hash    : instr -> int
val i_fv      : instr -> int EcIdent.Mid.t
val i_node    : instr -> instr_node

val s_equal   : stmt -> stmt -> bool
val s_compare : stmt -> stmt -> int
val s_hash    : stmt -> int
val s_fv      : stmt -> int EcIdent.Mid.t
val s_subst   : e_subst -> stmt -> stmt

(* -------------------------------------------------------------------- *)
val i_asgn     : lvalue * expr -> instr
val i_rnd      : lvalue * expr -> instr
val i_call     : lvalue option * xpath * expr list -> instr
val i_if       : expr * stmt * stmt -> instr
val i_while    : expr * stmt -> instr
val i_match    : expr * ((EcIdent.t * ty) list * stmt) list -> instr
val i_assert   : expr -> instr
val i_abstract : EcIdent.t -> instr

val s_asgn     : lvalue * expr -> stmt
val s_rnd      : lvalue * expr -> stmt
val s_call     : lvalue option * xpath * expr list -> stmt
val s_if       : expr * stmt * stmt -> stmt
val s_while    : expr * stmt -> stmt
val s_match    : expr * ((EcIdent.t * ty) list * stmt) list -> stmt
val s_assert   : expr -> stmt
val s_abstract : EcIdent.t -> stmt
val s_seq      : stmt -> stmt -> stmt
val s_empty    : stmt

val stmt  : instr list -> stmt
val rstmt : instr list -> stmt

(* the following functions raise Not_found if the argument does not match *)
val destr_asgn   : instr -> lvalue * expr
val destr_rnd    : instr -> lvalue * expr
val destr_call   : instr -> lvalue option * xpath * expr list
val destr_if     : instr -> expr * stmt * stmt
val destr_while  : instr -> expr * stmt
val destr_match  : instr -> expr * ((EcIdent.t * ty) list * stmt) list
val destr_assert : instr -> expr

val is_asgn   : instr -> bool
val is_rnd    : instr -> bool
val is_call   : instr -> bool
val is_if     : instr -> bool
val is_while  : instr -> bool
val is_match  : instr -> bool
val is_assert : instr -> bool

(* -------------------------------------------------------------------- *)
val get_uninit_read : stmt -> Sx.t

(* -------------------------------------------------------------------- *)
type funsig = {
  fs_name   : symbol;
  fs_arg    : EcTypes.ty;
  fs_anames : variable list option;
  fs_ret    : EcTypes.ty;
}

val fs_equal : funsig -> funsig -> bool

(* -------------------------------------------------------------------- *)
type 'a use_restr = {
  ur_pos : 'a option;   (* If not None, can use only element in this set. *)
  ur_neg : 'a;          (* Cannot use element in this set. *)
}

val ur_empty : 'a -> 'a use_restr
val ur_full  : 'a -> 'a use_restr
val ur_app   : ('a -> 'b) -> 'a use_restr -> 'b use_restr
val ur_equal : ('a -> 'a -> bool) -> 'a use_restr -> 'a use_restr -> bool

(* Correctly handles the [None] cases for subset comparison. *)
val ur_pos_subset : ('a -> 'a -> bool) -> 'a option -> 'a option -> bool
val ur_union :
  ('a -> 'a -> 'a) ->
  ('a -> 'a -> 'a) ->
  'a use_restr -> 'a use_restr -> 'a use_restr

(* -------------------------------------------------------------------- *)
(* - [oi_allowed] : list of functor parameters that can be called by [M.f].
   - [oi_in]      : true if equality of globals is required to ensure
     equality of result and globals (in the post). *)
type oi_param = {
  oi_allowed : xpath list;
  oi_in      : bool;
}

(* map from a functor `M` procedures to the procedure information *)
type oi_params = oi_param Msym.t

val params_fv : oi_params -> int EcIdent.Mid.t -> int EcIdent.Mid.t

val is_in : oi_param -> bool

val allowed   : oi_param -> xpath list
val allowed_s : oi_param -> Sx.t

val params_equal : oi_params -> oi_params -> bool

val filter_param : (xpath -> bool) -> oi_param -> oi_param

(* -------------------------------------------------------------------- *)
(* ['a] will be instantiated by [EcCoreFol.form] *)

type mr_xpaths = EcPath.Sx.t use_restr

type mr_mpaths = EcPath.Sm.t use_restr

type 'a p_mod_restr = {
  mr_xpaths : mr_xpaths;
  mr_mpaths : mr_mpaths;
  mr_params : oi_params;
  mr_cost   : 'a ;              (* of type [Tmodcost _] *)
}

val p_mr_equal :
  ('a -> 'a -> bool) ->
  'a p_mod_restr ->
  'a p_mod_restr ->
  bool

val p_mr_hash : ('a -> int) -> 'a p_mod_restr -> int

val mr_xpaths_fv : mr_xpaths -> int EcIdent.Mid.t
val mr_mpaths_fv : mr_mpaths -> int EcIdent.Mid.t

(* -------------------------------------------------------------------- *)
(* Private type to ensure that [mt_restr] is well-formed w.r.t. [mt_params]. *)
type 'a p_module_type = private {          (* Always in eta-normal form *)
  mt_params : (EcIdent.t * 'a p_module_type) list;
  mt_name   : EcPath.path;
  mt_args   : EcPath.mpath list;
  mt_restr  : 'a p_mod_restr;
}

(* only to be used in [EcCoreFol]. Use [EcModules.mk_mt_r] everywhere else. *)
val _prelude_mk_mt_r :
  check     : ('a -> bool) ->
  mt_params : ((EcIdent.t * 'a p_module_type) list) ->
  mt_name   : EcPath.path ->
  mt_args   : EcPath.mpath list ->
  mt_restr  : 'a p_mod_restr ->
  'a p_module_type

(* -------------------------------------------------------------------- *)
type module_sig_body_item = Tys_function of funsig

type module_sig_body = module_sig_body_item list

(* Private type to ensure that [mt_restr] is well-formed w.r.t. [mt_params]. *)
type 'a p_module_sig = private {
  mis_params : (EcIdent.t * 'a p_module_type) list;
  mis_body   : module_sig_body;
  mis_restr  : 'a p_mod_restr;
}

(* only to be used in [EcCoreFol]. Use [EcModules.mk_msig_r] everywhere else. *)
val _prelude_mk_msig_r :
  check      : ('a -> bool) ->
  mis_params : (EcIdent.t * 'a p_module_type) list ->
  mis_body   : module_sig_body ->
  mis_restr  : 'a p_mod_restr ->
  'a p_module_sig

(* -------------------------------------------------------------------- *)
type 'a p_top_module_sig = {
  tms_sig  : 'a p_module_sig;
  tms_loca : is_local;
}

(* -------------------------------------------------------------------- *)
(* Simple module signature, without restrictions. *)
type 'a p_module_smpl_sig = {
  miss_params : (EcIdent.t * 'a p_module_type) list;
  miss_body   : module_sig_body;
}

val sig_smpl_sig_coincide : 'a p_module_sig -> 'b p_module_smpl_sig -> bool

(* -------------------------------------------------------------------- *)
type uses = {
  us_calls  : xpath list;
  us_reads  : Sx.t;
  us_writes : Sx.t;
}

val mk_uses : xpath list -> Sx.t -> Sx.t -> uses

type function_def = {
  f_locals : variable list;
  f_body   : stmt;
  f_ret    : EcTypes.expr option;
  f_uses   : uses;
}

val fd_equal : function_def -> function_def -> bool
val fd_hash  : function_def -> int

(* -------------------------------------------------------------------- *)
type 'a p_function_body =
| FBdef   of function_def
| FBalias of xpath
| FBabs   of oi_param * ('a * symbol)
 (* In [FBabs (oi, (mc, fsymb))], the element [(mc, fsymb)]
    represents the projection of [mc] over [fsymb].
    - [mc] is a formula of type `Tmod_cost` *)

type 'a p_function_ = {
  f_name   : symbol;
  f_sig    : funsig;
  f_def    : 'a p_function_body;
}

(* -------------------------------------------------------------------- *)
type abs_uses = {
  aus_calls  : EcPath.xpath list;
  aus_reads  : (EcTypes.prog_var * EcTypes.ty) list;
  aus_writes : (EcTypes.prog_var * EcTypes.ty) list;
}

type 'a p_module_expr = {
  me_name     : symbol;
  me_body     : 'a p_module_body;
  me_comps    : 'a p_module_comps;
  me_sig_body : module_sig_body;
  me_params   : (EcIdent.t * 'a p_module_type) list;
}

(* Invariant:
   In an abstract module [ME_Decl mt], [mt] must not be a functor, i.e. it must
   be fully applied. Therefore, we must have:
   [List.length mp.mt_params = List.length mp.mt_args]  *)
and 'a p_module_body =
  | ME_Alias       of int * EcPath.mpath
  | ME_Structure   of 'a p_module_structure    (* Concrete modules. *)
  | ME_Decl        of 'a p_module_type         (* Abstract modules. *)

and 'a p_module_structure = {
  ms_body      : 'a p_module_item list;
}

and 'a p_module_item =
  | MI_Module   of 'a p_module_expr
  | MI_Variable of variable
  | MI_Function of 'a p_function_

and 'a p_module_comps = 'a p_module_comps_item list

and 'a p_module_comps_item = 'a p_module_item

type 'a p_top_module_expr = {
  tme_expr : 'a p_module_expr;
  tme_loca : locality;
}

(* -------------------------------------------------------------------- *)
val p_mty_equal :
  ('a -> 'a -> bool) ->
  'a p_module_type ->
  'a p_module_type ->
  bool

val p_mty_hash : ('a -> int) -> 'a p_module_type -> int

(* -------------------------------------------------------------------- *)
val get_uninit_read : stmt -> Ssym.t
val get_uninit_read_of_fun : _ p_function_ -> Ssym.t
val get_uninit_read_of_module : path -> _ p_module_expr -> (xpath * Ssym.t) list
