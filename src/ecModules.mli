(* -------------------------------------------------------------------- *)
open EcCoreFol
open EcSymbols

(* -------------------------------------------------------------------- *)
include module type of struct include EcCoreModules end

(* -------------------------------------------------------------------- *)
type mod_restr         = EcCoreFol.mod_restr
type module_type       = form p_module_type
type module_sig        = form p_module_sig
type module_smpl_sig   = form p_module_smpl_sig
type function_body     = form p_function_body
type function_         = form p_function_
type module_expr       = form p_module_expr
type module_body       = form p_module_body
type module_structure  = form p_module_structure
type module_item       = form p_module_item
type module_comps      = form p_module_comps
type module_comps_item = form p_module_comps_item
type top_module_sig    = form p_top_module_sig
type top_module_expr   = form p_top_module_expr

(* -------------------------------------------------------------------- *)
(* Smart constructor for module types *)
val mk_mt_r :
  mt_params : ((EcIdent.t * module_type) list) ->
  mt_name   : EcPath.path ->
  mt_args   : EcPath.mpath list ->
  mt_restr  : mod_restr ->
  module_type

(* Update existing module type *)
val update_mt :
  ?mt_params : (EcIdent.t * EcCoreFol.module_type) list ->
  ?mt_name   : EcPath.path ->
  ?mt_args   : EcPath.mpath list ->
  ?mt_restr  : EcCoreFol.form p_mod_restr ->
  module_type ->
  module_type

(* -------------------------------------------------------------------- *)
(* Smart constructor for module types *)
val mk_msig_r :
  mis_params : (EcIdent.t * module_type) list ->
  mis_body   : module_sig_body ->
  mis_restr  : mod_restr ->
  module_sig

(* Update existing module type *)
val update_msig :
  ?mis_params : (EcIdent.t * module_type) list ->
  ?mis_body   : module_sig_body ->
  ?mis_restr  : mod_restr ->
  module_sig ->
  module_sig

(* -------------------------------------------------------------------- *)
(* Careful, the available oracles are empty in both [mr_empty] and [mr_full]. *)
val mr_empty : mod_restr
val mr_full  : mod_restr

val mr_hash  : mod_restr -> int
val mr_equal : mod_restr -> mod_restr -> bool

val mr_add_restr :
  mod_restr -> EcPath.Sx.t use_restr -> EcPath.Sm.t use_restr -> mod_restr

(* -------------------------------------------------------------------- *)
val cost_has_restr      : cost      -> bool
val proc_cost_has_restr : proc_cost -> bool
val modcost_has_restr   : mod_cost  -> bool

val f_cost_has_restr         : form ->           [`Known of bool | `Unknown]
val f_modcost_has_restr      : form ->           [`Known of bool | `Unknown]
val f_modcost_proc_has_restr : form -> symbol -> [`Known of bool | `Unknown]

(* -------------------------------------------------------------------- *)
val mty_equal : module_type -> module_type -> bool
val mty_hash  : module_type -> int
