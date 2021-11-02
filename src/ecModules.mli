(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcCoreFol

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

(* Careful, the available oracles are empty in both [mr_empty] and [mr_full]. *)
val mr_empty : mod_restr
val mr_full  : mod_restr

val mr_hash  : mod_restr -> int
val mr_equal : mod_restr -> mod_restr -> bool

val mr_add_restr :
  mod_restr -> EcPath.Sx.t use_restr -> EcPath.Sm.t use_restr -> mod_restr

(* val add_oinfo : mod_restr -> string -> oi_params -> cost -> mod_restr *)
(* val change_oicalls : mod_restr -> string -> xpath list -> mod_restr *)

(* val has_compl_restriction : mod_restr -> bool *)

(* -------------------------------------------------------------------- *)
val mty_equal : module_type -> module_type -> bool
val mty_hash  : module_type -> int
