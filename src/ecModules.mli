(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcPath
open EcCoreFol

(* -------------------------------------------------------------------- *)
include module type of struct include EcCoreModules end

(* -------------------------------------------------------------------- *)
(* Instantiation of EcCoreModules.PreOI on EcCoreFol.c_bnd *)
module OI : sig
  type t = c_bnd PreOI.t

  val hash  : t -> int
  val equal : t -> t -> bool

  val is_in : t -> bool

  val c_self      : t -> c_bnd
  val c_params    : t -> c_bnd Mx.t
  val c_abs_calls : t -> c_bnd Mx.t
  val c_full      : t -> bool
  val cost        : t -> c_bnd r_cost

  val allowed   : t -> xpath list
  val allowed_s : t -> Sx.t

  val mk : xpath list -> bool -> c_bnd r_cost -> t

  val filter : (xpath -> bool) -> t -> t
end

type orcl_info = EcCoreFol.orcl_info

val r_cost_default : c_bnd r_cost

(* -------------------------------------------------------------------- *)
type mod_restr         = EcCoreFol.mod_restr
type module_type       = c_bnd p_module_type
type module_sig        = c_bnd p_module_sig
type module_smpl_sig   = c_bnd p_module_smpl_sig
type function_body     = c_bnd p_function_body
type function_         = c_bnd p_function_
type module_expr       = c_bnd p_module_expr
type module_body       = c_bnd p_module_body
type module_structure  = c_bnd p_module_structure
type module_item       = c_bnd p_module_item
type module_comps      = c_bnd p_module_comps
type module_comps_item = c_bnd p_module_comps_item

(* Careful, the available oracles are empty in both [mr_empty] and [mr_full]. *)
val mr_empty : mod_restr
val mr_full  : mod_restr

val mr_hash  : mod_restr -> int
val mr_equal : mod_restr -> mod_restr -> bool

val mr_add_restr :
  mod_restr -> EcPath.Sx.t use_restr -> EcPath.Sm.t use_restr -> mod_restr

val add_oinfo : mod_restr -> string -> OI.t -> mod_restr
val change_oicalls : mod_restr -> string -> xpath list -> mod_restr
val oicalls_filter :
  mod_restr ->
  EcSymbols.Msym.key ->
  (EcPath.xpath -> bool) ->
  mod_restr

val has_compl_restriction : mod_restr -> bool

(* -------------------------------------------------------------------- *)
val mty_equal : module_type -> module_type -> bool
val mty_hash  : module_type -> int
