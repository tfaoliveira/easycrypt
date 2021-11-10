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
open EcCoreFol

module Sid = EcIdent.Sid
module Mid = EcIdent.Mid

(* -------------------------------------------------------------------- *)
include EcCoreModules

(* -------------------------------------------------------------------- *)
type module_type       = EcCoreFol.module_type
type mod_restr         = EcCoreFol.mod_restr
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

let mr_empty = {
  mr_xpaths = ur_empty EcPath.Sx.empty;
  mr_mpaths = ur_empty EcPath.Sm.empty;
  mr_params = Msym.empty;
  mr_cost   = f_cost_zero;
}

let mr_full = {
  mr_xpaths = ur_full EcPath.Sx.empty;
  mr_mpaths = ur_full EcPath.Sm.empty;
  mr_params = Msym.empty;
  mr_cost   = f_cost_zero;
}

let mr_add_restr
    (mr : mod_restr)
    (rx : Sx.t use_restr)
    (rm : Sm.t use_restr) : mod_restr
  =
  { mr with
    mr_xpaths = ur_union Sx.union Sx.inter mr.mr_xpaths rx;
    mr_mpaths = ur_union Sm.union Sm.inter mr.mr_mpaths rm; }

(* let change_oinfo restr f oi =
 *   { restr with mr_oinfos = Msym.add f oi restr.mr_oinfos }
 *
 * let add_oinfo restr f oi = change_oinfo restr f oi *)

(* let change_oicalls (restr : mod_restr) (f : string) (ocalls : xpath list) =
 *   let oi_params =
 *     try
 *       let oi_param = Msym.find f restr.mr_params in
 *       let filter x = List.mem x ocalls in
 *       filter_param oi_param
 *     with Not_found -> OI.mk ocalls true r_cost_default
 *   in
 *   { restr with mr_params = oi_params; } *)

(* -------------------------------------------------------------------- *)
let cost_has_restr (c : cost) : bool =
  not (is_inf c.c_self) ||
  Mx.exists (fun _ bnd -> not (is_inf bnd)) c.c_calls ||
  c.c_full

let f_cost_has_restr (c : form) =
  if is_modcost c then
    let c = destr_cost c in
    `Known (cost_has_restr c)
  else `Unknown

let modcost_has_restr (mc : mod_cost) : bool =
  Msym.exists (fun _ proc_c -> cost_has_restr proc_c) mc

let f_modcost_has_restr (mc : form) =
  if is_modcost mc then
    let mc = destr_modcost mc in
    `Known (modcost_has_restr mc)
  else `Unknown

let f_modcost_proc_has_restr (mc : form) proc =
  if is_modcost mc then
    let mc = destr_modcost mc in
    let p = Msym.find proc mc in
    `Known (cost_has_restr p)
  else `Unknown

(* -------------------------------------------------------------------- *)
let mty_hash  = EcCoreFol.mty_hash
let mty_equal = EcCoreFol.mty_equal

let mr_equal  = EcCoreFol.mr_equal
let mr_hash   = EcCoreFol.mr_hash
