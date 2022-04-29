(* -------------------------------------------------------------------- *)
open EcSymbols
open EcPath
open EcCoreFol
open EcUtils

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
type top_module_sig    = form p_top_module_sig
type top_module_expr   = form p_top_module_expr

(* -------------------------------------------------------------------- *)
(* Smart constructor for module types *)
let mk_mt_r = EcCoreFol.mk_mt_r

(* Update existing module type *)
let update_mt ?mt_params ?mt_name ?mt_args ?mt_restr mt : module_type =
  let mt_params = odfl mt.mt_params mt_params
  and mt_name   = odfl mt.mt_name   mt_name
  and mt_args   = odfl mt.mt_args   mt_args
  and mt_restr  = odfl mt.mt_restr  mt_restr in
  mk_mt_r ~mt_params ~mt_name ~mt_args ~mt_restr

(* -------------------------------------------------------------------- *)
(* Smart constructor for module sigs *)
let mk_msig_r = EcCoreFol.mk_msig_r

(* Update existing module sig *)
let update_msig ?mis_params ?mis_body ?mis_restr mis : module_sig =
  let mis_params = odfl mis.mis_params mis_params
  and mis_body   = odfl mis.mis_body   mis_body
  and mis_restr  = odfl mis.mis_restr  mis_restr in
  mk_msig_r ~mis_params ~mis_body ~mis_restr

(* -------------------------------------------------------------------- *)
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

(* -------------------------------------------------------------------- *)
let cost_has_restr (c : cost) : bool =
  not (is_inf c.c_self) ||
  Mx.exists (fun _ bnd -> not (is_inf bnd)) c.c_calls ||
  c.c_full

let f_cost_has_restr (c : form) =
  if is_cost c then
    let c = destr_cost c in
    `Known (cost_has_restr c)
  else `Unknown

(* -------------------------------------------------------------------- *)
let proc_cost_has_restr (c : cost) : bool =
  not (f_equal f_cost_inf c.c_self || f_equal f_cost_inf0 c.c_self) ||
  Mx.exists (fun _ bnd -> not (is_inf bnd)) c.c_calls ||
  c.c_full

let modcost_has_restr (mc : mod_cost) : bool =
  Msym.exists (fun _ proc_c -> proc_cost_has_restr proc_c) mc

let f_modcost_has_restr (mc : form) =
  if is_modcost mc then
    let mc = destr_modcost mc in
    `Known (modcost_has_restr mc)
  else `Unknown

let f_modcost_proc_has_restr (mc : form) proc =
  if is_modcost mc then
    let mc = destr_modcost mc in
    let p = Msym.find proc mc in
    `Known (proc_cost_has_restr p)
  else `Unknown

(* -------------------------------------------------------------------- *)
let mty_hash  = EcCoreFol.mty_hash
let mty_equal = EcCoreFol.mty_equal

let mr_equal  = EcCoreFol.mr_equal
let mr_hash   = EcCoreFol.mr_hash
