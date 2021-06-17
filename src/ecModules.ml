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
(* Instantiation of EcCoreModules.PreOI on EcCoreFol.form. *)
module OI : sig
  type t = c_bnd PreOI.t

  val hash  : t -> int
  val equal : t -> t -> bool

  val is_in : t -> bool

  val cost_self : t ->          c_bnd
  val cost      : t -> xpath -> c_bnd

  val cost_calls : t -> c_bnd Mx.t

  val costs : t -> c_bnd * c_bnd Mx.t

  val allowed   : t -> xpath list
  val allowed_s : t -> Sx.t

  val mk :
    xpath list -> bool -> c_bnd -> c_bnd Mx.t -> t

  val filter : (xpath -> bool) -> t -> t
end = struct
  type t = c_bnd PreOI.t

  let is_in        = PreOI.is_in
  let allowed      = PreOI.allowed
  let allowed_s    = PreOI.allowed_s
  let cost_self    = PreOI.cost_self
  let cost         = PreOI.cost
  let cost_calls   = PreOI.cost_calls
  let costs        = PreOI.costs
  let mk           = PreOI.mk
  let filter       = PreOI.filter
  let equal        = PreOI.equal EcCoreFol.c_bnd_equal
  let hash         = PreOI.hash EcCoreFol.c_bnd_hash
end

type orcl_info = EcCoreFol.orcl_info

(* -------------------------------------------------------------------- *)
type module_type       = EcCoreFol.module_type
type mod_restr         = EcCoreFol.mod_restr
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

let mr_empty = {
  mr_xpaths = ur_empty EcPath.Sx.empty;
  mr_mpaths = ur_empty EcPath.Sm.empty;
  mr_oinfos = Msym.empty;
}

let mr_full = {
  mr_xpaths = ur_full EcPath.Sx.empty;
  mr_mpaths = ur_full EcPath.Sm.empty;
  mr_oinfos = Msym.empty;
}

let mr_add_restr mr (rx : Sx.t use_restr) (rm : Sm.t use_restr) =
  { mr_xpaths = ur_union Sx.union Sx.inter mr.mr_xpaths rx;
    mr_mpaths = ur_union Sm.union Sm.inter mr.mr_mpaths rm;
    mr_oinfos = mr.mr_oinfos; }

let change_oinfo restr f oi =
  { restr with mr_oinfos = Msym.add f oi restr.mr_oinfos }

let add_oinfo restr f oi = change_oinfo restr f oi

let oicalls_filter restr f filter =
  match Msym.find f restr.mr_oinfos with
  | oi -> change_oinfo restr f (OI.filter filter oi)
  | exception Not_found -> restr

let change_oicalls (restr : mod_restr) (f : string) (ocalls : xpath list) =
  let oi =
    try
      let oi = Msym.find f restr.mr_oinfos in
      let filter x = List.mem x ocalls in
      OI.filter filter oi
    with Not_found -> OI.mk ocalls true C_unbounded Mx.empty
  in
  add_oinfo restr f oi

let has_compl_restriction mr =
  Msym.exists (fun _ oi ->
      let self, calls = PreOI.costs oi in
      self <> C_unbounded || Mx.exists (fun _ bnd -> bnd <> C_unbounded) calls
    ) mr.mr_oinfos

(* -------------------------------------------------------------------- *)
let mty_hash  = EcCoreFol.mty_hash
let mty_equal = EcCoreFol.mty_equal

let mr_equal  = EcCoreFol.mr_equal
let mr_hash   = EcCoreFol.mr_hash
