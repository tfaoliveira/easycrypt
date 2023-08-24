(* -------------------------------------------------------------------- *)
open EcUtils
open EcTypes
open EcCoreFol

(* -------------------------------------------------------------------- *)
module Epoch = struct
  type t = int

  let init : t = 0

  let lt = (<)
  let leq = (<=)

  let next (e : t) : t = e + 1
  let max (e : t) (e' : t) = max e e'
  let min (e : t) (e' : t) = min e e'
end

(* -------------------------------------------------------------------- *)
type local_kind =
| LD_var    of ty * form option
| LD_mem    of EcMemory.memtype
| LD_modty  of mod_info * EcModules.module_type
| LD_hyp    of form
| LD_abs_st of EcModules.abs_uses

(* -------------------------------------------------------------------- *)
type l_local = {
  l_id    : EcIdent.t;
  l_epoch : Epoch.t;
  l_kind  : local_kind;
}

type l_locals = l_local list

let l_id x = x.l_id

let l_epoch x = x.l_epoch

(* -------------------------------------------------------------------- *)
type hyps = {
  h_tvar   : EcDecl.ty_params;
  h_local  : l_local list;
  h_agents : EcIdent.t list;
}

let hyps_epoch (hyps : hyps) : Epoch.t =
  List.fold_left (fun e l -> Epoch.max e l.l_epoch) Epoch.init hyps.h_local

let by_id_opt (id : EcIdent.t) (hyps : hyps) : l_local option =
  List.ofind (EcIdent.id_equal id |- l_id) hyps.h_local
