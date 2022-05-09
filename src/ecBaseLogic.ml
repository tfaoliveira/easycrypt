(* -------------------------------------------------------------------- *)
open EcTypes
open EcCoreFol

(* -------------------------------------------------------------------- *)
type local_kind =
| LD_var    of ty * form option
| LD_mem    of EcMemory.memtype
| LD_modty  of EcModules.module_type
| LD_hyp    of form
| LD_abs_st of EcModules.abs_uses

type l_local = {
  l_id   : EcIdent.t;
  l_kind : local_kind;
}

type l_locals = l_local list

let l_id x = x.l_id

type hyps = {
  h_tvar  : EcDecl.ty_params;
  h_local : l_local list;
}
