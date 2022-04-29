(* -------------------------------------------------------------------- *)
(* Function for cost                                                    *)
open EcUtils
open EcTypes
open EcFol
open EcEnv
open EcPath
open EcSymbols

(* -------------------------------------------------------------------- *)
let cost_orcl (proc : symbol) (o : xpath) (mc : form) : form =
  let mo, mf = mget_ident o.x_top, o.x_sub in
  f_cost_proj_r mc (Param {proc; param_m = EcIdent.name mo; param_p = mf})

(* -------------------------------------------------------------------- *)
type csub_res = { cond : form; res : form; }

(* Backward reasoning on cost.
   [cost_sub c1 c2] looks for a solution [x] of [c1 = x + c2]. *)
let cost_sub ~(c : form) ~(sub : form) : csub_res =
  { cond = f_cost_subcond c sub; res = f_cost_add c (f_cost_opp sub); }

(* [f1], [f2] of type [txint].
   Condition under which [(f1 - f2) + f2 = f1] *)
let f_xsubcond (f1 : form) (f2 : form) : form =
  f_or (f_is_inf f1) (f_is_int f2)

(* Same as [cost_sub], but only for the concrete cost.
   [c] of type [tcost], [sub] of type [xint]. *)
let cost_sub_self ~(c : form) ~(sub : form) : csub_res =
  let cond = f_xsubcond (f_cost_proj_r c Conc) sub in
  let sub_c = f_cost_r (cost_r sub Mx.empty true) in
  { cond; res = f_cost_add c (f_cost_opp sub_c); }

(* -------------------------------------------------------------------- *)
(* [c] of type [tcost], [a] of type [xint] *)
let cost_add_self ~(c : form) ~(a : form) : form =
  let a_c = f_cost_r (cost_r a Mx.empty true) in
  f_cost_add c a_c

(* -------------------------------------------------------------------- *)
let loaded (env : env) : bool =
  is_some (EcEnv.Theory.by_path_opt EcCoreLib.CI_Xint.p_Xint env) &&
  is_some (EcEnv.Theory.by_path_opt EcCoreLib.CI_Xint.p_choaretac env)

exception LoadChoareFirst

let check_loaded (env : env) : unit =
  if not (loaded env) then raise LoadChoareFirst

let pp_exn fmt exn =
  match exn with
  | LoadChoareFirst -> Format.fprintf fmt "load the `CHoareTactic' theory first"
  | _ -> raise exn

let _ = EcPException.register pp_exn

(* -------------------------------------------------------------------- *)
(* [choare_xsum cost (m,n)]:
   [cost] of type [tint -> tcost], [m] of type [tint], [n] of type [txint].

   [n] must be finite, i.e. [n = f_N n_fin].  *)
let choare_xsum (cost : form) (m, n) : form =
  f_bigicost cost m (f_xoget n)


(* -------------------------------------------------------------------- *)
let free_expr (e : EcTypes.expr) : bool =
  match e.e_node with
  | Elocal _ | Evar _ | Eint _ -> true

  | Eop    _ | Eproj  _
  | Etuple _ | Eapp   _
  | Equant _ | Elet   _
  | Eif    _ | Ematch _ -> false

let cost_of_expr pre menv e =
  if free_expr e then f_x0 else f_coe pre menv e

let cost_of_expr_any menv e =
  if free_expr e then f_x0 else f_coe f_true menv e
