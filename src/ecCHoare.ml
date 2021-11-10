(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

open EcUtils
open EcTypes
open EcFol
open EcEnv
open EcPath
open EcSymbols

(* TODO A: cleanup file *)

(* -------------------------------------------------------------------- *)
let oget_c_bnd = EcCoreFol.oget_c_bnd

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

let f_xsub (f1 : form) (f2 : form) : form * form =
  f_xsubcond f1 f2, f_xadd f1 (f_xopp f2)

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
(* Result of a backward reasoning on cost: given [c1] and [c2], we try to solve
   the equation [c1 = x + c2] over [x]. *)
type cost_backward_res = [
  | `Ok of form * cost          (* [`Ok (c,x)] means that [x] is a solution
                                   whenever [c] holds. *)
  | `FullError                  (* full minus not full *)
]

(* Backward reasoning on cost.
   [cost_sub c1 c2] looks for a solution [x] of [c1 = x + c2]. *)
let cost_vec_sub (c1 : cost) (c2 : cost) : cost_backward_res =
  let exception Failed of [`FullError ] in
  try
    let cond, c_self = f_xsub c1.c_self c2.c_self in

    let call_cond = ref f_true in
    let c_calls =
      EcPath.Mx.merge (fun _ call1 call2 ->
          let call1 = oget_c_bnd call1 c1.c_full
          and call2 = oget_c_bnd call2 c2.c_full in

          let xcond, bnd = f_xsub call1 call2 in
          call_cond := f_and_simpl !call_cond xcond;
          Some bnd
        ) c1.c_calls c2.c_calls
    in
    let c_full = c1.c_full && c2.c_full in

    if c1.c_full && not c2.c_full then
      raise (Failed `FullError);

    (* final condition *)
    let fcond = f_and_simpl cond !call_cond in

    `Ok (fcond, cost_r c_self c_calls c_full)
  with Failed x -> (x :> cost_backward_res)


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
let q_List    = [EcCoreLib.i_top; "List"]

let tlist =
  let tlist = EcPath.fromqsymbol (q_List, "list") in
  fun ty -> EcTypes.tconstr tlist [ty]

let range =
  let rg = EcPath.fromqsymbol (q_List @ ["Range"], "range") in
  let rg = f_op rg [] (toarrow [tint; tint] (tlist tint)) in
  fun m n -> f_app rg [m; n] (tlist tint)

let f_predT = f_op EcCoreLib.CI_Pred.p_predT [tint] (tpred tint)

let f_op_xbig =
  f_op EcCoreLib.CI_Xint.p_big [tint]
    (toarrow [tpred tint; tfun tint txint; tlist tint] txint)

let f_op_big =
  let p_big =
    EcPath.fromqsymbol ([EcCoreLib.i_top;"StdBigop"; "Bigint"; "BIA"], "big")
  in

  f_op p_big [tint]
    (toarrow [tpred tint; tfun tint tint; tlist tint] tint)

let f_xbig f m n =
  f_app f_op_xbig [f_predT; f; range m n] txint

let f_big f m n =
  f_app f_op_big [f_predT; f; range m n] tint

let choare_sum (cost : cost) (m, n) : cost =
  cost_map (fun f -> f_xbig f m n) cost

(* [choare_xsum cost (m,n)]:
   [cost] of type [tcost], [m] of type [tint], [n] of type [txint].

   [n] must be finite, i.e. [n = f_N n_fin]. Then this is a sum of integers:
      [choare_xsum cost (m,n) = choare_sum cost (m,n_fin)]. *)
let choare_xsum (cost : form) (m, n) : form =
  assert false (* TODO A: *)


(* -------------------------------------------------------------------- *)
let rec free_expr (e : EcTypes.expr) : bool =
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
