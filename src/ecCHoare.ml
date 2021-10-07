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
open EcModules
open EcPath

(* -------------------------------------------------------------------- *)
let oget_c_bnd = EcCoreFol.oget_c_bnd

(* [xint] from a [c_bnd] of type [mode] *)
let xi_of_c_bnd ~(mode:[`Xint | `Int]) (c : c_bnd) : form =
  match c with
  | C_unbounded -> f_Inf
  | C_bounded f -> match mode with
    | `Xint -> f
    | `Int  -> f_N f

(* -------------------------------------------------------------------- *)
(* cost of an oracle call (param or abstract) *)
let cost_orcl (o : xpath) (oi : OI.t) : c_bnd =
  let oi_cost = OI.cost oi in
  let c : c_bnd option =
    try Some (EcPath.Mx.find o oi_cost.r_params) with
    | Not_found ->
      EcPath.Mx.find_opt o oi_cost.r_abs_calls
  in
  oget_c_bnd c oi_cost.r_full

(* -------------------------------------------------------------------- *)
(* Function for cost                                                    *)

let f_subcond (f1 : form) (f2 : form) : form =
  f_or (f_is_inf f1) (f_is_int f2)

let f_xsub (f1 : form) (f2 : form) : form * form =
  f_subcond f1 f2, f_xadd f1 (f_xopp f2)

(* [a] of type [xint] *)
let cost_sub_self (c : cost) (a : form) : form * cost =
  let cond, c_self = match c.c_self with
    | C_unbounded -> f_true, C_unbounded
    | C_bounded x ->
      let cond, x = f_xsub x a in
      cond, C_bounded x
  in
  cond, cost_r c_self c.c_calls c.c_full

(* [a] of type [xint] *)
let cost_add_self (c : cost) (a : form) : cost =
  let c_self = c_bnd_map (fun x -> f_xadd x a) c.c_self in
  cost_r c_self c.c_calls c.c_full

(* -------------------------------------------------------------------- *)
(* Result of a backward reasoning on cost: given [c1] and [c2], we try to solve
   the equation [c1 = x + c2] over [x]. *)
type cost_backward_res = [
  | `Ok of form * cost          (* [`Ok (c,x)] means that [x] is a solution
                                   whenever [c] holds. *)
  | `XError of EcPath.xpath     (* error with oracle call [x] *)
  | `FullError                  (* full minus not full *)
]

(* Backward reasoning on cost.
   [cost_sub c1 c2] looks for a solution [x] of [c1 = x + c2]. *)
let cost_sub (c1 : cost) (c2 : cost) : cost_backward_res =
  let exception Failed of [`XError of EcPath.xpath | `FullError ] in
  try
    let cond, c_self = match c1.c_self, c2.c_self with
      | C_bounded s1, C_bounded s2 ->
        let cond, c = f_xsub s1 s2 in
        cond, C_bounded c
      | _ -> f_true, C_unbounded
    in
    let c_calls =
      EcPath.Mx.merge (fun x call1 call2 ->
          let call1 = oget_c_bnd call1 c1.c_full
          and call2 = oget_c_bnd call2 c2.c_full in
          match call1, call2 with
          | C_bounded call1, C_bounded call2 ->
            let bnd = C_bounded (f_int_sub_simpl call1 call2) in
            Some bnd
          | C_unbounded, _ -> Some C_unbounded
          | C_bounded _, C_unbounded -> raise (Failed (`XError x))
        ) c1.c_calls c2.c_calls
    in
    let c_full = c1.c_full && c2.c_full in

    if c1.c_full && not c2.c_full then
      raise (Failed `FullError);

    `Ok (cond, cost_r c_self c_calls c_full)
  with Failed x -> (x :> cost_backward_res)


(* -------------------------------------------------------------------- *)
(* let cost_map f_xmap f_map c =
 *   EcPath.Mx.fold (fun f cb res ->
 *       let c_calls =
 *         EcPath.Mx.add f
 *           (call_bound_r (cb.cb_cost) (f_map cb.cb_called))
 *           res.c_calls in
 *       cost_r res.c_self c_calls
 *     ) c.c_calls
 *     (cost_r (f_xmap c.c_self) EcPath.Mx.empty) *)

let cost_app (c : cost) (args : form list) : cost =
  cost_map
    (fun ty c ->
       let ty = match ty with
         | `Xint -> txint
         | `Int -> tint in
       f_app_simpl c args ty
    ) c

(* -------------------------------------------------------------------- *)
let loaded (env : env) : bool =
  is_some (EcEnv.Theory.by_path_opt EcCoreLib.CI_xint.p_Xint env) &&
  is_some (EcEnv.Theory.by_path_opt EcCoreLib.CI_xint.p_choaretac env)

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
  f_op EcCoreLib.CI_xint.p_big [tint]
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
  cost_map (fun ty f ->
      match ty with
      | `Xint -> f_xbig f m n
      | `Int  -> f_big f m n
    ) cost

(* -------------------------------------------------------------------- *)
let rec free_expr (e : EcTypes.expr) : bool =
  match e.e_node with
  | Elocal _ | Evar _ | Eint _ -> true

  | Eop _
  | Eproj _ | Etuple _ | Eapp _
  | Equant _ | Elet _ | Eif _ | Ematch _ -> false

let cost_of_expr pre menv e =
  if free_expr e then f_x0 else f_coe pre menv e

let cost_of_expr_any menv e =
  if free_expr e then f_x0 else f_coe f_true menv e
