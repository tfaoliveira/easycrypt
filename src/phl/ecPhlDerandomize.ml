(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcIdent
open EcTypes
open EcFol
open EcModules
open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
exception Failure

(* -------------------------------------------------------------------- *)
let derandomize env =
  let rec aux0 infos s =
    aux infos (List.rev s.s_node)

  and aux (me, (rd0, wr0)) s =
    match s with [] -> me, ([], []) | i :: s ->

    try
      match i.i_node with
      | Srnd (lv, e) -> begin
          if not (Mid.is_empty e.e_fv) then
            raise Failure;

          let pv, pvty = match lv with LvVar (pv, ty) -> pv, ty | _ -> raise Failure in

          if pv.pv_kind <> PVloc then raise Failure;

          let me, (rnds, body) = aux (me, (rd0, wr0)) s in

          let rd = EcPV.s_read_r  env rd0 (stmt s) in
          let wr = EcPV.s_write_r env wr0 (stmt s) in

          let me, pv' =
            if EcPV.PV.mem_pv env pv rd || EcPV.PV.mem_pv env pv wr then
              let vr = { v_name = EcPath.xbasename pv.pv_name; v_type = pvty; } in
              let me, vr = fresh_pv me vr in
              let vr = pv_loc (EcMemory.xpath me) vr in
              (me, vr)
            else (me, pv) in

          let asgn =
            if pv_equal pv pv' then None else
            Some (i_asgn (LvVar (pv, pvty), e_var pv' pvty)) in

          me, (((pv', pvty), e) :: rnds, List.ocons asgn body)
        end

      | Sif (e, s1, s2) ->
          let rd1 = EcPV.PV.union rd0 (EcPV.s_read  env s2) in
          let wr1 = EcPV.PV.union rd0 (EcPV.s_write env s2) in
          let rd2 = EcPV.PV.union rd0 (EcPV.s_read  env s1) in
          let wr2 = EcPV.PV.union rd0 (EcPV.s_write env s1) in

          let me, (rnds, body) = aux (me, (rd0, wr0)) s in

          let me, (rnds1, body1) = aux0 (me, (rd1, wr1)) s1 in
          let me, (rnds2, body2) = aux0 (me, (rd2, wr2)) s2 in

          let body1 = List.rev body1 in
          let body2 = List.rev body2 in

          me, ((rnds1 @ rnds2 @ rnds), i_if (e, stmt body1, stmt body2) :: body)

      | _ -> raise Failure

    with Failure ->
      let me, (rnds, body) = aux (me, (rd0, wr0)) s in
      me, (rnds, i :: body)

  in

  fun me s ->
    let me, (rnds, body) =
      aux0 (me, (EcPV.PV.empty, EcPV.PV.empty)) s in

    let rnds = List.map (fun ((pv, pvty), e) ->
      i_rnd (LvVar (pv, pvty), e)) (List.rev rnds) in

    (me, stmt (rnds @ List.rev body))

(* -------------------------------------------------------------------- *)
let t_derandomize tc =
  let concl = FApi.tc1_goal tc in
  let env   = FApi.tc1_env  tc in

  match concl.f_node with
  | FhoareS hs -> begin
      try
        let me, body = derandomize env hs.hs_m hs.hs_s in
        let concl = { hs with hs_m = me; hs_s = body; } in
        FApi.xmutate1 tc `Dernd [EcFol.f_hoareS_r concl]

      with Failure -> EcLowGoal.t_id tc
    end

  | _ ->
      EcLowGoal.t_id tc
