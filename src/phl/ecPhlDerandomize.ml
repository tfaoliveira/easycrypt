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
let derandomize hyps =
  let env = EcEnv.LDecl.toenv hyps in

  let rec aux0 ?(top = false) infos s =
    aux top infos (List.rev s.s_node)

  and aux top (me, (rd0, wr0)) s =
    match s with [] -> me, ([], [], []) | i :: s ->

    try
      match i.i_node with
      | Srnd (lv, e) -> begin
          if not (Mid.is_empty e.e_fv) then
            raise Failure;

          let pv, pvty = match lv with LvVar (pv, ty) -> pv, ty | _ -> raise Failure in

          if pv.pv_kind <> PVloc then raise Failure;

          let me, (rnds, ll, body) = aux top (me, (rd0, wr0)) s in

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

          let ll = if top then ll else e :: ll in

          me, (((pv', pvty), e) :: rnds, ll, List.ocons asgn body)
        end

      | Sif (e, s1, s2) ->
          let rd1 = EcPV.PV.union rd0 (EcPV.s_read  env s2) in
          let wr1 = EcPV.PV.union rd0 (EcPV.s_write env s2) in
          let rd2 = EcPV.PV.union rd0 (EcPV.s_read  env s1) in
          let wr2 = EcPV.PV.union rd0 (EcPV.s_write env s1) in

          let me, (rnds, ll, body) = aux top (me, (rd0, wr0)) s in

          let me, (rnds1, ll1, body1) = aux0 (me, (rd1, wr1)) s1 in
          let me, (rnds2, ll2, body2) = aux0 (me, (rd2, wr2)) s2 in

          let body1 = List.rev body1 in
          let body2 = List.rev body2 in

          me, ((rnds2 @ rnds1 @ rnds), (ll2 @ ll1 @ ll),
               i_if (e, stmt body1, stmt body2) :: body)

      | Swhile (e, wbody) -> begin
          let vari =
            match omap i_node (List.ohead s) with
            | Some (Sasgn (LvVar (x, _), { e_node = Eint z }))
                when EcBigInt.equal z EcBigInt.zero -> x
            | _ -> raise Failure in

          let bound =
            match e.e_node with
            | Eapp ({ e_node = Eop (p, _) }, [e1; e2]) ->
                if not (EcPath.p_equal p EcCoreLib.CI_Int.p_int_lt) then
                  raise Failure;
                if not (Mid.is_empty e2.e_fv) then
                  raise Failure;
                if not (EcReduction.EqTest.for_expr env e1 (e_var vari tint)) then
                  raise Failure;
                e2
            | _ -> raise Failure in

          begin
            match List.rev wbody.s_node with
            | { i_node = Sasgn (LvVar (pv, _), incr) } :: body -> begin
                if not (EcEnv.NormMp.pv_equal env vari pv) then
                  raise Failure;
                match incr.e_node with
                | Eapp ({ e_node = Eop (p, _) }, [ei1; ei2]) ->
                    if not (EcPath.p_equal p EcCoreLib.CI_Int.p_int_add) then
                      raise Failure;
                    if not (EcReduction.EqTest.for_expr env ei1 (e_var vari tint)) then
                      raise Failure;
                    if not (EcReduction.EqTest.for_expr env ei2 (e_int EcBigInt.one)) then
                      raise Failure;
                    if EcPV.PV.mem_pv env vari (EcPV.is_write env body) then
                      raise Failure

                | _ -> raise Failure
              end

            | _ -> raise Failure
          end;

          let me, (rnds  , ll,  body) = aux top (me, (rd0, wr0)) s in
          let me, (wrnds, wll, wbody) = aux0 (me, (rd0, wr0)) wbody in

          let lsplit ety e =
            let rty = ttuple [ety; tlist ety] in
            let op  = e_op (EcPath.pqname EcCoreLib.CI_List.p_List "lsplit") in
            let op  = op [ety] (tfun (tlist ety) rty) in
            e_app op [e] rty in

          let me, wrnds = List.fold_left_map (fun me ((pv, ty), e) ->
              let vr     = EcPath.xbasename pv.pv_name ^ "_s" in
              let vr     = { v_name = vr; v_type = ty; } in
              let me, vr = fresh_pv me vr in
              let vr     = pv_loc (EcMemory.xpath me) vr in
              let asgn   = i_asgn (LvVar (pv, ty), lsplit ty (e_var vr (tlist ty))) in
              let rnd    = EcTypes.e_dlist ty e bound in
              (me, (((vr, tlist ty), rnd), asgn))) me wrnds in

          let wrnds, asgn = List.split wrnds in

          me, (wrnds @ rnds, wll @ ll, i_while (e, stmt (asgn @ wbody)) :: body)
        end

      | _ -> raise Failure

    with Failure ->
      let me, (rnds, ll, body) = aux top (me, (rd0, wr0)) s in
      me, (rnds, ll, i :: body)

  in

  fun me s ->
    let me, (rnds, ll, body) =
      aux0 ~top:true (me, (EcPV.PV.empty, EcPV.PV.empty)) s in

    let rnds = List.map (fun ((pv, pvty), e) ->
      i_rnd (LvVar (pv, pvty), e)) (List.rev rnds) in

    (me, ll, stmt (rnds @ List.rev body))

(* -------------------------------------------------------------------- *)
let t_derandomize tc =
  let concl = FApi.tc1_goal tc in
  let hyps  = FApi.tc1_hyps tc in
  let env   = EcEnv.LDecl.toenv hyps in

  match concl.f_node with
  | FhoareS hs -> begin
      try
        let me, ll, body = derandomize hyps hs.hs_m hs.hs_s in
        let ll =
          List.map
            (fun e ->
              f_forall_simpl [fst me, GTmem (snd me)]
                (f_lossless
                   (oget (as_tdistr (EcEnv.Ty.hnorm e.e_ty env)))
                   (form_of_expr (fst me) e)))
            ll in
        let concl = { hs with hs_m = me; hs_s = body; } in
        FApi.xmutate1 tc `Dernd (ll @ [EcFol.f_hoareS_r concl])

      with Failure -> EcLowGoal.t_id tc
    end

  | _ ->
      EcLowGoal.t_id tc
