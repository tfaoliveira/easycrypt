(* -------------------------------------------------------------------- *)
open EcUtils
open EcFol
open EcEnv
open EcModules

open EcCoreGoal
open EcLowGoal
open EcLowPhlGoal

module L   = EcLocation
module APT = EcParsetree
module TTC = EcProofTyping
module PT  = EcProofTerm

(* -------------------------------------------------------------------- *)
(* destr_exists_prenex destructs recursively existentials in a formula
 *  whenever possible.
 * For instance:
 * - E x p1 /\ E y p2 -> [x,y] (p1 /\ p2)
 * - E x p1 /\ E x p2 -> [] (E x p1 /\ E x p2)
 * - p1 => E x p2 -> [x] (p1 => p2)
 * - E x p1 => p2 -> [] (E x p1 => p2)
 *)
let destr_exists_prenex env on f =
  let disjoint bds1 bds2 =
    List.for_all
      (fun (id1, _) -> List.for_all (fun (id2, _) -> id1 <> id2) bds2)
      bds1
  in

  let rec prenex_exists bds p =
    match sform_of_form p with
    | SFand (`Sym, (f1, f2)) ->
        let (bds1, f1) = prenex_exists [] f1 in
        let (bds2, f2) = prenex_exists [] f2 in
          if   disjoint bds1 bds2
          then (bds1@bds2@bds, f_and f1 f2)
          else (bds, p)

    | SFor (`Sym, (f1, f2)) ->
        let (bds1, f1) = prenex_exists [] f1 in
        let (bds2, f2) = prenex_exists [] f2 in
          if   disjoint bds1 bds2
          then (bds1@bds2@bds, f_or f1 f2)
          else (bds, p)

    | SFimp (f1, f2) ->
        let (bds2, f2) = prenex_exists bds f2 in
          (bds2@bds, f_imp f1 f2)

    | SFquant (Lexists, bd, lazy p) ->

        if EcQuantum.is_classical_form env ~on p then
          let (bds, p) = prenex_exists bds p in
          (bd::bds, p)
        else
          (bds, p)

    | SFif (f, ft, fe) ->
        let (bds1, f1) = prenex_exists [] ft in
        let (bds2, f2) = prenex_exists [] fe in
          if   disjoint bds1 bds2
          then (bds1@bds2@bds, f_if f f1 f2)
          else (bds, p)

    | _ -> (bds, p)
  in
    (* Make it fail as with destr_exists *)
    match prenex_exists [] f with
    | [] , _ -> destr_error "exists"
    | bds, f -> (bds, f)

(* -------------------------------------------------------------------- *)
let get_to_gens fs =
  let do_id f =
    let id =
      match f.f_node with
      | Fpvar (pv, m) -> id_of_pv pv m
      | _             -> EcIdent.create "f" in
    id, f in
  List.map do_id fs

(* -------------------------------------------------------------------- *)
let t_hr_exists_elim_r ?bound tc =
  let only_classical =
    (* FIXME QUANTUM : all logic need this restriction or only equiv *)
    (*let concl = FApi.tc1_goal tc in
      is_equivS concl || is_equivF concl *)
    true
  in
  let pre = tc1_get_pre tc in
  let on = if only_classical then tc1_get_mem tc else [] in
  let bd, pre =
    try  destr_exists_prenex (FApi.tc1_env tc) on pre
    with DestrError _ -> [], pre in
  let bd, pre =
    bound
      |> omap (fun bound ->
             let bound = min bound (List.length bd) in
             let bd1, bd2 = List.takedrop bound bd in

             (bd1, f_exists bd2 pre))
      |? (bd, pre) in

  (* FIXME: check that bd is not bound in the post *)
  let concl = f_forall bd (set_pre ~pre (FApi.tc1_goal tc)) in
  FApi.xmutate1 tc `HlExists [concl]

(* -------------------------------------------------------------------- *)
let t_hr_exists_intro_r fs tc =
  let hyps  = FApi.tc1_hyps tc in
  let concl = FApi.tc1_goal tc in
  let pre   = tc1_get_pre  tc in
  let post  = tc1_get_post tc in
  let side  = is_equivS concl || is_equivF concl in
  let gen   = get_to_gens fs in
  let eqs   = List.map (fun (id, f) -> f_eq (f_local id f.f_ty) f) gen in
  let bd    = List.map (fun (id, f) -> (id, GTty f.f_ty)) gen in
  let pre   = f_and (f_exists bd (f_ands eqs)) pre in

  let h = LDecl.fresh_id hyps "h" in
  let ms, subst =
    match side with
    | true ->
        let ml, mr = as_seq2 (LDecl.fresh_ids hyps ["&ml"; "&mr"]) in
        let s = Fsubst.f_subst_id in
        let s = Fsubst.f_bind_mem s mleft ml in
        let s = Fsubst.f_bind_mem s mright mr in
        ([ml; mr], s)

    | false ->
        let m = LDecl.fresh_id hyps "&m" in
        let s = Fsubst.f_subst_id in
        let s = Fsubst.f_bind_mem s mhr m in
        ([m], s)
  in

  let args =
    let do1 (_, f) = PAFormula (Fsubst.f_subst subst f) in
    List.map do1 gen
  in

  let tactic =
    FApi.t_seqsub (EcPhlConseq.t_conseq pre post)
      [ t_intros_i (ms@[h]) @!
        t_and_intro @+ [
           t_exists_intro_s args @! t_trivial;
           t_apply_hyp h
        ]
      ; t_trivial
      ; t_id ]
  in
  FApi.t_internal tactic tc

(* -------------------------------------------------------------------- *)
let t_hr_exists_elim  = FApi.t_low0 "hr-exists-elim"  t_hr_exists_elim_r
let t_hr_exists_intro = FApi.t_low1 "hr-exists-intro" t_hr_exists_intro_r

(* -------------------------------------------------------------------- *)
let process_exists_intro ~(elim : bool) fs tc =
  let (hyps, concl) = FApi.tc1_flat tc in
  let penv =
    match concl.f_node with
    | FhoareF hf -> fst (LDecl.hoareF hf.hf_f hyps)
    | FhoareS hs -> LDecl.push_active hs.hs_m hyps
    | FcHoareF hf -> fst (LDecl.hoareF hf.chf_f hyps)
    | FcHoareS hs -> LDecl.push_active hs.chs_m hyps
    | FbdHoareF bhf -> fst (LDecl.hoareF bhf.bhf_f hyps)
    | FbdHoareS bhs -> LDecl.push_active bhs.bhs_m hyps
    | FequivF ef -> fst (LDecl.equivF ef.ef_fl ef.ef_fr hyps)
    | FequivS es -> LDecl.push_all [es.es_ml; es.es_mr] hyps
    | _ -> tc_error_noXhl ~kinds:hlkinds_Xhl !!tc
  in

  let fs =
    List.map
      (fun f -> TTC.pf_process_form_opt !!tc penv None f)
      fs
  in

  let tc = t_hr_exists_intro_r fs tc in

  if elim then
    t_hr_exists_elim_r ~bound:(List.length fs) (FApi.as_tcenv1 tc)
  else tc

(* -------------------------------------------------------------------- *)
let process_ecall oside (l, tvi, fs) tc =
  let (hyps, concl) = FApi.tc1_flat tc in

  let hyps, kind =
    match concl.f_node with
    | FhoareS hs when is_none oside ->
        (LDecl.push_active hs.hs_m hyps, `Hoare (List.length hs.hs_s.s_node))
    | FequivS es ->
        let n1 = List.length es.es_sl.s_node in
        let n2 = List.length es.es_sr.s_node in
        (LDecl.push_all [es.es_ml; es.es_mr] hyps, `Equiv (n1, n2))
    | _ -> tc_error_noXhl ~kinds:[`Hoare `Stmt; `Equiv `Stmt] !!tc
  in

  let t_local_seq p1 tc =
    match kind, oside with
    | `Hoare n, _ ->
        EcPhlApp.t_hoare_app
          (Zpr.cpos (n-1)) p1 tc
    | `Equiv (n1, n2), None ->
        EcPhlApp.t_equiv_app
          (Zpr.cpos (n1-1), Zpr.cpos (n2-1)) p1 tc
    | `Equiv (n1, n2), Some `Left ->
        EcPhlApp.t_equiv_app
          (Zpr.cpos (n1-1), Zpr.cpos n2) p1 tc
    | `Equiv(n1, n2), Some `Right ->
        EcPhlApp.t_equiv_app
          (Zpr.cpos n1, Zpr.cpos (n2-1)) p1 tc
  in

  let fs =
    List.map
      (fun f -> TTC.pf_process_form_opt !!tc hyps None f)
      fs
  in

  let ids, p1 =
    let sub = t_local_seq f_true tc in

    let sub = FApi.t_rotate `Left 1 sub in
    let sub = FApi.t_focus (t_hr_exists_intro_r fs) sub in
    let sub = FApi.t_focus (t_hr_exists_elim_r ~bound:(List.length fs)) sub in

    let ids =
      try  fst (EcFol.destr_forall (FApi.tc_goal sub))
      with DestrError _ -> [] in
    let ids = List.map (snd_map gty_as_ty) ids in

    let nms = List.map (fun (_, x) -> (EcIdent.create "_", x)) ids in
    let sub = FApi.t_focus (EcLowGoal.t_intros_i (List.fst nms)) sub in
    let pte = PT.ptenv_of_penv (FApi.tc_hyps sub) !!tc in
    let pt  = PT.process_pterm pte (APT.FPNamed (l, tvi)) in

    let pt =
      List.fold_left (fun pt (id, ty) ->
          PT.apply_pterm_to_arg_r pt (PT.PVAFormula (f_local id ty)))
        pt ids in

    assert (PT.can_concretize pt.PT.ptev_env);
    let _pt, ax = PT.concretize pt in

    let sub = FApi.t_focus (EcPhlCall.t_call oside ax) sub in
    let sub = FApi.t_rotate `Left 1 sub in
    let sub = oget (get_post (FApi.tc_goal sub)) in

    let subst =
      List.fold_left2
        (fun s id f -> Fsubst.f_bind_local s id f)
        Fsubst.f_subst_id (List.fst ids) fs in

    (nms, Fsubst.f_subst subst sub) in

  let tc = t_local_seq p1 tc in
  let tc = FApi.t_rotate `Left 1 tc in
  let tc = FApi.t_focus (t_hr_exists_intro_r fs) tc in
  let tc = FApi.t_focus (t_hr_exists_elim_r ~bound:(List.length fs)) tc in
  let tc = FApi.t_focus (EcLowGoal.t_intros_i (List.fst ids)) tc in

  let pte = PT.ptenv_of_penv (FApi.tc_hyps tc) (FApi.tc_penv tc) in
  let pt  = PT.process_pterm pte (APT.FPNamed (l, tvi)) in

  let pt =
    List.fold_left (fun pt (id, ty) ->
        PT.apply_pterm_to_arg_r pt (PT.PVAFormula (f_local id ty)))
      pt ids in

  assert (PT.can_concretize pt.PT.ptev_env);

  let pt, ax = PT.concretize pt in

  let tc = FApi.t_focus (EcPhlCall.t_call oside ax) tc in
  let tc = FApi.t_focus (EcLowGoal.Apply.t_apply_bwd_hi ~dpe:true pt) tc in

  FApi.t_last EcPhlAuto.t_auto (FApi.t_rotate `Right 1 tc)
