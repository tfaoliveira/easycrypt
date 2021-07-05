(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcModules
open EcFol

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
module LowInternal = struct
  exception No_wp

  let wp_asgn_aux m lv e (lets, f) =
    let let1 = lv_subst m lv (form_of_expr m e) in
      (let1::lets, f)

  let rec wp_stmt onesided env m (stmt: EcModules.instr list) letsf =
    match stmt with
    | [] -> stmt, letsf
    | i :: stmt' ->
        try
          let letsf = wp_instr onesided env m i letsf in
          wp_stmt onesided env m stmt' letsf
        with No_wp -> (stmt, letsf)

  and wp_instr onesided env m i letsf =
    match i.i_node with
    | Sasgn (lv,e) ->
        wp_asgn_aux m lv e letsf

    | Sif (e,s1,s2) ->
        let r1,letsf1 = wp_stmt onesided env m (List.rev s1.s_node) letsf in
        let r2,letsf2 = wp_stmt onesided env m (List.rev s2.s_node) letsf in
        if List.is_empty r1 && List.is_empty r2 then begin
          let post1 = mk_let_of_lv_substs env letsf1 in
          let post2 = mk_let_of_lv_substs env letsf2 in
          let post  = f_if (form_of_expr m e) post1 post2 in
            ([], post)
        end else raise No_wp

    | Sassert e when onesided ->
        let phi = form_of_expr m e in
        let lets,f = letsf in
        (lets, EcFol.f_and_simpl phi f)

    | _ -> raise No_wp

  let rec ewp_stmt env m (stmt: EcModules.instr list) letspf =
    match stmt with
    | [] -> stmt, letspf
    | i :: stmt' ->
        try
          let letspf = ewp_instr env m i letspf in
          ewp_stmt env m stmt' letspf
        with No_wp -> (stmt, letspf)

    and ewp_instr env m i letspf =
      match i.i_node with
      | Sasgn (lv, e) ->
        wp_asgn_aux m lv e letspf

      | Srnd(lv, distr) ->
        let (lets,(p,f)) = letspf in
        let ty_distr = proj_distr_ty env (EcTypes.e_ty distr) in
        let x_id = EcIdent.create (symbol_of_lv lv) in
        let x = f_local x_id ty_distr in
        let distr = EcFol.form_of_expr m distr in
        let let1 = lv_subst m lv x in
        let lets = let1 :: lets in
        let p = mk_let_of_lv_substs env (lets,p) in
        let f = mk_let_of_lv_substs env (lets,f) in
        let p = f_forall [(x_id,GTty ty_distr)] (f_imp (f_in_supp x distr) p) in
        let f = f_Ep ty_distr distr (f_lambda [(x_id,GTty ty_distr)] f) in
        ([], (p, f))

      | Sif(e, s1, s2) ->
        let r1,(lets1,(p1,f1)) = ewp_stmt env m (List.rev s1.s_node) letspf in
        let r2,(lets2,(p2,f2)) = ewp_stmt env m (List.rev s2.s_node) letspf in
        if List.is_empty r1 && List.is_empty r2 then begin
          let p1 = mk_let_of_lv_substs env (lets1,p1) in
          let f1 = mk_let_of_lv_substs env (lets1,f1) in
          let p2 = mk_let_of_lv_substs env (lets2,p2) in
          let f2 = mk_let_of_lv_substs env (lets2,f2) in
          let e = form_of_expr m e in
          let p = f_if e p1 p2 in
          let f = f_if e f1 f2 in
          ([], (p, f))
        end else raise No_wp

      | _ -> raise No_wp

end

let wp ?(uselet=true) ?(onesided=false) env m s post =
  let r,letsf =
    LowInternal.wp_stmt onesided env m (List.rev s.s_node) ([],post)
  in
  let pre = mk_let_of_lv_substs ~uselet env letsf in
  (List.rev r, pre)

let ewp ?(uselet=true) env m s post epost =
  let r,(lets,(p,f)) =
    LowInternal.ewp_stmt env m (List.rev s.s_node) ([],(post, epost))
  in
  let pre = mk_let_of_lv_substs ~uselet env (lets,p) in
  let epre = mk_let_of_lv_substs ~uselet env (lets,f) in
  (List.rev r, (pre, epre))

(* -------------------------------------------------------------------- *)
module TacInternal = struct
  let check_wp_progress tc i (_s : stmt) rm =
    if EcUtils.is_some i && not (List.is_empty rm) then
      tc_error !!tc "remaining %i instruction(s)" (List.length rm)

  let t_hoare_wp ?(uselet=true) i tc =
    let env = FApi.tc1_env tc in
    let hs = tc1_as_hoareS tc in
    let (s_hd, s_wp) = o_split i hs.hs_s in
    let m = EcMemory.memory hs.hs_m in
    let s_wp = EcModules.stmt s_wp in
    let (s_wp, post) = wp ~uselet ~onesided:true env m s_wp hs.hs_po in
    check_wp_progress tc i hs.hs_s s_wp;
    let s = EcModules.stmt (s_hd @ s_wp) in
    let concl = f_hoareS_r { hs with hs_s = s; hs_po = post} in
    FApi.xmutate1 tc `Wp [concl]

  let t_ehoare_wp ?(uselet=true) i tc =
    let env = FApi.tc1_env tc in
    let hs = tc1_as_ehoareS tc in
    let (s_hd, s_wp) = o_split i hs.ehs_s in
    let m = EcMemory.memory hs.ehs_m in
    let s_wp = EcModules.stmt s_wp in
    let (s_wp, (post, epost)) = ewp ~uselet env m s_wp hs.ehs_po hs.ehs_epo in
    check_wp_progress tc i hs.ehs_s s_wp;
    let s = EcModules.stmt (s_hd @ s_wp) in
    let concl = f_eHoareS_r { hs with ehs_s = s; ehs_po = post; ehs_epo = epost} in
    FApi.xmutate1 tc `Wp [concl]

  let t_bdhoare_wp ?(uselet=true) i tc =
    let env = FApi.tc1_env tc in
    let bhs = tc1_as_bdhoareS tc in
    let (s_hd, s_wp) = o_split i bhs.bhs_s in
    let s_wp = EcModules.stmt s_wp in
    let m = EcMemory.memory bhs.bhs_m in
    let s_wp,post = wp ~uselet env m s_wp bhs.bhs_po in
    check_wp_progress tc i bhs.bhs_s s_wp;
    let s = EcModules.stmt (s_hd @ s_wp) in
    let concl = f_bdHoareS_r { bhs with bhs_s = s; bhs_po = post} in
    FApi.xmutate1 tc `Wp [concl]

  let t_equiv_wp ?(uselet=true) ij tc =
    let env = FApi.tc1_env tc in
    let es = tc1_as_equivS tc in
    let i = omap fst ij and j = omap snd ij in
    let s_hdl,s_wpl = o_split i es.es_sl in
    let s_hdr,s_wpr = o_split j es.es_sr in
    let meml, s_wpl = EcMemory.memory es.es_ml, EcModules.stmt s_wpl in
    let memr, s_wpr = EcMemory.memory es.es_mr, EcModules.stmt s_wpr in
    let post = es.es_po in
    let s_wpl, post = wp ~uselet env meml s_wpl post in
    let s_wpr, post = wp ~uselet env memr s_wpr post in
    check_wp_progress tc i es.es_sl s_wpl;
    check_wp_progress tc j es.es_sr s_wpr;
    let sl = EcModules.stmt (s_hdl @ s_wpl) in
    let sr = EcModules.stmt (s_hdr @ s_wpr) in
    let concl = f_equivS_r {es with es_sl = sl; es_sr=sr; es_po = post} in
    FApi.xmutate1 tc `Wp [concl]
end

(* -------------------------------------------------------------------- *)
let t_wp_r ?(uselet=true) k g =
  let module T = TacInternal in

  let (th, teh, tbh, te) =
    match k with
    | None -> (Some (T.t_hoare_wp   ~uselet None),
               Some (T.t_ehoare_wp  ~uselet None),
               Some (T.t_bdhoare_wp ~uselet None),
               Some (T.t_equiv_wp   ~uselet None))

    | Some (Single i) -> (Some (T.t_hoare_wp   ~uselet (Some i)),
                          Some (T.t_ehoare_wp  ~uselet (Some i)),
                          Some (T.t_bdhoare_wp ~uselet (Some i)),
                          None (* ------------------- *))

    | Some (Double (i, j)) ->
        (None, None, None, Some (T.t_equiv_wp ~uselet (Some (i, j))))

  in
    t_hS_or_bhS_or_eS ?th ?teh ?tbh ?te g

let t_wp ?(uselet=true) = FApi.t_low1 "wp" (t_wp_r ~uselet)
