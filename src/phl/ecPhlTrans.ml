(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcTypes
open EcFol
open EcEnv
open EcPV
open EcTransMatching
open EcModules
open EcMaps

open EcCoreGoal
open EcLowPhlGoal

module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
module Low = struct
  (* ------------------------------------------------------------------ *)
  let transitivity_side_cond hyps prml prmr poml pomr p q p1 q1 pomt p2 q2 =
    let env = LDecl.toenv hyps in
    let cond1 =
      let fv1 = PV.fv env mright p1 in
      let fv2 = PV.fv env mleft  p2 in
      let fv  = PV.union fv1 fv2 in
      let elts, glob = PV.ntr_elements fv in
      let bd, s = generalize_subst env mhr elts glob in
      let s1 = PVM.of_mpv s mright in
      let s2 = PVM.of_mpv s mleft in
      let concl = f_and (PVM.subst env s1 p1) (PVM.subst env s2 p2) in
      f_forall_mems [prml;prmr] (f_imp p (f_exists bd concl)) in
    let cond2 =
      let m2 = LDecl.fresh_id hyps "&m" in
      let q1 = Fsubst.f_subst_mem mright m2 q1 in
      let q2 = Fsubst.f_subst_mem mleft  m2 q2 in
      f_forall_mems [poml;(m2,pomt);pomr] (f_imps [q1;q2] q) in
    (cond1, cond2)

  (* ------------------------------------------------------------------ *)
  let t_equivS_trans_r (mt, c2) (p1, q1) (p2, q2) tc =
    let hyps = FApi.tc1_hyps tc in
    let es = tc1_as_equivS tc in
    let m1, m3 = es.es_ml, es.es_mr in
    let cond1, cond2 =
      transitivity_side_cond hyps
        m1 m3 m1 m3 es.es_pr es.es_po p1 q1 mt p2 q2 in
    let cond3 =
      f_equivS_r { es with
        es_mr = (mright,mt);
        es_sr = c2;
        es_pr = p1;
        es_po = q1;
      } in
    let cond4 =
      f_equivS_r { es with
        es_ml = (mleft, mt);
        es_sl = c2;
        es_pr = p2;
        es_po = q2;
      } in

     FApi.xmutate1 tc `Trans [cond1; cond2; cond3; cond4]

  (* ------------------------------------------------------------------ *)
  let t_equivF_trans_r f (p1, q1) (p2, q2) tc =
    let env, hyps, _ = FApi.tc1_eflat tc in
    let ef = tc1_as_equivF tc in
    let (prml, prmr), (poml, pomr) = Fun.equivF_memenv ef.ef_fl ef.ef_fr env in
    let (_, pomt) = snd (Fun.hoareF_memenv f env) in
    let cond1, cond2 =
      transitivity_side_cond
        hyps prml prmr poml pomr
        ef.ef_pr ef.ef_po p1 q1 pomt p2 q2 in
    let cond3 = f_equivF p1 ef.ef_fl f q1 in
    let cond4 = f_equivF p2 f ef.ef_fr q2 in

    FApi.xmutate1 tc `Trans [cond1; cond2; cond3; cond4]
end

(* -------------------------------------------------------------------- *)
let t_equivS_trans = FApi.t_low3 "equiv-trans" Low.t_equivS_trans_r
let t_equivF_trans = FApi.t_low3 "equiv-trans" Low.t_equivF_trans_r

(* -------------------------------------------------------------------- *)
let process_replace_stmt s p c p1 q1 p2 q2 tc =
  let hyps = FApi.tc1_hyps tc in
  let es = tc1_as_equivS tc in
  let ct = match oget s with `Left -> es.es_sl | `Right -> es.es_sr in
  let mt = snd (match oget s with `Left -> es.es_ml | `Right -> es.es_mr) in
  (* Translation of the stmt *)
  let names, p' = trans_block p in
  let r  = EcReduction.full_red in
  let r' = EcReduction.no_red in
  let e  = EcFMatching.mk_engine (EcPattern.pat_stmt ct) p' hyps r r r' in
  let map = match EcFMatching.search_eng e with
    | None -> Mstr.empty
    | Some m ->
       let m = (EcFMatching.get_n_matches m).EcFMatching.me_matches in
       let m = Mstr.map_filter (fun n -> EcIdent.Mid.find_opt n m) names in
       let m =
         let env = EcEnv.LDecl.toenv hyps in
         Mstr.map_filter
           (fun pat ->
             try Some (EcFMatching.Translate.stmt_of_pattern env pat).s_node
             with EcFMatching.Translate.Invalid_Type p ->
               let gstate  = EcEnv.gstate env in
               let verbose = EcGState.getflag "debug" gstate in
               let ppe = EcPrinting.PPEnv.ofenv env in
               if verbose then
                 EcEnv.notify env `Warning "----- translating stmt failed : %a : %a"
                   (EcPrinting.pp_pattern ppe) p
                   (EcPrinting.pp_ogty ppe) p.EcPattern.p_ogty;
               None) m in
       m
  in
  let c = c @ [EcLocation.mk_loc EcLocation._dummy
                 (EcParsetree.PSident
                    (EcLocation.mk_loc EcLocation._dummy
                       (EcIdent.name EcPattern.default_end_name)))] in
  let c = (EcLocation.mk_loc EcLocation._dummy
             (EcParsetree.PSident
                    (EcLocation.mk_loc EcLocation._dummy
                       (EcIdent.name EcPattern.default_start_name)))) :: c in
  let p1, q1 =
    let hyps = LDecl.push_all [es.es_ml; (mright, mt)] hyps in
    TTC.pf_process_form !!tc hyps tbool p1,
    TTC.pf_process_form !!tc hyps tbool q1 in
  let p2, q2 =
    let hyps = LDecl.push_all [(mleft, mt); es.es_mr] hyps in
    TTC.pf_process_form !!tc hyps tbool p2,
    TTC.pf_process_form !!tc hyps tbool q2 in
  let c = TTC.tc1_process_prhl_stmt tc (oget s) ~map c in
  t_equivS_trans (mt, c) (p1, q1) (p2, q2) tc

(* -------------------------------------------------------------------- *)
let process_trans_stmt s c p1 q1 p2 q2 tc =
  let hyps = FApi.tc1_hyps tc in
  let es = tc1_as_equivS tc in
  let mt = snd (match oget s with `Left -> es.es_ml | `Right -> es.es_mr) in
  let p1, q1 =
    let hyps = LDecl.push_all [es.es_ml; (mright, mt)] hyps in
    TTC.pf_process_form !!tc hyps tbool p1,
    TTC.pf_process_form !!tc hyps tbool q1 in
  let p2, q2 =
    let hyps = LDecl.push_all [(mleft, mt); es.es_mr] hyps in
    TTC.pf_process_form !!tc hyps tbool p2,
    TTC.pf_process_form !!tc hyps tbool q2 in
  (* Translation of the stmt *)
  let c = TTC.tc1_process_prhl_stmt tc (oget s) c in
  t_equivS_trans (mt,c) (p1, q1) (p2, q2) tc

(* -------------------------------------------------------------------- *)
let process_trans_fun f p1 q1 p2 q2 tc =
  let env, hyps, _ = FApi.tc1_eflat tc in
  let ef = tc1_as_equivF tc in
  let f = EcTyping.trans_gamepath env f in
  let (_, prmt), (_, pomt) = Fun.hoareF_memenv f env in
  let (prml, prmr), (poml, pomr) = Fun.equivF_memenv ef.ef_fl ef.ef_fr env in
  let process ml mr fo =
    TTC.pf_process_form !!tc (LDecl.push_all [ml; mr] hyps) tbool fo in
  let p1 = process prml (mright, prmt) p1 in
  let q1 = process poml (mright, pomt) q1 in
  let p2 = process (mleft,prmt) prmr p2 in
  let q2 = process (mleft,pomt) pomr q2 in
  t_equivF_trans f (p1, q1) (p2, q2) tc

(* -------------------------------------------------------------------- *)
let process_equiv_trans (tk, p1, q1, p2, q2) g =
  match tk with
  | TKfun f -> process_trans_fun f p1 q1 p2 q2 g
  | TKstmt (s, c) -> process_trans_stmt s c p1 q1 p2 q2 g
  | TKparsedStmt (s, p, c) -> process_replace_stmt s p c p1 q1 p2 q2 g
