(* -------------------------------------------------------------------- *)
open EcUtils
open EcAst
open EcFol

open EcCoreGoal
open EcLowPhlGoal
open EcLowGoal

(* -------------------------------------------------------------------- *)
module LowInternal = struct
  (* ------------------------------------------------------------------ *)
  let t_hoare_skip_r tc =
    let hs = tc1_as_hoareS tc in

    if not (List.is_empty hs.hs_s.s_node) then
      tc_error !!tc "instruction list is not empty";

    let concl = f_imp hs.hs_pr hs.hs_po in
    let concl = f_forall_mems [hs.hs_m] concl in

    FApi.xmutate1 tc `Skip [concl]

  let t_hoare_skip = FApi.t_low0 "hoare-skip" t_hoare_skip_r

  (* ------------------------------------------------------------------ *)
  let t_ehoare_skip_r tc =
    let hs = tc1_as_ehoareS tc in

    if not (List.is_empty hs.ehs_s.s_node) then
      tc_error !!tc "instruction list is not empty";

    let concl = f_xreal_le hs.ehs_po hs.ehs_pr in
    let concl = f_forall_mems [hs.ehs_m] concl in

    FApi.xmutate1 tc `Skip [concl]

  let t_ehoare_skip = FApi.t_low0 "ehoare-skip" t_ehoare_skip_r

  (* ------------------------------------------------------------------ *)
  let t_bdhoare_skip_r_low tc =
    let bhs = tc1_as_bdhoareS tc in

    if not (List.is_empty bhs.bhs_s.s_node) then
      tc_error !!tc ~who:"skip" "instruction list is not empty";
    if bhs.bhs_cmp <> FHeq && bhs.bhs_cmp <> FHge then
      tc_error !!tc ~who:"skip" "";

    let concl = f_imp bhs.bhs_pr bhs.bhs_po in
    let concl = f_forall_mems [bhs.bhs_m] concl in
    let goals =
      if   f_equal bhs.bhs_bd f_r1
      then [concl]
      else [f_eq bhs.bhs_bd f_r1; concl]
    in

    FApi.xmutate1 tc `Skip goals

  (* ------------------------------------------------------------------ *)
  let t_bdhoare_skip_r tc =
    let t_trivial = FApi.t_seqs [t_simplify ~delta:`No; t_split; t_fail] in
    let t_conseq  = EcPhlConseq.t_bdHoareS_conseq_bd FHeq f_r1 in
      FApi.t_internal
        (FApi.t_seqsub t_conseq
           [FApi.t_try t_trivial; t_bdhoare_skip_r_low])
        tc

  let t_bdhoare_skip = FApi.t_low0 "bdhoare-skip" t_bdhoare_skip_r

  (* ------------------------------------------------------------------ *)
(* FIXME QUANTUM use function from EcPhlConseq *)
let qe_implies env qe1 qe2 =
  is_qe_empty qe2 ||
  EcReduction.EqTest.for_qe env ~norm:true qe1 qe2

let check_qe_implies tc qe1 qe2 =
  let env = FApi.tc1_env tc in
  if not (qe_implies env qe1 qe2) then
    begin
      let open EcPrinting in
      let ppe = PPEnv.ofenv env in
      tc_error !!tc ~who:"skip" "@[not able to prove@ %a@ implies@ %a@]"
        (pp_qe ppe) qe1 (pp_qe ppe) qe2;
    end

  let t_equiv_skip_core tc =
    let es = tc1_as_qequivS tc in

    if not (List.is_empty es.es_sl.s_node) then
      tc_error !!tc ~who:"skip" "left instruction list is not empty";
    if not (List.is_empty es.es_sr.s_node) then
      tc_error !!tc ~who:"skip" "right instruction list is not empty";
    if not (EcReduction.is_conv_ec (FApi.tc1_hyps tc) es.es_pr es.es_po) then
      tc_error !!tc ~who:"skip" "the pre is not equal to the post";
    FApi.xmutate1 tc `Skip []



  let t_equiv_skip tc =
    let es = tc1_as_qequivS tc in
    (EcPhlConseq.t_equivS_conseq_core ~witheq:false es.es_po es.es_po @+
      [ t_id;
        t_trivial;
        t_equiv_skip_core ]) tc

end

(* -------------------------------------------------------------------- *)
let t_skip =
  t_hS_or_bhS_or_eS
    ~th: LowInternal.t_hoare_skip
    ~teh: LowInternal.t_ehoare_skip
    ~tbh:LowInternal.t_bdhoare_skip
    ~te: LowInternal.t_equiv_skip
