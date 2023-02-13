(* -------------------------------------------------------------------- *)
open EcFol

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
module Low = struct

  (*TODO: annotations: make a variant that removes all unused labels.*)

  let s_labels_clean side asum asrt s =
    match side with
    | `Left ->
         EcCoreModules.s_labels_clean
           (fun l -> a_labels_is_left  asum l || a_labels_is_left  asrt l) s
    | `Right ->
         EcCoreModules.s_labels_clean
           (fun l -> a_labels_is_right asum l || a_labels_is_right asrt l) s

  let t_equiv_label_clean side tc =
    let es = tc1_as_equivS tc in
    let s =
      match side with
      | `Left  -> es.es_sl
      | `Right -> es.es_sr in
    let s = s_labels_clean side es.es_am es.es_as s in
    let sl,sr = match side with `Left -> s, es.es_sr | `Right -> es.es_sl, s in
    let concl = f_equivS_r { es with es_sl = sl; es_sr = sr } in
    FApi.xmutate1 tc `Label [concl]

  (*TODO: annotations: to handle the case of not-unique labels: copy all the first labels and last labels to fresh labels.*)
  (*The annotations linking two first labels or two last labels and nothing else should have their labels renamed*)
  (*The annotations linking two first labels or two last labels and something else should have their labels duplicated*)
  (*The other annotations should be preserved.*)
  let t_equiv_label_firsts tc =
    let es = tc1_as_equivS tc in
    let lls, sl = tc1_firsts_label tc es.es_sl in
    let lrs, sr = tc1_firsts_label tc es.es_sr in
    let amlr, am__ =
      a_labels_partition
        (fun ll lr ->
          List.exists
            (fun l -> EcIdent.name l = EcIdent.name ll) lls &&
          List.exists
            (fun l -> EcIdent.name l = EcIdent.name lr) lrs) es.es_am in
    let aslr, as__ =
      a_labels_partition
        (fun ll lr ->
          List.exists
            (fun l -> EcIdent.name l = EcIdent.name ll) lls &&
          List.exists
            (fun l -> EcIdent.name l = EcIdent.name lr) lrs) es.es_as in
    let f = f_and (f_ands (List.map (fun (_, _, f) -> f) amlr)) es.es_pr in
    let concl1 = f_imp_simpl f (f_ands (List.map (fun (_, _, f) -> f) aslr)) in
    let concl2 = f_equivS_r { es with es_sl = sl; es_sr = sr; es_pr = f; es_am = am__; es_as = as__ } in
    FApi.xmutate1 tc `Label [concl1; concl2]

  let t_equiv_label_lasts tc =
    let es = tc1_as_equivS tc in
    let lls, sl = tc1_lasts_label tc es.es_sl in
    let lrs, sr = tc1_lasts_label tc es.es_sr in
    let amlr, am__ =
      a_labels_partition
        (fun ll lr ->
          List.exists
            (fun l -> EcIdent.name l = EcIdent.name ll) lls &&
          List.exists
            (fun l -> EcIdent.name l = EcIdent.name lr) lrs) es.es_am in
    let aslr, as__ =
      a_labels_partition
        (fun ll lr ->
          List.exists
            (fun l -> EcIdent.name l = EcIdent.name ll) lls &&
          List.exists
            (fun l -> EcIdent.name l = EcIdent.name lr) lrs) es.es_as in
    let f = f_and (f_ands (List.map (fun (_, _, f) -> f) aslr)) es.es_po in
    let f = f_imp_simpl (f_ands (List.map (fun (_, _, f) -> f) amlr)) f in
    let concl = f_equivS_r { es with es_sl = sl; es_sr = sr; es_po = f; es_am = am__; es_as = as__ } in
    FApi.xmutate1 tc `Label [concl]

  let t_equiv_label =
    FApi.t_seqs
      [t_equiv_label_lasts;
       FApi.t_seqsub
         t_equiv_label_firsts
         [EcHiGoal.process_trivial; FApi.t_seqs [t_equiv_label_clean `Left; t_equiv_label_clean `Right]]]

end

(* -------------------------------------------------------------------- *)
let t_label side tc =
  match side with
  | None ->
    Low.t_equiv_label tc
  | Some side ->
    Low.t_equiv_label_clean side tc
