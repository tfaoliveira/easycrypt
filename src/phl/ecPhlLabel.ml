(* -------------------------------------------------------------------- *)
open EcFol

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
module Low = struct
  let t_equiv_label_clean side tc =
    let es = tc1_as_equivS tc in
    let s =
      match side with
      | `Left  -> es.es_sl
      | `Right -> es.es_sr in
    let l, s = tc1_last_label tc s in
    let b =
      match side with
      | `Left  -> not (a_labels_is_not_left  l es.es_am && a_labels_is_not_left  l es.es_as)
      | `Right -> not (a_labels_is_not_right l es.es_am && a_labels_is_not_right l es.es_as) in
    if b
    then tc_error !!tc "label-clean: label marked for removal was used in an annotation";
    let sl,sr = match side with `Left -> s, es.es_sr | `Right -> es.es_sl, s in
    let concl = f_equivS_r { es with es_sl = sl; es_sr = sr } in
    FApi.xmutate1 tc `Label [concl]

  let t_equiv_label tc =
    let es = tc1_as_equivS tc in
    let ll, sl = tc1_last_label tc es.es_sl in
    let lr, sr = tc1_last_label tc es.es_sr in
    let aml, am_   = a_labels_partition_left  ll es.es_am in
    let amlr, aml_ = a_labels_partition_right lr aml in
    let am_r, am__ = a_labels_partition_right lr am_ in
    let asl, as_   = a_labels_partition_left  ll es.es_as in
    let aslr, asl_ = a_labels_partition_right lr asl in
    let as_r, as__ = a_labels_partition_right lr as_ in
    let b =
      match aml_, am_r, asl_, as_r with
      | [], [], [], [] -> false
      | _, _, _, _ -> true in
    if b
    then tc_error !!tc "label: one of the two labels selected is used in an annotation that does not use the other";
    let f = f_and (f_ands (List.map (fun (_, _, f) -> f) aslr)) es.es_po in
    let f = f_imp (f_ands (List.map (fun (_, _, f) -> f) amlr)) f in
    let concl = f_equivS_r { es with es_sl = sl; es_sr = sr; es_po = f; es_am = am__; es_as = as__ } in
    FApi.xmutate1 tc `Label [concl]
end

(* -------------------------------------------------------------------- *)
let t_label side tc =
  match side with
  | None ->
    Low.t_equiv_label tc
  | Some side ->
    Low.t_equiv_label_clean side tc
