(* -------------------------------------------------------------------- *)
open EcParsetree
open EcModules
open EcFol
open EcPV
open EcReduction
open EcCoreGoal
open EcLowGoal
open EcLowPhlGoal
open EcQuantum
open EcPrinting

module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)

let qsubst_unitary env s m qr f =
  EcQuantum.build_subst env s (fst m) qr
      (f_app_simpl f [form_of_qr env qr (fst m)]
         (qr_ty env qr))

(*
q1 disjoint r1
-------------------------------------
q1 <- U[f] ~ skip :
    P{(q1/f q1)<1>}, r1 = r2
    ==>
    P, r1 = r2
*)
let wp_equiv_disj_unitary (side:side) tc =
  let env = FApi.tc1_env tc in
  let es  = tc1_as_qequivS tc in
  let m,s =
    match side with
    | `Left  -> es.es_ml, es.es_sl
    | `Right -> es.es_mr, es.es_sr
  in

  let (qr, f), s = tc1_last_unitary tc s in

  check_disjoint_qe ~who:"unitary" tc side qr es.es_po.ec_e;

  let f = form_of_expr (fst m) f in
  let subst = qsubst_unitary env PVM.empty m qr f in
  let ec_f = PVM.subst env subst es.es_po.ec_f in
  let es_po = { es.es_po with ec_f } in
  let concl =
    match side with
      | `Left  -> f_qequivS_r { es with es_sl=s; es_po; }
      | `Right -> f_qequivS_r { es with es_sr=s; es_po; }
  in
  FApi.xmutate1 tc `Unitary [concl]


(*
q1 : t
q2 : t
r1 disjoint q1
r2 disjoint q1
-----------------------------------------------------
q1 <- U[f1] ~ q2 <- U[f2] :
    P{(q1/f1 q1)<1>, (q2/f2 q2)<2>} /\
   (forall (x:t), (f1<1> x) = (f2<2> x)),
   (q1,r1= q2, r2)
    ==>
    P, (q1,r1 = q2, r2)
*)

let wp_equiv_unitary_core
    (r1  : quantum_ref)
    (r2  : quantum_ref)
    tc =

  let env = FApi.tc1_env tc in
  let es  = tc1_as_qequivS tc in

  let (qr1, f1), es_sl = tc1_last_unitary tc es.es_sl in
  let (qr2, f2), es_sr = tc1_last_unitary tc es.es_sr in

  let ty1 = qr_ty env qr1 in
  let ty2 = qr_ty env qr2 in

  if not (EqTest.for_type env ty1 ty2) then
    (let ppe = PPEnv.ofenv env in
     tc_error !!tc ~who:"unitary" "@[%a and@ %a@ should have the same type@]"
       (pp_quantum_ref ppe) qr1
       (pp_quantum_ref ppe) qr2);


  let f1 = form_of_expr (fst es.es_ml) f1 in
  let f2 = form_of_expr (fst es.es_mr) f2 in

  let who = "unitary" in

  let qe = es.es_po.ec_e in

  check_disjoint ~who tc qr1 r1;
  check_disjoint ~who tc qr2 r2;

  ensure_iso ~who tc qe { qe with qel = qrtuple [qr1; r1]; qer = qrtuple [qr2; r2] };

  let subst = qsubst_unitary env PVM.empty es.es_ml qr1 f1 in
  let subst = qsubst_unitary env subst es.es_mr qr2 f2 in

  let eq_cond =
    let x = EcIdent.create "x" in
    let f_x = f_local x ty1 in
    f_forall_simpl [x, GTty ty1]
         (f_eq_simpl (f_app_simpl f1 [f_x] ty1) (f_app_simpl f2 [f_x] ty1)) in
  let es_po =
    { es.es_po with
      ec_f = f_and_simpl (PVM.subst env subst es.es_po.ec_f) eq_cond } in
  let concl = f_qequivS_r { es with es_sl; es_sr; es_po } in

  FApi.xmutate1 tc `Unitary [concl]


let wp_equiv_unitary tc =
  let env = FApi.tc1_env tc in
  let es  = tc1_as_qequivS tc in

  let (qr1, _), _ = tc1_last_unitary tc es.es_sl in

  let _, iso2 = build_partial_iso_qr env qr1 es.es_po.ec_e.qel in
  let (_, r) = destr_qr_pair iso2.iso_def in
  let r = { iso2 with iso_def = r } in

  let r1 = apply_iso r es.es_po.ec_e.qel in
  let r2 = apply_iso r es.es_po.ec_e.qer in
  wp_equiv_unitary_core r1 r2 tc

let process_unitary (side:oside) =
  match side with
  | None -> wp_equiv_unitary
  | Some side -> wp_equiv_disj_unitary side



(* ------------------------------------------------------------------------- *)
(* Quantum Initialisation                                                    *)

let qsubst_init env s m qr e =
  EcQuantum.build_subst env s (fst m) qr e

(*
q disjoint r1
----------------------------------------------
q <~ e ~ skip : P{(q/e)<1>}, r1 = r2 ==> P, r1 = r2
*)
let wp_equiv_disj_init (side:side) tc =
  let env = FApi.tc1_env tc in
  let es  = tc1_as_qequivS tc in
  let m,s =
    match side with
    | `Left  -> es.es_ml, es.es_sl
    | `Right -> es.es_mr, es.es_sr
  in

  let (qr, e), s = tc1_last_init tc s in

  EcQuantum.check_disjoint_qe ~who:"qinit" tc side qr es.es_po.ec_e;

  let e = form_of_expr (fst m) e in
  let subst = qsubst_init env PVM.empty m qr e in
  let ec_f = PVM.subst env subst es.es_po.ec_f in
  let es_po = { es.es_po with ec_f } in
  let concl =
    match side with
      | `Left  -> f_qequivS_r { es with es_sl=s; es_po; }
      | `Right -> f_qequivS_r { es with es_sr=s; es_po; }
  in
  FApi.xmutate1 tc `Unitary [concl]


(*
g1: t1 -> t g2: t2 -> t
r1 disjoint f1 q1
r2 disjoint f2 q2
-----------------------------------------------
q1 <~ e1 ~ q2 <~ e2 :
P{(q1/e1)<1>, (q2/e2)<2>} /\
(g1 e1)<1> = (g2 e2)<2>,
r1 = r2
==>
P, g1 q1, r1 = g2 q2, r2
*)
let wp_equiv_init_core g1 g2 r1 r2 tc =
  let env = FApi.tc1_env tc in
  let es  = tc1_as_qequivS tc in

  let (qr1, e1), es_sl = tc1_last_init tc es.es_sl in
  let (qr2, e2), es_sr = tc1_last_init tc es.es_sr in

  let ty1 = qr_ty env qr1 in
  let ty2 = qr_ty env qr2 in

  assert (EqTest.for_type env (qr_ty env g1.iso_def) (qr_ty env g2.iso_def));
  assert (EqTest.for_type env ty1 g1.iso_ty);
  assert (EqTest.for_type env ty2 g2.iso_ty);

  let f1 = form_of_expr (fst es.es_ml) e1 in
  let f2 = form_of_expr (fst es.es_mr) e2 in

  let who = "qinit" in

  let qe = es.es_po.ec_e in

  let gq1 = apply_iso g1 qr1 in
  let gq2 = apply_iso g2 qr2 in

  ensure_iso ~who tc qe { qe with qel = qrtuple [gq1; r1]; qer = qrtuple [gq2; r2] };
  check_disjoint ~who tc qr1 r1;
  check_disjoint ~who tc qr2 r2;

  let g1, g2 =
    if es.es_po.ec_e.qeg then
      (* Special case if there is global equality *)
      let gg1 = qr_glob env qr1 in (* qr1 -> tyg *)
      let gg2 = qr_glob env qr2 in (* qr2 -> tyg' *)
      let iso = ensure_iso_qr ~who tc (apply_iso gg1 qr1) (apply_iso gg2 qr2) in
      (* iso: tyg -> tyg' *)
      let g1 = { g1 with iso_def =
                 qrtuple [g1.iso_def;
                          apply_iso iso (apply_iso gg1 (iso_qrvar g1))] } in
      let g2 = { g2 with iso_def =
                 qrtuple [g2.iso_def;
                          apply_iso gg2 (iso_qrvar g2)] } in
      g1, g2
    else g1, g2
  in

  let ty = qr_ty env g1.iso_def in
  let g1 = EcQuantum.form_of_qr_fun env g1 in
  let g2 = EcQuantum.form_of_qr_fun env g2 in

  let subst = qsubst_init env PVM.empty es.es_ml qr1 f1 in
  let subst = qsubst_init env subst es.es_mr qr2 f2 in

  let eq_cond =
    f_eq (f_app_simpl g1 [f1] ty) (f_app_simpl g2 [f2] ty) in

  let es_po =
    { ec_f = f_and_simpl (PVM.subst env subst es.es_po.ec_f) eq_cond
    ; ec_e = {qe with qel = r1; qer = r2 } } in
  let concl = f_qequivS_r { es with es_sl; es_sr; es_po } in

  FApi.xmutate1 tc `Unitary [concl]

let wp_equiv_init tc =
  let env = FApi.tc1_env tc in
  let es  = tc1_as_qequivS tc in

  let (qr1, _), _ = tc1_last_init tc es.es_sl in
  let (qr2, _), _ = tc1_last_init tc es.es_sr in

  let doit qr q =
    let iso1, iso2 = build_partial_iso_qr env qr q in
    let (g1, _), (g2, r) =
      destr_qr_pair iso1.iso_def, destr_qr_pair iso2.iso_def in
    let g1 = { iso1 with iso_def = g1 } in
    let g2 = { iso2 with iso_def = g2 } in
    let r = { iso2 with iso_def = r } in
    g1, g2, r
  in

  let g1, g2, r = doit qr1 es.es_po.ec_e.qel in
  let r1 = apply_iso r es.es_po.ec_e.qel in
  let r2 = apply_iso r es.es_po.ec_e.qer in
  let g2 =
    try
      build_iso env qr2 (apply_iso g2 es.es_po.ec_e.qer)
    with MissingSubterm missing ->
       tc_error !!tc ~who:"unitary" "@[%a@]" (pp_missing env) missing in
  wp_equiv_init_core g1 g2 r1 r2 tc

let process_init (side:oside) =
  match side with
  | None -> wp_equiv_init
  | Some side -> wp_equiv_disj_init side
