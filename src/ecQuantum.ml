open EcMaps
open EcUtils
open EcTypes
open EcModules
open EcFol
open EcEnv
open EcPV

module PS = PrefixSet

type iso_reference =
  { iso_var : EcSymbols.symbol;
    iso_ty  : ty;
    iso_def : quantum_ref;     (* use only iso_var *)
  }

let pp_iso ppe fmt iso =
  Format.fprintf fmt "@[(%s, %a) ->@ %a@]"
    iso.iso_var (EcPrinting.pp_type ppe) iso.iso_ty
    (EcPrinting.pp_quantum_ref ppe) iso.iso_def

exception NotFull of quantum_ref

(* ---------------------------------------------------------------------- *)
(* Trusted code                                                           *)

let init_check_iso env iso =
  let pv_iso = pv_loc iso.iso_var in

  let ps = ref PS.empty in

  let rec fill (proj: int list) qr =
    match qr with
    | QRvar (x,_) ->
      assert (pv_equal pv_iso x);
      assert (not (PS.conflict !ps proj));
      ps := PS.add !ps proj
    | QRproj (qr, i) -> fill (i::proj) qr
    | QRtuple qrs ->
      assert (proj = []);
      List.iter (fill []) qrs
  in

  fill [] iso.iso_def;
  !ps

let check_iso env iso =
  let ps = init_check_iso env iso in
  (* check that ps is full *)
  let rec check_full ps proj ty =
    if PS.is_member ps then ()
    else if PS.is_empty ps then raise (NotFull proj)
    else
      match (Ty.hnorm ty env).ty_node with
      | Ttuple tys ->
        let get i = PS.get_proj ps i in
        let check i ty = check_full (get i) (qrproj(proj,i)) ty in
        List.iteri check tys
      | _ -> raise (NotFull proj)
  in
  check_full ps (qrvar (pv_loc iso.iso_var, iso.iso_ty)) iso.iso_ty

let apply_iso iso qr =
  qr_subst_pv (pv_loc iso.iso_var) qr iso.iso_def

let apply_iso_qe iso qe =
  { qeg = qe.qeg
  ; qel = apply_iso iso qe.qel
  ; qer = apply_iso iso qe.qer }

(* ---------------------------------------------------------------------- *)
(* Untrusted code                                                         *)

let compact_iso env iso =
  let ps = init_check_iso env iso in
  let rec aux ps ty =
    if PS.is_member ps || PS.is_empty ps then ps
    else match (Ty.hnorm ty env).ty_node with
    | Ttuple tys ->
      let pss = List.mapi (fun i ty -> aux (PS.get_proj ps i) ty) tys in
      if List.for_all PS.is_member pss then PS.member
      else PS.of_list pss
    | _ -> ps in
  let ps = aux ps iso.iso_ty in

  let rec build proj ps =
    match PS.to_list ps with
    | None -> proj
    | Some l ->
        let doit (i,t) = if PS.is_empty t then None else Some (build (qrproj (proj,i)) (PS.get_proj ps i)) in
        qrtuple (List.filter_map doit l) in

  build (qrvar (pv_loc iso.iso_var, iso.iso_ty)) ps

let compact_iso2 env iso =
  match iso.iso_def with
  | QRtuple [qr1; qr2] ->
      let doit q = compact_iso env {iso with iso_def = q} in
      { iso with iso_def = qrtuple [doit qr1; doit qr2] }
  | _ -> assert false



let qrprojs qr projs =
  List.fold_left (fun q i -> qrproj (q, i)) qr projs

let qrpvprojs pv ty projs = qrprojs (qrvar (pv, ty)) projs

let split_pv env pv ty =
  let rec aux qr typ =
    match (Ty.hnorm typ env).ty_node with
    | Ttuple tys ->
      qrtuple (List.mapi (fun i ty -> aux (qrproj(qr, i)) ty) tys)
    | _ -> qr in
  aux (qrvar (pv,ty)) ty

exception MissingSubterm of (quantum_ref * quantum_ref)

let pp_missing env fmt (qr1, qr2) =
  let ppe = EcPrinting.PPEnv.ofenv env in
  Format.fprintf fmt "not able to reconstruct %a from %a"
    (EcPrinting.pp_quantum_ref ppe) qr1
    (EcPrinting.pp_quantum_ref ppe) qr2

let init_build_iso env qr1 qr2 =
  (* Build the set of all pv occuring in qr1 qr2 *)
  let pv = qr_touch env PV.empty qr1 in
  let pv = qr_touch env pv qr2 in
  let qr1, qr2 = ref qr1, ref qr2 in
  let doit pv ty =
    let qr = split_pv env pv ty in
    qr1 := qr_subst_pv pv qr !qr1;
    qr2 := qr_subst_pv pv qr !qr2
  in
  PV.iter doit (fun _ -> assert false) pv;
  let qr1, qr2 = !qr1, !qr2 in

  let iso_var = "k" in
  let iso_ty = qr_ty env qr1 in
  let k = qrvar (pv_loc iso_var, iso_ty) in
  (* Build the map of accessible projection form qr1 *)
  let map = ref BatMap.empty in
  let add pv proj q =
    map := BatMap.add (pv, proj) q !map in
  let rec fill k proj qr =
    match qr with
    | QRvar (pv, _) -> add pv proj k
    | QRtuple qs ->
      assert (proj = []);
      List.iteri (fun i q -> fill (qrproj(k,i)) [] q) qs
    | QRproj(q, i) -> fill k (i::proj) q in
  fill k [] qr1;
  !map, iso_var, iso_ty, qr1, qr2

let build_iso env qr1 qr2 =
  let map, iso_var, iso_ty, _, qr2 = init_build_iso env qr1 qr2 in
  (* try to build qr2 from the map of projection *)
  let get (pv,ty) projs =
    try BatMap.find (pv, projs) map
    with Not_found ->
      raise (MissingSubterm (qrpvprojs pv ty projs, qr1)) in

  let rec build projs qr =
    match qr with
    | QRvar pv -> get pv projs
    | QRtuple qs ->
      assert (projs = []);
      qrtuple (List.map (build []) qs)
    | QRproj(q, i) -> build (i::projs) q in
  let iso_def = build [] qr2 in
  { iso_var; iso_ty; iso_def }

(*
     P => q1 = q2 /\ q1' = q2'
     -----------------------------------------------
     P, (r1, q1 = r2, q2) |=> P, (r1, q1' = r2, q2')

*)

let build_partial_iso_qr env qr1 qr2 =
  let map, iso_var, iso_ty, _, qr2 = init_build_iso env qr1 qr2 in
  (* try to build qr2 from the map of projection *)

  let q1' = ref [] in
  let r1 = ref [] in
  let add (pv,ty) projs =
    if BatMap.mem (pv, projs) map then
      r1 := qrpvprojs pv ty projs :: !r1
    else
      q1' := qrpvprojs pv ty projs :: !q1' in

  let rec build projs qr =
    match qr with
    | QRvar pv -> add pv projs
    | QRtuple qs ->
      assert (projs = []);
      List.iter (build []) qs
    | QRproj(q, i) -> build (i::projs) q in

  build [] qr2;
  (* we have qr2 ~ r1, q1' and r1 is in qr1 *)
  let r1, q1' = qrtuple !r1, qrtuple !q1' in
  let qr1' = qrtuple [qr1; q1'] in
  let iso = build_iso env qr1' qr2 in

  (* Build the missing part of qr1 *)
  let q1 = ref [] in
  let ps = init_check_iso env iso in
  let var = pv_loc iso.iso_var in
  let add_q1 proj =
    q1 := proj :: !q1 in
  let rec complete ps proj ty =
    if PS.is_member ps then ()
    else if PS.is_empty ps then add_q1 proj
    else match (Ty.hnorm ty env).ty_node with
     | Ttuple tys ->
        let get i = PS.get_proj ps i in
        let complete i ty = complete (get i) (qrproj(proj, i))  ty in
        List.iteri complete tys
      | _ -> add_q1 proj in
  complete ps (qrvar(var,iso.iso_ty)) iso.iso_ty;
  (* Only the missing part of qr1 is in q1 because r1 is in qr1 *)
  let q1 = apply_iso {iso with iso_def = qrtuple !q1} qr1' in
  (* we have qr1 ~ r1, q1 *)
  let iso1 = build_iso env qr1 (qrtuple [r1; q1]) in
  let iso2 = build_iso env qr2 (qrtuple [r1; q1']) in
  let ppe = EcPrinting.PPEnv.ofenv env in
  Format.eprintf "iso1 = %a@." (pp_iso ppe) iso1;
  Format.eprintf "iso2 = %a@." (pp_iso ppe) iso2;
  let iso1 = compact_iso2 env iso1 in
  let iso2 = compact_iso2 env iso2 in
  Format.eprintf "iso1 = %a@." (pp_iso ppe) iso1;
  Format.eprintf "iso2 = %a@." (pp_iso ppe) iso2;
  iso1, iso2

let build_partial_iso env qe1 qe2 =
  let iso1, iso2 = build_partial_iso_qr env qe1.qel qe2.qel in
  apply_iso_qe iso1 qe1, apply_iso_qe iso2 qe2
