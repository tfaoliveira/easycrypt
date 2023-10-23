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

exception NotFull of int list

(* ---------------------------------------------------------------------- *)
(* Trusted code                                                           *)

let check_iso env iso =

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

  (* check that ps is full *)
  let rec check_full (proj: int list) ps ty =
    if PS.is_member ps then ()
    else
      match (Ty.hnorm ty env).ty_node with
      | Ttuple tys ->
        let get i =
          try PS.get_proj ps i with Not_found -> raise (NotFull (i::proj)) in
        let check i ty = check_full (i::proj) (get i) ty in
        List.iteri check tys
      | _ -> raise (NotFull proj)
  in

  check_full [] !ps iso.iso_ty

let apply_iso iso qe =
  { qeg = qe.qeg
  ; qel = qr_subst_pv (pv_loc iso.iso_var) qe.qel iso.iso_def
  ; qer = qr_subst_pv (pv_loc iso.iso_var) qe.qel iso.iso_def }


(* ---------------------------------------------------------------------- *)
(* Untrusted code                                                         *)

let qrprojs pv ty projs =
  List.fold_right (fun i q -> qrproj (q, i)) projs (qrvar (pv, ty))

let split_pv env pv ty =
  let rec aux proj typ =
    match (Ty.hnorm typ env).ty_node with
    | Ttuple tys ->
      qrtuple (List.mapi (fun i ty -> aux (i::proj) ty) tys)
    | _ ->
      qrprojs pv ty proj in
  aux [] ty

exception MissingSubterm of (quantum_ref * quantum_ref)

let pp_missing env fmt (qr1, qr2) =
  let ppe = EcPrinting.PPEnv.ofenv env in
  Format.fprintf fmt "not able to reconstruct %a from %a"
    (EcPrinting.pp_quantum_ref ppe) qr1
    (EcPrinting.pp_quantum_ref ppe) qr2


let build_iso env qR1 qr2 =
  (* Build the set of all pv occuring in qr1 qr2 *)
  let pv = qr_touch env PV.empty qR1 in
  let pv = qr_touch env pv qr2 in
  let qr1, qr2 = ref qR1, ref qr2 in
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

  (* try to build qr2 from the map of projection *)

  let get (pv,ty) projs =
    try BatMap.find (pv, projs) !map
    with Not_found -> raise (MissingSubterm (qrprojs pv ty projs, qR1)) in

  let rec build projs qr =
    match qr with
    | QRvar pv -> get pv projs

    | QRtuple qs ->
      assert (projs = []);
      qrtuple (List.map (build []) qs)
    | QRproj(q, i) -> build (i::projs) q in
  let iso_def = build [] qr2 in
  { iso_var; iso_ty; iso_def }
