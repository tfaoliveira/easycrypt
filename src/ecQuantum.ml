open EcMaps
open EcUtils
open EcTypes
open EcModules
open EcFol
open EcEnv
open EcPV
open EcCoreGoal
open EcLowGoal

module PS = PrefixSet

type qr_fun =
  { iso_var : EcSymbols.symbol;
    iso_ty  : ty;
    iso_def : quantum_ref;     (* use only iso_var *)
  }

let pp_qr_fun ppe fmt iso =
  Format.fprintf fmt "@[(%s, %a) ->@ %a@]"
    iso.iso_var (EcPrinting.pp_type ppe) iso.iso_ty
    (EcPrinting.pp_quantum_ref ppe) iso.iso_def

exception NotFull of qr_fun

exception MissingSubterm of (quantum_ref * quantum_ref)

let pp_missing env fmt (qr1, qr2) =
  let ppe = EcPrinting.PPEnv.ofenv env in
  Format.fprintf fmt "not able to reconstruct@ %a@ from@ %a"
    (EcPrinting.pp_quantum_ref ppe) qr1
    (EcPrinting.pp_quantum_ref ppe) qr2

let qr_side (side:side) qe =
  match side with
  | `Left -> qe.qel
  | `Right -> qe.qer

let form_of_qr_fun env iso =
  let x = EcIdent.create iso.iso_var in
  let ty = iso.iso_ty in
  let f_x = f_local x ty in
  let rec aux qr =
    match qr with
    | QRvar (x,ty) -> f_x
    | QRtuple qs   -> f_tuple (List.map aux qs)
    | QRproj(q,i)  -> f_proj_env env (aux q) i
  in
  f_lambda [x, GTty ty] (aux iso.iso_def)

let qrprojs qr projs =
  List.fold_left (fun q i -> qrproj (q, i)) qr projs

let qrpvprojs pv ty projs = qrprojs (qrvar (pv, ty)) projs

let iso_qrvar iso = qrvar (pv_loc iso.iso_var, iso.iso_ty)

let destr_qr_pair qr =
  match qr with
  | QRtuple [q1; q2] -> q1, q2
  | _ -> assert false

(* ---------------------------------------------------------------------- *)
(* Trusted code                                                           *)


module PrefixMap : sig
  type prefix = int list
  type 'a t

  val empty : 'a t
  val add : 'a t -> prefix -> 'a -> 'a t

  val build:
    mk_proj  : ('a -> int -> 'a) ->
    mk_tuple : ('a list -> 'a) ->
    hnorm    : (ty -> ty) ->
   'a t -> 'a -> ty -> 'a
end =
struct
  type prefix = int list

  type 'a t =
    | Member of 'a
    | Split of 'a t Mint.t

  let empty : 'a t =
    Split Mint.empty

  let is_empty = function
    | Member _ -> false
    | Split children -> Mint.is_empty children

  let rec add (t : 'a t) (p : prefix) a : 'a t =
    match t, p with
    | Member _, _ -> assert false

    | Split _, [] ->
       assert (is_empty t);
       Member a

    | Split children, i :: subp ->
       let change subt =
         Some (add (Option.value ~default:empty subt) subp a) in
       Split (Mint.change change i children)

  let get_proj children i =
    try Mint.find i children with Not_found -> empty

  let build ~(mk_proj  : 'a -> int -> 'a)
            ~(mk_tuple : 'a list -> 'a)
            ~(hnorm    : ty -> ty)
            (t : 'a t)
            (f : 'a)
            (ty: ty) =
    let rec aux t f ty =
      match t with
      | Member a -> a
      | Split children ->
        if is_empty t then f
        else
          match (hnorm ty).ty_node with
          | Ttuple tys ->
              let doit i ty =
                aux (get_proj children i) (mk_proj f i) ty in
              mk_tuple (List.mapi doit tys)
          | _ -> assert false in
    aux t f ty

end


(* --------------------------------------------------------- *)
(* iso_reference                                             *)
(* f : t1 -> t2 is a iso reference if                        *)
(* there exists fi : t2 -> t1, such that                     *)
(*  forall k:t1, k = fi (f k), and f k is valid              *)

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
    else
      let ty = Ty.hnorm ty env in
      match ty.ty_node with
      | Ttuple tys ->
        let get i = PS.get_proj ps i in
        let check i ty = check_full (get i) (qrproj(proj,i)) ty in
        List.iteri check tys
      | _ ->
          if not (EcReduction.EqTest.for_type env ty tunit) then
          raise (NotFull {iso with iso_def = proj})
  in
  check_full ps (qrvar (pv_loc iso.iso_var, iso.iso_ty)) iso.iso_ty

let apply_iso iso qr =
  qr_subst_pv (pv_loc iso.iso_var) qr iso.iso_def

let apply_iso_qe iso qe =
  { qeg = qe.qeg
  ; qel = apply_iso iso qe.qel
  ; qer = apply_iso iso qe.qer }

let is_qr_valid env qr =
  let norm = EcEnv.NormMp.norm_pvar env in
  EcModules.is_quantum_valid ~norm qr


let check_disjoint ~who tc q1 q2 =
  let open EcPrinting in
  let env = FApi.tc1_env tc in
  if not(is_qr_valid env (qrtuple [q1; q2])) then
    let ppe = PPEnv.ofenv env in
    tc_error !!tc ~who "%a should be disjoint from %a"
       (pp_quantum_ref ppe) q1
       (pp_quantum_ref ppe) q2

let check_disjoint_qe ~who tc side qr qe =
  let open EcPrinting in
  let env = FApi.tc1_env tc in
  if qe.qeg && not (EcModules.qr_is_loc qr) then
    tc_error !!tc ~who "%a should not contains global quantum variable"
       (pp_quantum_ref (PPEnv.ofenv env)) qr;
  check_disjoint ~who tc qr (qr_side side qe)

let build_subst env s m qr f =

  let map = ref (PVMap.create env : (ty * form PrefixMap.t) PVMap.t) in
  let find (x,ty) =
    match PVMap.find x !map with
    | Some tpm -> tpm
    | None -> (ty, PrefixMap.empty) in

  let add x projs f =
    let (ty,pm) = find x in
    let pm = PrefixMap.add pm projs f in
    map := PVMap.add (fst x) (ty, pm) !map in

  let rec fill qr projs f =
    match qr with
    | QRvar x -> add x projs f
    | QRtuple qs ->
        assert (projs = []);
        List.iteri (fun i q ->
          fill q [] (f_proj_env ~simpl:true env f i)) qs
    | QRproj (q,i) ->
        fill q (i::projs) f in

  fill qr [] f;

  let raw = PVMap.raw !map in

  Mnpv.fold (fun x (ty, pm) s ->
      let f =
        PrefixMap.build
          ~mk_proj:(f_proj_env ~simpl:true env)
          ~mk_tuple:f_tuple
          ~hnorm:(fun ty -> EcEnv.Ty.hnorm ty env)
          pm (f_pvar x ty m) ty in
      PVM.add env x m f s
    ) raw s


let qr_glob env qr =
  let iso_var = "x" in
  let iso_ty = qr_ty env qr in

  let glob = ref [] in
  let x = qrvar (pv_loc iso_var, iso_ty) in
  let rec aux x qr =
    match qr with
    | QRvar (v, ty) ->
      if is_glob v then glob := x :: !glob
    | QRtuple qs ->
      List.iteri (fun i q -> aux (qrproj (x,i)) q) qs
    | QRproj(q,i) -> aux x q in
  aux x qr;

  let iso_def = qrtuple !glob in
  { iso_var; iso_ty; iso_def }

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

let compact_iso1 env iso =
  { iso with iso_def = compact_iso env iso }

let compact_iso2 env iso =
  match iso.iso_def with
  | QRtuple [qr1; qr2] ->
      let doit q = compact_iso env {iso with iso_def = q} in
      { iso with iso_def = qrtuple [doit qr1; doit qr2] }
  | _ -> assert false

let split_pv env pv ty =
  let rec aux qr typ =
    match (Ty.hnorm typ env).ty_node with
    | Ttuple tys ->
      qrtuple (List.mapi (fun i ty -> aux (qrproj(qr, i)) ty) tys)
    | _ -> qr in
  aux (qrvar (pv,ty)) ty

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
     P, (r1, q1 = r2, q2) | => P, (r1, q1' = r2, q2')

*)

let complete_iso env iso =
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
  {iso with iso_def = qrtuple !q1}

(* build_partial_iso_qr env qr1 qr2 = iso1, iso2
   iso2 : qr1 -> r, q1
   iso2 : qr2 -> r, q2 *)

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
  let iso_q1 = complete_iso env iso in
  (* Only the missing part of qr1 is in q1 because r1 is in qr1 *)
  let q1 = apply_iso iso_q1 qr1' in
  (* we have qr1 ~ r1, q1 *)
  let iso1 = compact_iso2 env (build_iso env qr1 (qrtuple [r1; q1])) in
  let iso2 = compact_iso2 env (build_iso env qr2 (qrtuple [r1; q1'])) in

  iso1, iso2

let build_partial_iso env qe1 qe2 =
  let iso1, iso2 = build_partial_iso_qr env qe1.qel qe2.qel in
  apply_iso_qe iso1 qe1, apply_iso_qe iso2 qe2

let check_with_iso_err env qe1 qe2 =
  let iso = build_iso env qe1.qel qe2.qel in
  let _   = check_iso env iso in
  let qe1 = apply_iso_qe iso qe1 in
  EcReduction.EqTest.for_qe env ~norm:true qe1 qe2

let has_iso env qe1 qe2 =
  try check_with_iso_err env qe1 qe2
  with MissingSubterm _ | NotFull _ -> false

let ensure_iso ~who tc qe1 qe2 =
  let env = FApi.tc1_env tc in
  match check_with_iso_err env qe1 qe2 with
  | true -> ()

  | false ->
    let ppe = EcPrinting.PPEnv.ofenv env in
    tc_error !!tc ~who "@[not able to find a iso-reference between@ %a@ and@ %a@]"
      (EcPrinting.pp_qe ppe) qe1
      (EcPrinting.pp_qe ppe) qe2

  | exception (MissingSubterm missing) ->
    let ppe = EcPrinting.PPEnv.ofenv env in
    tc_error !!tc ~who "@[not able to find a iso-reference between@ %a@ and@ %a@ %a@]"
      (EcPrinting.pp_qe ppe) qe1
      (EcPrinting.pp_qe ppe) qe2
      (pp_missing env) missing

  | exception (NotFull iso) ->
    let ppe = EcPrinting.PPEnv.ofenv env in
    tc_error !!tc ~who "@[not able to find a iso-reference between@ %a@ and@ %a@ %a@]"
      (EcPrinting.pp_qe ppe) qe1
      (EcPrinting.pp_qe ppe) qe2
      (pp_missing env) (apply_iso iso qe1.qel, qe2.qel)


let ensure_iso_qr ~who tc qr1 qr2 =
  let env = FApi.tc1_env tc in
  try
    let iso = build_iso env qr1 qr2 in
    check_iso env iso;
    let qr1 = apply_iso iso qr1 in
    if EcReduction.EqTest.for_qr env ~norm:true qr1 qr2 then iso
    else raise Not_found
  with
  | Not_found ->
    let ppe = EcPrinting.PPEnv.ofenv env in
    tc_error !!tc ~who "@[not able to find a iso-reference between@ %a@ and@ %a@]"
      (EcPrinting.pp_quantum_ref ppe) qr1
      (EcPrinting.pp_quantum_ref ppe) qr2

  | MissingSubterm missing ->
    let ppe = EcPrinting.PPEnv.ofenv env in
    tc_error !!tc ~who "@[not able to find a iso-reference between@ %a@ and@ %a@ %a@]"
      (EcPrinting.pp_quantum_ref ppe) qr1
      (EcPrinting.pp_quantum_ref ppe) qr2
      (pp_missing env) missing

  | NotFull iso ->
    let ppe = EcPrinting.PPEnv.ofenv env in
    tc_error !!tc ~who "@[not able to find a iso-reference between@ %a@ and@ %a@ %a@]"
      (EcPrinting.pp_quantum_ref ppe) qr1
      (EcPrinting.pp_quantum_ref ppe) qr2
      (pp_missing env) (apply_iso iso qr1, qr2)
