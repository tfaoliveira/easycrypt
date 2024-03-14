open ECAst
open ECEnv
open ECLowPhlGoal
open ECTypes
open EcCoreFol

type env = { env_ec : EcEnv.env; env_ssa : EcIdent.t MMsym.t }

let find (m : MMsym.t) (x : symbol) : 'a =
  match MMsym.all x m with
  | [res] -> res
  | _ -> assert false
  
(* ------------------------------------------------------------- *)
let rec poly_of_expr (env: env) (e: expr) : form =
  let trans_args (e: expr) =
    match e.expr_node with
    | Eint i -> mk_form (Fint i) e.ty
    | Elocal v -> mk_form (Flocal (find env.env_ssa v)) e.ty
    | Evar v -> mk_form (Fpvar (PVloc (find env.env_ssa v))) e.ty
    | _ -> assert false
  in

  let decode_op (q: qsymbol) : (form list -> form) =
    match q with
    | (["Top"; "JWord"; "W8"], "+") -> (fun args -> mk_form (Eapp fop_int_add args) tint) 
    | (["Top"; "JWord"; "W8"], "*") -> (fun args -> mk_form (Eapp fop_int_mul args) tint)
    | (qs, q) -> Format.eprintf "Unknown qpath at dec_op_poly_of_cond: ";
    List.iter (Format.eprintf "%s.") qs;
    Format.eprintf "%s@." q;
    assert false
  in

  match e.expr_node with
  | Eint i -> mk_form (Fint f) e.ty 
  | Elocal idn -> mk_form (Flocal (find env.env_ssa idn)) e.ty 
  | Evar v -> mk_form (FPvar (PVloc find env.env_ssa idn)) e.ty 
  | Eop _  -> assert false 
  | Eapp (Eop (p, _), args) -> 
    let args = List.map trans_args args in
    let op = decode_op (EcPath.toqsymbol p) in
    op args
  | Eapp  _ -> assert false 
  | Equant () -> assert false 
  | Elet  _  -> assert false 
  | Etuple _ -> assert false 
  | Eif   _  -> assert false 
  | Ematch _ -> assert false 
  | Eproj  _ -> assert false 

(* ------------------------------------------------------------- *)
let poly_of_instr (env: env) (inst: instr) : env * form = 
  let trans_lvar (env: env) (lvar) (ty: ty) : env * form =
    begin
      match lv with
      | LvVar (PVLoc pv, _) -> 
        let id = fresh pv in
        let env = {env with env.env_ssa = MMsym.add pv id env.env_ssa} in
        (env, mk_form (Flocal id) ty)
      | _ -> assert false (* TODO *)
    end
  in

  match inst.instr_node with
  | Sasgn (lv, e) -> 
    let id = fresh idn.id_symb in
    let f = poly_of_expr env e in
    let (env, fl) = trans_lvar env lv f.f_ty in
    (env, mk_form (Fapp (fop_eq fint) f fl))
    (* FIXME ^ find actual equality *)
  | _ -> assert false

(* ------------------------------------------------------------- *)
let rec poly_of_cond (env: env) (f: form) : env * form =
  let trans_args (f: form) =
    match f.f_node with
    | Fint i as f -> f 
    | Flocal idn -> mk_form (Flocal (find env.env_ssa idn)) f.f_ty 
    | Fpvar pv -> assert false
    | _ -> assert false
  in

  let decode_op (q: qsymbol) : (form list -> form) =
    match q with
    | ["Top"; "JWord"; "W8"], "+" -> (fun [a;b] as args -> mk_form (Eapp fop_int_add args)) 
    | ["Top"; "JWord"; "W8"], "*" -> (fun [a;b] as args -> mk_form (Eapp fop_int_mul args)) 
    | (qs, q) -> Format.eprintf "Unknown qpath at dec_op_poly_of_cond: ";
    List.iter (Format.eprintf "%s.") qs;
    Format.eprintf "%s@." q;
    assert false
  in

  match f.f_node with
  | Fint   i as f -> f
  | Flocal idn -> mk_form (Flocal (find env.env_ssa idn)) f.f_ty 
  | Fpvar  pvar, mem_ -> assert false 
  | Fglob  idn, mem -> assert false
  | Fop    (p, tys) -> assert false
  | Fapp   (Fop (p, _), args) -> (decode_op (EcPath.to_qsymbol p)) (trans_args args)
  | Fquant (qtf, bndgs, f) -> assert false
  | Fif    (fcnd, ft, ff) -> assert false
  | Fmatch (fv, fpats, ty) ->assert false
  | Flet   (lpat, flet, flval) -> assert false
  | Fapp   (f, args) -> assert false
  | Ftuple (fs) -> assert false
  | Fproj  (f, i) -> assert false

  | FhoareF sHF  -> assert false
  | FhoareS sHS-> assert false

  | FcHoareF cHF  -> assert false
  | FcHoareS cHS-> assert false

  | FbdHoareF bdHF  -> assert false
  | FbdHoareS bdHS-> assert false

  | FeHoareF eHF -> assert false
  | FeHoareS eHS-> assert false

  | FequivF equivF -> assert false
  | FequivS equivS-> assert false

  | FeagerF eagerF-> assert false

  | Fcoe coe-> assert false

  | Fpr pr -> assert false

