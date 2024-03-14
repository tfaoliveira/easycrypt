open EcAst
open EcEnv
open EcLowPhlGoal
open EcTypes
open EcCoreFol
open EcSymbols
open EcIdent

type env = { env_ec : EcEnv.env; env_ssa : EcIdent.t MMsym.t }

let find (m : 'a MMsym.t) (x : symbol) : 'a =
  match MMsym.all x m with
  | [res] -> res
  | _ -> assert false
  
(* ------------------------------------------------------------- *)
let rec poly_of_expr (env: env) (e: expr) : form =
  let trans_args (e: expr) =
    match e.e_node with
    | Eint i -> mk_form (Fint i) e.e_ty
    | Evar (PVloc v) -> mk_form (Flocal (find env.env_ssa v)) e.e_ty
    | Elocal v -> mk_form (Flocal (find env.env_ssa (name v))) e.e_ty
    | _ -> assert false
  in

  let decode_op (q: qsymbol) : (form list -> form) =
    match q with
    | (["Top"; "JWord"; "W8"], "+") -> (fun [a;b] -> f_int_add a b) 
    | (["Top"; "JWord"; "W8"], "*") -> (fun [a;b] -> f_int_mul a b)
    | (qs, q) -> Format.eprintf "Unknown qpath at dec_op_poly_of_cond: ";
    List.iter (Format.eprintf "%s.") qs;
    Format.eprintf "%s@." q;
    assert false
  in

  match e.e_node with
  | Eint i -> mk_form (Fint i) e.e_ty 
  | Elocal v -> mk_form (Flocal (find env.env_ssa (name v))) e.e_ty 
  | Evar (PVloc v) -> mk_form (Flocal (find env.env_ssa v)) e.e_ty 
  | Eop _  -> assert false 
  | Eapp ({e_node = Eop (p, _); _}, args) -> 
    let args = List.map trans_args args in
    let op = decode_op (EcPath.toqsymbol p) in
    op args
  | Eapp  _ -> assert false 
  | Equant _ -> assert false 
  | Elet  _  -> assert false 
  | Etuple _ -> assert false 
  | Eif   _  -> assert false 
  | Ematch _ -> assert false 
  | Eproj  _ -> assert false 

(* ------------------------------------------------------------- *)
let poly_of_instr (env: env) (inst: instr) : env * form = 
  let trans_lvar (env: env) (lv: lvalue) (ty: ty) : env * form =
    begin
      match lv with
      | LvVar (PVloc pv, _) -> 
        let id = create pv in
        let env = { env with env_ssa = MMsym.add pv id env.env_ssa } in
        (env, mk_form (Flocal id) ty)
      | _ -> assert false (* TODO *)
    end
  in

  match inst.i_node with
  | Sasgn (lv, e) -> 
    let f = poly_of_expr env e in
    let (env, fl) = trans_lvar env lv f.f_ty in
    (env, f_eq f fl)
    (* FIXME ^ find actual equality *)
  | _ -> assert false

(* ------------------------------------------------------------- *)
let rec poly_of_cond (env: env) (f: form) : form =
  let trans_args (f: form) : form =
    match f.f_node with
    | Fint i -> f
    | Flocal idn -> mk_form (Flocal (find env.env_ssa (name idn))) f.f_ty 
    | Fpvar _ -> assert false
    | _ -> assert false
  in

  let decode_op (q: qsymbol) : (form list -> form) =
    match q with
    | ["Top"; "JWord"; "W8"], "+" -> (fun [a;b] -> f_int_add a b) 
    | ["Top"; "JWord"; "W8"], "*" -> (fun [a;b] -> f_int_mul a b) 
    | (qs, q) -> Format.eprintf "Unknown qpath at dec_op_poly_of_cond: ";
    List.iter (Format.eprintf "%s.") qs;
    Format.eprintf "%s@." q;
    assert false
  in

  match f.f_node with
  | Fint   i -> f
  | Flocal idn -> mk_form (Flocal (find env.env_ssa (name idn))) f.f_ty
  | Fpvar  (pvar, mem_) -> assert false 
  | Fglob  (idn, mem) -> assert false
  | Fop    (p, tys) -> assert false
  | Fapp   ({f_node = Fop (p, _); _ }, args) -> (decode_op (EcPath.toqsymbol p)) (List.map trans_args args) 
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

