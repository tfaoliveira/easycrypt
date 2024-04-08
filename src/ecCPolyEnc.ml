open EcAst
open EcEnv
open EcLowPhlGoal
open EcTypes
open EcCoreFol
open EcSymbols
open EcIdent

let retname = "__zzz" 


type env = { (* env_ec : EcEnv.env;*) env_ssa : EcIdent.t MMsym.t }

let find (m : 'a MMsym.t) (x : symbol) : 'a option =
  match MMsym.all x m with
  | [res] -> Some res
  | _ -> None 

let decode_op (q: qsymbol) : form list -> form =
  match q with
    | ["Top"; "JWord"; "W8"], "+" 
    | ["Top"; "CoreInt"], "add"
    -> fun fs -> 
      begin match fs with 
      | [a;b] -> f_int_add a b 
      | _ -> assert false
    end
    | ["Top"; "JWord"; "W8"], "*" -> fun fs -> 
      begin match fs with
        | [a;b] -> f_int_mul a b
        | _ -> assert false
      end
    | ["Top"; "Pervasive"], "=" -> fun fs ->
        begin match fs with
        | [a;b] -> f_eq a b
        | _ -> assert false
        end
    | (qs, q) -> begin 
      Format.eprintf "Unknown qpath at dec_op_trans_expr: ";
      List.iter (Format.eprintf "%s.") qs;
      Format.eprintf "%s@." q;
      assert false
    end
  
(* ------------------------------------------------------------- *)
let rec trans_expr (env: env) (e: expr) : env * form =
  let trans_args (env: env) (e: expr) =
    match e.e_node with
    | Eint i -> (env, mk_form (Fint i) e.e_ty)
    | Evar (PVloc v) -> begin match (find env.env_ssa v) with
      | Some x -> (env, mk_form (Flocal x) e.e_ty)
      | None -> let x = create v in 
        ({env_ssa = MMsym.add v x env.env_ssa}, mk_form (Flocal x) e.e_ty)
    end
    | Elocal v -> begin match (find env.env_ssa (name v)) with
      | Some v_ when v_ = v -> (env, mk_form (Flocal v) e.e_ty)
      | Some _ -> (Format.eprintf "Inconsistent bindings for local"; assert false)
      | None -> ({env_ssa = MMsym.add (name v) v env.env_ssa}, mk_form (Flocal v) e.e_ty)
    end

    | _ -> assert false
  in

  match e.e_node with
  | Eint i -> (env, mk_form (Fint i) e.e_ty )
  | Elocal v -> begin match (find env.env_ssa (name v)) with
    | Some v_ when v_ = v -> (env, mk_form (Flocal v) e.e_ty)
    | Some _ -> (Format.eprintf "Inconsistent binding of local variable"; assert false)
    | None -> ({env_ssa = MMsym.add (name v) v env.env_ssa}, mk_form (Flocal v) e.e_ty)
  end
  | Evar (PVloc v) -> begin match (find env.env_ssa v) with
    | Some x -> (env, mk_form (Flocal x) e.e_ty)
    | None -> let x = create v in
      ({env_ssa = MMsym.add v x env.env_ssa}, mk_form (Flocal x) e.e_ty)
    end
  | Evar (_) -> assert false
  | Eop _  -> assert false 
  | Eapp ({e_node = Eop (p, _); _}, args) -> 
    let (env, args) = List.fold_left_map (fun env arg -> trans_args env arg) env args in
    let op = decode_op (EcPath.toqsymbol p) in
    (env, op args)
  | Eapp  _ -> assert false 
  | Equant _ -> assert false 
  | Elet  _  -> assert false 
  | Etuple _ -> assert false 
  | Eif   _  -> assert false 
  | Ematch _ -> assert false 
  | Eproj  _ -> assert false 

  (* FIXME: Get unique identifier for ret variable *)
let trans_ret (env: env) (rete: expr) : env * form =
  let retv = create retname in
  let env = {env_ssa = MMsym.add retname retv env.env_ssa} in
  let env, e = trans_expr env rete in
  (env, f_eq (mk_form (Flocal retv) rete.e_ty) e)

(* ------------------------------------------------------------- *)
let trans_instr (env: env) (inst: instr) : env * form = 


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
    let (env, f) = trans_expr env e in
    let (env, fl) = trans_lvar env lv f.f_ty in
    (env, f_eq f fl)
    (* FIXME ^ find actual equality *)
  | _ -> assert false

(* ------------------------------------------------------------- *)
let rec trans_form (env: env) (f: form) : env * form =
  let trans_args (env: env) (f: form) : env * form =
    match f.f_node with
    | Fint _i -> (env, f)
    | Flocal idn -> begin match (find env.env_ssa (name idn)) with
      | Some idn_ when idn = idn_ -> (env, mk_form (Flocal idn) f.f_ty)
      | Some _ -> (Format.eprintf "Inconsistent local bindings"; assert false)
      | None -> ({env_ssa = MMsym.add (name idn) idn env.env_ssa}, mk_form (Flocal idn) f.f_ty)
    end
    | Fpvar (PVloc (s), _) when s = "res" -> begin
      match (find env.env_ssa retname) with
      | Some ret -> (env, mk_form (Flocal ret) f.f_ty)
      | None -> failwith "Should have return binding at postcondition"
    end
    | Fpvar _ -> assert false
    | _ -> assert false
  in

  match f.f_node with
  | Fint   _i -> (env, f)
  | Flocal idn -> begin match (find env.env_ssa (name idn)) with
    | Some idn_ when idn = idn_ -> (env, mk_form (Flocal idn) f.f_ty)
    | Some _ -> (Format.eprintf "Inconsistent local bindings"; assert false)
    | None -> ({env_ssa = MMsym.add (name idn) idn env.env_ssa}, mk_form (Flocal idn) f.f_ty)
  end
  | Fpvar  (_pvar, _mem_) -> assert false 
  | Fglob  (_idn, _mem) -> assert false
  | Fop    (_p, _tys) -> assert false
  | Fapp   ({f_node = Fop (p, _); _ }, args) -> 
      let env, args = List.fold_left_map trans_args env args in
      (env, (decode_op (EcPath.toqsymbol p)) args)
  | Fquant (_qtf, _bndgs, _f) -> assert false
  | Fif    (_fcnd, _ft, _ff) -> assert false
  | Fmatch (_fv, _fpats, _ty) ->assert false
  | Flet   (_lpat, _flet, _flval) -> assert false
  | Fapp   (_f, _args) -> assert false
  | Ftuple (_fs) -> assert false
  | Fproj  (_f, _i) -> assert false

  | FhoareF _sHF  -> assert false
  | FhoareS _sHS -> assert false

  | FcHoareF _cHF  -> assert false
  | FcHoareS _cHS -> assert false

  | FbdHoareF _bdHF  -> assert false
  | FbdHoareS _bdHS -> assert false

  | FeHoareF _eHF -> assert false
  | FeHoareS _eHS -> assert false

  | FequivF _equivF -> assert false
  | FequivS _equivS -> assert false

  | FeagerF _eagerF -> assert false

  | Fcoe _coe -> assert false

  | Fpr _pr -> assert false

