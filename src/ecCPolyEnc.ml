open EcAst
open EcEnv
open EcLowPhlGoal
open EcTypes
open EcCoreFol
open EcSymbols
open EcIdent

let retname = "__zzz" 

type env = { env_ec : EcEnv.env; env_ssa : EcIdent.t MMsym.t }

(* DEBUG FUNCTION *)
let debug_print_form_variant (f: form) : unit =
  match f.f_node with
  | Fquant    _ -> Format.eprintf "Fquant\n"
  | Fif       _ -> Format.eprintf "Fif\n"
  | Fmatch    _ -> Format.eprintf "Fmatch\n"
  | Flet      _ -> Format.eprintf "Flet\n"
  | Fint      _ -> Format.eprintf "Fint\n"
  | Flocal    _ -> Format.eprintf "Flocal\n"
  | Fpvar     _ -> Format.eprintf "Fpvar\n"
  | Fglob     _ -> Format.eprintf "Fglob\n"
  | Fop       _ -> Format.eprintf "Fop\n"
  | Fapp      _ -> Format.eprintf "Fapp\n"
  | Ftuple    _ -> Format.eprintf "Ftuple\n"
  | Fproj     _ -> Format.eprintf "Fproj\n"

  | FhoareF   _ -> Format.eprintf "FhoareF\n"
  | FhoareS   _ -> Format.eprintf "FhoareS\n"

  | FcHoareF  _ -> Format.eprintf "FcHoareF\n"
  | FcHoareS  _ -> Format.eprintf "FcHoareS\n"

  | FbdHoareF _ -> Format.eprintf "FbdHoareF\n"
  | FbdHoareS _ -> Format.eprintf "FbdHoareS\n"

  | FeHoareF  _ -> Format.eprintf "FeHoareF\n"
  | FeHoareS  _ -> Format.eprintf "FeHoareS\n"

  | FequivF   _ -> Format.eprintf "FequivF\n"
  | FequivS   _ -> Format.eprintf "FequivS\n"

  | FeagerF   _ -> Format.eprintf "FeagerF\n"

  | Fcoe      _ -> Format.eprintf "Fcoe\n"

  | Fpr       _ -> Format.eprintf "Fpr\n"

(* DEBUG function*)
let debug_print_exp_variant (e: expr) : unit =
  match e.e_node with
  | Eint   _ -> Format.eprintf "Eint\n"
  | Elocal _ -> Format.eprintf "Elocal\n"
  | Evar   _ -> Format.eprintf "Evar\n"
  | Eop    _ -> Format.eprintf "Eop\n"
  | Eapp   _ -> Format.eprintf "Eapp\n"
  | Equant _ -> Format.eprintf "Equant\n"
  | Elet   _ -> Format.eprintf "Elet\n"
  | Etuple _ -> Format.eprintf "Etuple\n"
  | Eif    _ -> Format.eprintf "Eif\n"
  | Ematch _ -> Format.eprintf "Ematch\n"
  | Eproj  _ -> Format.eprintf "Eproj\n"


let op_is_rshift (q: qsymbol) : bool =
  match q with
  | ["Top"; "JWord"; _], "`|>>`" -> true
  | _ -> false

 

let decode_op (q: qsymbol) : form list -> form =
  match q with
    | ["Top"; "JWord"; "W8"], "+" 
    | ["Top"; "JWord"; "W16"], "+" 
    | ["Top"; "JWord"; "W32"], "+" 
    | ["Top"; "CoreInt"], "add"
    -> fun fs -> 
      begin match fs with 
      | [a;b] -> f_int_add a b 
      | _ -> assert false
    end
    | ["Top"; "JWord"; "W32"], "*"
    | ["Top"; "JWord"; "W8"], "*" -> fun fs -> 
      begin match fs with
        | [a;b] -> f_int_mul a b
        | _ -> assert false
      end
    | ["Top"; "JWord"; "W2u16"], "sigextu32" -> fun fs ->
      begin match fs with
      | [a] -> a
      | _ -> assert false
      end
    | ["Top"; "JWord"; "W2u16"], "truncateu16" -> fun fs ->
      begin match fs with
      | [a] -> a
      | _ -> assert false
      end
    | ["Top"; "Pervasive"], "=" -> fun fs ->
        begin match fs with
        | [a;b] -> f_eq a b
        | _ -> assert false
        end
    | ["Top"; "JWord"; "W32"], "of_int" 
    | ["Top"; "JWord"; "W16"], "of_int" 
    | ["Top"; "JWord"; "W8"], "of_int" -> fun fs ->
      begin match fs with
      | [a] -> a
      | _ -> assert false
      end
    | (qs, q) -> begin 
      Format.eprintf "Unknown qpath at dec_op_trans_expr: ";
      List.iter (Format.eprintf "%s.") qs;
      Format.eprintf "%s@." q;
      assert false
    end
  
let decode_op_args (q: qsymbol) : form list -> form =
  match q with
    | ["Top"; "JWord"; "W2u16"], "sigextu32" -> fun fs ->
      begin match fs with
      | [a] -> a
      | _ -> assert false
      end
  | ["Top"; "JWord"; "W32"], "of_int" 
  | ["Top"; "JWord"; "W16"], "of_int"   
  | ["Top"; "JWord"; "W8"], "of_int" -> fun fs ->
    begin match fs with
    | [a] -> a
    | _ -> assert false
    end
  | ["Top"; "JWord"; "W2u16"], "truncateu16" -> fun fs ->
    begin match fs with
    | [a] -> a
    | _ -> assert false
    end
  | ["Top"; "JWord"; "W16"], "[-]" -> fun fs ->
    begin match fs with
    | [a] -> f_int_opp a
    | _ -> assert false
    end
  | ["Top"; "JWord"; "W16"], "to_uint" -> fun fs ->
    begin match fs with
    | [a] -> a
    | _ -> assert false
    end
  | (h, t) -> Format.eprintf "Unknown arg operator: %a\n" 
    (fun _ s -> List.iter (Format.eprintf "%s") (fst s); Format.eprintf "%s" (snd s)) (h, t); 
    assert false



(* ------------------------------------------------------------- *)
let rec trans_expr (env: env) (e: expr) : env * form =
  let rec trans_args (env: env) (e: expr) =
    match e.e_node with
    | Eint i -> (env, mk_form (Fint i) e.e_ty)
    | Evar (PVloc v) -> begin match (MMsym.last v env.env_ssa) with
      | Some x -> (env, mk_form (Flocal x) e.e_ty)
      | None -> let x = create v in 
        ({env with env_ssa = MMsym.add v x env.env_ssa}, mk_form (Flocal x) e.e_ty)
      end
    | Elocal v -> begin match (MMsym.last (name v) env.env_ssa ) with
      | Some v_ when v_ = v -> (env, mk_form (Flocal v) e.e_ty)
      | Some _ -> (Format.eprintf "Inconsistent bindings for local"; assert false)
      | None -> ({env with env_ssa = MMsym.add (name v) v env.env_ssa}, mk_form (Flocal v) e.e_ty)
    end
    | Eapp ({e_node = Eop (p, _); _}, args) -> 
      let (env, args) = List.fold_left_map (fun env arg -> trans_args env arg) env args in
      let op = decode_op_args (EcPath.toqsymbol p) in
      (env, op args)
  
    | _ -> let fmt = EcPrinting.pp_expr (EcPrinting.PPEnv.ofenv env.env_ec) in
            Format.eprintf "Problem expresion: %a\n" fmt e; assert false
  in

  match e.e_node with
  | Eint i -> (env, mk_form (Fint i) e.e_ty )
  | Elocal v -> begin match (MMsym.last (name v) env.env_ssa ) with
    | Some v_ when v_ = v -> (env, mk_form (Flocal v) e.e_ty)
    | Some _ -> (Format.eprintf "Inconsistent binding of local variable"; assert false)
    | None -> ({env with env_ssa = MMsym.add (name v) v env.env_ssa}, mk_form (Flocal v) e.e_ty)
  end
  | Evar (PVloc v) -> begin match (MMsym.last v env.env_ssa ) with
    | Some x -> (env, mk_form (Flocal x) e.e_ty)
    | None -> let x = create v in
      ({env with env_ssa = MMsym.add v x env.env_ssa}, mk_form (Flocal x) e.e_ty)
    end
  | Eapp ({e_node = Eop (p, _); _}, args) -> 
    let (env, args) = List.fold_left_map (fun env arg -> trans_args env arg) env args in
    let op = decode_op (EcPath.toqsymbol p) in
    (env, op args)
  | Evar (_) -> assert false
  | Eop _  -> assert false 
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
  let env = {env with env_ec = EcEnv.Var.bind_local retv rete.e_ty env.env_ec; 
    env_ssa = MMsym.add retname retv env.env_ssa} in
  let env, e = trans_expr env rete in
  (env, f_eq (mk_form (Flocal retv) rete.e_ty) e)



let trans_rshift (env: env) (inst: instr) : env * form =
  let trans_lvar (env: env) (lv: lvalue) (ty: ty) : env * form =
    begin
      match lv with
      | LvVar (PVloc pv, _) -> 
        let id = create_tagged pv in
        let env = { env with env_ssa = MMsym.add pv id env.env_ssa } in
        (env, mk_form (Flocal id) ty)
      | _ -> assert false (* TODO *)
    end
  in

  let rec trans_args (env: env) (e: expr) =
    match e.e_node with
    | Eint i -> (env, mk_form (Fint i) e.e_ty)
    | Evar (PVloc v) -> begin match (MMsym.last v env.env_ssa) with
      | Some x -> (env, mk_form (Flocal x) e.e_ty)
      | None -> let x = create_tagged v in 
        ({env with env_ssa = MMsym.add v x env.env_ssa}, mk_form (Flocal x) e.e_ty)
      end
    | Elocal v -> begin match (MMsym.last (name v) env.env_ssa ) with
      | Some v_ when v_ = v -> (env, mk_form (Flocal v) e.e_ty)
      | Some _ -> (Format.eprintf "Inconsistent bindings for local"; assert false)
      | None -> ({env with env_ssa = MMsym.add (name v) v env.env_ssa}, mk_form (Flocal v) e.e_ty)
    end
    | Eapp ({e_node = Eop (p, _); _}, args) -> 
      let (env, args) = List.fold_left_map (fun env arg -> trans_args env arg) env args in
      let op = decode_op_args (EcPath.toqsymbol p) in
      (env, op args)
  
    | _ -> let fmt = EcPrinting.pp_expr (EcPrinting.PPEnv.ofenv env.env_ec) in
            Format.eprintf "Problem expresion: %a\n" fmt e; assert false
  in

  let decode_op_rshift (q: qsymbol) : form list -> form =
    match q with
    | ["Top"; "JWord"; "W32"], "`|>>`" -> fun fs ->
      begin match fs with 
      | [a; {f_node = Fint _; _} as sa] -> f_int_add 
        (f_int_mul (f_int_pow (f_int (BI.of_int 2)) sa) a) 
        (mk_form (Flocal (create_tagged "TEMP")) a.f_ty)
      | _ -> assert false 
      end
    | (_h,t) -> Format.eprintf "Unknown rshift: %s\n" t; assert false
  in

  match inst.i_node with
  | Sasgn (lv, e) -> begin
    match e.e_node with
    | Eapp ({e_node = Eop(p, _); _}, [x; sa]) -> 
      let env, x = trans_args env x in
      let op = decode_op_rshift (EcPath.toqsymbol p) in
      let env, sa = trans_expr env sa in
      let env, y = trans_lvar env lv e.e_ty in
      (env, f_eq x (op [y; sa]))
    | Eint   _ -> assert false
    | Elocal _ -> assert false
    | Evar   _ -> assert false
    | Eop    _ -> assert false
    | Eapp   _ -> assert false
    | Equant _ -> assert false
    | Elet   _ -> assert false
    | Etuple _ -> assert false
    | Eif    _ -> assert false
    | Ematch _ -> assert false
    | Eproj  _ -> assert false
    | _ -> let fmt = EcPrinting.pp_instr (EcPrinting.PPEnv.ofenv env.env_ec) in
            Format.eprintf "Bad rshift: %a\n" fmt inst; assert false
    end
    (* FIXME ^ MMsym.last actual equality? *)
  | _ -> assert false

 

(* ------------------------------------------------------------- *)
let trans_instr (env: env) (inst: instr) : env * form = 
  let trans_lvar (env: env) (lv: lvalue) (ty: ty) : env * form =
    begin
      match lv with
      | LvVar (PVloc pv, _) -> 
        let id = create_tagged pv in
        let env = { env with env_ssa = MMsym.add pv id env.env_ssa } in
        (env, mk_form (Flocal id) ty)
      | _ -> assert false (* TODO *)
    end
  in

  match inst.i_node with
  | Sasgn (_, {e_node = Eapp ({e_node = Eop(p, _); _}, _); _}) 
    when op_is_rshift (EcPath.toqsymbol p) ->
    trans_rshift env inst 
  | Sasgn (lv, e) -> 
    let (env, f) = trans_expr env e in
    let (env, fl) = trans_lvar env lv f.f_ty in
    (env, f_eq f fl)
    (* FIXME ^ MMsym.last actual equality? *)
  | _ -> assert false

(* ------------------------------------------------------------- *)
(* TODO: Add logical and procesing

                                                                *)
let rec trans_form (env: env) (f: form) : env * form =
  let rec trans_args (env: env) (f: form) : env * form =
    match f.f_node with
    | Fint _i -> (env, f)
    | Flocal idn -> begin match (MMsym.last (name idn) env.env_ssa ) with
      | Some idn (* when idn = idn_*) -> (env, mk_form (Flocal idn) f.f_ty)
      (*| Some _ -> (Format.eprintf "Inconsistent local bindings"; assert false)*)
      (* FIXME check this *)
      | None -> ({env with env_ssa = MMsym.add (name idn) idn env.env_ssa}, mk_form (Flocal idn) f.f_ty)
    end
    | Fpvar (PVloc (s), _) when s = "res" -> begin
      match (MMsym.last retname env.env_ssa ) with
      | Some ret -> (env, mk_form (Flocal ret) f.f_ty)
      | None -> failwith "Should have return binding at postcondition"
    end
    | Fapp ({f_node = Fop (p, _); _}, args) -> 
      let (env, args) = List.fold_left_map (fun env arg -> trans_args env arg) env args in
      let op = decode_op_args (EcPath.toqsymbol p) in
      (env, op args)
    | Fpvar _ -> assert false
    | Fproj  (f, i) -> begin match (f, i) with
      | ({f_node = Fapp ({f_node = Fop (p, _); _}, args); _}, 1) 
        when (EcPath.toqsymbol p) = (["Top"; "IntDiv"], "edivz") ->
        let env, args = List.fold_left_map trans_args env args in
        begin match args with
        | [a;b] -> (env, f_proj (f_int_edivz a b) 1 f.f_ty)
        | _ -> assert false
        end
      | _ -> assert false
      end 
    | _ -> let fmt = EcPrinting.pp_form (EcPrinting.PPEnv.ofenv env.env_ec) in
      debug_print_form_variant f;
      Format.eprintf " is bad form: %a\n" fmt f; assert false
  in

  match f.f_node with
  | Fint   _i -> (env, f)
  | Flocal idn -> begin match (MMsym.last (name idn) env.env_ssa ) with
    | Some idn (* when idn = idn_ *) -> (env, mk_form (Flocal idn) f.f_ty)
    (*| Some _ -> (Format.eprintf "Inconsistent local bindings"; assert false)*)
    (* FIXME check this ^*)
    | None -> ({env with env_ssa = MMsym.add (name idn) idn env.env_ssa}, mk_form (Flocal idn) f.f_ty)
  end
  | Fpvar  (_pvar, _mem_) -> assert false 
  | Fglob  (_idn, _mem) -> assert false
  | Fop    (p, _tys) -> begin match (EcPath.toqsymbol p) with
    | ["Top"; "Pervasive"], "true" -> (env, f_true)
    | (h,t) -> let () = List.iter (Format.eprintf "%s ") h in
      let () = Format.eprintf "%s\n" t in
      let fmt = EcPrinting.pp_form (EcPrinting.PPEnv.ofenv env.env_ec) in
            Format.eprintf "Problem form: %a\n" fmt f; assert false
    end
  | Fapp   ({f_node = Fop (p, _); _ }, args) -> 
      let env, args = List.fold_left_map trans_args env args in
      (env, (decode_op (EcPath.toqsymbol p)) args)
  | Fquant (_qtf, _bndgs, _f) -> assert false
  | Fif    (_fcnd, _ft, _ff) -> assert false
  | Fmatch (_fv, _fpats, _ty) ->assert false
  | Flet   (_lpat, _flet, _flval) -> assert false
  | Fapp   (_f, _args) -> assert false
  | Ftuple (_fs) -> assert false
  | Fproj  (f, i) -> begin match (f, i) with
    | ({f_node = Fapp ({f_node = Fop (p, _); _}, _); _}, 2) ->
      let (qh, qt) = EcPath.toqsymbol p in
      List.iter (Format.eprintf "%s.") qh;
      Format.eprintf "%s" qt; assert false
    | _ -> assert false
    end
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
