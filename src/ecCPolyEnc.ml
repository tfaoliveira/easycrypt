open EcAst
open EcEnv
open EcLowPhlGoal
open EcTypes
open EcCoreFol
open EcCoreModules
open EcSymbols
open EcIdent

let f_int_mod (f: form) (q: form) =
  f_proj (f_int_edivz f q) 1 tint

let f_int_eq (f: form) (q: form) =
  f_app (fop_eq tint) [f;q] tbool

let print_form (env: env) (f: form) : unit = 
  let fmt = EcPrinting.pp_form (EcPrinting.PPEnv.ofenv env) in
  Format.eprintf "%a@." fmt f

let print_expr (env: env) (e: expr) : unit = 
  let fmt = EcPrinting.pp_expr (EcPrinting.PPEnv.ofenv env) in
  Format.eprintf "%a@." fmt e

let print_instr (env: env) (i: instr) : unit =
  let fmt = EcPrinting.pp_instr (EcPrinting.PPEnv.ofenv env) in
  Format.eprintf "%a@." fmt i

let print_id (env: env) (id: t) : unit = 
  let fmt = EcPrinting.pp_local (EcPrinting.PPEnv.ofenv env) in
  Format.eprintf "%a@." fmt id


(* -------------------------------------------------------- *)
(* AUXILIARY DEBUG FUNCTIONS: *)

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

(* CONSTANT NAMES: *)

let retname = "__zzz" 
let tempname = "TEMP"

(* TYPE DEFINITIONS: *)
type env = { env_ec : EcEnv.env; env_ssa : EcIdent.t MMsym.t }

(* Reduces arguments to function call to single variables, adding the needed assignments *)
let rec ssa_of_arg (env: env) (arg: expr) : env * (instr list) * expr =
  match arg.e_node with
  | Eint _ | Evar _ | Elocal _ | Eop _ -> (env, [], arg)
  | Eapp _  ->
    let env, insts, e = ssa_of_expr env arg in
    let temp = create_tagged tempname in
    let inst = i_asgn ((LvVar (PVloc (name temp), e.e_ty)), e) in
    let env = {env with env_ssa = MMsym.add (name temp) temp env.env_ssa} in
    (env, insts @ [inst], mk_expr (Elocal temp) e.e_ty)
  | _ -> assert false

(* Reduces an expression to a correct right hand side of an assignment in SSA
   Either:
   - Constant int
   - Variable (local or global)
   - Operator application to arguments which are one of the two above cases
*)
and ssa_of_expr (env: env) (e: expr) : env * (instr list) * expr =
  match e.e_node with
  | Eint _ | Evar _ | Elocal _ | Eop _ -> (env, [] , e)
  | Eapp (op, args) -> 
    let (env, insts), args = List.fold_left_map 
      (fun (env, insts) arg -> let env, ainsts, arg = ssa_of_arg env arg in ((env, insts @ ainsts), arg))
      (env, []) args
    in (env, insts, e_app op args e.e_ty)
  | _ -> assert false

let ssa_of_instr ?(strict: bool = true) (env: env) (inst: instr) : env * (instr list) =
  match inst.i_node with
  | Sasgn (lv, e) -> let env, insts, e = ssa_of_expr env e in
    begin match lv with
    | LvVar (PVloc v, ty) -> begin
      match MMsym.last v env.env_ssa with
        | None -> let id = create v in
        ({env with env_ssa = MMsym.add v id env.env_ssa}, insts @ [i_asgn (lv, e)])
        | Some _ -> let id = create_tagged v in
        let lv = LvVar (PVloc (name id), ty) in
        ({env with env_ssa = MMsym.add (name id) id env.env_ssa}, insts @ [i_asgn (lv, e)])
    end
    (* (env, insts @ [i_asgn (lv, e)]) *)
    | _ -> assert false
  end
  | _ -> if strict 
    then 
    begin 
      Format.eprintf "Only assignment supported in SSA conversion for now@.";
      assert false 
    end
    else (env, [inst])

let ssa_of_prog ?(strict: bool = true) (env: env) (body: instr list) : env * (instr list) = 
  let env, body = List.fold_left_map (ssa_of_instr ~strict:strict) env body in
  (env, List.flatten body)

type poly_op = 
  | Assign of (form -> form list -> form)
  | Eq of (form list -> form)

let decode_op (env: env) (q: qsymbol) : env * poly_op =
  match q with
  | ["Top"; "JWord"; _], "+" 
  | ["Top"; "CoreInt"], "add" -> 
  (env, 
  Assign (fun f fs -> 
    begin match fs with 
    | [a;b] -> f_eq f (f_int_add a b)
    | _ -> assert false
    end))
  | ["Top"; "JWord"; _], "*" -> 
  (env, 
  Assign (fun f fs -> 
    begin match fs with
      | [a;b] -> f_eq f (f_int_mul a b)
      | _ -> assert false
    end))
  | ["Top"; "JWord"; _], "`|>>`" -> 
    let temp = create_tagged tempname in
  ({env with env_ssa = MMsym.add (name temp) temp env.env_ssa }, 
  Assign (fun f fs -> 
    begin match fs with 
    | [a; sa] -> (* FIXME: allowing variable shift amounts for now, might change later? *)
      f_eq a @@
      f_int_add 
      (f_int_mul 
        (f_int_pow (f_int @@ BI.of_int 2) sa) 
        f) 
      (mk_form (Flocal temp) f.f_ty)
    | _ -> assert false 
    end))
  | ["Top"; "JWord"; _], "[-]" -> 
  (env, 
  Assign (fun f fs ->
    begin match fs with
    | [a] -> f_eq f (f_int_opp a)
    | _ -> assert false
    end))
  | ["Top"; "JWord"; "W2u16"], "sigextu32" -> 
  (env, 
  Assign (fun f fs ->
    begin match fs with
    | [a] -> f_eq f a
    | _ -> assert false
    end))
  | ["Top"; "JWord"; "W2u16"], "truncateu16" -> 
  (env, 
  Assign (fun f fs ->
    begin match fs with
    | [a] -> f_eq f a
    | _ -> assert false
    end))
(* FIXME: add typecast stuff *)
  | ["Top"; "JWord"; _], "of_int" -> 
  (env, 
  Assign (fun f fs ->
    begin match fs with
    | [a] -> f_eq f a
    | _ -> assert false
    end))
  | ["Top"; "JWord"; _], "to_uint" -> 
  (env, 
  Assign (fun f fs ->
    begin match fs with
    | [a] -> f_eq f a
    | _ -> assert false
    end))
  | ["Top"], "eq_mod" ->
  (env, 
  Eq (fun fs -> 
    begin match fs with (* FIXME: add list support on third argument *)
     | [a; b; c] -> 
       (f_eq
       (f_int_mod a c)
       (f_int_mod b c))
     | _ -> assert false
    end))
  | ["Top"; "Pervasive"], "=" ->
  (env, 
  Eq (fun fs ->
    begin match fs with
    | [a; b] -> f_eq a b 
    | _ -> assert false
    end))
  | (qs, q) -> 
  begin 
    Format.eprintf "Unknown qpath at dec_op_trans_expr: ";
    List.iter (Format.eprintf "%s.") qs;
    Format.eprintf "%s@." q;
    assert false
  end
  

(* ------------------------------------------------------------- *)
let rec trans_expr (env: env) (f:form) (e: expr) : env * form =
  let rec trans_arg (env: env) (e: expr) =
    match e.e_node with
    | Eint i -> (env, mk_form (Fint i) e.e_ty)
    | Evar (PVloc v) -> begin match (MMsym.last v env.env_ssa) with
      | Some x -> (env, mk_form (Flocal x) e.e_ty)
      | None -> let x = create v in 
        ({env with env_ssa = MMsym.add v x env.env_ssa}, mk_form (Flocal x) e.e_ty)
      end
    | Elocal v -> begin match (MMsym.last (name v) env.env_ssa ) with
      | Some v_ when v_ = v -> (env, mk_form (Flocal v) e.e_ty)
      | Some v_ -> (Format.eprintf "Inconsistent bindings for local %s:@." (name v_); print_id env.env_ec v; 
        print_id env.env_ec v_; assert false)
      | None -> ({env with env_ssa = MMsym.add (name v) v env.env_ssa}, mk_form (Flocal v) e.e_ty)
    end
    | _ -> let fmt = EcPrinting.pp_expr (EcPrinting.PPEnv.ofenv env.env_ec) in
            Format.eprintf "Problem expresion: %a\n" fmt e; assert false
  in

  match e.e_node with
  | Eint _ | Evar (PVloc _) | Elocal _ -> 
    let env, fv = trans_arg env e 
    in (env, f_eq f fv)
  | Eapp ({e_node = Eop (p, _); _}, args) -> 
    let (env, args) = List.fold_left_map trans_arg env args in
    let env, op = decode_op env (EcPath.toqsymbol p) in
    begin
      match op with
      | Assign op -> (env, op f args)
      | Eq _ -> Format.eprintf "Invalid operation inside procedure@.";
      print_expr env.env_ec e; assert false
    end
      
  |  _ -> (* FIXME: add error handling code *)
    assert false 

  (* FIXME: Get unique identifier for ret variable *)
let trans_ret (env: env) (rete: expr) : env * form =
  let retv = create retname in
  let env = {env with env_ec = EcEnv.Var.bind_local retv rete.e_ty env.env_ec; 
    env_ssa = MMsym.add retname retv env.env_ssa} in
  let fr = mk_form (Flocal retv) rete.e_ty in
  trans_expr env fr rete


(* ------------------------------------------------------------- *)
let trans_instr (env: env) (inst: instr) : env * form = 
  let trans_lvar (lv: lvalue) (ty: ty) : (symbol * t) * form =
    begin
      match lv with
      | LvVar (PVloc pv, _) -> 
        let id = begin match MMsym.last pv env.env_ssa with
        | Some id -> id 
        | None -> Format.eprintf "Unregistered lv %s@." pv; assert false 
        end in
        ((pv, id), mk_form (Flocal id) ty)
      | _ -> assert false (* TODO *)
    end
  in

  match inst.i_node with
  | Sasgn (lv, e) -> 
    let ((_pv, _id), fl) = trans_lvar lv tint in (* FIXME: check if hardcoded int type is ok*)
    let env, f = trans_expr env fl e in
    (env, f)
    (* ({env with env_ssa = MMsym.add pv id env.env_ssa}, f) *)
  | _ -> assert false

(* ------------------------------------------------------------- *)
(* TODO: Add logical and procesing
                                                                *)

(* Returns env 
    + list of temporaries (as f_eq forms)
    + form *)
let rec trans_form (env: env) (f: form) : env * (form list) * form =
  let trans_arg (env: env) (f: form) : (env * form) option =
    match f.f_node with (* TODO: Verify argument handling for forms*)
    | Fint _i -> Some (env, f)
    | Flocal idn -> begin match (MMsym.last (name idn) env.env_ssa ) with
      | Some idn (* when idn = idn_*) -> Some (env, mk_form (Flocal idn) f.f_ty)
      (*| Some _ -> (Format.eprintf "Inconsistent local bindings"; assert false)*)
      (* FIXME check this *)
      | None -> Some ({env with env_ssa = MMsym.add (name idn) idn env.env_ssa}, mk_form (Flocal idn) f.f_ty)
    end
    | Fpvar (PVloc (s), _) when s = "res" -> begin
      match (MMsym.last retname env.env_ssa ) with
      | Some ret -> Some (env, mk_form (Flocal ret) f.f_ty)
      | None -> assert false
    end
    | Fop    (p, _tys) -> 
    begin 
      match (EcPath.toqsymbol p) with
      | ["Top"; "Pervasive"], "true" -> Some (env, f_true)
      | (h,t) -> let () = List.iter (Format.eprintf "%s ") h in
        let () = Format.eprintf "%s\n" t in
        let fmt = EcPrinting.pp_form (EcPrinting.PPEnv.ofenv env.env_ec) in
              Format.eprintf "Problem form: %a\n" fmt f; 
              debug_print_form_variant f; assert false
    end
    | _ -> None
  in

  match f.f_node with
  | Fint _ | Flocal _ | Fpvar _ | Fop _ -> 
    let env, f = Option.get @@ trans_arg env f in (env, [], f)
  | Fapp   ({f_node = Fop (p, _); _ }, args) -> 
      let (env, temps), args = List.fold_left_map 
        (fun (env, temps) f -> let env, new_temps, arg = trans_form env f in
        (env, temps @ new_temps), arg) (env, []) args in
      begin
        match decode_op env (EcPath.toqsymbol p) with
        | (env, Assign op) ->
          let ntemp = create_tagged tempname in
          let env = {env with env_ssa = MMsym.add tempname ntemp env.env_ssa } in
          let ntf = mk_form (Flocal ntemp) tint in (* FIXME: hardcoded int type *)
          (env, (op ntf args)::temps,ntf)
        | (env, Eq op) ->
          (env, temps, op args)
      end
  (* | Fproj  (f, i) -> begin match (f, i) with (* might not be needed? *)
    | ({f_node = Fapp ({f_node = Fop (p, _); _}, _); _}, 2) ->
      let (qh, qt) = EcPath.toqsymbol p in
      List.iter (Format.eprintf "%s.") qh;
      Format.eprintf "%s" qt; assert false
    | _ -> assert false
    end *)
  | _ -> assert false (* FIXME: Add error handling code *)
  
let trans_hoare (env: env) (pre: form) (body: instr list) (ret: expr) (post: form) : env * form = 
  let env, pre_ts, pre = trans_form env pre in
  let pre_f = f_imps pre_ts pre in
  let env, body = ssa_of_prog env body in (* FIXME: check if ssa should update env or not *)
  let () = List.iter (print_instr env.env_ec) body in (* DEBUG PRINT, REMOVE LATER *)
  let env, body = List.fold_left_map trans_instr env body in
  let env, ret = trans_ret env ret in
  let prog = f_imps body ret in
  let env, post_ts, post = trans_form env post in
  let post_f = f_imps post_ts post in
  let f = f_imp pre_f @@ f_imp prog post_f in
  let ids = MMsym.fold (fun _ l acc -> l @ acc) env.env_ssa [] |> List.map (fun x -> x, GTty tint) in
  (env, f_forall ids f)
  

