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

let print_qsymbol ((q, s): qsymbol) : unit = 
  List.iter (Format.eprintf "%s.") q;
  Format.eprintf "%s@." s

let of_seq1 (xs: 'a list) : 'a =
  match xs with
  | [a] -> a
  | _ -> assert false

let of_seq2 (xs: 'a list) : 'a * 'a =
  match xs with
  | [a;b] -> (a,b)
  | _ -> assert false


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
  | FbdHoareF _ -> Format.eprintf "FbdHoareF\n"
  | FbdHoareS _ -> Format.eprintf "FbdHoareS\n"

  | FeHoareF  _ -> Format.eprintf "FeHoareF\n"
  | FeHoareS  _ -> Format.eprintf "FeHoareS\n"

  | FequivF   _ -> Format.eprintf "FequivF\n"
  | FequivS   _ -> Format.eprintf "FequivS\n"

  | FeagerF   _ -> Format.eprintf "FeagerF\n"
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

let retname = "RET"
let tempname = "TEMP"

(* TYPE DEFINITIONS: *)
type env = { env_ec : EcEnv.env; env_ssa : EcIdent.t MMsym.t }

let update_env name id env =
  {env with env_ssa = MMsym.add name id env.env_ssa}

let mk_temp_form (env: env) (ty: ty) : env * form =
  let temp = create_tagged tempname in
  let env = update_env (name temp) temp env in
  let temp = mk_form (Flocal temp) ty in
  (env, temp)

let int_form i = f_int @@ BI.of_int i
let lshift_const_form f n = f_int_mul f @@ f_int @@ BI.(lshift one n)
let lshift_form f f_sa = match f_sa.f_node with
  | Fint n -> lshift_const_form f (BI.to_int n)
  | _ -> f_int_mul f @@ f_int_pow (int_form 2) f_sa

let bitmask_form (n:int) : form =
  let n = n+1 in
  f_int @@ BI.(sub (lshift one n) one)

let join_int_form (f_h: form) (f_l: form) (n: form) : form =
  (* assert (n.f_ty = tint); *)
  f_int_add (lshift_form f_h n) f_l

  (* split f n => f = join hb lb n, (hb, lb)*)
let split_int_form (env: env) (f: form) (n: form) : env * form * (form * form) = 
  (* assert (n.f_ty = tint); *)
  let env, hb = mk_temp_form env tint in
  let env, lb = mk_temp_form env tint in
  let f_c = join_int_form hb lb n in
  let f_c = f_eq f f_c in
  (env, f_c, (hb, lb))


(* f*f = f <=> f*(f-1) = 0*)
let is_bit_form (f: form) : form =
  f_eq f (f_int_mul f f)

let ssa_of_expr (env: env) (e: expr) : env * (instr list) * expr =
  let ssa_of_expr_aux2 (env: env) (e: expr) : env * (instr list) * expr =
    match e.e_node with
    | Eint _ | Eop _ -> (env, [] , e)
    | Evar (PVloc v) ->
      begin
        match MMsym.last v env.env_ssa with
        | Some x -> (env, [], mk_expr (Elocal x) e.e_ty)
        | None -> (env, [] , e)
      end
    | Elocal v ->
      begin
        match MMsym.last (name v) env.env_ssa with
        | Some x -> (env, [], mk_expr (Elocal x) e.e_ty)
        | None -> (env, [] , e)
      end
    | _ ->  assert false
  in

  let rec ssa_of_expr_aux (env: env) (e: expr) : env * (instr list) * expr =
    match e.e_node with
    | Eapp (op, args) ->
      let env, insts, args =
        List.fold_left (fun (env,acc1,acc2) x ->
            let env,instr,a = ssa_of_expr_aux env x in
            env, acc1 @ instr, acc2 @ [a]
          )
          (env,[],[]) args
      in
      let e = e_app op args e.e_ty in
      let temp = create_tagged tempname in
      let inst = i_asgn ((LvVar (PVloc (name temp), e.e_ty)), e) in
      update_env (name temp) temp env, insts @ [inst], mk_expr (Elocal temp) e.e_ty

    | _ -> ssa_of_expr_aux2 env e
  in

  match e.e_node with
  | Eapp (op, args) ->
    let env, insts, args =
      List.fold_left (fun (env,acc1,acc2) x ->
          let env,instr,a = ssa_of_expr_aux env x in
          env, acc1 @ instr, acc2 @ [a]
        )
        (env,[],[]) args
    in
    let e = e_app op args e.e_ty in
    env, insts , e

  | _ -> ssa_of_expr_aux2 env e

let ssa_of_instr (env: env) (inst: instr) : env * (instr list) =
  match inst.i_node with
  | Sasgn (lv, e) ->
    let env, insts, e = ssa_of_expr env e in
    begin match lv with
      | LvVar (PVloc v, ty) ->
        let id = create_tagged v in
        let lv = LvVar (PVloc (name id), ty) in
        let env = update_env v id env in
        update_env (name id) id env, insts @ [i_asgn (lv, e)]
      | _ -> assert false
    end
  | _ -> assert false

let ssa_of_prog (env: env) (body: instr list) : env * (instr list) =
  List.fold_left (fun (env,acc) x ->
      let env,i = ssa_of_instr env x in
      env, acc @ i
    )
    (env,[]) body

(* ------------------------------------------------------------- *)

let app_two_list l f =
  match l with
  | [a;b] -> f a b
  | _ -> assert false

let rec trans_expr (env: env) (lv :form list) (e: expr) : env * form list =
  let rec trans_arg (env: env) (e: expr) =
    match e.e_node with
    | Eint i -> env, mk_form (Fint i) e.e_ty
    | Evar (PVloc v) ->
      begin
        match MMsym.last v env.env_ssa with
        | Some x ->
          (env, mk_form (Flocal x) e.e_ty)
        | None ->
          let x = create_tagged v in
          update_env v x env, mk_form (Flocal x) tint
      end
    | Elocal v ->
      begin
        match MMsym.last (name v) env.env_ssa with
        | Some x ->
          env, mk_form (Flocal x) e.e_ty
        | None ->
          let x = create_tagged (name v) in
          update_env (name v) x env, mk_form (Flocal v) tint
      end
    | _ ->
      let fmt = EcPrinting.pp_expr (EcPrinting.PPEnv.ofenv env.env_ec) in
      Format.eprintf "Problem expresion: %a\n" fmt e;
      assert false
  in

  (* AUXILIARY: *)

  match e.e_node with
  | Eint _ | Evar (PVloc _) | Elocal _ ->
    let env, fv = trans_arg env e in
    let lv = of_seq1 lv in
    env, [f_eq lv fv]

  | Eapp ({e_node = Eop (p, _); _}, args) ->
    let env, args = List.fold_left_map trans_arg env args in
    begin
      match EcPath.toqsymbol p with
      | ["Top"; "CoreInt"], "add" ->
        let f_r = app_two_list args f_int_add in
        let lv = of_seq1 lv in
        env, [f_eq lv f_r]

      | ["Top"; "CoreInt"], "mul" ->
        let f_r = app_two_list args f_int_mul in
        let lv = of_seq1 lv in
        env, [f_eq lv f_r]

      (* FIXME: should add temp = temp*temp here? *)
      | ["Top"; "JWord"; "W16"], "+" -> (* FIXME: what is the correct path? *)
        let lv = of_seq1 lv in
        let env, temp = mk_temp_form env tint in
        let f_r = app_two_list args f_int_add in
        let f_l = join_int_form temp lv (int_form 16) in
        let f_t = is_bit_form temp in
        env, [f_t; f_eq f_l f_r]
      (* a + b = res + c, c = 0 *)

      | ["Top"; "JWord"; "W32"], "*" ->(* FIXME: what is the correct path? *)
        let lv = of_seq1 lv in
        let env, temp = mk_temp_form env tint in
        let f_r = app_two_list args f_int_mul in
        let f_l = join_int_form temp lv (int_form 16) in
        env, [f_eq f_r f_l]

      (* s, t' = split t 31 
         hb, lb = split t' sa 
         mask = 2^32 - 2^(32 - (sa + 1))
         1|11111111|0000000000
         1|1111111111 <- sa bits
         2^32 - 2^sa = 2^31 + 2^30 + ... + 2^sa
         s*(s-1) = 0
         res = s * mask + hb *)
      | ["Top"; "JWord"; "W32"], "`|>>`" ->
        let int_of_form (f:form) : BI.zint =
          match f.f_node with
          | Fint i -> i
          (* Need to check if variable value is constant *)
          | _ -> assert false (* FIXME: hardcoded to barret example until lookup is implemented *)
        in
        let lv = of_seq1 lv in
        let t, sa = of_seq2 args in
        let sa = int_of_form sa |> BI.to_int in
        let env, fs1, (s, t') = split_int_form env t (int_form 31) in       
        let fmask = bitmask_form sa in
        let fmask = f_int_mul fmask s in
        let fr = join_int_form fmask t' (int_form 27) in (* fmask << 27 + t'*)
        let env, fs2, (hb, _lb) = split_int_form env fr (int_form 26) in
        let f_res = f_eq hb lv in
        env, [is_bit_form s; fs1; fs2; f_res]
        (* let lv = of_seq1 lv in *)
        (* let t, sa = of_seq2 args in *)
        (* let env, fs1, (s, t') = split_int_form env t (int_form 31) in *)
        (* let env, fs2, (hb, _lb) = split_int_form env t' sa in *)
        (* let fmask = f_int_pow (int_form 2) (int_form 32) in *)
        (* let fmask = f_int_sub fmask @@ f_int_pow (int_form 2) (f_int_sub (int_form 31) sa) in *)
        (* let f_res = f_eq (f_int_add hb @@ f_int_mul s fmask) lv in *)
        (* env, [fs1; fs2; f_res] *)
      (* FIXME: check return forms*)        

      | ["Top"], "rshift_w32_int" ->
        let int_of_form (f:form) : BI.zint =
          match f.f_node with
          | Fint i -> i
          (* Need to check if variable value is constant *)
          | _ -> assert false (* FIXME: hardcoded to barret example until lookup is implemented *)
        in
        let lv = of_seq1 lv in
        let t, sa = of_seq2 args in
        let sa = int_of_form sa |> BI.to_int in
        let sa = sa + 1 in
        let env, fs1, (s, t') = split_int_form env t (int_form 31) in       
        let fmask = bitmask_form sa in
        let fmask = f_int_mul fmask s in
        let fr = join_int_form fmask t' (int_form 27) in (* fmask << 27 + t'*)
        let env, fs2, (hb, _lb) = split_int_form env fr (int_form 26) in
        let f_res = f_eq hb lv in
        env, [is_bit_form s; fs1; fs2; f_res]

      | ["Top"; "JWord"; s], "of_int" ->
        let s = match s with
        | "W8" -> 8
        | "W16" -> 16
        | "W32" -> 32
        | _ -> assert false
        in
        let lv = of_seq1 lv in
        let a = of_seq1 args in
        let env, f_a, (_tmp, res) = split_int_form env a (int_form s) in
        env, [f_a; f_eq lv res]

      (* 16bit word b = s|lb,
      s = sign bit
      (2^32 - 2^15)*s + lb *)
      | ["Top"; "JWord"; "W2u16"], "sigextu32" ->
        let lv = of_seq1 lv in
        let t = of_seq1 args in
        let env, fs, (s, t') = split_int_form env t (int_form 15) in
        let fmask = bitmask_form 17 in 
        let res = join_int_form (f_int_mul fmask s) t' (int_form 15) in
        let f_res = f_eq lv res in
        env, [is_bit_form s; fs; f_res] 

      | ["Top"; "JWord"; "W2u16"], "truncateu16" ->
        let lv = of_seq1 lv in
        let t = of_seq1 args in
        let env, temp = mk_temp_form env tint in
        env, [f_eq t (join_int_form temp lv (int_form 16))]

      (* FIXME: Check semantics and soundness *)
      | ["Top"; "JWord"; "W16"], "[-]" ->
        let lv = of_seq1 lv in
        let t = of_seq1 args in
        env, [f_eq lv @@ f_int_opp t]
        

  (* | ["Top"; "JWord"; _], "`|>>`" -> *)
  (*   let temp = create_tagged tempname in *)
  (*   ({env with env_ssa = MMsym.add (name temp) temp env.env_ssa }, *)
  (*    Assign (fun f fs -> *)
  (*        begin match fs with *)
  (*          | [a; sa] -> (\* FIXME: allowing variable shift amounts for now, might change later? *\) *)
  (*            f_eq a @@ *)
  (*            f_int_add *)
  (*              (f_int_mul *)
  (*                 (f_int_pow (f_int @@ BI.of_int 2) sa) *)
  (*                 f) *)
  (*              (mk_form (Flocal temp) f.f_ty) *)
  (*          | _ -> assert false *)
  (*        end)) *)

  (* | ["Top"; "JWord"; _], "[-]" -> *)
  (*   (env, *)
  (*    Assign (fun f fs -> *)
  (*        begin match fs with *)
  (*          | [a] -> f_eq f (f_int_opp a) *)
  (*          | _ -> assert false *)
  (*        end)) *)
  (* (\* FIXME: add typecast stuff *\) *)
  (* | ["Top"; "JWord"; _], "to_uint" -> *)
  (*   (env, *)
  (*    Assign (fun f fs -> *)
  (*        begin match fs with *)
  (*          | [a] -> f_eq f a *)
  (*          | _ -> assert false *)
  (*        end)) *)

      | qs, q -> Format.eprintf "Unregistered op: "; List.iter (Format.eprintf "%s.") qs;
        Format.eprintf "%s@." q; assert false
    end
  |  _ -> assert false (* FIXME: add error handling code *)

let trans_instr (env: env) (inst: instr) : env * form list =
  let trans_lvar (lv: lvalue) : form list =
    match lv with
    | LvVar (PVloc pv, _) ->
      let id =
        match MMsym.last pv env.env_ssa with
        | Some id -> assert (pv = name id); id
        | None -> assert false
      in
      [mk_form (Flocal id) tint]
    | LvTuple ([(PVloc _p1v, _); (PVloc _pv2, _)]) -> assert false
    | _ -> assert false
  in
  match inst.i_node with
  | Sasgn (lv, e) ->
    let fl = trans_lvar lv in
    trans_expr env fl e
  | _ -> assert false

(* ------------------------------------------------------------- *)
(* FIXME: Get unique identifier for ret variable *)
let trans_ret (env: env) (rete: expr) : env * form list =
  let retv = create_tagged retname in
  let env = update_env retname retv env in
  let env =
    {env with env_ec = EcEnv.Var.bind_local retv rete.e_ty env.env_ec}
  in
  let fr = mk_form (Flocal retv) rete.e_ty in
  trans_expr env [fr] rete

(* ------------------------------------------------------------- *)
(* TODO: Add logical and procesing
*)

let rec trans_form (env: env) (f: form) : env * form list * form =
  let rec list_of_eclist (f: form) : form list = 
    match f.f_node with
    | Fapp ({f_node = Fop (p, _); _ }, args) 
      when (EcPath.toqsymbol p = (["Top"; "List"], "::")) ->
      List.map list_of_eclist args |> List.flatten
    | Fop (p, _) when (EcPath.toqsymbol p = (["Top"; "List"], "[]")) ->
      []
    | _ -> [f]
  in

  let trans_form_list (env: env) (fs: form list) : env * form list * form list =
    let (env, dfs), fs = List.fold_left_map 
      (fun (env, dfs) f -> let env, new_dfs, fr = trans_form env f in
        (env, dfs @ new_dfs), fr) (env, []) fs in
    env, dfs, fs
  in
  
  match f.f_node with
  | Fint _i -> env, [], f
  | Flocal idn ->
    begin
      match MMsym.last (name idn) env.env_ssa with
      | Some idn -> env, [], mk_form (Flocal idn) f.f_ty
      | None -> assert false
    end
  | Fpvar (PVloc s, _) when s = "res" ->
    begin
      match MMsym.last retname env.env_ssa with
      | Some ret -> env, [], mk_form (Flocal ret) f.f_ty
      | None -> assert false
    end
  | Fop (p, _tys) ->
    begin
      match EcPath.toqsymbol p with
      | ["Top"; "Pervasive"], "true" -> env, [], f_true
      | q -> print_qsymbol q; assert false
    end
  | Fapp ({f_node = Fop (p, _); _ }, args) 
    when ((EcPath.toqsymbol p) = (["Top"], "eq_mod")) ->
        begin
          match args with
          | [a; b; c] ->
            let env, a_dfs, a = trans_form env a in
            let env, b_dfs, b = trans_form env b in
            let c = list_of_eclist c in
            let env, c_dfs, c = trans_form_list env c in
            let env, f_mod = List.fold_left 
              (fun (env, facc) f -> 
              let env, temp = mk_temp_form env tint in
                (env, f_int_add facc @@ f_int_mul temp f)) (env, int_form 0) c
            in
            let f_r = f_int_add b f_mod in
            env, a_dfs @ b_dfs @ c_dfs , f_eq a f_r
          | _ -> assert false
        end
  | Fapp ({f_node = Fop (p, _); _ }, args) ->
    let env, f_defs, args = trans_form_list env args in
    let env, new_defs, f =
      match EcPath.toqsymbol p with
      | ["Top"; "JWord"; _], "+"
      | ["Top"; "CoreInt"], "add" -> env, [], app_two_list args f_int_add
      | ["Top"; "CoreInt"], "mul"
      | ["Top"; "JWord"; _], "*" -> env, [], app_two_list args f_int_mul
      | ["Top"; "Pervasive"], "=" -> env, [], app_two_list args f_eq
      | ["Top"; "Ring"; "IntID"], "exp" -> env, [], app_two_list args f_int_pow
      | ["Top"; "JWord"; "W16"], "of_int" ->
        let w = of_seq1 args in
        let env, f_t, (_tmp, res) = split_int_form env w (int_form 16) in
        env, [f_t], res
      (* FIXME: fix output form *)
      | ["Top"; "JWord"; "W16"], "to_uint" ->
        env, [], of_seq1 args (* Conversion to int is identity? *)
      | q -> print_qsymbol q; assert false
    in
    env, f_defs @ new_defs, f
  | _ -> assert false (* equality of unknow variables : x1 = x2 *)

let trans_hoare env (pre: form) (body: instr list) (ret: expr) (post: form) : form =
  let env_ssa = MMsym.empty in (* FIXME: need to add proc args as bindings here *)
  let env = {env_ec = env; env_ssa = env_ssa } in
  let env, body = ssa_of_prog env body in (* FIXME: check if ssa should update env or not *)
  let env, intrs, ret =  ssa_of_expr env ret in
  let body = body @ intrs in
  let () = List.iter (print_instr env.env_ec) body in (* DEBUG PRINT, REMOVE LATER *)
  let env, body = List.fold_left_map trans_instr env body in
  let env, ret = trans_ret env ret in
  let env, pre_dfs, pre = trans_form env pre in
  let pre = f_imps pre_dfs pre in
  let env, post_dfs, post = trans_form env post in
  let post = f_imps post_dfs post in
  let f = f_imp pre (f_imps (List.flatten body) (f_imps ret post)) in
  let ids =
    MMsym.fold (fun _ l acc -> l @ acc) env.env_ssa [] |> List.map (fun x -> x, GTty tint)
  in
  f_forall ids f
