open EcUtils
(* open EcTyping *)
open EcFol
open EcTypes
open EcPath
open EcIdent
open EcEnv
open EcModules
open EcPattern

(* ---------------------------------------------------------------------- *)
exception Matches
exception NoMatches
exception CannotUnify
exception NoNext


type environnement = {
    env_hyps             : EcEnv.LDecl.hyps;
    env_unienv           : EcUnify.unienv;
    env_red_strat        : reduction_strategy;
    env_red_info_p       : EcReduction.reduction_info;
    env_red_info_a       : EcReduction.reduction_info;
    env_restore_unienv   : EcUnify.unienv option;
    env_subst            : Psubst.p_subst;
    env_current_binds    : pbindings;
    env_meta_restr_binds : pbindings Mid.t;
    env_fmt              : Format.formatter;
    env_ppe              : EcPrinting.PPEnv.t;
    (* FIXME : ajouter ici les stratégies *)
  }

type pat_continuation =
  | ZTop
  | Znamed     of pattern * meta_name * pbindings option * pat_continuation

  (* Zor (cont, e_list, ne) :
       - cont   : the continuation if the matching is correct
       - e_list : if not, the sorted list of next engines to try matching with
       - ne     : if no match at all, then take the nengine to go up
   *)
  | Zor        of pat_continuation * engine list * nengine

  (* Zand (before, after, cont) :
       - before : list of couples (form, pattern) that has already been checked
       - after  : list of couples (form, pattern) to check in the following
       - cont   : continuation if all the matches succeed
   *)
  | Zand       of (axiom * pattern) list
                  * (axiom * pattern) list
                  * pat_continuation

  | Zbinds     of pat_continuation * pbindings

and engine = {
    e_head         : axiom;
    e_pattern      : pattern;
    e_continuation : pat_continuation;
    e_env          : environnement;
  }

and nengine = {
    ne_continuation : pat_continuation;
    ne_env          : environnement;
  }

let restore_environnement (env : environnement) : environnement =
  match env.env_restore_unienv with
  | None -> env
  | Some unienv ->
     let dst = env.env_unienv in
     let src = unienv in
     EcUnify.UniEnv.restore dst src;
     env

let add_binds (env : environnement) (env_current_binds : (ident * gty option) list)
    : environnement =
  { env with env_current_binds }

type ismatch =
  | Match
  | NoMatch

let my_mem = EcIdent.create "new_mem"

let form_of_expr = EcFol.form_of_expr my_mem

let suffix2 (l1 : 'a list) (l2 : 'b list) : ('a list * 'a list) * ('b list * 'b list) =
  let (l12,l11), (l22,l21) = List.prefix2 (List.rev l1) (List.rev l2) in
  (List.rev l11,List.rev l12), (List.rev l21,List.rev l22)

let mem_ty_univar (ty : ty) =
  try ty_check_uni ty; true
  with
  | FoundUnivar -> false

let is_modty (m : mpath) (mt : module_type) (mr : mod_restr) (env : environnement) =
  let env = LDecl.toenv env.env_hyps in
  let ms = Mod.by_mpath_opt m env in
  match ms with
  | None -> false
  | Some ms ->
    let ms = ms.me_sig in
    try EcTyping.check_modtype_with_restrictions env m ms mt mr; true with
       | _ ->
    false



let rec map_for_all2 (f : 'a -> 'a -> 'b -> bool * 'b) (l1 : 'a list) (l2 : 'a list) (b : 'b): bool * 'b =
  match l1, l2 with
  | [],[] -> true, b
  | [], _ | _,[] -> false, b
  | a1::r1, a2::r2 ->
     let c, b = f a1 a2 b in
     if c then map_for_all2 f r1 r2 b
     else false, b


let rec eq_type (ty1 : ty) (ty2 : ty) (env : environnement) : bool * environnement =
  let unienv = EcUnify.UniEnv.copy env.env_unienv in
  (try
     EcUnify.unify (EcEnv.LDecl.toenv env.env_hyps) env.env_unienv ty1 ty2;
     true
   with
   | _ -> false),
  { env with env_restore_unienv = Some (odfl unienv env.env_restore_unienv); }

let eq_memtype (m1 : EcMemory.memtype) (m2 : EcMemory.memtype) (env : environnement) =
  EcMemory.mt_equal m1 m2, env

let rec eq_memory (m1 : EcMemory.memory) (m2 : EcMemory.memory) (_env : environnement) =
  EcMemory.mem_equal m1 m2
  (* || match Mid.find_opt m1 env.env_subst.Psubst.ps_patloc,
   *          Mid.find_opt m2 env.env_subst.Psubst.ps_patloc with
   *    | Some (Pat_Axiom (Axiom_Memory m1')),
   *      Some (Pat_Axiom (Axiom_Memory m2'))
   *         when not (EcMemory.mem_equal m1 m1')
   *              && not (EcMemory.mem_equal m2 m2') -> eq_memory m1' m2' env
   *    | Some (Pat_Axiom (Axiom_Memory m1')), _
   *         when not (EcMemory.mem_equal m1 m1') -> eq_memory m1' m2 env
   *    | _, Some (Pat_Axiom (Axiom_Memory m2'))
   *         when not (EcMemory.mem_equal m2 m2') -> eq_memory m1 m2' env
   *    | _ -> false *)

let eq_memenv (m1 : EcMemory.memenv) (m2 : EcMemory.memenv) (_env : environnement) =
  EcMemory.me_equal m1 m2

let rec eq_mpath (m1 : mpath) (m2 : mpath) (env : environnement) : bool =
  EcReduction.EqTest.for_mp (EcEnv.LDecl.toenv env.env_hyps) m1 m2
  (* then true
   * else
   * let (margsl1,margsl2),(margsr1,margsr2) = suffix2 m1.m_args m2.m_args in
   * if not (List.for_all2 (fun a b -> eq_mpath a b env) margsl2 margsr2) then false
   * else
   * match margsl1, margsr1 with
   * | [], [] -> eq_module m1.m_top m2.m_top env
   * | [], _  -> begin
   *     match m1.m_top with
   *     | `Local id1 -> begin
   *         match Mid.find_opt id1 env.env_subst.Psubst.ps_patloc with
   *         | Some (Pat_Axiom (Axiom_Mpath m1')) ->
   *            eq_mpath m1' (mpath m2.m_top margsr1) env
   *         | _ -> false
   *       end
   *     | _ -> false
   *   end
   * | _, []  -> begin
   *     match m2.m_top with
   *     | `Local id2 -> begin
   *         match Mid.find_opt id2 env.env_subst.Psubst.ps_patloc with
   *         | Some (Pat_Axiom (Axiom_Mpath m2')) ->
   *            eq_mpath (mpath m1.m_top margsl1) m2' env
   *         | _ -> false
   *       end
   *     | _ -> false
   *   end
   * | _      -> assert false *)

and eq_module (mt1 : mpath_top) (mt2 : mpath_top) (_env : environnement) =
  if EcPath.mt_equal mt1 mt2 then true
  else match mt1, mt2 with
       | `Local id1, `Local id2 -> id_equal id1 id2
       | _ -> false

let eq_xpath (x1 : xpath) (x2 : xpath) (env : environnement) : bool =
  EcReduction.EqTest.for_xp (EcEnv.LDecl.toenv env.env_hyps) x1 x2
  || (if p_equal x1.x_sub x2.x_sub then eq_mpath x1.x_top x2.x_top env
      else false)

let eq_name (n1 : meta_name) (n2 : meta_name) =
  0 = id_compare n1 n2

let eq_instr (i1 : EcModules.instr) (i2 : EcModules.instr) (env : environnement) =
  EcReduction.EqTest.for_instr (EcEnv.LDecl.toenv env.env_hyps) i1 i2

let eq_stmt (s1 : EcModules.stmt) (s2 : EcModules.stmt) (env : environnement) =
  EcReduction.EqTest.for_stmt (EcEnv.LDecl.toenv env.env_hyps) s1 s2

let eq_lvalue (lv1 : lvalue) (lv2 :lvalue) (_env : environnement) : bool =
  lv_equal lv1 lv2

let eq_op
      ((op1, lty1) : EcPath.path * EcTypes.ty list)
      ((op2, lty2) : EcPath.path * EcTypes.ty list)
      (env : environnement) =
  if EcPath.p_equal op1 op2
  then
    List.fold_left2
      (fun (b,env) ty1 ty2 ->
        let (b',env) = eq_type ty1 ty2 env
        in (b'&&b,env))
      (true,env) lty1 lty2
  else false,env

let eq_prog_var (x1 : prog_var) (x2 : prog_var) (env : environnement) =
  pv_equal x1 x2
  || (x1.pv_kind = x2.pv_kind && eq_xpath x1.pv_name x2.pv_name env)

let eq_hoarecmp (c1 : hoarecmp) (c2 : hoarecmp) (_ : environnement) : bool =
  c1 = c2


let eq_gty (gty1 : gty) (gty2 : gty) (env : environnement) : bool * environnement =
  match gty1, gty2 with
  | GTty ty1, GTty ty2 -> eq_type ty1 ty2 env
  | _,_ -> EcCoreFol.gty_equal gty1 gty2, env

let eq_sym (s1 : fun_symbol) (s2 : fun_symbol) (env : environnement) =
  match s1,s2 with
  | Sym_Form_Proj (i1,t1), Sym_Form_Proj (i2,t2) ->
     if not (i1 = i2) then false, env
     else eq_type t1 t2 env
  | Sym_Form_Pvar t1, Sym_Form_Pvar t2 | Sym_Form_App t1, Sym_Form_App t2
    | Sym_Form_Match t1, Sym_Form_Match t2 -> eq_type t1 t2 env
  | Sym_Form_Quant (q1, b1), Sym_Form_Quant (q2, b2) ->
     if not (q1 = q2) then false, env
     else
       map_for_all2
         (fun (n1,gt1) (n2,gt2) env ->
           if not (id_equal n1 n2) then false, env
           else eq_gty gt1 gt2 env) b1 b2 env
  | Sym_Form_Let lp1, Sym_Form_Let lp2 -> lp_equal lp1 lp2, env
  | Sym_Form_Prog_var k1, Sym_Form_Prog_var k2 -> k1 = k2, env
  | Sym_Quant (q1,b1), Sym_Quant (q2,b2) ->
     if not (q1 = q2) then false, env
     else
       map_for_all2
         (fun (n1,ogt1) (n2,ogt2) env ->
           if not (id_equal n1 n2) then false, env
           else match ogt1, ogt2 with
                | Some gt1, Some gt2 -> eq_gty gt1 gt2 env
                | _, _ -> true, env) b1 b2 env
  | _,_ -> s1 = s2, env

let eq_binding (id1,gt1) (id2,gt2) env =
  if not (id_equal id1 id2) then false, env
  else eq_gty gt1 gt2 env

let eq_pbinding (id1,ogt1) (id2,ogt2) env =
  match ogt1,ogt2 with
  | Some gt1, Some gt2 -> eq_binding (id1,gt1) (id2,gt2) env
  | _ -> id_equal id1 id2, env


let is_gty (p : pattern) (gty1 : gty) env = match gty1, p with
  | _, Pat_Type (_,gty2) -> eq_gty gty1 gty2 env
  | GTty ty1, (Pat_Axiom (Axiom_Form { f_ty = ty2 }
                          | Axiom_Local (_,ty2))
               | Pat_Fun_Symbol ((Sym_Form_App ty2
                                  | Sym_Form_Proj (_,ty2)
                                  | Sym_Form_Match ty2
                                  | Sym_Form_Pvar ty2),_)) ->
     eq_type ty1 ty2 env
  | GTmem _, Pat_Axiom (Axiom_MemEnv (_,mt2)) ->
     eq_gty gty1 (GTmem mt2) env
  | GTmodty (mt,mr), Pat_Axiom (Axiom_Mpath m) ->
     is_modty m mt mr env, env
  | _ -> false, env


let eq_form (f1 : form) (f2 : form) (env : environnement) =
  let eq_ty, _ = eq_type f1.f_ty f2.f_ty env in
  if eq_ty && not(ty_equal f1.f_ty f2.f_ty)
  then
    raise (Invalid_argument
             (String.concat " and "
                (List.map EcTypes.dump_ty [f1.f_ty;f2.f_ty])))
  else
    EcReduction.is_conv_param env.env_red_info_a env.env_hyps f1 f2

let rec eq_axiom (o1 : axiom) (o2 : axiom) (env : environnement) :
      bool * environnement =
  let aux o1 o2 =
    match o1,o2 with
    | Axiom_Form f1, Axiom_Form f2 ->
       eq_form f1 f2 env, env

    | Axiom_Memory m1, Axiom_Memory m2 ->
       eq_memory m1 m2 env, env

    | Axiom_MemEnv m1, Axiom_MemEnv m2 ->
       eq_memenv m1 m2 env, env

    | Axiom_Prog_Var x1, Axiom_Prog_Var x2 ->
       eq_prog_var x1 x2 env, env

    | Axiom_Op (op1,lty1), Axiom_Op (op2,lty2) ->
       eq_op (op1,lty1) (op2,lty2) env

    | Axiom_Module m1, Axiom_Module m2 ->
       eq_module m1 m2 env, env

    | Axiom_Mpath m1, Axiom_Mpath m2 ->
       eq_mpath m1 m2 env, env

    | Axiom_Mpath { m_top = mt1 ; m_args = [] }, Axiom_Module mt2
      | Axiom_Module mt1, Axiom_Mpath { m_top = mt2 ; m_args = [] } ->
       eq_module mt1 mt2 env, env

    | Axiom_Instr i1, Axiom_Instr i2 ->
       eq_instr i1 i2 env, env

    | Axiom_Stmt s1, Axiom_Stmt s2 ->
       eq_stmt s1 s2 env, env

    | Axiom_Lvalue lv1, Axiom_Lvalue lv2 ->
       eq_lvalue lv1 lv2 env, env

    | Axiom_Xpath x1, Axiom_Xpath x2 ->
       eq_xpath x1 x2 env, env

    | Axiom_Hoarecmp c1, Axiom_Hoarecmp c2 ->
       eq_hoarecmp c1 c2 env, env

    | Axiom_Local (id1,ty1), Axiom_Local (id2,ty2) ->
       let eq_ty, env = eq_type ty1 ty2 env in
       eq_ty && eq_name id1 id2, env

    | Axiom_Op (op1,lty1), Axiom_Form { f_node = Fop (op2,lty2) } ->
       eq_op (op1,lty1) (op2,lty2) env

    | Axiom_Form { f_node = Fop (op1,lty1) }, Axiom_Op (op2,lty2) ->
       eq_op (op1,lty1) (op2,lty2) env

    | Axiom_Local (id1,ty1), Axiom_Form { f_node = Flocal id2; f_ty = ty2 } ->
       let eq_ty, env = eq_type ty1 ty2 env in
       eq_ty && eq_name id1 id2, env

    | Axiom_Form { f_node = Flocal id1; f_ty = ty1 }, Axiom_Local (id2,ty2) ->
       let eq_ty, env = eq_type ty1 ty2 env in
       eq_ty && eq_name id1 id2, env

    | _,_ -> false, env
  in
  aux o1 o2

and eq_pat (p1 : pattern) (p2 : pattern) (env : environnement) =
  let env_restore_unienv = env.env_restore_unienv in
  let env = { env with env_restore_unienv = None } in
  let eq, env = match p1, p2 with
    | Pat_Anything, _ | _, Pat_Anything -> true, env
    | Pat_Instance _, _ | _, Pat_Instance _ -> assert false
    | Pat_Red_Strat (p1,red1), Pat_Red_Strat (p2,red2) ->
       if red1 == red2 then eq_pat p1 p2 env
       else false, env
    | Pat_Or lp1, Pat_Or lp2 ->
       let eq, env = map_for_all2 eq_pat lp1 lp2 env in
       eq, { env with env_restore_unienv }
    | Pat_Sub p1, Pat_Sub p2 -> eq_pat p1 p2 env
    | Pat_Type (p1,gt1), Pat_Type (p2,gt2) ->
       let eq, env = eq_gty gt1 gt2 env in
       if not eq then false, env
       else eq_pat p1 p2 env
    | Pat_Type (p1, gt1), p2 | p2, Pat_Type (p1, gt1) ->
       let eq, env = is_gty p2 gt1 env in
       if eq then eq_pat p1 p2 env
       else false, env
    | Pat_Axiom a1, Pat_Axiom a2 ->
       eq_axiom a1 a2 env
    | Pat_Fun_Symbol (s1, lp1), Pat_Fun_Symbol (s2, lp2) ->
       let eq_sym, env = eq_sym s1 s2 env in
       if not eq_sym then false, env
       else map_for_all2 eq_pat lp1 lp2 env
    | Pat_Meta_Name (p1,n1,b1), Pat_Meta_Name (p2,n2,b2) when eq_name n1 n2 ->
       let eq, env = match b1, b2 with
         | Some b1, Some b2 -> map_for_all2 eq_pbinding b1 b2 env
         | _                -> true, env in
       if not eq then false, env
       else eq_pat p1 p2 env
    | Pat_Meta_Name (_,n1,_), p2' | p2', Pat_Meta_Name (_,n1,_) -> begin
        match Mid.find_opt n1 env.env_subst.Psubst.ps_patloc with
        | Some p1' -> eq_pat p1' p2' env
        | None -> false, env
       end

    | Pat_Axiom a, Pat_Fun_Symbol (s,lp)
      | Pat_Fun_Symbol (s,lp), Pat_Axiom a -> begin
        match s, lp, a with
        | Sym_Form_If, [p1;p2;p3],
          Axiom_Form { f_node = Fif (f1,f2,f3) } ->
           let eq, env = eq_pat p1 (pat_form f1) env in
           if not eq
           then false, env
           else
           let eq, env = eq_pat p2 (pat_form f2) env in
           if not eq
           then false, env
           else eq_pat p3 (pat_form f3) env

        | Sym_Form_App pty, pop::pargs,
          Axiom_Form { f_node = Fapp (_,_) ; f_ty = fty } ->
           let eq, env = eq_type pty fty env in
           if not eq then false, env
           else
           eq_pat (Pat_Fun_Symbol(Sym_App,pop::pargs)) p2 env

        | Sym_Form_Tuple, pt,
          Axiom_Form { f_node = Ftuple ft } ->
           map_for_all2 eq_pat pt (List.map pat_form ft) env

        | Sym_Form_Proj (pi,pty), [p1],
          Axiom_Form { f_node = Fproj (f1,fi) ; f_ty = fty } when pi = fi ->
           let eq, env = eq_type pty fty env in
           if not eq then false, env
           else eq_pat p1 (pat_form f1) env

        | Sym_Form_Match pty, pop::pargs,
          Axiom_Form { f_node = Fmatch (fop,fargs,fty) }
          when 0 = List.compare_lengths pargs fargs ->
           let eq, env = eq_type pty fty env in
           if not eq then false, env
           else
           let eq, env = eq_pat pop (pat_form fop) env in
           if not eq then false, env
           else
           map_for_all2 eq_pat pargs (List.map pat_form fargs) env

        | Sym_Form_Quant (pq,pb), [p1],
          Axiom_Form { f_node = Fquant (fq,fb,f1) }
          when pq = fq ->
           let eq, env = map_for_all2 eq_binding pb fb env in
           if not eq then false, env
           else
           eq_pat p1 (pat_form f1) env

        | Sym_Form_Let plp, [p1;p2],
          Axiom_Form { f_node = Flet (flp,f1,f2) } ->
           if not (lp_equal plp flp) then false, env
           else
           let eq, env = eq_pat p1 (pat_form f1) env in
           if not eq then false, env
           else eq_pat p2 (pat_form f2) env

        | Sym_Form_Pvar pty, [ppv;pm],
          Axiom_Form { f_node = Fpvar (fpv,fm) ; f_ty = fty } ->
           let eq, env = eq_type pty fty env in
           if not eq then false, env
           else
           let eq, env = eq_pat pm (pat_memory fm) env in
           if not eq then false, env
           else
             eq_pat ppv (pat_pv fpv) env

        | Sym_Form_Prog_var k1, [p1],
          Axiom_Prog_Var { pv_name = xp ; pv_kind = k2 } when k1 = k2 ->
           eq_pat p1 (pat_xpath xp) env

        | Sym_Form_Glob, [pmp;pm],
          Axiom_Form { f_node = Fglob (fmp,fm) } ->
           let eq, env = eq_pat pm (pat_memory fm) env in
           if not eq then false, env
           else eq_pat pmp (pat_mpath fmp) env

        | Sym_Form_Hoare_F, [pr1;xp1;po1],
          Axiom_Form { f_node = FhoareF { hf_pr = pr2;
                                          hf_f  = xp2;
                                          hf_po = po2; } } ->
           map_for_all2 eq_pat [pr1;xp1;po1]
             [pat_form pr2; pat_xpath xp2; pat_form po2] env

        | Sym_Form_Hoare_S, [m1;pr1;s1;po1],
          Axiom_Form { f_node = FhoareS { hs_m  = m2;
                                          hs_pr = pr2;
                                          hs_s  = s2;
                                          hs_po = po2; } } ->
           map_for_all2 eq_pat [m1;pr1;s1;po1]
             [pat_memenv m2; pat_form pr2; pat_stmt s2; pat_form po2] env

        | Sym_Form_bd_Hoare_F, [pr1;xp1;po1;cmp1;bd1],
          Axiom_Form { f_node = FbdHoareF { bhf_pr  = pr2;
                                            bhf_f   = xp2;
                                            bhf_po  = po2;
                                            bhf_cmp = cmp2;
                                            bhf_bd  = bd2; } } ->
           map_for_all2 eq_pat [pr1;xp1;po1;cmp1;bd1]
             [pat_form pr2; pat_xpath xp2; pat_form po2; pat_cmp cmp2; pat_form bd2] env

        | Sym_Form_bd_Hoare_S, [m1;pr1;s1;po1;cmp1;bd1],
          Axiom_Form { f_node = FbdHoareS { bhs_m   = m2;
                                            bhs_pr  = pr2;
                                            bhs_s   = s2;
                                            bhs_po  = po2;
                                            bhs_cmp = cmp2;
                                            bhs_bd  = bd2; } } ->
           map_for_all2 eq_pat [m1;pr1;s1;po1;cmp1;bd1]
             [pat_memenv m2; pat_form pr2; pat_stmt s2; pat_form po2; pat_cmp cmp2; pat_form bd2] env

        | Sym_Form_Equiv_F, [pr1;xpl1;xpr1;po1],
          Axiom_Form { f_node = FequivF { ef_pr = pr2;
                                          ef_fl = xpl2;
                                          ef_fr = xpr2;
                                          ef_po = po2; } } ->
           map_for_all2 eq_pat [pr1;xpl1;xpr1;po1]
             [pat_form pr2; pat_xpath xpl2; pat_xpath xpr2; pat_form po2] env

        | Sym_Form_Equiv_S, [ml1;mr1;pr1;sl1;sr1;po1],
          Axiom_Form { f_node = FequivS { es_ml = ml2;
                                          es_mr = mr2;
                                          es_pr = pr2;
                                          es_sl = sl2;
                                          es_sr = sr2;
                                          es_po = po2; } } ->
           map_for_all2 eq_pat [ml1;mr1;pr1;sl1;sr1;po1]
             [pat_memenv ml2; pat_memenv mr2; pat_form pr2; pat_stmt sl2; pat_stmt sr2; pat_form po2] env

        | Sym_Form_Eager_F, [pr1;sl1;xpl1;xpr1;sr1;po1],
          Axiom_Form { f_node = FeagerF { eg_pr = pr2;
                                          eg_sl = sl2;
                                          eg_fl = xpl2;
                                          eg_fr = xpr2;
                                          eg_sr = sr2;
                                          eg_po = po2; } } ->
           map_for_all2 eq_pat [pr1;sl1;xpl1;xpr1;sr1;po1]
             [pat_form pr2; pat_stmt sl2; pat_xpath xpl2; pat_xpath xpr2; pat_stmt sr2; pat_form po2] env

        | Sym_Form_Pr, [m1;xp1;args1;event1],
          Axiom_Form { f_node = Fpr { pr_mem   = m2;
                                      pr_fun   = xp2;
                                      pr_args  = args2;
                                      pr_event = event2; } } ->
           map_for_all2 eq_pat [m1;xp1;args1;event1]
             [pat_memory m2; pat_xpath xp2; pat_form args2; pat_form event2] env

        | Sym_Stmt_Seq, s1, Axiom_Stmt { s_node = s2 }
             when 0 = List.compare_lengths s1 s2 ->
           map_for_all2 eq_pat s1 (List.map pat_instr s2) env

        | Sym_Instr_Assign, [lv1;e1],
          Axiom_Instr { i_node = Sasgn (lv2,e2) }
          | Sym_Instr_Sample, [lv1;e1],
            Axiom_Instr { i_node = Srnd (lv2,e2) } ->
           map_for_all2 eq_pat [lv1;e1]
             [pat_lvalue lv2; pat_form (form_of_expr e2)] env

        | Sym_Instr_Call, xp1::args1,
          Axiom_Instr { i_node = Scall (None,xp2,args2) } ->
           map_for_all2 eq_pat (xp1::args1)
             ((pat_xpath xp2)::
                (List.map (fun x -> pat_form (form_of_expr x)) args2)) env

        | Sym_Instr_Call_Lv, lv1::xp1::args1,
          Axiom_Instr { i_node = Scall (Some lv2,xp2,args2) } ->
           map_for_all2 eq_pat (lv1::xp1::args1)
             ((pat_lvalue lv2)::(pat_xpath xp2)::
                (List.map (fun x -> pat_form (form_of_expr x)) args2)) env

        | Sym_Instr_If, [cond1;st1;sf1],
          Axiom_Instr { i_node = Sif (cond2,st2,sf2) } ->
           map_for_all2 eq_pat [cond1;st1;sf1]
             [pat_form (form_of_expr cond2); pat_stmt st2; pat_stmt sf2] env

        | Sym_Instr_While, [cond1;s1],
          Axiom_Instr { i_node = Swhile (cond2,s2) } ->
           map_for_all2 eq_pat [cond1;s1]
             [pat_form (form_of_expr cond2); pat_stmt s2] env

        | Sym_Instr_Assert, [cond1],
          Axiom_Instr { i_node = Sassert cond2 } ->
           eq_pat cond1 (pat_form (form_of_expr cond2)) env

        | Sym_Xpath, [mp1;p1],
          Axiom_Xpath { x_top = mp2; x_sub = p2 } ->
           let eq, env = eq_pat p1 (pat_op p2 []) env in
           if not eq then false, env
           else
           let eq, env = eq_pat mp1 (pat_mpath mp2) env in
           eq, env

        | Sym_Mpath, [m1], Axiom_Mpath _ ->
           eq_pat m1 p2 env

        | Sym_Mpath, [mtop1], Axiom_Module _ ->
           eq_pat mtop1 p2 env

        | Sym_Mpath, mtop1::margs1,
          Axiom_Mpath { m_top = mtop2; m_args = margs2 } ->
           let (margs11,margs12), (margs21,margs22) = suffix2 margs1 margs2 in
           let mtop1 = p_mpath mtop1 margs11 in
           let mtop2 = if margs21 = [] then pat_mpath_top mtop2
                       else pat_mpath (mpath mtop2 margs21) in
           map_for_all2 eq_pat (mtop1::margs12)
             (mtop2::(List.map pat_mpath margs22)) env

        | Sym_Mpath, _, _ ->
           false, env

        | Sym_App, op1::args1,
          Axiom_Form { f_node = Fapp (op2,args2) } ->
           let (args11,args12), (args21,args22) = suffix2 args1 args2 in
           let op1 = p_app op1 args11 None in
           let op2 = f_app op2 args21
                       (EcTypes.toarrow (List.map f_ty args22) (f_ty op2)) in
           map_for_all2 eq_pat (op1::args12) (List.map pat_form (op2::args22)) env

        | Sym_Quant (q1,pb1), [p1],
          Axiom_Form { f_node = Fquant (q2,b2,f1) } when q1 = q2 ->
           let eq, env = map_for_all2 eq_pbinding pb1
                           (List.map (fun (x,y) -> x,Some y) b2) env in
           if not eq then false, env
           else
           eq_pat p1 (pat_form f1) env

        | _ -> false, env

      end
    | _, _ -> false, env
  in
  let env = if eq then env else restore_environnement env in
  eq, { env with env_restore_unienv }

let rec merge_binds bs1 bs2 env = match bs1,bs2 with
  | [], _ | _,[] -> Some (env,bs1,bs2)
  | (x,_)::_, (y,_)::_
       when List.mem_assoc x env.env_current_binds
            || List.mem_assoc y env.env_current_binds ->
     None
  | (x,ty1)::r1, (y,ty2)::r2
       when eq_name x y ->
     let eq_gty, env = eq_gty ty1 ty2 env in
     if eq_gty then
       let env =
         { env with env_current_binds = env.env_current_binds @ [y, Some ty2]; }
       in merge_binds r1 r2 env
     else
       let _ = restore_environnement env in None
  | _ -> None

(* -------------------------------------------------------------------------- *)
let pat_add_fv map (n : ident) =
  match Mid.find_opt n map with
  | None -> Mid.add n 1 map
  | Some i -> Mid.add n (i+1) map

let pat_fv_union m1 m2 =
  Mid.fold_left (fun m n _ -> pat_add_fv m n) m1 m2

let pat_fv p env =
  let rec aux (map : int Mid.t) = function
    | Pat_Anything -> map
    | Pat_Meta_Name (p,n,_) ->
       aux (pat_add_fv map n) p
    | Pat_Sub p -> aux map p
    | Pat_Or lp -> List.fold_left aux map lp
    | Pat_Instance _ -> assert false
    | Pat_Red_Strat (p,_) -> aux map p
    | Pat_Type (p,_) -> aux map p
    | Pat_Fun_Symbol (Sym_Form_Quant (_,b),lp) ->
       let map' = List.fold_left aux Mid.empty lp in
       let map' =
         Mid.filter
           (fun x _ -> not (List.exists (fun (y,_) -> id_equal x y) b))
           map' in
       pat_fv_union map map'
    | Pat_Fun_Symbol (Sym_Quant (_,b),lp) ->
       let map' = List.fold_left aux Mid.empty lp in
       let map' =
         Mid.filter
           (fun x _ -> not (List.exists (fun (y,_) -> id_equal x y) b))
           map' in
       pat_fv_union map map'
    | Pat_Fun_Symbol (_,lp) -> List.fold_left aux map lp
    | Pat_Axiom a ->
       match a with
       | Axiom_Form f -> pat_fv_union f.f_fv map
       | Axiom_Memory m -> pat_add_fv map m
       | Axiom_Instr i -> pat_fv_union map i.i_fv
       | Axiom_Stmt s -> pat_fv_union map s.s_fv
       | Axiom_MemEnv (m,_) -> pat_add_fv map m
       | Axiom_Prog_Var pv -> aux map (pat_xpath pv.pv_name)
       | Axiom_Xpath xp -> aux map (pat_mpath xp.x_top)
       | Axiom_Mpath mp ->
          if None <> EcEnv.Mod.by_mpath_opt mp (LDecl.toenv env.env_hyps)
          then map
          else
            List.fold_left aux (aux map (pat_mpath_top mp.m_top))
              (List.map pat_mpath mp.m_args)
       | Axiom_Module (`Local id) -> pat_add_fv map id
       | Axiom_Module _ -> map
       | Axiom_Local (id,_) -> pat_add_fv map id
       | Axiom_Op _ -> map
       | Axiom_Hoarecmp _ -> map
       | Axiom_Lvalue lv ->
          match lv with
          | LvVar (pv,_) -> aux map (pat_pv pv)
          | LvTuple t ->
             List.fold_left aux map (List.map (fun (x,_) -> pat_pv x) t)
          | LvMap ((_,_),pv,e,_) ->
             aux (pat_fv_union map e.e_fv) (pat_pv pv)
  in aux Mid.empty p


let restr_bds_check (env : environnement) (p : pattern) (restr : pbindings) =
  let mr = Sid.of_list (List.map fst restr) in
  let m = Mid.set_diff (pat_fv p env) mr in
  Mid.for_all (fun x _ -> LDecl.has_id x env.env_hyps) m


(* add_match can raise the exception : CannotUnify *)
let nadd_match (e : nengine) (name : meta_name) (p : pattern)
      (orb : pbindings option) : nengine =
  let env = e.ne_env in
  let subst = env.env_subst in
  let p = Psubst.p_subst subst p in
  if odfl true (omap (fun r -> restr_bds_check env p r) orb)
  then
    let env_subst = Psubst.p_bind_local subst name p in
    { e with ne_env = { env with env_subst } }
  else raise CannotUnify

let e_next (e : engine) : nengine =
  { ne_continuation = e.e_continuation;
    ne_env = e.e_env;
  }

let n_engine (a : axiom) (e_pattern : pattern) (n : nengine) =
  { e_head = a;
    e_pattern;
    e_continuation = n.ne_continuation;
    e_env = n.ne_env;
  }

let add_match (e : engine) n p b =
  n_engine e.e_head e.e_pattern (nadd_match (e_next e) n p b)

let sub_engine e p b f =
  { e with e_head = f; e_pattern = Pat_Sub p;
           e_env = { e.e_env with env_current_binds = b; }; }

let fold_left_list (f : 'a -> 'b -> 'b * 'a) (a : 'a) (l : 'b list) : 'a * 'b list =
  let rec aux a acc l = match l with
    | [] -> a,List.rev acc
    | x::rest -> let x,a = f a x in aux a (x::acc) rest in
  aux a [] l

let omap_list (default : 'a -> 'b) (f : 'a -> 'b option) (l : 'a list) : 'b list option =
  let rec aux acc there_is_Some = function
    | [] -> if there_is_Some then Some (List.rev acc) else None
    | x::rest when there_is_Some -> aux ((odfl (default x) (f x))::acc) there_is_Some rest
    | x::rest -> match f x with
                 | None -> aux ((default x)::acc) false rest
                 | Some x -> aux (x::acc) true rest in
  aux [] false l

let olist f (l : 'a list) = omap_list (fun x -> x) f l

let ofold_list default (f : 'env -> 'p -> 'a option * 'env) (e : 'env) (lp : 'p list) =
  let rec aux e acc there_is_Some = function
    | [] -> if there_is_Some then Some (List.rev acc),e else None,e
    | x::rest ->
       match f e x with
       | None,e -> aux e ((default x)::acc) there_is_Some rest
       | Some x,e -> aux e (x::acc) true rest
  in aux e [] false lp

let myomap f (o,e) = match o with
  | None -> None,e
  | Some x -> Some (f x),e

(* let rec mpath_to_pattern (m : mpath) =
 *   Pat_Fun_Symbol (Sym_Mpath, (Pat_Axiom (Axiom_Module m.m_top))
 *                              ::(List.map mpath_to_pattern m.m_args))
 *
 * let rec pat_of_mpath (m : mpath) =
 *   let args = List.map pat_of_mpath m.m_args in
 *   let m = Pat_Axiom (Axiom_Module m.m_top) in
 *   Pat_Fun_Symbol (Sym_Mpath, m::args)
 *
 * let rec pat_of_xpath (x : xpath) =
 *   Pat_Fun_Symbol (Sym_Xpath, [Pat_Axiom (Axiom_Op (x.x_sub,[])); pat_of_mpath x.x_top]) *)


(* ---------------------------------------------------------------------- *)
let rec expr_of_form f : expr = match f.f_node with
  | Fquant (q,bds,f1) ->
     let q = match q with
       | Llambda -> `ELambda
       | Lexists -> `EExists
       | Lforall -> `EForall in
     e_quantif q (List.map (fun (x,y) -> (x,gty_as_ty y)) bds) (expr_of_form f1)
  | Fif (f1,f2,f3) ->
     e_if (expr_of_form f1) (expr_of_form f2) (expr_of_form f3)
  | Fmatch (f1,fargs,ty) ->
     e_match (expr_of_form f1) (List.map expr_of_form fargs) ty
  | Flet (lv,f1,f2) ->
     e_let lv (expr_of_form f1) (expr_of_form f2)
  | Fint i -> e_int i
  | Flocal id -> e_local id f.f_ty
  | Fpvar (pv,_) -> e_var pv f.f_ty
  | Fop (op,lty) -> e_op op lty f.f_ty
  | Fapp (op,args) -> e_app (expr_of_form op) (List.map expr_of_form args) f.f_ty
  | Ftuple t -> e_tuple (List.map expr_of_form t)
  | Fproj (f1,i) -> e_proj (expr_of_form f1) i f.f_ty
  | FhoareF _
    | Fglob _
    | FhoareS _
    | FbdHoareF _
    | FbdHoareS _
    | FequivF _
    | FequivS _
    | FeagerF _
    | Fpr _ -> assert false


let rewrite_term e f = Psubst.p_subst e.e_env.env_subst (pat_form f)

let all_map2 (f : 'a -> 'b -> 'c -> bool * 'a) (a : 'a) (lb : 'b list)
      (lc : 'c list) : bool * 'a =
  let rec aux a1 a lb lc =
    match lb, lc with
    | [], [] -> true, a
    | [], _ | _, [] -> raise NoMatches
    | b::lb, c::lc ->
       match f a b c with
       | false, _ -> false, a1
       | true, a -> aux a1 a lb lc
  in aux a a lb lc

(* ---------------------------------------------------------------------- *)
let add_gty (id : ident) (p : pattern) (m : gty Mid.t) =
  match p with
  | Pat_Type (_,gty) -> Mid.add id gty m
  | Pat_Axiom (Axiom_Local (_,ty))
    | Pat_Axiom (Axiom_Form { f_ty = ty })
    | Pat_Fun_Symbol (Sym_Form_App ty,_)
    | Pat_Fun_Symbol (Sym_Form_Proj (_,ty),_)
    | Pat_Fun_Symbol (Sym_Form_Match ty,_)
    | Pat_Fun_Symbol (Sym_Form_Pvar ty,_)
    -> Mid.add id (GTty ty) m
  | Pat_Axiom (Axiom_MemEnv (_,mt)) -> Mid.add id (GTmem mt) m
  | _ -> m

let rec abstract_opt
          (other_args : Sid.t)
          (ep : pattern option * gty Mid.t * engine)
          ((arg,parg) : Name.t * pattern) :
          pattern option * gty Mid.t * engine =
  match ep with
  | None, map, e -> None, map, e
  | Some p, map, e ->
     let eq_pat' (mgty,env) p pp =
       match p, pp with
       | Pat_Meta_Name (_,n,_), _
            when Mid.mem n other_args -> false, (mgty,env)
       | _, Pat_Meta_Name (_,n,_)
            when Mid.mem n other_args -> false, (mgty,env)
       | _,_ ->
          let eq, env = eq_pat p pp env in
          if eq then eq, (add_gty arg pp (add_gty arg p mgty), env)
          else eq, (mgty, env)
     in
     let aux (mgty,env) p a =
       let rec f (mgty,env) p =
         let eq, (mgty,env) = eq_pat' (mgty,env) p a in
         if eq then
           (mgty,env), Pat_Meta_Name(Pat_Anything,arg,None)
         else
         (mgty,env), p in
       let (mgty,env), p' = p_map_fold f (mgty,env) p in
       if   p = p'
       then
         None, (mgty,env)
       else
         Some p', (mgty,env)
     in
     let p = Psubst.p_subst e.e_env.env_subst p in
     let parg = Psubst.p_subst e.e_env.env_subst parg in
     match aux (map,e.e_env) p parg with
     | None, (map,env) ->
        None, map, { e with e_env = restore_environnement env }
     | Some p, (map,env) ->
        Some p, map, { e with e_env = restore_environnement env }


(* ---------------------------------------------------------------------- *)
let rec process (e : engine) : nengine =
  let e = match e.e_env.env_red_strat
                  (Psubst.p_subst e.e_env.env_subst e.e_pattern) e.e_head with
    | None -> e
    | Some (p,a) ->
       let e_or = { e with e_pattern = p; e_head = a } in
       { e with e_continuation = Zor (e.e_continuation, [e_or], (e_next e)) }
  in
  match e.e_pattern, e.e_head with
  | Pat_Anything, _ -> next Match e

  | Pat_Meta_Name (p,name,ob), _ ->
     let env_meta_restr_binds =
       odfl e.e_env.env_meta_restr_binds
         (omap (fun b -> Mid.add name b e.e_env.env_meta_restr_binds) ob) in
     let e_env = { e.e_env with env_meta_restr_binds; } in
     process { e with
         e_pattern = p; e_env;
         e_continuation = Znamed(Pat_Axiom e.e_head,name,ob,e.e_continuation);
       }

  | Pat_Sub p, _ ->
     let le = sub_engines e p in
     process { e with
         e_pattern = p;
         e_continuation = Zor (e.e_continuation,le,e_next e);
       }

  | Pat_Type (p,ty), o2 -> begin
      match o2,ty with
      | Axiom_Local (_,ty1), GTty ty2 ->
         let eq, env = eq_type ty1 ty2 e.e_env in
         if eq then
           process { e with e_pattern = p; e_env = env; }
         else next NoMatch { e with e_env = restore_environnement env }
      | Axiom_Form f, GTty ty ->
         let eq_ty, env = eq_type ty f.f_ty e.e_env in
         if eq_ty then
           process { e with e_pattern = p; e_env = env }
         else
           next NoMatch { e with e_env = restore_environnement env; }
      | Axiom_Module mtop, GTmodty (mty,mrestr) ->
         if is_modty (mpath mtop []) mty mrestr e.e_env
         then process { e with e_pattern = p }
         else next NoMatch e
      | Axiom_Mpath m, GTmodty (mty,mrestr) ->
         if is_modty m mty mrestr e.e_env
         then process { e with e_pattern = p }
         else next NoMatch e
      | Axiom_Memory _, GTmem _ -> assert false
      | Axiom_MemEnv m, GTmem mt ->
         let eq_ty, env = eq_memtype (EcMemory.memtype m) mt e.e_env in
         if eq_ty
         then process { e with e_pattern = p; e_env = env; }
         else next NoMatch { e with e_env = restore_environnement env; }
      | _ -> (* FIXME : add cases about others gty *)
         next NoMatch e
    end

  | Pat_Or [], _ -> next NoMatch e
  | Pat_Or (p::pl), _ ->
     let f p = { e with e_pattern = p; } in
     process { e with
         e_pattern = p;
         e_continuation = Zor (e.e_continuation,List.map f pl,e_next e);
       }

  | Pat_Red_Strat (e_pattern,env_red_strat),_ ->
     process { e with e_pattern; e_env = { e.e_env with env_red_strat; } }

  | Pat_Fun_Symbol (Sym_Form_Quant (q1,bs1), [p]),
    Axiom_Form { f_node = Fquant (q2,bs2,f2) } -> begin
      (* FIXME : lambda case to be considered in higher order *)
      if not(q1 = q2) then next NoMatch e
      else
      if 0 > List.compare_lengths bs1 bs2 then next NoMatch e
      else
        let (pbs1,_), (fbs1,fbs2) = List.prefix2 bs1 bs2 in
        let env_restore_unienv = e.e_env.env_restore_unienv in
        let e = { e with e_env = { e.e_env with env_restore_unienv } } in
        let eq, env = map_for_all2 eq_gty (List.map snd pbs1) (List.map snd fbs1) e.e_env in
        if not eq then
          let e_env = restore_environnement e.e_env in
          next NoMatch { e with e_env = { e_env with env_restore_unienv } }
        else
          let f s (id1,gty1) (id2,_) = Psubst.p_bind_gty s id2 id1 gty1 in
          let s = List.fold_left2 f env.env_subst pbs1 fbs1 in
          let e_pattern = Psubst.p_subst s p in
          process { e with
              e_pattern;
              e_env = { env with env_subst = s; env_restore_unienv; };
              e_head = Axiom_Form (f_quant q2 fbs2 f2);
            }
    end

  | Pat_Axiom o1, o2 ->
     let eq_ty, env = eq_axiom o1 o2 e.e_env in
     if eq_ty then next Match { e with e_env = env }
     else next NoMatch { e with e_env = restore_environnement env }

  | Pat_Fun_Symbol(Sym_App,(Pat_Meta_Name(Pat_Anything,name,ob))::pargs),axiom
    | Pat_Fun_Symbol(Sym_App,(Pat_Meta_Name(Pat_Type(Pat_Anything,_),name,ob))::pargs),axiom
    | Pat_Fun_Symbol(Sym_Form_App _,(Pat_Meta_Name(Pat_Anything,name,ob))::pargs),axiom
    | Pat_Fun_Symbol(Sym_Form_App _,(Pat_Meta_Name(Pat_Type(Pat_Anything,_),name,ob))::pargs),axiom ->
     begin
       (* higher order *)
       let add_ident i x =
         EcIdent.create (String.concat "$" ["s";string_of_int i]),
         Psubst.p_subst e.e_env.env_subst x in
       let args = List.mapi add_ident pargs in
       let env_meta_restr_binds =
         odfl e.e_env.env_meta_restr_binds
           (omap (fun b -> Mid.add name b e.e_env.env_meta_restr_binds) ob) in
       let e = { e with e_env = { e.e_env with env_meta_restr_binds } } in
       let abstract m (p,m2,e) arg =
         let op,m,e = abstract_opt m (Some p,m2,e) arg in
         odfl p op, m, e in
       let pat, map, e =
         (* FIXME : add strategies to adapt the order of the arguments *)
         List.fold_left (abstract (Sid.of_list (List.map fst args)))
           (Psubst.p_subst e.e_env.env_subst (Pat_Axiom axiom),Mid.empty,e) args in
       let f (name,_) = (name,Mid.find_opt name map) in
       let args = List.map f args in
       (* let pat = omap (p_quant Llambda args) pat in *)
       let pat = p_quant Llambda args pat in
       let pat = Psubst.p_subst e.e_env.env_subst pat in
       (* let (pat, e) = match rewrite_pattern_opt e pat with
        *   | Some pat,e -> pat, e
        *   | None, e -> pat, e in *)
       let m,e =
         try
           (* match pat with
            * | Some pat -> *)
              let e = add_match e name pat ob in
              Match, e
           (* | _ -> raise CannotUnify *)
         with
         | CannotUnify -> NoMatch, { e with e_env = restore_environnement e.e_env }
       in
       next m e
     end

  | Pat_Fun_Symbol (symbol, lp), o2 -> begin
      match o2 with
      | Axiom_Local (_id,_ty) ->
         (* this should not appear in o2 *)
         next NoMatch e
      | Axiom_Form f -> begin
          match symbol, lp, f.f_node with
          | Sym_Form_If, p1::p2::p3::[], Fif (f1,f2,f3) ->
             let zand = [(Axiom_Form f2,p2);(Axiom_Form f3,p3)] in
             let e =
               { e with
                 e_head = Axiom_Form f1;
                 e_pattern = p1;
                 e_continuation = Zand ([],zand,e.e_continuation);
               }
             in process e
          | Sym_Form_App ty, pop :: pargs, Fapp (fop, fargs) ->
             let oe =
               let (rev_fargs2,rev_fargs1),(rev_pargs2,rev_pargs1) =
                 List.prefix2 (List.rev fargs) (List.rev pargs) in
               let fargs1,fargs2,pargs1,pargs2 =
                 List.rev rev_fargs1,List.rev rev_fargs2,
                 List.rev rev_pargs1,List.rev rev_pargs2 in
               match fargs1,pargs1 with
               | _::_,_::_ -> assert false
               | _, [] ->
                  let fop' = f_app
                               fop
                               fargs1
                               (EcTypes.toarrow (List.map f_ty fargs2) (f_ty fop))
                  in
                  let zand = List.map2 (fun x y -> Axiom_Form x, y) fargs2 pargs2 in
                  let pop = match pargs1 with
                    | [] -> pop
                    | _ -> Pat_Fun_Symbol (Sym_Form_App
                                             (* FIXME : is this the right type ?? *)
                                             ty, pop::pargs1) in
                  let zand = (Axiom_Form fop', pop)::zand in
                  let e_pattern,e_head,zand =
                    match List.rev zand with
                    | [] -> assert false
                    | (Axiom_Form f,p)::l -> p,Axiom_Form f,l
                    | _ -> assert false in
                  let e_continuation = e.e_continuation in
                  let e_continuation = Zand ([],zand,e_continuation) in
                  (* let e_list =
                   *   (\* let rp = obeta_reduce e.e_env p in *\)
                   *   let l1 =
                   *     match rp with
                   *     | None -> []
                   *     | Some e_pattern ->
                   *        [{ e with e_pattern }] in
                   *   let rf = f_betared f in
                   *   let l2 = match fop.f_node with
                   *     | Fquant (Llambda,_,_) ->
                   *        [{ e with e_head = Axiom_Form rf; }]
                   *     | _ -> [] in
                   *   l1@l2 in *)
                  (* let e_continuation = match e_list with
                   *   | [] -> e_continuation
                   *   | _ -> Zor (e_continuation,e_list,e_next e) in *)
                  Some (fun () ->
                      process { e with
                          e_pattern;
                          e_head;
                          e_continuation; })
               | [], _::_ ->
                  let p = Pat_Fun_Symbol (Sym_Form_App
                                            (* FIXME : is this the right type ?? *)
                                            ty, (pop::pargs1)) in
                  let zand = List.map2 (fun x y -> Axiom_Form x, y) fargs2 pargs2 in
                  Some (fun () ->
                      process { e with
                          e_pattern = p;
                          e_continuation = Zand ([],zand,e.e_continuation)
                    })
             in
             (odfl (fun () -> next NoMatch e) oe) ()
          | Sym_App, (Pat_Meta_Name (p,_,_))::_,_ -> begin
              match p with
              | Pat_Type _ -> assert false
              | Pat_Anything -> assert false
              | _ -> assert false
            end
          | Sym_Form_Tuple, lp, Ftuple lf
               when 0 = List.compare_lengths lp lf -> begin
              match lp, lf with
              | [], _::_ | _::_,[] -> assert false
              | [], [] -> next Match e
              | p::ptuple, f::ftuple ->
                 let zand = List.map2 (fun x y -> Axiom_Form x, y) ftuple ptuple in
                 let cont = Zand ([],zand,e.e_continuation) in
                 process { e with
                     e_pattern = p;
                     e_head = Axiom_Form f;
                     e_continuation = cont }
            end
          | Sym_Form_Proj (i,ty), [e_pattern], Fproj (f1,j) when i = j ->
             let eq_ty, e_env = eq_type ty f.f_ty e.e_env in
             if eq_ty then
               process { e with e_pattern; e_env;
                                e_head = Axiom_Form f1 }
             else next NoMatch { e with e_env = restore_environnement e_env }
          | Sym_Form_Match ty, p::pl, Fmatch (fmatch,fl,_)
               when 0 = List.compare_lengths pl fl ->
             let eq_ty, env = eq_type ty f.f_ty e.e_env in
             if eq_ty
             then
               let zand = List.map2 (fun x y -> Axiom_Form x, y) fl pl in
               process {
                   e with
                   e_pattern = p;
                   e_head = Axiom_Form fmatch;
                   e_continuation = Zand ([],zand,e.e_continuation);
                 }
             else next NoMatch { e with e_env = restore_environnement env }
          | Sym_Form_Pvar ty, p1::p2::[], Fpvar (_,m) ->
             let eq_ty, env = eq_type f.f_ty ty e.e_env in
             if eq_ty
             then
               process { e with
                   e_pattern = p2;
                   e_head = Axiom_Memory m;
                   e_continuation = Zand ([],[Axiom_Form f,p1],e.e_continuation);
                 }
             else next NoMatch { e with e_env = restore_environnement env }
          | Sym_Form_Prog_var k, [p], Fpvar (x2,_) when k = x2.pv_kind ->
             process { e with
                 e_pattern = p;
                 e_head = Axiom_Xpath x2.pv_name;
               }
          | Sym_Form_Glob, p1::p2::[], Fglob (x,m) ->
             let zand = [Axiom_Mpath x,p1] in
             process { e with
                 e_pattern = p2;
                 e_head = Axiom_Memory m;
                 e_continuation = Zand ([],zand,e.e_continuation);
               }
          | Sym_Form_Hoare_F, [ppre;px;ppost], FhoareF hF ->
             let fpre,fx,fpost = hF.hf_pr,hF.hf_f,hF.hf_po in
             let zand = [Axiom_Form fpre,ppre;
                         Axiom_Form fpost,ppost] in
             process { e with
                 e_pattern = px;
                 e_head = Axiom_Xpath fx;
                 e_continuation = Zand ([],zand,e.e_continuation);
               }
          | Sym_Form_Hoare_S, [pmem;ppre;ps;ppost], FhoareS hs ->
             let fmem,fpre,fs,fpost = hs.hs_m,hs.hs_pr,hs.hs_s,hs.hs_po in
             let zand = [Axiom_Form fpre,ppre;
                         Axiom_Form fpost,ppost;
                         Axiom_Stmt fs,ps] in
             process { e with
                 e_pattern = pmem;
                 e_head = Axiom_MemEnv fmem;
                 e_continuation = Zand ([],zand,e.e_continuation); }
          | Sym_Form_bd_Hoare_F, [ppre;pf;ppost;pcmp;pbd], FbdHoareF bhf ->
             let fpre,ff,fpost,fcmp,fbd =
               bhf.bhf_pr,bhf.bhf_f,bhf.bhf_po,bhf.bhf_cmp,bhf.bhf_bd in
             let zand = [Axiom_Hoarecmp fcmp,pcmp;
                         Axiom_Form fbd,pbd;
                         Axiom_Form fpre,ppre;
                         Axiom_Form fpost,ppost] in
             process { e with
                 e_pattern = pf;
                 e_head = Axiom_Xpath ff;
                 e_continuation = Zand ([],zand,e.e_continuation); }
          | Sym_Form_bd_Hoare_S, [pmem;ppre;ps;ppost;pcmp;pbd], FbdHoareS bhs ->
             let fmem,fpre,fs,fpost,fcmp,fbd =
               bhs.bhs_m,bhs.bhs_pr,bhs.bhs_s,bhs.bhs_po,bhs.bhs_cmp,bhs.bhs_bd in
             let zand = [Axiom_Hoarecmp fcmp,pcmp;
                         Axiom_Form fbd,pbd;
                         Axiom_Form fpre,ppre;
                         Axiom_Form fpost,ppost;
                         Axiom_Stmt fs,ps] in
             process { e with
                 e_pattern = pmem;
                 e_head = Axiom_MemEnv fmem;
                 e_continuation = Zand ([],zand,e.e_continuation); }
          | Sym_Form_Equiv_F, [ppre;pf1;pf2;ppost], FequivF ef ->
             let fpre,ff1,ff2,fpost =
               ef.ef_pr,ef.ef_fl,ef.ef_fr,ef.ef_po in
             let zand = [Axiom_Xpath ff2,pf2;
                         Axiom_Form fpre,ppre;
                         Axiom_Form fpost,ppost] in
             process { e with
                 e_pattern = pf1;
                 e_head = Axiom_Xpath ff1;
                 e_continuation = Zand ([],zand,e.e_continuation); }
          | Sym_Form_Equiv_S, [pmem1;pmem2;ppre;ps1;ps2;ppost], FequivS es ->
             let fmem1,fmem2,fpre,fs1,fs2,fpost =
               es.es_ml,es.es_mr,es.es_pr,es.es_sl,es.es_sr,es.es_po in
             let zand = [Axiom_MemEnv fmem2,pmem2;
                         Axiom_Stmt fs1,ps1;
                         Axiom_Stmt fs2,ps2;
                         Axiom_Form fpre,ppre;
                         Axiom_Form fpost,ppost] in
             process { e with
                 e_pattern = pmem1;
                 e_head = Axiom_MemEnv fmem1;
                 e_continuation = Zand ([],zand,e.e_continuation); }
          | Sym_Form_Eager_F, [ppre;ps1;pf1;pf2;ps2;ppost], FeagerF eg ->
             let fpre,fs1,ff1,ff2,fs2,fpost =
               eg.eg_pr,eg.eg_sl,eg.eg_fl,eg.eg_fr,eg.eg_sr,eg.eg_po in
             let zand = [Axiom_Xpath ff2,pf2;
                         Axiom_Stmt fs1,ps1;
                         Axiom_Stmt fs2,ps2;
                         Axiom_Form fpre,ppre;
                         Axiom_Form fpost,ppost] in
             process { e with
                 e_pattern = pf1;
                 e_head = Axiom_Xpath ff1;
                 e_continuation = Zand ([],zand,e.e_continuation); }
          | Sym_Form_Pr, [pmem;pf;pargs;pevent], Fpr pr ->
             let fmem,ff,fargs,fevent =
               pr.pr_mem,pr.pr_fun,pr.pr_args,pr.pr_event in
             let zand = [
                 Axiom_Xpath ff,pf;
                 Axiom_Form fargs,pargs;
                 Axiom_Form fevent,pevent
               ] in
             process { e with
                 e_pattern = pmem;
                 e_head = Axiom_Memory fmem;
                 e_continuation =
                   Zand ([Axiom_Memory fmem,pmem],zand,e.e_continuation); }
          | _ -> next NoMatch e
        end

      | Axiom_Memory _ | Axiom_MemEnv _ | Axiom_Prog_Var _ | Axiom_Op _ ->
         next NoMatch e

      | Axiom_Module _ -> begin
          match symbol, lp with
          | Sym_Mpath, [p] ->
             process { e with e_pattern = p }
          | _ -> next NoMatch e
        end

      | Axiom_Mpath m -> begin
          match symbol, lp with
          | Sym_Mpath, p::rest ->
             let (pargs1,pargs2),(margs1,margs2) = suffix2 rest m.m_args in
             let zand = List.map2 (fun x y -> (Axiom_Mpath x),y) margs2 pargs2 in
             let e_continuation = match zand with
               | [] -> e.e_continuation
               | _  -> Zand ([],zand,e.e_continuation) in
             let m = match margs1 with
               | [] ->
                  Axiom_Module m.m_top
               | _  -> if margs2 = [] then Axiom_Mpath m
                       else Axiom_Mpath (mpath m.m_top margs1)
             in
             let p = match pargs1 with
               | [] -> p
               | _ ->
                  Pat_Fun_Symbol (Sym_Mpath, p::pargs1)
             in
             process { e with
                 e_pattern = p;
                 e_head = m;
                 e_continuation
               }
          | _ -> next NoMatch e

        end

      | Axiom_Instr i -> begin
          match symbol, lp, i.i_node with
          | Sym_Instr_Assign, [plv;prv], Sasgn (flv,fe)
            | Sym_Instr_Sample, [plv;prv], Srnd (flv,fe) ->
             let frv = form_of_expr fe in
             let zand = [Axiom_Form frv,prv] in
             process { e with
                 e_pattern = plv;
                 e_head = Axiom_Lvalue flv;
                 e_continuation = Zand ([],zand,e.e_continuation); }
          | Sym_Instr_Call, pf::pargs, Scall (None,ff,fargs)
               when 0 = List.compare_lengths pargs fargs ->
             let fmap x y = (Axiom_Form (form_of_expr x),y) in
             let zand = List.map2 fmap fargs pargs in
             process { e with
                 e_pattern = pf;
                 e_head = Axiom_Xpath ff;
                 e_continuation = Zand ([],zand,e.e_continuation); }
          | Sym_Instr_Call_Lv, plv::pf::pargs, Scall (Some flv,ff,fargs) ->
             let fmap x y = (Axiom_Form (form_of_expr x),y) in
             let zand = List.map2 fmap fargs pargs in
             let zand = (Axiom_Lvalue flv,plv)::zand in
             process { e with
                 e_pattern = pf;
                 e_head = Axiom_Xpath ff;
                 e_continuation = Zand ([],zand,e.e_continuation); }
          | Sym_Instr_If, [pe;ptrue;pfalse], Sif (fe,strue,sfalse) ->
             let zand = [Axiom_Stmt strue,ptrue;
                         Axiom_Stmt sfalse,pfalse] in
             process { e with
                 e_pattern = pe;
                 e_head = Axiom_Form (form_of_expr fe);
                 e_continuation = Zand ([],zand,e.e_continuation); }
          | Sym_Instr_While, [pe;pbody], Swhile (fe,fbody) ->
             let zand = [Axiom_Stmt fbody,pbody] in
             process { e with
                 e_pattern = pe;
                 e_head = Axiom_Form (form_of_expr fe);
                 e_continuation = Zand ([],zand,e.e_continuation); }
          | Sym_Instr_Assert, [pe], Sassert fe ->
             process { e with
                 e_pattern = pe;
                 e_head = Axiom_Form (form_of_expr fe);
               }
          | _ -> next NoMatch e
        end

      | Axiom_Stmt s -> begin
          match symbol,lp,s.s_node with
          | Sym_Stmt_Seq,[],[] -> next Match e
          | Sym_Stmt_Seq,pi::pl,fi::fl ->
             let pl = Pat_Fun_Symbol (Sym_Stmt_Seq, pl) in
             let zand = [Axiom_Stmt (stmt fl),pl] in
             process { e with
                 e_pattern = pi;
                 e_head = Axiom_Instr fi;
                 e_continuation = Zand ([],zand,e.e_continuation);
               }
          | _ -> next NoMatch e
        end

      | Axiom_Lvalue _ -> next NoMatch e

      | Axiom_Xpath x -> begin
          match symbol,lp with
          | Sym_Xpath, [pm;pf] ->
             let zand = [Axiom_Mpath x.x_top,pm] in
             process { e with
                 e_pattern = pf;
                 e_head = Axiom_Op (x.x_sub,[]);
                 e_continuation = Zand ([],zand,e.e_continuation); }
          | _ -> next NoMatch e
        end

      | Axiom_Hoarecmp _ -> next NoMatch e

    end

  | Pat_Instance (_,_,_,_), _ -> (* FIXME *) assert false

and next (m : ismatch) (e : engine) : nengine = next_n m (e_next e)

and next_n (m : ismatch) (e : nengine) : nengine =
  match m,e.ne_continuation with
  | NoMatch, ZTop -> raise NoMatches

  | Match, ZTop   -> e

  | NoMatch, Znamed (_f, _name, _ob, ne_continuation) ->
     next_n NoMatch { e with
         ne_continuation;
         ne_env = restore_environnement e.ne_env;
       }

  | Match, Znamed (f, name, ob, ne_continuation) ->
     let m,e =
       try
         let ne = nadd_match e name f ob in
         Match, { ne with ne_continuation; }
       with
       | CannotUnify ->
          NoMatch, { e with ne_continuation;
                            ne_env = restore_environnement e.ne_env; } in
     next_n m e

  | NoMatch, Zand (_,_,ne_continuation) ->
     next_n NoMatch { e with
         ne_continuation;
         ne_env = restore_environnement e.ne_env;
       }

  | Match, Zand (_before,[],ne_continuation) ->
     next_n Match { e with ne_continuation }

  | Match, Zand (before,(f,p)::after,z) ->
     let p = Psubst.p_subst e.ne_env.env_subst p in
     process (n_engine f p
                { e with ne_continuation = Zand ((f,p)::before,after,z)})

  | Match, Zor (ne_continuation, _, _) -> next_n Match { e with ne_continuation }

  | NoMatch, Zor (_, [], ne) ->
     next_n NoMatch { ne with ne_env = restore_environnement e.ne_env; }

  | NoMatch, Zor (_, e'::engines, ne) ->
     process { e' with
         e_continuation = Zor (e'.e_continuation, engines, ne);
         e_env = restore_environnement e'.e_env;
       }

  | Match, Zbinds (ne_continuation, env_current_binds) ->
     next_n Match { e with ne_continuation; ne_env = { e.ne_env with env_current_binds } }

  | NoMatch, Zbinds (ne_continuation, env_current_binds) ->
     let env = restore_environnement e.ne_env in
     let ne_env = { env with env_current_binds } in
     next_n NoMatch { e with ne_continuation; ne_env; }

and sub_engines (e : engine) (p : pattern) : engine list =
  match e.e_head with
  | Axiom_Memory _   -> []
  | Axiom_MemEnv _   -> []
  | Axiom_Prog_Var _ -> []
  | Axiom_Op _       -> []
  | Axiom_Module _   -> []
  | Axiom_Lvalue _   -> []
  | Axiom_Xpath _    -> []
  | Axiom_Hoarecmp _ -> []
  | Axiom_Mpath _    -> []
  | Axiom_Local _    -> []
  | Axiom_Instr i    -> begin
      match i.i_node with
      | Sasgn (_,expr) | Srnd (_,expr) ->
         [sub_engine e p e.e_env.env_current_binds
            (Axiom_Form (form_of_expr expr))]
      | Scall (_,_,args) ->
         List.map (fun x -> sub_engine e p e.e_env.env_current_binds
                              (Axiom_Form (form_of_expr x))) args
      | Sif (cond,strue,sfalse) ->
         [sub_engine e p e.e_env.env_current_binds
            (Axiom_Form (form_of_expr cond));
          sub_engine e p e.e_env.env_current_binds (Axiom_Stmt strue);
          sub_engine e p e.e_env.env_current_binds (Axiom_Stmt sfalse)]
      | Swhile (cond,body) ->
         [sub_engine e p e.e_env.env_current_binds
            (Axiom_Form (form_of_expr cond));
          sub_engine e p e.e_env.env_current_binds (Axiom_Stmt body)]
      | Sassert cond ->
         [sub_engine e p e.e_env.env_current_binds
            (Axiom_Form (form_of_expr cond))]
      | _ -> []
    end
  | Axiom_Stmt s ->
     List.map (fun x -> sub_engine e p e.e_env.env_current_binds (Axiom_Instr x)) s.s_node
  | Axiom_Form f -> begin
      match f.f_node with
      | Flet _
        | FhoareF _
        | FhoareS _
        | FbdHoareF _
        | FbdHoareS _
        | FequivF _
        | FequivS _
        | FeagerF _
        | Fint _
        | Flocal _
        | Fop _-> []
      | Fif (cond,f1,f2) ->
         List.map (sub_engine e p e.e_env.env_current_binds)
           [Axiom_Form cond;Axiom_Form f1;Axiom_Form f2]
      | Fapp (f, args) ->
         List.map (sub_engine e p e.e_env.env_current_binds)
           ((Axiom_Form f)::(List.map (fun x -> Axiom_Form x) args))
      | Ftuple args ->
         List.map (sub_engine e p e.e_env.env_current_binds)
           (List.map (fun x -> Axiom_Form x) args)
      | Fproj (f,_) -> [sub_engine e p e.e_env.env_current_binds (Axiom_Form f)]
      | Fmatch (f,fl,_) ->
         List.map (sub_engine e p e.e_env.env_current_binds)
           ((Axiom_Form f)::(List.map (fun x -> Axiom_Form x) fl))
      | Fpr pr ->
         List.map (sub_engine e p e.e_env.env_current_binds)
           [Axiom_Memory pr.pr_mem;
            Axiom_Form pr.pr_args;
            Axiom_Form pr.pr_event]
      | Fquant (_,bs,f) ->
         [sub_engine e p (List.map (fun (x,y) -> (x,Some y)) bs) (Axiom_Form f)]
      | Fglob (mp,mem) ->
         List.map (sub_engine e p e.e_env.env_current_binds)
           [Axiom_Module mp.m_top;Axiom_Memory mem]
      | Fpvar (_pv,mem) ->
         [sub_engine e p e.e_env.env_current_binds (Axiom_Memory mem)]
    end


let get_matches (e : engine) : Psubst.p_subst = e.e_env.env_subst
let get_n_matches (e : nengine) : Psubst.p_subst = e.ne_env.env_subst

let search_eng e =
  try Some(process e) with
  | NoMatches -> None

let pattern_of_axiom (bindings: bindings) (a : axiom) =
  let sbd           = Mid.of_list bindings in
  let pat_axiom x   = Pat_Axiom x in
  let pat_form x    = Pat_Axiom (Axiom_Form x) in
  let axiom_expr e  = Axiom_Form (form_of_expr e) in
  let axiom_mpath m = Axiom_Mpath m in
  let pat_instr i   = Pat_Axiom (Axiom_Instr i) in
  let typ ty p      = Pat_Type(p,GTty ty) in

  let rec aux a     = match a with
    | Axiom_Local (id,ty) ->
       if Mid.mem id sbd
       then Some (p_type (Pat_Meta_Name(Pat_Anything,id,None)) (GTty ty))
       else Some (pat_axiom a)
    | Axiom_Form f -> begin
        let fty = f.f_ty in
        match f.f_node with
        | Fquant(quant,binds,f)
             when Mid.set_disjoint (Sid.of_list (List.map fst binds)) sbd ->
           omap (fun fi -> typ fty (p_f_quant quant binds fi)) (aux_f f)
        | Fquant _ -> raise (Invalid_argument "quantificator on variables that are aimed to be abstracted as meta-variables.")
        | Fif(f1,f2,f3) ->
           omap (function [p1;p2;p3] -> typ fty (p_if p1 p2 p3) | _ -> assert false)
             (omap_list pat_form aux_f [f1;f2;f3])
        | Fmatch(f,args,ty) ->
           omap (function op::l -> p_match op ty l | _ -> assert false)
             (omap_list pat_form aux_f (f::args))
        | Flet (lp,f1,f2) -> begin
            match lp with
            | LSymbol (id,_) when Mid.mem id sbd ->
               raise (Invalid_argument
                        "let-operation on a variable that is aimed to be abstracted as a meta-variable.")
            | LTuple tuple when not(Mid.set_disjoint (Sid.of_list (List.map fst tuple)) sbd) ->
               raise (Invalid_argument
                        "let-operation on variables that are aimed to be abstracted as meta-variables.")
            | LRecord _ ->
               raise (Invalid_argument
                        "let-operation using the notation of fmap.")
            | _ ->
               omap (function [p1;p2] -> typ fty (p_let lp p1 p2) | _ -> assert false)
                 (omap_list pat_form aux_f [f1;f2])
          end
        | Fint _ -> None
        | Flocal id ->
           if Mid.mem id sbd
           then Some (p_type (Pat_Meta_Name(Pat_Anything,id,None)) (GTty fty))
           else if mem_ty_univar fty
           then Some (pat_local id fty)
           else None
        | Fpvar(x,m) ->
           omap (function [p1;p2] -> p_pvar p1 fty p2 | _ -> assert false)
             (omap_list pat_axiom aux [Axiom_Prog_Var x;Axiom_Memory m])
        | Fglob(mp, m) ->
           omap (function [p1;p2] -> p_glob p1 p2 | _ -> assert false)
             (omap_list pat_axiom aux [Axiom_Mpath mp;Axiom_Memory m])
        | Fop (op,lty) ->
           Some(p_type (pat_op op lty) (GTty fty))
        | Fapp ({ f_node = Flocal id },args) when Mid.mem id sbd ->
           let p =
             p_app (Pat_Meta_Name(Pat_Anything,id,None))
               (List.map (fun x ->  odfl (pat_form x) (aux_f x)) args) (Some fty) in
           Some (p_type p (GTty fty))
        | Fapp(fop,args) ->
           if mem_ty_univar fty
           then
             let pargs = List.map (fun arg -> odfl (pat_form arg) (aux_f arg)) args in
             let pop = odfl (pat_form fop) (aux_f fop) in
             Some (p_type (p_app pop pargs (Some fty)) (GTty fty))
           else
             omap (function
                 | pop::pargs ->
                    p_type (p_app pop pargs (Some fty)) (GTty fty)
                 | _ -> assert false)
               (omap_list pat_form aux_f (fop::args))
        | Ftuple args ->
           omap (fun l -> p_type (p_tuple l) (GTty fty))
             (omap_list pat_form aux_f args)
        | Fproj(f1,i) ->
           if mem_ty_univar fty
           then
             Some (p_proj (odfl (pat_form f1) (aux_f f1)) i fty)
           else
             omap (fun p -> p_proj p i fty) (aux_f f)
        | FhoareF h ->
           omap (function [p1;p2;p3] -> p_hoareF p1 p2 p3 | _ -> assert false)
             (omap_list pat_axiom aux
                [Axiom_Form h.hf_pr;
                 Axiom_Xpath h.hf_f;
                 Axiom_Form h.hf_po])
        | FhoareS h ->
           omap (function [p1;p2;p3;p4] -> p_hoareS p1 p2 p3 p4 | _ -> assert false)
             (omap_list pat_axiom aux
                [Axiom_MemEnv h.hs_m;
                 Axiom_Form h.hs_pr;
                 Axiom_Stmt h.hs_s;
                 Axiom_Form h.hs_po])
        | FbdHoareF h ->
           omap (function [p1;p2;p3;p4;p5] -> p_bdHoareF p1 p2 p3 p4 p5 | _ -> assert false)
             (omap_list pat_axiom aux
                [Axiom_Form h.bhf_pr;
                 Axiom_Xpath h.bhf_f;
                 Axiom_Form h.bhf_po;
                 Axiom_Hoarecmp h.bhf_cmp;
                 Axiom_Form h.bhf_bd])
        | FbdHoareS h ->
           omap (function [p1;p2;p3;p4;p5;p6] -> p_bdHoareS p1 p2 p3 p4 p5 p6 | _ -> assert false)
             (omap_list pat_axiom aux
                [Axiom_MemEnv h.bhs_m;
                 Axiom_Form h.bhs_pr;
                 Axiom_Stmt h.bhs_s;
                 Axiom_Form h.bhs_po;
                 Axiom_Hoarecmp h.bhs_cmp;
                 Axiom_Form h.bhs_bd])
        | FequivF h ->
           omap (function [p1;p2;p3;p4] -> p_equivF p1 p2 p3 p4 | _ -> assert false)
             (omap_list pat_axiom aux
                [Axiom_Form h.ef_pr;
                 Axiom_Xpath h.ef_fl;
                 Axiom_Xpath h.ef_fr;
                 Axiom_Form h.ef_po])
        | FequivS h ->
           omap (function [p1;p2;p3;p4;p5;p6] -> p_equivS p1 p2 p3 p4 p5 p6 | _ -> assert false)
             (omap_list pat_axiom aux
                [Axiom_MemEnv h.es_ml;
                 Axiom_MemEnv h.es_mr;
                 Axiom_Form h.es_pr;
                 Axiom_Stmt h.es_sl;
                 Axiom_Stmt h.es_sr;
                 Axiom_Form h.es_po])
        | FeagerF h ->
           omap (function [p1;p2;p3;p4;p5;p6] -> p_eagerF p1 p2 p3 p4 p5 p6 | _ -> assert false)
             (omap_list pat_axiom aux
                [Axiom_Form h.eg_pr;
                 Axiom_Stmt h.eg_sl;
                 Axiom_Xpath h.eg_fl;
                 Axiom_Xpath h.eg_fr;
                 Axiom_Stmt h.eg_sr;
                 Axiom_Form h.eg_po])
        | Fpr pr ->
           let pr_event = pr.pr_event in
           (* let mhr,memty = EcMemory.empty_local mhr pr.pr_fun in
            * let pr_event = mk_form (Fquant (Llambda,[mhr, GTmem memty],pr_event)) pr_event.f_ty in *)
           omap (function [p1;p2;p3;p4] -> p_pr p1 p2 p3 p4 | _ -> assert false)
             (omap_list pat_axiom aux
                [Axiom_Memory pr.pr_mem;
                 Axiom_Xpath pr.pr_fun;
                 Axiom_Form pr.pr_args;
                 Axiom_Form pr_event])
      end
    | Axiom_Memory m when Mid.mem m sbd ->
       (* let gty = match Mid.find_opt m sbd with
        *   | Some gty -> gty
        *   | None -> assert false in
        * Some (Pat_Type(Pat_Meta_Name(Pat_Anything,m),gty)) *)
        Some (Pat_Meta_Name(Pat_Anything,m,None))
    | Axiom_MemEnv m when Mid.mem (fst m) sbd ->
       (* let gty = match Mid.find_opt (fst m) sbd with
        *   | Some gty -> gty
        *   | None -> assert false in
        * Some (Pat_Type(Pat_Meta_Name(Pat_Anything, fst m),gty)) *)
       Some (p_type (Pat_Meta_Name(Pat_Anything, fst m, None)) (GTmem (snd m)))
    | Axiom_Prog_Var pv ->
       omap (fun x -> p_prog_var x pv.pv_kind) (aux (Axiom_Xpath pv.pv_name))
    | Axiom_Op _ -> None
    | Axiom_Module mt -> begin
        match mt with
        | `Local id when Mid.mem id sbd ->
           let gty = match Mid.find_opt id sbd with
             | Some gty -> gty
             | None -> assert false in
           Some (p_type (Pat_Meta_Name(Pat_Anything, id, None)) gty)
           (* Some (Pat_Meta_Name(Pat_Anything, id)) *)
        | _ -> None
      end
    | Axiom_Mpath m ->
       omap (function mt::margs -> p_mpath mt margs | _ -> assert false)
         (omap_list pat_axiom aux ((Axiom_Module m.m_top)::(List.map axiom_mpath m.m_args)))
    | Axiom_Instr i -> begin
        match i.i_node with
        | Sasgn (lv,e) ->
           omap (function [p1;p2] -> p_assign p1 p2 | _ -> assert false)
             (omap_list pat_axiom aux [Axiom_Lvalue lv; Axiom_Form (form_of_expr e)])
        | Srnd (lv,e) ->
           omap (function [p1;p2] -> p_sample p1 p2 | _ -> assert false)
             (omap_list pat_axiom aux [Axiom_Lvalue lv; Axiom_Form (form_of_expr e)])
        | Scall (None,f,args) ->
           omap (function p1::pargs -> p_call None p1 pargs | _ -> assert false)
             (omap_list pat_axiom aux ((Axiom_Xpath f)::(List.map axiom_expr args)))
        | Scall (Some lv,f,args) ->
           omap (function p1::p2::pargs -> p_call (Some p1) p2 pargs | _ -> assert false)
             (omap_list pat_axiom aux ((Axiom_Lvalue lv)::(Axiom_Xpath f)::(List.map axiom_expr args)))
        | Sif (e,strue,sfalse) ->
           omap (function [p1;p2;p3] -> p_instr_if p1 p2 p3 | _ -> assert false)
             (omap_list pat_axiom aux [axiom_expr e;Axiom_Stmt strue;Axiom_Stmt sfalse])
        | Swhile (e,sbody) ->
           omap (function [p1;p2] -> p_while p1 p2 | _ -> assert false)
             (omap_list pat_axiom aux [axiom_expr e;Axiom_Stmt sbody])
        | Sassert e ->
           omap (fun x -> p_assert x) (aux (axiom_expr e))
        | Sabstract id when Mid.mem id sbd ->
           Some (Pat_Meta_Name (Pat_Anything, id, None))
        | Sabstract _ -> None
      end
    | Axiom_Stmt s ->
       omap (fun l -> p_stmt l) (omap_list pat_instr aux_i s.s_node)
    | Axiom_Lvalue lv -> begin
        match lv with
        | LvVar (pv,ty) ->
           omap (fun x -> p_type x (GTty ty)) (aux (Axiom_Prog_Var pv))
        | LvTuple l ->
           let default (pv,ty) = p_type (pat_pv pv) (GTty ty) in
           let aux (pv,ty) =
             omap (fun x -> p_type x (GTty ty)) (aux (Axiom_Prog_Var pv)) in
           omap (fun l -> p_tuple l) (omap_list default aux l)
        | LvMap _ -> (* FIXME *) raise (Invalid_argument "bleuh")
      end
    | Axiom_Xpath xp ->
       omap (fun mp -> p_xpath mp (pat_op xp.x_sub []))
         (aux (Axiom_Mpath xp.x_top))
    | Axiom_Hoarecmp _ -> None
    | Axiom_MemEnv _ | Axiom_Memory _ -> None
  and aux_f f = aux (Axiom_Form f)
  and aux_i i = aux (Axiom_Instr i)
  in aux a

let rec prefix_binds bs1 bs2 =
  let rec aux acc bs1 bs2 = match bs1,bs2 with
  | (x,ty1)::r1, (y,ty2)::r2 when eq_name x y && gty_equal ty1 ty2 ->
     aux ((x,ty1)::acc) r1 r2
  | _ -> List.rev acc
  in aux [] bs1 bs2

let rec prefix_pbinds bs1 bs2 =
  let rec aux acc bs1 bs2 = match bs1,bs2 with
  | (x,Some ty1)::r1, (y,Some ty2)::r2 when eq_name x y && gty_equal ty1 ty2 ->
     aux ((x,Some ty1)::acc) r1 r2
  | (x,None)::r1, (y,Some ty1)::r2 | (x,Some ty1)::r1, (y,None)::r2
       when eq_name x y ->
     aux ((x,Some ty1)::acc) r1 r2
  | (x,None)::r1, (y,None)::r2 when eq_name x y ->
     aux ((x,None)::acc) r1 r2
  | _ -> List.rev acc
  in aux [] bs1 bs2

let add_meta_bindings (name : meta_name) (b : pbindings)
      (mbs : pbindings Mid.t) =
  match Mid.find_opt name mbs with
  | None -> Mid.add name b mbs
  | Some b' -> Mid.add name (prefix_pbinds b' b) mbs

let get_meta_bindings (p : pattern) : pbindings Mid.t =
  let rec aux current_bds meta_bds p = match p with
  | Pat_Anything -> meta_bds
  | Pat_Meta_Name (p,n,_) ->
     aux current_bds (add_meta_bindings n current_bds meta_bds) p
  | Pat_Sub p -> aux current_bds meta_bds p
  | Pat_Or lp -> List.fold_left (aux current_bds) meta_bds lp
  | Pat_Instance _ -> assert false
  | Pat_Red_Strat (p,_) -> aux current_bds meta_bds p
  | Pat_Type (p,_) -> aux current_bds meta_bds p
  | Pat_Axiom (Axiom_Form { f_node = Fquant (_,b,f) } ) ->
     let b = List.map (fun (x,y) -> (x,Some y)) b in
     aux (current_bds @ b) meta_bds (pat_form f)
  | Pat_Axiom _ -> meta_bds
  | Pat_Fun_Symbol (Sym_Form_Quant (_,b),[p]) ->
     let b = List.map (fun (x,y) -> (x,Some y)) b in
     aux (current_bds @ b) meta_bds p
  (* | Pat_Fun_Symbol (Sym_Form_Pr, [pm;pf;pargs;pevent]) ->
   *    let meta_bds = aux (current_bds @ [mhr,None]) meta_bds pevent in
   *    List.fold_left (aux current_bds) meta_bds [pm;pf;pargs] *)
  | Pat_Fun_Symbol (_,lp) -> List.fold_left (aux current_bds) meta_bds lp
  in aux [] Mid.empty p

let rec write_meta_bindings (m : pbindings Mid.t) (p : pattern) =
  let aux = write_meta_bindings m in
  match p with
  | Pat_Anything          -> p
  | Pat_Meta_Name (p,n,_) ->
     Pat_Meta_Name (aux p,n,Mid.find_opt n m)
  | Pat_Sub p             -> Pat_Sub (aux p)
  | Pat_Or lp             -> Pat_Or (List.map aux lp)
  | Pat_Instance _        -> assert false
  | Pat_Red_Strat (p,f)   -> Pat_Red_Strat (aux p,f)
  | Pat_Type (p,gty)      -> Pat_Type (aux p,gty)
  | Pat_Axiom _           -> p
  | Pat_Fun_Symbol (s,lp) -> Pat_Fun_Symbol (s,List.map aux lp)

let pattern_of_axiom b a =
  let p = odfl (pat_axiom a) (pattern_of_axiom b a) in
  let m = get_meta_bindings p in
  write_meta_bindings m p

let pattern_of_form b f = pattern_of_axiom b (Axiom_Form f)



module PReduction = struct
  open EcReduction
  open EcPattern.Psubst

  let rec h_red_args
        (p_f : 'a -> pattern)
        (f : environnement -> 'a -> pattern option)
        (env : environnement) = function
    | [] -> None
    | a :: r ->
       match f env a with
       | Some a -> Some (a :: (List.map p_f r))
       | None -> omap (fun l -> (p_f a)::l) (h_red_args p_f f env r)

  let is_record (env : environnement) (f : form) =
    match EcFol.destr_app f with
    | { f_node = Fop (p,_) }, _ ->
       EcEnv.Op.is_record_ctor (LDecl.toenv env.env_hyps) p
    | _ -> false

  let reduce_local_opt (env : environnement) (id : Name.t) : pattern option =
    if env.env_red_info_p.delta_h id
    then
      let p = Pat_Meta_Name (Pat_Anything,id,None) in
      let p' = Psubst.p_subst env.env_subst p in
      if p = p'
      then
        try Some (Pat_Axiom(Axiom_Form(LDecl.unfold id env.env_hyps))) with
        | NotReducible -> None
      else Some p'
    else None

  let rec h_red_pattern_opt (env : environnement) = function
    | Pat_Anything -> None
    | Pat_Meta_Name _ -> None
    | Pat_Sub _ -> None
    | Pat_Or _ -> None
    | Pat_Instance _ -> assert false
    | Pat_Red_Strat _ -> None
    | Pat_Type _ -> None
    | Pat_Axiom a -> h_red_axiom_opt env a
    | Pat_Fun_Symbol _ -> None

  and h_red_axiom_opt (env : environnement) = function
    | Axiom_Hoarecmp _    -> None
    | Axiom_Memory m      -> h_red_mem_opt env m
    | Axiom_MemEnv m      -> h_red_memenv_opt env m
    | Axiom_Prog_Var pv   -> h_red_prog_var_opt env pv
    | Axiom_Op (op,lty)   -> h_red_op_opt env op lty
    | Axiom_Module m      -> h_red_mpath_top_opt env m
    | Axiom_Mpath m       -> h_red_mpath_opt env m
    | Axiom_Instr i       -> h_red_instr_opt env i
    | Axiom_Stmt s        -> h_red_stmt_opt env s
    | Axiom_Lvalue lv     -> h_red_lvalue_opt env lv
    | Axiom_Xpath x       -> h_red_xpath_opt env x
    | Axiom_Local (id,ty) -> h_red_local_opt env id ty
    | Axiom_Form f        -> h_red_form_opt env f

  and h_red_mem_opt env m : pattern option =
    if env.env_red_info_p.delta_h m
    then
      match MName.find_opt m env.env_subst.ps_patloc with
      | Some _ as p -> p
      | None ->
         omap pat_memory (MName.find_opt m env.env_subst.ps_mem)
    else None

  and h_red_memenv_opt env m =
    if env.env_red_info_p.delta_h (fst m)
    then match MName.find_opt (fst m) env.env_subst.ps_patloc with
         | Some _ as p -> p
         | None ->
            omap (fun m' -> pat_memenv (m',snd m))
              (MName.find_opt (fst m) env.env_subst.ps_mem)
    else None

  and h_red_prog_var_opt env pv =
    omap (fun x -> p_prog_var x pv.pv_kind) (h_red_xpath_opt env pv.pv_name)

  and h_red_op_opt env op lty =
    if env.env_red_info_p.delta_p op
    then Some (pat_form (EcEnv.Op.reduce (LDecl.toenv env.env_hyps) op lty))
    else None

  and h_red_mpath_top_opt env m =
    if env.env_red_info_p.modpath
    then
      match m with
      | `Concrete _ -> None
      | `Local id ->
      match MName.find_opt id env.env_subst.ps_patloc with
      | Some _ as p -> p
      | None ->
         omap pat_mpath (MName.find_opt id env.env_subst.ps_mp)
    else None

  and h_red_mpath_opt env m =
    if env.env_red_info_p.modpath
    then match h_red_mpath_top_opt env m.m_top with
         | Some p ->
            Some (p_mpath p (List.map pat_mpath m.m_args))
         | None ->
            omap (fun l -> p_mpath (pat_mpath_top m.m_top) l)
              (h_red_args pat_mpath h_red_mpath_opt env m.m_args)
    else None

  and h_red_instr_opt env i =
    match i.i_node with
    | Sasgn (lv,e) -> begin
        match h_red_lvalue_opt env lv with
        | Some lv -> Some (p_assign lv (pat_form (form_of_expr e)))
        | None ->
           omap (fun p -> p_assign (pat_lvalue lv) p)
             (h_red_form_opt env (form_of_expr e))
      end
    | Srnd (lv,e) -> begin
        match h_red_lvalue_opt env lv with
        | Some lv -> Some (p_sample lv (pat_form (form_of_expr e)))
        | None ->
           omap (fun p -> p_sample (pat_lvalue lv) p)
             (h_red_form_opt env (form_of_expr e))
      end
    | Scall (olv,f,args) -> begin
        match omap (h_red_lvalue_opt env) olv with
        | Some (Some lv) ->
           Some (p_call (Some lv) (pat_xpath f)
                   (List.map (fun x -> pat_form (form_of_expr x)) args))
        | Some None | None ->
        match h_red_xpath_opt env f with
        | Some f ->
           Some (p_call (omap pat_lvalue olv) f
                   (List.map (fun x -> pat_form (form_of_expr x)) args))
        | None ->
           let olv = omap pat_lvalue olv in
           omap
             (fun args -> p_call olv (pat_xpath f) args)
             (h_red_args (fun e -> pat_form (form_of_expr e))
                (fun env e -> h_red_form_opt env (form_of_expr e)) env args)
      end
    | Sif (cond,s1,s2) -> begin
        match h_red_form_opt env (form_of_expr cond) with
        | Some cond ->
           Some (p_instr_if cond (pat_stmt s1) (pat_stmt s2))
        | None ->
        match h_red_stmt_opt env s1 with
        | Some s1 ->
           Some (p_instr_if (pat_form(form_of_expr cond)) s1 (pat_stmt s2))
        | None ->
           omap
             (fun s2 -> p_instr_if (pat_form(form_of_expr cond)) (pat_stmt s1) s2)
             (h_red_stmt_opt env s2)
      end
    | Swhile (cond,s) -> begin
        match h_red_form_opt env (form_of_expr cond) with
        | Some cond -> Some (p_while cond (pat_stmt s))
        | None ->
           omap (fun s -> p_while (pat_form(form_of_expr cond)) s)
             (h_red_stmt_opt env s)
      end
    | Sassert e -> omap p_assert (h_red_form_opt env (form_of_expr e))
    | Sabstract name ->
       if env.env_red_info_p.delta_h name
       then MName.find_opt name env.env_subst.ps_patloc
       else None

  and h_red_stmt_opt env s =
    omap (fun l -> Pat_Fun_Symbol(Sym_Stmt_Seq,l))
      (h_red_args pat_instr h_red_instr_opt env s.s_node)

  and h_red_lvalue_opt env = function
    | LvVar (pv,ty) ->
       omap (fun x -> p_lvalue_var x ty) (h_red_prog_var_opt env pv)
    | LvTuple l ->
       omap p_lvalue_tuple
         (h_red_args (fun (pv,ty) -> pat_lvalue (LvVar(pv,ty)))
            (fun env x -> h_red_lvalue_opt env (LvVar x)) env l)
    | LvMap _ -> None


  and h_red_xpath_opt env x =
    if env.env_red_info_p.modpath
    then match h_red_mpath_opt env x.x_top with
         | Some p -> Some (p_xpath p (pat_op x.x_sub []))
         | None -> None
    else None

  and h_red_local_opt env id _ty = MName.find_opt id env.env_subst.ps_patloc

  and h_red_form_opt (env : environnement) (f : form) =
    let ri = env.env_red_info_p in
    let hyps = env.env_hyps in

    match f.f_node with
    (* β-reduction *)
    | Fapp ({ f_node = Fquant (Llambda, _, _)}, _) when ri.beta ->
       begin
         try Some (Pat_Axiom(Axiom_Form(f_betared f))) with
         | _ -> None
       end

    (* ζ-reduction *)
    | Flocal x -> reduce_local_opt env x

    (* ζ-reduction *)
    | Fapp ({ f_node = Flocal x }, args) ->
       let pargs = List.map pat_form args in
       EcPattern.p_app_simpl_opt (reduce_local_opt env x) pargs (Some f.f_ty)

    (* ζ-reduction *)
    | Flet (LSymbol(x,_), e1, e2) when ri.zeta ->
       let s = Psubst.p_bind_local Psubst.p_subst_id x (pat_form e1) in
       Some (Psubst.p_subst s (pat_form e2))

    (* ι-reduction (let-tuple) *)
    | Flet (LTuple ids, { f_node = Ftuple es }, e2) when ri.iota ->
       let s =
         List.fold_left2
           (fun s (x,_) e1 -> Psubst.p_bind_local s x (pat_form e1))
           Psubst.p_subst_id ids es
       in
       Some(Psubst.p_subst s (pat_form e2))

    (* ι-reduction (let-records) *)
    | Flet (LRecord (_, ids), f1, f2) when ri.iota && is_record env f1 ->
       let args  = snd (EcFol.destr_app f1) in
       let subst =
         List.fold_left2 (fun subst (x, _) e ->
             match x with
             | None   -> subst
             | Some x -> Psubst.p_bind_local subst x (pat_form e))
           Psubst.p_subst_id ids args
       in
       Some (Psubst.p_subst subst (pat_form f2))

    (* ι-reduction (records projection) *)
    | Fapp ({ f_node = Fop (p, _); f_ty = ty} as f1, args)
         when ri.iota && EcEnv.Op.is_projection (LDecl.toenv env.env_hyps) p -> begin
        let op =
          match args with
          | [mk] -> begin
              match odfl (pat_form mk) (h_red_form_opt env mk) with
              | Pat_Axiom
                (Axiom_Form
                   { f_node =
                       Fapp ({ f_node = Fop (mkp, _) }, mkargs) } ) ->
                 if not (EcEnv.Op.is_record_ctor (LDecl.toenv env.env_hyps) mkp) then
                   None
                 else
                   let v = oget (EcEnv.Op.by_path_opt p (LDecl.toenv env.env_hyps)) in
                   let v = proj3_2 (EcDecl.operator_as_proj v) in
                   let v = try Some(List.nth mkargs v)
                           with _ -> None in
                   begin
                     match v with
                     | None -> None
                     | Some v -> h_red_form_opt env v
                   end
              | _ -> None
            end
          | _ -> None
        in match op with
           | None ->
              omap (fun x -> p_app x (List.map pat_form args) (Some ty))
                (h_red_form_opt env f1)
           | _ -> op
      end

    (* ι-reduction (tuples projection) *)
    | Fproj(f1, i) when ri.iota ->
       let f' = f_proj_simpl f1 i f.f_ty in
       if f_equal f f'
       then omap (fun x -> p_proj x i f.f_ty) (h_red_form_opt env f1)
       else Some (pat_form f')

    (* ι-reduction (if-then-else) *)
    | Fif (f1, f2, f3) when ri.iota ->
       let f' = f_if_simpl f1 f2 f3 in
       if f_equal f f'
       then omap (fun x -> p_if x (pat_form f2) (pat_form f3)) (h_red_form_opt env f1)
       else Some (pat_form f')

    (* ι-reduction (match-fix) *)
    | Fapp ({ f_node = Fop (p, tys); } as f1, fargs)
         when ri.iota && EcEnv.Op.is_fix_def (LDecl.toenv env.env_hyps) p -> begin

        try
          let op  = oget (EcEnv.Op.by_path_opt p (LDecl.toenv env.env_hyps)) in
          let fix = EcDecl.operator_as_fix op in

          if List.length fargs <> snd (fix.EcDecl.opf_struct) then
            raise NotReducible;

          let args  = Array.of_list (List.map pat_form fargs) in
          let myfun (opb, acc) v =
            let v = args.(v) in
            let v = odfl v (h_red_pattern_opt env v) in

            match p_destr_app v
              (* fst_map (fun x -> x.f_node) (EcFol.destr_app v) *)
            with
            | Pat_Axiom(Axiom_Form { f_node = Fop (p, _)}), cargs
                 when EcEnv.Op.is_dtype_ctor (LDecl.toenv env.env_hyps) p -> begin
                let idx = EcEnv.Op.by_path p (LDecl.toenv env.env_hyps) in
                let idx = snd (EcDecl.operator_as_ctor idx) in
                match opb with
                | EcDecl.OPB_Leaf   _  -> assert false
                | EcDecl.OPB_Branch bs ->
                   ((Parray.get bs idx).EcDecl.opb_sub, cargs :: acc)
              end
            | _ -> raise NotReducible in
          let pargs = List.fold_left myfun
                        (fix.EcDecl.opf_branches, []) (fst fix.EcDecl.opf_struct)
          in

          let pargs, (bds, body) =
            match pargs with
            | EcDecl.OPB_Leaf (bds, body), cargs -> (List.rev cargs, (bds, body))
            | _ -> assert false
          in

          let subst =
            List.fold_left2
              (fun subst (x, _) fa -> Psubst.p_bind_local subst x fa)
              Psubst.p_subst_id fix.EcDecl.opf_args (List.map pat_form fargs) in

          let subst =
            List.fold_left2
              (fun subst bds cargs ->
                List.fold_left2
                  (fun subst (x, _) fa -> Psubst.p_bind_local subst x fa)
                  subst bds cargs)
              subst bds pargs in

          let body = EcFol.form_of_expr EcFol.mhr body in
          let body =
            EcFol.Fsubst.subst_tvar
              (EcTypes.Tvar.init (List.map fst op.EcDecl.op_tparams) tys) body in

          Some (Psubst.p_subst subst (pat_form body))

        with NotReducible ->
          omap (fun x -> p_app x (List.map pat_form fargs) (Some f.f_ty))
            (h_red_form_opt env f1)
      end

    (* μ-reduction *)
    | Fglob (mp, m) when ri.modpath ->
       let f' = EcEnv.NormMp.norm_glob (LDecl.toenv env.env_hyps) m mp in
       if f_equal f f' then None
       else Some (pat_form f')

    (* μ-reduction *)
    | Fpvar (pv, m) when ri.modpath ->
       let pv' = EcEnv.NormMp.norm_pvar (LDecl.toenv env.env_hyps) pv in
       if pv_equal pv pv' then None
       else Some (p_pvar (pat_pv pv') f.f_ty (pat_memory m))

    (* logical reduction *)
    | Fapp ({f_node = Fop (p, tys); } as fo, args)
         when is_some ri.logic && is_logical_op p
      ->
       let pcompat =
         match oget ri.logic with `Full -> true | `ProductCompat -> false
       in

       let f' =
         match op_kind p, args with
         | Some (`Not), [f1]    when pcompat -> Some (pat_form (f_not_simpl f1))
         | Some (`Imp), [f1;f2] when pcompat -> Some (pat_form (f_imp_simpl f1 f2))
         | Some (`Iff), [f1;f2] when pcompat -> Some (pat_form (f_iff_simpl f1 f2))


         | Some (`And `Asym), [f1;f2] -> Some (pat_form (f_anda_simpl f1 f2))
         | Some (`Or  `Asym), [f1;f2] -> Some (pat_form (f_ora_simpl f1 f2))
         | Some (`And `Sym ), [f1;f2] -> Some (pat_form (f_and_simpl f1 f2))
         | Some (`Or  `Sym ), [f1;f2] -> Some (pat_form (f_or_simpl f1 f2))
         | Some (`Int_le   ), [f1;f2] -> Some (pat_form (f_int_le_simpl f1 f2))
         | Some (`Int_lt   ), [f1;f2] -> Some (pat_form (f_int_lt_simpl f1 f2))
         | Some (`Real_le  ), [f1;f2] -> Some (pat_form (f_real_le_simpl f1 f2))
         | Some (`Real_lt  ), [f1;f2] -> Some (pat_form (f_real_lt_simpl f1 f2))
         | Some (`Int_add  ), [f1;f2] -> Some (pat_form (f_int_add_simpl f1 f2))
         | Some (`Int_opp  ), [f]     -> Some (pat_form (f_int_opp_simpl f))
         | Some (`Int_mul  ), [f1;f2] -> Some (pat_form (f_int_mul_simpl f1 f2))
         | Some (`Real_add ), [f1;f2] -> Some (pat_form (f_real_add_simpl f1 f2))
         | Some (`Real_opp ), [f]     -> Some (pat_form (f_real_opp_simpl f))
         | Some (`Real_mul ), [f1;f2] -> Some (pat_form (f_real_mul_simpl f1 f2))
         | Some (`Real_inv ), [f]     -> Some (pat_form (f_real_inv_simpl f))
         | Some (`Eq       ), [f1;f2] -> begin
             match fst_map f_node (destr_app f1), fst_map f_node (destr_app f2) with
             | (Fop (p1, _), args1), (Fop (p2, _), args2)
                  when EcEnv.Op.is_dtype_ctor (LDecl.toenv env.env_hyps) p1
                       && EcEnv.Op.is_dtype_ctor (LDecl.toenv env.env_hyps) p2 ->

                let idx p =
                  let idx = EcEnv.Op.by_path p (LDecl.toenv env.env_hyps) in
                  snd (EcDecl.operator_as_ctor idx)
                in
                if   idx p1 <> idx p2
                then Some p_false
                else Some (pat_form (f_ands (List.map2 f_eq args1 args2)))

             | (_, []), (_, []) ->
                let eq_ty1, env = eq_type f1.f_ty EcTypes.tunit env in
                let o =
                  if eq_ty1
                  then
                    let eq_ty2, env = eq_type f2.f_ty EcTypes.tunit env in
                    if eq_ty2
                    then Some f_true
                    else let _ = restore_environnement env in None
                  else let _ = restore_environnement env in None in
                begin
                  match o with
                  | Some f -> Some (pat_form f)
                  | None ->
                     if   f_equal f1 f2 || is_alpha_eq env.env_hyps f1 f2
                     then Some p_true
                     else Some (pat_form (f_eq_simpl f1 f2))
                end

             | _ ->
                if   f_equal f1 f2 || is_alpha_eq hyps f1 f2
                then Some p_true
                else Some (pat_form (f_eq_simpl f1 f2))
           end

         | _ when ri.delta_p p ->
            let op = h_red_op_opt env p tys in
            EcPattern.p_app_simpl_opt op (List.map pat_form args) (Some f.f_ty)

         | _ -> Some (pat_form f)
       in
       begin
         match f' with
         | Some (Pat_Axiom(Axiom_Form f')) ->
            if f_equal f f'
            then omap (fun l -> p_app (pat_form fo) l (Some f.f_ty))
                   (h_red_args pat_form h_red_form_opt env args)
            else Some (pat_form f')
         | Some _ -> f'
         | None -> None
       end

    (* δ-reduction *)
    | Fop (p, tys) ->
       h_red_op_opt env p tys

    (* δ-reduction *)
    | Fapp ({ f_node = Fop (p, tys) }, args) when ri.delta_p p ->
       let op = h_red_op_opt env p tys in
       EcPattern.p_app_simpl_opt op (List.map pat_form args) (Some f.f_ty)

    (* η-reduction *)
    | Fquant (Llambda, [x, GTty _], { f_node = Fapp (f, [{ f_node = Flocal y }]) })
         when id_equal x y && not (Mid.mem x f.f_fv)
      -> Some (pat_form f)

    (* contextual rule - let *)
    | Flet (lp, f1, f2) ->
       omap (fun x -> p_let lp x (pat_form f2)) (h_red_form_opt env f1)

    (* Contextual rule - application args. *)
    | Fapp (f1, args) ->
       omap (fun x -> p_app x (List.map pat_form args) (Some f.f_ty))
         (h_red_form_opt env f1)

    (* Contextual rule - bindings *)
    | Fquant (Lforall as t, b, f1)
      | Fquant (Lexists as t, b, f1) when ri.logic = Some `Full -> begin
        let ctor = match t with
          | Lforall -> p_forall_simpl
          | Lexists -> p_exists_simpl
          | _       -> assert false in

        try
          let localkind_of_binding (id,gty) =
            match gty with
            | GTty ty -> id,EcBaseLogic.LD_var (ty,None)
            | GTmodty (mt,mr) -> id,EcBaseLogic.LD_modty (mt,mr)
            | GTmem mt -> id,EcBaseLogic.LD_mem mt in
          let b' = List.map localkind_of_binding b in
          let env_hyps = List.fold_left (fun h (id,k) -> LDecl.add_local id k h)
              env.env_hyps b' in
          omap (ctor b) (h_red_form_opt {env with env_hyps } f1)
        with NotReducible ->
          let f' = ctor b (pat_form f1) in
          if (match f' with | Pat_Axiom(Axiom_Form f') -> f_equal f f'
                            | _ -> false)
          then None
          else Some f'
      end

    | _ -> None

  (* let red_core_opt (env : environnement) (p : pattern) (a : axiom) =
   *   match p,a with
   *   | *)

end

(* val mkengine    : base -> engine *)
let mkenv ?ppe ?fmt (h : LDecl.hyps) (red_info_p : EcReduction.reduction_info)
      (red_info_a : EcReduction.reduction_info)
      (unienv : EcUnify.unienv)
    : environnement =
  let env = {
      env_hyps             = h;
      env_unienv           = unienv;
      env_red_strat        = (fun _ _ -> None);
      env_red_info_p       = red_info_p;
      env_red_info_a       = red_info_a;
      env_restore_unienv   = None;
      env_subst            = Psubst.p_subst_id;
      env_current_binds    = [] ;
      env_meta_restr_binds = Mid.empty;
      env_ppe              = odfl (EcPrinting.PPEnv.ofenv (LDecl.toenv h)) ppe;
      env_fmt              = odfl Format.std_formatter fmt;
    } in
  let env_red_strat p a =
    match PReduction.h_red_pattern_opt env p with
    | Some p -> Some (p, a)
    | None ->
    match a with
    | Axiom_Form f -> begin
       match EcReduction.h_red_opt env.env_red_info_a env.env_hyps f with
       | Some f -> Some (p, axiom_form f)
       | None -> None
      end
    | _ ->
    match PReduction.h_red_pattern_opt env (pat_axiom a) with
    | Some (Pat_Axiom a) -> Some (p, a)
    | _ -> None in
  { env with env_red_strat }


let mkengine (a : axiom) (p : pattern) (env : environnement) : engine =
  { e_head = a;
    e_pattern = p;
    e_env = env;
    e_continuation = ZTop;
  }

let mk_engine ?ppe ?fmt f e_pattern env_hyps env_red_strat env_red_info_a env_unienv = {
    e_pattern;
    e_head         = axiom_form f;
    e_continuation = ZTop;
    e_env          = {
        env_hyps;
        env_unienv;
        env_red_strat;
        env_red_info_p       = EcReduction.no_red;
        env_red_info_a;
        env_restore_unienv   = None;
        env_subst            = Psubst.p_subst_id;
        env_current_binds    = [];
        env_meta_restr_binds = Mid.empty;
        env_ppe              = odfl (EcPrinting.PPEnv.ofenv (LDecl.toenv env_hyps)) ppe;
        env_fmt              = odfl Format.std_formatter fmt;
      };
  }

let search ?ppe ?fmt (f : form) (p : pattern) (h : LDecl.hyps)
      (red_info_p : EcReduction.reduction_info)
      (red_info_a : EcReduction.reduction_info)
      (unienv : EcUnify.unienv) =
  try
    let env = mkenv ?ppe ?fmt h red_info_p red_info_a unienv in
    let ne = process (mkengine (axiom_form f) p env) in
    Some (get_n_matches ne, ne.ne_env)
  with
  | NoMatches -> None

(* -------------------------------------------------------------------------- *)
let red_make_strat_from_env (env: environnement) (p : pattern) (a : axiom) : (pattern * axiom) option =
  match a with
  | Axiom_Form f -> begin
      try omap (fun f -> (p,Axiom_Form f))
            (EcReduction.h_red_opt env.env_red_info_a env.env_hyps f)
      with | EcEnv.NotReducible -> assert false
    end
  | _ ->
     begin
       try omap (fun p -> (p,a)) (PReduction.h_red_pattern_opt env p)
       with | EcEnv.NotReducible -> assert false
     end
