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
    env_hyps           : EcEnv.LDecl.hyps;
    env_unienv         : EcUnify.unienv;
    env_red_strat      : reduction_strategy;
    env_red_info       : EcReduction.reduction_info;
    env_restore_unienv : EcUnify.unienv option;
    env_map            : EcPattern.map;
    (* FIXME : ajouter ici les stratégies *)
  }

type pat_continuation =
  | ZTop
  | Znamed     of pattern * meta_name * pat_continuation

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

  | Zbinds     of pat_continuation * binding Mid.t

and engine = {
    e_head         : axiom;
    e_pattern      : pattern;
    e_binds        : binding Mid.t;
    e_continuation : pat_continuation;
    e_env          : environnement;
  }

and nengine = {
    ne_continuation : pat_continuation;
    ne_binds        : binding Mid.t;
    ne_env          : environnement;
  }

(* val mkengine    : base -> engine *)
let mkengine (f : form) (p : pattern) (h : LDecl.hyps)
      (strategy : reduction_strategy) (red_info : EcReduction.reduction_info)
      (unienv : EcUnify.unienv)
    : engine = {
    e_head         = Axiom_Form f;
    e_binds        = Mid.empty ;
    e_continuation = ZTop ;
    e_pattern      = p ;
    e_env          = {
        env_hyps           = h;
        env_unienv         = unienv;
        env_red_strat      = strategy;
        env_red_info       = red_info;
        env_restore_unienv = None;
        env_map            = MName.empty;
      } ;
  }

let restore_environnement (env : environnement) : environnement =
  match env.env_restore_unienv with
  | None -> env
  | Some unienv ->
     let dst = env.env_unienv in
     let src = unienv in
     EcUnify.UniEnv.restore dst src;
     env

type ismatch =
  | Match
  | NoMatch

let my_mem = EcIdent.create "new_mem"

let form_of_expr = EcFol.form_of_expr my_mem

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

let eq_type (ty1 : ty) (ty2 : ty) (env : environnement) : bool * environnement =
  let unienv = EcUnify.UniEnv.copy env.env_unienv in
  (try
     EcUnify.unify (EcEnv.LDecl.toenv env.env_hyps) env.env_unienv ty1 ty2;
     true
   with
   | _ -> false),
  { env with env_restore_unienv = Some (odfl unienv env.env_restore_unienv); }

let eq_memtype (m1 : EcMemory.memtype) (m2 : EcMemory.memtype) (env : environnement) =
  EcMemory.mt_equal m1 m2, env

let eq_form (f1 : form) (f2 : form) (env : environnement) =
  let eq_ty, _ = eq_type f1.f_ty f2.f_ty env in
  if eq_ty && not(ty_equal f1.f_ty f2.f_ty)
  then
    raise (Invalid_argument
             (String.concat " and "
                (List.map EcTypes.dump_ty [f1.f_ty;f2.f_ty])))
  else
    EcReduction.is_conv_param env.env_red_info env.env_hyps f1 f2

let eq_memory (m1 : EcMemory.memory) (m2 : EcMemory.memory) (_env : environnement) =
  EcMemory.mem_equal m1 m2

let eq_memenv (m1 : EcMemory.memenv) (m2 : EcMemory.memenv) (_env : environnement) =
  EcMemory.me_equal m1 m2

let eq_prog_var (x1 : prog_var) (x2 : prog_var) (env : environnement) =
  EcReduction.EqTest.for_pv (EcEnv.LDecl.toenv env.env_hyps) x1 x2

let eq_module (m1 : mpath_top) (m2 : mpath_top) (_env : environnement) =
  EcPath.mt_equal m1 m2

let eq_name (n1 : meta_name) (n2 : meta_name) =
  0 = id_compare n1 n2

let eq_instr (i1 : EcModules.instr) (i2 : EcModules.instr) (env : environnement) =
  EcReduction.EqTest.for_instr (EcEnv.LDecl.toenv env.env_hyps) i1 i2

let eq_stmt (s1 : EcModules.stmt) (s2 : EcModules.stmt) (env : environnement) =
  EcReduction.EqTest.for_stmt (EcEnv.LDecl.toenv env.env_hyps) s1 s2

let eq_lvalue (lv1 : lvalue) (lv2 :lvalue) (_env : environnement) : bool =
  lv_equal lv1 lv2

let eq_mpath (m1 : mpath) (m2 : mpath) (env : environnement) : bool =
  EcReduction.EqTest.for_mp (EcEnv.LDecl.toenv env.env_hyps) m1 m2

let eq_xpath (x1 : xpath) (x2 : xpath) (env : environnement) : bool =
  EcReduction.EqTest.for_xp (EcEnv.LDecl.toenv env.env_hyps) x1 x2

let eq_hoarecmp (c1 : hoarecmp) (c2 : hoarecmp) (_ : environnement) : bool =
  c1 = c2

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


let eq_gty (gty1 : gty) (gty2 : gty) (env : environnement) : bool * environnement =
  match gty1, gty2 with
  | GTty ty1, GTty ty2 -> eq_type ty1 ty2 env
  | _,_ -> EcCoreFol.gty_equal gty1 gty2, env

let eq_axiom (o1 : axiom) (o2 : axiom) (env : environnement) :
      bool * environnement =
  let aux o1 o2 =
    match o1,o2 with
    (* | Axiom_Form { f_node = Fop (op1,lty1) },
     *   Axiom_Form { f_node = Fop (op2,lty2) } ->
     *    eq_op (op1,lty1) (op2,lty2) env *)

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
  let eq_ax, env = aux o1 o2 in
  if eq_ax then true, env
  else
    match env.env_red_strat (Pat_Axiom o1) o2 with
    | None -> false, env
    | Some (Pat_Axiom o1,o2) -> aux o1 o2
    | Some _ -> assert false


let rec merge_binds bs1 bs2 map = match bs1,bs2 with
  | [], _ | _,[] -> Some (map,bs1,bs2)
  | (_,ty1)::_, (_,ty2)::_ when not(gty_equal ty1 ty2) -> None
  | (id1,_)::_, (_,_)::_ when Mid.mem id1 map -> None
  | (id1,_)::bs1, (id2,ty2)::bs2 ->
     merge_binds bs1 bs2 (Mid.add id1 (id2,ty2) map)

(* add_match can raise the exception : CannotUnify *)
(* val add_match : matches -> name -> t_matches -> matches *)
let nadd_match (e : nengine) (name : meta_name) (p : pattern) : nengine =
  let env = e.ne_env in
  let map = env.env_map in
  let b = e.ne_binds in
  if Mid.set_disjoint b map
  then
    (* let fv =
     *   match p with
     *   | Pat_Axiom a -> begin
     *       match a with
     *       | Axiom_Form f     -> Mid.set_inter b (f_fv f)
     *       | Axiom_Memory m   -> Mid.set_inter b (Sid.singleton m)
     *       | Axiom_Instr i    -> Mid.set_inter b (i_fv i)
     *       | Axiom_Stmt s     -> Mid.set_inter b (s_fv s)
     *       | Axiom_MemEnv m   ->
     *          Mid.set_union
     *            (Mid.set_inter b (EcMemory.mt_fv (snd m)))
     *            (Mid.set_inter b (Sid.singleton (fst m)))
     *       | Axiom_Lvalue lv  ->
     *          Mid.set_inter b (i_fv (i_asgn (lv,e_int (EcBigInt.of_int 0))))
     *       | Axiom_Prog_Var _ -> Mid.empty
     *       | Axiom_Op _       -> Mid.empty
     *       | Axiom_Module _   -> Mid.empty
     *       | Axiom_Mpath _    -> Mid.empty
     *       | Axiom_Xpath _    -> Mid.empty
     *       | Axiom_Hoarecmp _ -> Mid.empty
     *       | Axiom_Local id   -> Mid.set_inter b (Sid.singleton id)
     *     end
     *   | _ -> (\* FIXME *\) Mid.empty
     * in *)
    let map, env = match Mid.find_opt name map with
      | None              -> Mid.add name p map, env
      | Some Pat_Axiom o1 -> begin
          match p with
          | Pat_Axiom a ->
             let eq_ax, env = eq_axiom o1 a env in
             if eq_ax then map, env
             else raise CannotUnify
          | _ -> assert false
        end
      | _                     -> (* FIXME *) assert false
    in { e with ne_env = { env with env_map = map } }
  else raise CannotUnify

let e_next (e : engine) : nengine =
  { ne_continuation = e.e_continuation;
    ne_binds = e.e_binds;
    ne_env = e.e_env;
  }

let n_engine (a : axiom) (e_pattern : pattern) (n : nengine) =
  { e_head = a;
    e_binds = n.ne_binds;
    e_pattern;
    e_continuation = n.ne_continuation;
    e_env = n.ne_env;
  }

let add_match (e : engine) n p =
  n_engine e.e_head e.e_pattern (nadd_match (e_next e) n p)

let sub_engine e p b f =
  { e with e_head = f; e_pattern = Pat_Sub p; e_binds = b }

let fold_left_list (f : 'a -> 'b -> 'b * 'a) (a : 'a) (l : 'b list) : 'a * 'b list =
  let rec aux a acc l = match l with
    | [] -> a,List.rev acc
    | x::rest -> let x,a = f a x in aux a (x::acc) rest in
  aux a [] l

(* let p_app_simpl p subst env : pattern * environnement =
 *   let rec aux env = function
 *     | Pat_Anything -> Pat_Anything, env
 *     | Pat_Meta_Name (p1,name) -> begin
 *         match MName.find_opt name subst with
 *         | None -> Pat_Meta_Name (p1,name), env
 *         | Some (Pat_Type (p2,ty1), GTty ty2) ->
 *            let unienv = EcUnify.UniEnv.copy env.env_unienv in
 *            if eq_type ty1 ty2 env
 *            then
 *              let env =
 *                if (unienv = env.env_unienv)
 *                then env
 *                else { env with
 *                       env_restore_unienv =
 *                         Some (odfl unienv env.env_restore_unienv); } in
 *              Pat_Type (p2,ty1), env
 *            else assert false
 *         | Some (p,GTty ty) -> Pat_Type (p,ty), env
 *         | Some (p,GTmem _) | Some (p, GTmodty _) -> p, env
 *       end
 *     | Pat_Red_Strat (p,f) ->
 *        let (p,env) = aux env p in
 *        Pat_Red_Strat (p,f), env
 *     | Pat_Sub p1 -> let p1,env = aux env p1 in Pat_Sub p1, env
 *     | Pat_Or lp ->
 *        let env,lp = fold_left_list aux env lp in
 *        Pat_Or lp, env
 *     | Pat_Instance (ret,name,fun_name,args) ->
 *        assert false
 *     | Pat_Fun_Symbol (symbol,lp) -> begin
 *         match symbol with
 *         | Sym_Form_Quant (q,binds) when MName.set_disjoint subst (MName.of_list binds) ->
 *            let env,lp = fold_left_list aux env lp in
 *            Pat_Fun_Symbol (Sym_Form_Quant (q,binds), lp), env
 *         | Sym_Form_Quant _ ->
 *            raise (Invalid_argument
 *                     "in p_app_simpl : invalid argument name, it has been found in a sub quantif.")
 *         | _ ->
 *            let env,lp = fold_left_list aux env lp in
 *            Pat_Fun_Symbol (symbol, lp), env
 *       end
 *     | Pat_Axiom axiom ->
 *        Pat_Axiom axiom, env
 *     | Pat_Type (p1,ty) -> let p1,env = aux env p1 in Pat_Type (p1, ty), env
 *   in aux env p *)

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

(* -------------------------------------------------------------------------- *)
let red_make_strat_from_info (i : EcReduction.reduction_info)
      (hyps : LDecl.hyps) (p : pattern) (a : axiom) : (pattern * axiom) option =
  match a with
  | Axiom_Form f ->
     omap (fun f -> (p,Axiom_Form f)) (EcReduction.h_red_opt i hyps f)
  | _ -> None

(* -------------------------------------------------------------------------- *)
let replace_id id subst env =
  match Mid.find_opt id subst with
  | None -> None, env
  | Some (Pat_Type (p,GTty ty1),GTty ty2) ->
     let eq_ty,env = eq_type ty2 ty1 env in
     if eq_ty
     then Some (Pat_Type (p,GTty ty1)), env
     else assert false
  | Some (_,GTty _) -> None, env
  | Some (p,GTmem _) | Some (p, GTmodty _) -> Some p, env

let p_app_simpl_opt p subst env =
  let id x = x in
  let rec aux env = function
    | Pat_Anything -> None,env
    | Pat_Meta_Name (_,name) -> replace_id name subst env
    | Pat_Sub p1 ->
       let oa, env = aux env p1 in
       omap (fun x -> Pat_Sub x) oa, env
    | Pat_Or lp ->
       myomap (fun x -> Pat_Or x) (ofold_list id aux env lp)
    | Pat_Fun_Symbol (symbol,lp) -> begin
        match symbol with
        | Sym_Form_Quant (q,binds)
             when Mid.set_disjoint subst (Mid.of_list binds) ->
           myomap (fun (x) -> Pat_Fun_Symbol (Sym_Form_Quant (q,binds), x))
             (ofold_list id aux env lp)
        | Sym_Quant (q,binds)
             when Mid.set_disjoint subst (Mid.of_list binds) ->
           myomap (fun (x) -> Pat_Fun_Symbol (Sym_Quant (q,binds), x))
             (ofold_list id aux env lp)
        | Sym_Form_Quant _ ->
           raise (Invalid_argument
                    "in p_app_simpl_opt : Sym_Form_Quant : invalid argument name, it has been found in a sub quantif.")
        | Sym_Quant _ ->
           raise (Invalid_argument
                    "in p_app_simpl_opt : Sym_Quant : invalid argument name, it has been found in a sub quantif.")
        | _ ->
           myomap (fun (x) -> Pat_Fun_Symbol (symbol, x))
             (ofold_list id aux env lp)
      end
    | Pat_Axiom axiom -> (* FIXME *) Some (Pat_Axiom axiom), env
    | Pat_Type (p1,ty) -> myomap (fun (p) -> Pat_Type (p,ty)) (aux env p1)
    | Pat_Red_Strat (p,f) -> myomap (fun (p) -> Pat_Red_Strat (p,f)) (aux env p)
    | Pat_Instance (opt_lv, name, fun_name, args) -> begin
        match replace_id name subst env with
        | None,env ->
           myomap (fun (x) -> Pat_Instance (opt_lv, name, fun_name, x))
             (ofold_list id aux env args)
        | Some p,env -> Some p,env
      end
  (* | Panything -> None
   * | Pnamed (_,id2) -> replace_id id2 subst
   * | Psub p -> omap (fun x -> Psub x) (aux p)
   * | Por l -> omap (fun x -> Por x) (olist aux l)
   * | Ptype (p,ty) -> omap (fun p -> Ptype (p,ty)) (aux p)
   * | Pobject o -> Some (Pobject o) (\* FIXME *\)
   * | Pif (p1,p2,p3) ->
   *    let p = match olist aux [p1;p2;p3] with
   *      | None -> None
   *      | Some ([p1;p2;p3]) -> Some (Pif (p1,p2,p3))
   *      | _ -> assert false in
   *    p
   * | Papp (op,args) ->
   *    let p = match olist aux (op::args) with
   *      | None -> None
   *      | Some (op::args) -> Some (Papp (op,args))
   *      | _ -> assert false
   *    in p
   * | Ptuple l -> omap (fun x -> Ptuple x) (olist aux l)
   * | Pproj (p,i) -> omap (fun x -> Pproj (x,i)) (aux p)
   * | Pmatch (op,l) ->
   *    let p = match olist aux (op::l) with
   *      | None -> None
   *      | Some (op::args) -> Some (Pmatch (op,args))
   *      | _ -> assert false
   *    in p
   * | Pquant (q,bds,p) when Mid.set_disjoint subst (Mid.of_list bds) ->
   *    omap (fun x -> Pquant (q,bds,x)) (aux p)
   * | Pquant _ ->
   *    raise (Invalid_argument
   *             "in p_app_simpl : invalid argument name, it has been found in a sub quantif.")
   * | Ppvar (p1,p2) ->
   *    let p = match aux p1 with
   *      | None -> None
   *      | Some p1 -> match aux p2 with
   *                   | None -> None
   *                   | Some p2 -> Some (Ppvar (p1,p2)) in p
   * | Pglob (p1,p2) ->
   *    let p = match aux p1 with
   *      | None -> None
   *      | Some p1 ->
   *         match aux p2 with
   *         | None -> None
   *         | Some p2 -> Some (Pglob (p1,p2)) in p
   * | Ppr (p1,p2,p3,p4) ->
   *    let p = match olist aux [p1;p2;p3;p4] with
   *      | None -> None
   *      | Some [p1;p2;p3;p4] -> Some (Ppr (p1,p2,p3,p4))
   *      | _ -> assert false in p
   * | Pprog_var _ -> None (\* FIXME : when the id is about a module name *\)
   * | Pxpath _ -> None
   * | Pmpath (op,args) ->
   *    let p = match olist aux (op::args) with
   *      | None -> None
   *      | Some (op::args) -> Some (Pmpath (op,args))
   *      | _ -> assert false
   *    in p *)
  in aux env p

(* let obeta_reduce env = function
 *   | Pat_Fun_Symbol (Sym_Form_App ty,
 *                     (Pat_Fun_Symbol (Sym_Form_Quant (Llambda,binds),[p]))
 *                     ::pargs) ->
 *      let (rev_bs2,rev_bs1),(rev_pargs2,rev_pargs1) =
 *        List.prefix2 (List.rev binds) (List.rev pargs) in
 *      let bs1,bs2,pargs1,pargs2 =
 *        List.rev rev_bs1,
 *        List.rev rev_bs2,
 *        List.rev rev_pargs1,
 *        List.rev rev_pargs2
 *      in
 *      let p = match pargs2 with
 *        | [] -> p
 *        | _ -> Pat_Fun_Symbol (Sym_Form_App
 *                                 (\* FIXME : is this the right type ? *\)
 *                                 ty, p::pargs2) in
 *      let p = match bs2 with
 *        | [] -> p
 *        | _ -> Pat_Fun_Symbol (Sym_Form_Quant (Llambda, bs2), [p]) in
 *      let subst = Mid.empty in
 *      let subst =
 *        try List.fold_left2 (fun a (b,t) c -> Mid.add_new Not_found b (c,t) a) subst bs1 pargs1
 *        with
 *        | Not_found -> raise (Invalid_argument "beta_reduce : two bindings have got the same name.")
 *      in
 *      p_app_simpl_opt p subst env
 *
 *   | Pat_Fun_Symbol(Sym_App,(Pat_Fun_Symbol(Sym_Quant(Llambda,names),[p]))::pargs) ->
 *      let (rev_bs2,rev_bs1),(rev_pargs2,rev_pargs1) =
 *        List.prefix2 (List.rev names) (List.rev pargs) in
 *      let bs1,bs2,pargs1,pargs2 =
 *        List.rev rev_bs1,
 *        List.rev rev_bs2,
 *        List.rev rev_pargs1,
 *        List.rev rev_pargs2
 *      in
 *      let p = match pargs2 with
 *        | [] -> p
 *        | _ -> Pat_Fun_Symbol (Sym_App, p::pargs2) in
 *      let p = match bs2 with
 *        | [] -> p
 *        | _ -> Pat_Fun_Symbol (Sym_Quant (Llambda, bs2), [p]) in
 *      let subst = Mid.empty in
 *      let subst =
 *        try List.fold_left2 (fun a b c -> Mid.add_new Not_found b c a)
 *              subst (List.map fst bs1) pargs1
 *        with
 *        | Not_found -> raise (Invalid_argument "beta_reduce : two bindings have got the same name.")
 *      in
 *      let subst = Mid.map (fun x -> x,GTmem (EcMemory.memtype (EcMemory.abstract mhr))) subst in
 *      p_app_simpl_opt p subst env
 *
 *   | _ -> None, env
 *
 *
 * let beta_reduce env p = match obeta_reduce env p with
 *   | None, env -> p, env
 *   | Some p, env -> p, env *)

let rec mpath_to_pattern (m : mpath) =
  Pat_Fun_Symbol (Sym_Mpath, (Pat_Axiom (Axiom_Module m.m_top))
                             ::(List.map mpath_to_pattern m.m_args))

let rec pat_of_mpath (m : mpath) =
  let args = List.map pat_of_mpath m.m_args in
  let m = Pat_Axiom (Axiom_Module m.m_top) in
  Pat_Fun_Symbol (Sym_Mpath, m::args)

let rec pat_of_xpath (x : xpath) =
  Pat_Fun_Symbol (Sym_Xpath, [Pat_Axiom (Axiom_Op (x.x_sub,[])); pat_of_mpath x.x_top])


let substitution n1 p1 p =
  let rec aux p = match p with
    | Pat_Anything -> Pat_Anything
    | Pat_Meta_Name (_,name) when eq_name n1 name -> p1
    | Pat_Meta_Name (p,name) -> Pat_Meta_Name (aux p,name)
    | Pat_Sub p -> Pat_Sub (aux p)
    | Pat_Or lp -> Pat_Or (List.map aux lp)
    | Pat_Type (p,ty) -> Pat_Type (aux p, ty)
    | Pat_Fun_Symbol (sym,lp) -> Pat_Fun_Symbol (sym,List.map aux lp)
    | Pat_Instance (_, name, _, _) when eq_name n1 name ->
       p1
    | Pat_Instance (lv, name, fun_name, args) ->
       Pat_Instance (lv, name, fun_name, List.map aux args)
    | Pat_Red_Strat (p,f) -> Pat_Red_Strat (aux p,f)
    | Pat_Axiom axiom ->
       match axiom with
       | Axiom_Local (id,_) when eq_name n1 id -> p1
       | Axiom_Local _ -> p
       | Axiom_Form f when Mid.mem n1 f.f_fv -> begin
           match f.f_node with
           | Flocal id when eq_name id n1 -> p1
           | Fquant (_quant,bs,_f') when Mid.mem n1 (Mid.of_list bs) ->
              (* FIXME *) Pat_Axiom axiom
           | Fquant (quant,bs,f') when Mid.mem n1 f'.f_fv ->
              Pat_Fun_Symbol (Sym_Form_Quant (quant,bs), [aux (Pat_Axiom (Axiom_Form f'))])
           | Fif (f1,f2,f3) ->
              let lp = List.map aux (List.map (fun x -> Pat_Axiom (Axiom_Form x)) [f1;f2;f3]) in
              Pat_Fun_Symbol (Sym_Form_If, lp)
           | Fmatch _ | Flet _-> Pat_Axiom axiom (* FIXME *)
           | Fint _ -> Pat_Axiom axiom
           | Fop _ -> Pat_Axiom axiom (* FIXME *)
           | Fapp (f1,fargs) ->
              let lp = f1 :: fargs in
              let lp = List.map (fun x -> Pat_Axiom (Axiom_Form x)) lp in
              let lp = List.map aux lp in
              Pat_Fun_Symbol (Sym_Form_App f.f_ty, lp)
           | Ftuple lp ->
              let lp = List.map (fun x -> Pat_Axiom (Axiom_Form x)) lp in
              let lp = List.map aux lp in
              Pat_Fun_Symbol (Sym_Form_Tuple, lp)
           | Fproj (f1,i) ->
              let p = aux (Pat_Axiom (Axiom_Form f1)) in
              Pat_Fun_Symbol (Sym_Form_Proj i, [p])
           | _ -> (* FIXME *) p
         end
       | Axiom_Instr i when Mid.mem n1 (EcModules.s_fv (EcModules.stmt [i])) -> begin
           match i.i_node with
           | Sabstract name when eq_name name n1 ->
              p1
           | Sabstract _ -> Pat_Axiom axiom
           | _ when Mid.mem n1 (EcModules.s_fv (EcModules.stmt [i])) ->
              Pat_Axiom axiom
           | Sasgn (lv,e) ->
              let lv' = Pat_Axiom (Axiom_Lvalue lv) in
              let e' = Pat_Axiom (Axiom_Form (form_of_expr e)) in
              Pat_Fun_Symbol (Sym_Instr_Assign, [lv'; aux e'])
           | Srnd (lv,e) ->
              let lv' = Pat_Axiom (Axiom_Lvalue lv) in
              let e' = Pat_Axiom (Axiom_Form (form_of_expr e)) in
              Pat_Fun_Symbol (Sym_Instr_Sample, [lv'; aux e'])
           | Scall (None,procedure,args) ->
              begin match procedure.x_top.m_top with
              | `Local id when eq_name id n1 ->
                 (* FIXME *) p1
              | _ ->
                 let args =
                   List.map
                     aux
                     (List.map
                        (fun x ->
                          Pat_Axiom (Axiom_Form (form_of_expr x)))
                        args)
                 in
                 let lp = (pat_of_xpath procedure)::args in
                 Pat_Fun_Symbol (Sym_Instr_Call, lp)
              end
           | Scall (Some lv,procedure,args) ->
              begin match procedure.x_top.m_top with
              | `Local id when eq_name id n1 ->
                 (* FIXME *) p1
              | _ ->
                 let args =
                   List.map
                     aux
                     (List.map
                        (fun x ->
                          Pat_Axiom (Axiom_Form (form_of_expr x)))
                        args)
                 in
                 let lp = (Pat_Axiom (Axiom_Lvalue lv))
                          ::(pat_of_xpath procedure)
                          ::args in
                 Pat_Fun_Symbol (Sym_Instr_Call_Lv, lp)
              end
           | Sif (e,strue, sfalse) ->
              let e = aux (Pat_Axiom (Axiom_Form (form_of_expr e))) in
              let ptrue = aux (Pat_Axiom (Axiom_Stmt strue)) in
              let pfalse = aux (Pat_Axiom (Axiom_Stmt sfalse)) in
              Pat_Fun_Symbol (Sym_Instr_If, [e;ptrue;pfalse])
           | Swhile (e,body) ->
              let e = aux (Pat_Axiom (Axiom_Form (form_of_expr e))) in
              let pbody = aux (Pat_Axiom (Axiom_Stmt body)) in
              Pat_Fun_Symbol (Sym_Instr_While, [e;pbody])
           | Sassert e ->
              let e = aux (Pat_Axiom (Axiom_Form (form_of_expr e))) in
              Pat_Fun_Symbol (Sym_Instr_Assert, [e])
         end
       | Axiom_Stmt s when Mid.mem n1 (EcModules.s_fv s) -> begin
           let pl = List.map (fun x -> Pat_Axiom (Axiom_Instr x)) s.s_node in
           let pl = List.map aux pl in
           Pat_Fun_Symbol (Sym_Stmt_Seq, pl)
         end
       | Axiom_Lvalue _ -> Pat_Axiom axiom
       | Axiom_Memory _ | Axiom_MemEnv _ | Axiom_Form _ | Axiom_Prog_Var _
         | Axiom_Op _ | Axiom_Module _ | Axiom_Instr _ | Axiom_Stmt _
         | Axiom_Xpath _ | Axiom_Hoarecmp _ | Axiom_Mpath _ ->
          Pat_Axiom axiom
  in aux p


let is_conv (e : environnement) (f1 : form) (f2 : form) =
  EcReduction.is_conv e.env_hyps f1 f2



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

let rec rewrite_pattern_opt (e : engine) (p : pattern) : pattern option * engine =
  let env = e.e_env in
  let map = env.env_map in
  let id x = x in
  let smap = Sid.of_list (Mid.keys map) in
  let get_form = function
    | Pat_Axiom (Axiom_Form f) -> f
    | _ -> assert false in
  let get_mpath = function
    | Pat_Axiom (Axiom_Mpath m) -> m
    | Pat_Type(Pat_Axiom(Axiom_Mpath m), GTmodty (mt,mr)) ->
       if is_modty m mt mr env
       then m
       else assert false
    | _ -> assert false in
  let get_xpath = function
    | Pat_Axiom (Axiom_Xpath x) -> x
    | _ -> assert false in
  let get_instr = function
    | Pat_Axiom (Axiom_Instr i) -> i
    | _ -> assert false in
  let get_prog_var = function
    | Pat_Axiom (Axiom_Prog_Var pv) -> pv
    | _ -> assert false in
  let get_memory = function
    | Pat_Axiom (Axiom_Memory m) -> m
    | _ -> assert false in
  let get_path = function
    | Pat_Axiom (Axiom_Op (op,[])) -> op
    | _ -> assert false in
  let get_mpath_top = function
    | Pat_Axiom (Axiom_Module m) -> m
    | Pat_Axiom (Axiom_Mpath { m_top = m; m_args = [] }) -> m
    | _ -> assert false in
  let pattern_axiom a = Pat_Axiom a in
  let pattern_form f = Pat_Axiom (Axiom_Form f) in
  let pattern_mpath m = Pat_Axiom (Axiom_Mpath m) in
  let pattern_instr i = Pat_Axiom (Axiom_Instr i) in
  let pattern_prog_var pv = Pat_Axiom (Axiom_Prog_Var pv) in
  let is_form = function
    | Pat_Axiom (Axiom_Form _) -> true
    | _ -> false in
  let is_typed (_,o) = odfl false (omap (fun _ -> true) o) in
  let rec aux_f e f = aux e (Pat_Axiom (Axiom_Form f))
  and aux_a e a = aux e (Pat_Axiom a)
  and aux e (p : pattern) : pattern option * engine =
    let env = e.e_env in
    match p with
    | Pat_Anything -> None,e
    | Pat_Meta_Name (_,name) -> begin
        match MName.find_opt name map with
        | None -> None,e
        | Some p -> Some p,e
      end
    | Pat_Sub _ -> None,e
    | Pat_Or _ -> None,e
    | Pat_Instance _ -> None,e
    | Pat_Red_Strat (p,_) -> aux e p
    | Pat_Type
        (Pat_Fun_Symbol
          (Sym_App,
            (Pat_Fun_Symbol(Sym_Quant(Llambda,binds),[p]))::args),
         GTty ty)
      when List.for_all is_typed binds && List.for_all is_form args -> begin
        (* assert false *)
        try
          let get_bind (x,o) = match o with
            | None -> raise NoNext
            | Some ty -> (x,ty) in
          let get_ty (_,o) = match o with
            | Some (GTty ty) -> ty
            | _ -> assert false in
          let fop,e = match aux e p with
            | Some (Pat_Axiom(Axiom_Form f)),env -> f, env
            | None, _ -> raise NoNext
            | Some (Pat_Axiom _),_ -> assert false
            | _ -> assert false in
          let env = e.e_env in
          let tyarrow = EcTypes.toarrow (List.map get_ty binds) ty in
          let f = f_quant Llambda (List.map get_bind binds) fop in
          let f = f_app f (List.map get_form args) tyarrow in
          let f = match env.env_red_strat Pat_Anything (Axiom_Form f) with
            | Some (_,Axiom_Form f) -> f
            | _ -> f in
          Some (Pat_Axiom(Axiom_Form f)), { e with e_env = env }
        with
        | _ -> None, { e with e_env = env }
      end
    | Pat_Type (p,GTty ty) -> begin
        match aux e p with
        | None,env -> None, env
        | Some (Pat_Axiom (Axiom_Form f) as op),e ->
           let eq_ty,env = eq_type ty f.f_ty e.e_env in
           if eq_ty
           then
             Some op, { e with e_env = env }
           else None, { e with e_env = restore_environnement env }
        | _ -> None,e
      end
    | Pat_Type (p,gty) -> myomap (fun x -> Pat_Type(x,gty)) (aux e p)
    | Pat_Axiom a -> begin
        match a with
        | Axiom_Local (id,ty) ->  begin
            match Mid.find_opt id map with
            | None -> None, e
            | Some p -> aux e (Pat_Type(p,GTty ty))
          end
        | Axiom_Form f -> begin
            match f.f_node with
            | Fquant (quant,bs,f')
                 when Sid.disjoint (Sid.of_list (List.map fst bs)) smap ->
               let oa,e = aux_f e f' in
               omap (fun f -> Pat_Axiom (Axiom_Form (f_quant quant bs (get_form f))))
                 oa,e
            | Fquant _ ->
               raise (Invalid_argument "in rewrite_term, a quantifier appeares in the matching map")
            | Fif (f1,f2,f3) ->
               myomap (function
                   | f1::f2::f3::[] ->
                      Pat_Axiom (Axiom_Form (f_if (get_form f1) (get_form f2) (get_form f3)))
                   | _ -> assert false)
                 (ofold_list id aux e (List.map pattern_form [f1;f2;f3]))
            | Fmatch (fop,fargs,ty) ->
               myomap (function
                   | fop::fargs ->
                      Pat_Axiom
                        (Axiom_Form
                           (mk_form
                              (Fmatch
                                 (get_form fop,List.map get_form fargs,ty))
                              ty))
                   | _ -> assert false)
                 (ofold_list id aux e (List.map pattern_form(fop::fargs)))
            | Flet (lv,f1,f2) -> begin
                match lv with
                | LSymbol (id,_) when Mid.mem id map ->
                   raise (Invalid_argument "in rewrite_term, a let-lvalue appeares in the matching map")
                | LTuple l when not(Sid.disjoint smap (Sid.of_list (List.map fst l))) ->
                   raise (Invalid_argument "in rewrite_term, one of the let-lvalues appear in the matching map")
                | _ ->
                   myomap (function
                       | f1::f2::[] ->
                          Pat_Axiom
                            (Axiom_Form
                               (f_let lv (get_form f1) (get_form f2)))
                       | _ -> assert false)
                     (ofold_list id aux e (List.map pattern_form [f1;f2]))
              end
            | Fint _ -> None, e
            | Flocal id -> begin
                match Mid.find_opt id map with
                | None -> None, e
                | Some (Pat_Axiom (Axiom_Form f')) -> begin
                    match aux_f e f' with
                    | None, e -> Some (Pat_Axiom(Axiom_Form f')),e
                    | Some a, e -> Some a, e
                  end
                | Some p -> aux e p
              end
            | Fpvar (pvar,mem) ->
               myomap (function
                   | (Pat_Axiom(Axiom_Prog_Var pvar))::(Pat_Axiom(Axiom_Memory mem))::[] ->
                      Pat_Axiom(Axiom_Form (f_pvar pvar f.f_ty mem))
                   | _ -> assert false)
                 (ofold_list pattern_axiom aux_a e [Axiom_Prog_Var pvar;Axiom_Memory mem])
            | Fglob (mpath,mem) ->
               myomap (function
                   | (Pat_Axiom(Axiom_Mpath mpath))::(Pat_Axiom(Axiom_Memory mem))::[] ->
                      Pat_Axiom(Axiom_Form (f_glob mpath mem))
                   | _ -> assert false)
                 (ofold_list pattern_axiom aux_a e [Axiom_Mpath mpath;Axiom_Memory mem])
            | Fop _ -> None, e
            | Fapp (f1,fargs) ->
               myomap (function
                   | fop::fargs ->
                      Pat_Axiom(Axiom_Form (f_app (get_form fop) (List.map get_form fargs) f.f_ty))
                   | _ -> assert false)
                 (ofold_list pattern_form aux_f e (f1::fargs))
            | Ftuple t ->
               myomap (fun (l) -> Pat_Axiom(Axiom_Form (f_tuple (List.map get_form l))))
                 (ofold_list pattern_form aux_f e t)
            | Fproj (f1,i) ->
               myomap (fun (fi) -> Pat_Axiom(Axiom_Form (f_proj (get_form fi) i f.f_ty)))
                 (aux_f e f1)
            | FhoareF h ->
               myomap (function
                   | [Pat_Axiom(Axiom_Form pr);
                      Pat_Axiom(Axiom_Xpath f);
                      Pat_Axiom(Axiom_Form po)] ->
                      Pat_Axiom(Axiom_Form (f_hoareF pr f po))
                   | _ -> assert false)
                 (ofold_list pattern_axiom aux_a e
                    [Axiom_Form h.hf_po;
                     Axiom_Xpath h.hf_f;
                     Axiom_Form h.hf_po])
            | FhoareS h ->
               myomap (function
                   | [Pat_Axiom(Axiom_MemEnv m);
                      Pat_Axiom(Axiom_Form pr);
                      Pat_Axiom(Axiom_Stmt s);
                      Pat_Axiom(Axiom_Form po)] ->
                      Pat_Axiom(Axiom_Form (f_hoareS m pr s po))
                   | _ -> assert false)
                 (ofold_list pattern_axiom aux_a e
                    [Axiom_MemEnv h.hs_m;
                     Axiom_Form h.hs_pr;
                     Axiom_Stmt h.hs_s;
                     Axiom_Form h.hs_po])
            | FbdHoareF h ->
               myomap (function
                   | [Pat_Axiom(Axiom_Form pr);
                      Pat_Axiom(Axiom_Xpath f);
                      Pat_Axiom(Axiom_Form po);
                      Pat_Axiom(Axiom_Hoarecmp cmp);
                      Pat_Axiom(Axiom_Form bd)] ->
                      Pat_Axiom(Axiom_Form (f_bdHoareF pr f po cmp bd))
                   | _ -> assert false)
                 (ofold_list pattern_axiom aux_a e
                    [Axiom_Form h.bhf_pr;
                     Axiom_Xpath h.bhf_f;
                     Axiom_Form h.bhf_po;
                     Axiom_Hoarecmp h.bhf_cmp;
                     Axiom_Form h.bhf_bd])
            | FbdHoareS h ->
               myomap (function
                   | [Pat_Axiom(Axiom_MemEnv m);
                      Pat_Axiom(Axiom_Form pr);
                      Pat_Axiom(Axiom_Stmt s);
                      Pat_Axiom(Axiom_Form po);
                      Pat_Axiom(Axiom_Hoarecmp cmp);
                      Pat_Axiom(Axiom_Form bd)] ->
                      Pat_Axiom(Axiom_Form (f_bdHoareS m pr s po cmp bd))
                   | _ -> assert false)
                 (ofold_list pattern_axiom aux_a e
                    [Axiom_MemEnv h.bhs_m;
                     Axiom_Form h.bhs_pr;
                     Axiom_Stmt h.bhs_s;
                     Axiom_Form h.bhs_po;
                     Axiom_Hoarecmp h.bhs_cmp;
                     Axiom_Form h.bhs_bd])
            | FequivF h ->
               myomap (function
                   | [Pat_Axiom(Axiom_Form pr);
                      Pat_Axiom(Axiom_Xpath fl);
                      Pat_Axiom(Axiom_Xpath fr);
                      Pat_Axiom(Axiom_Form po)] ->
                      Pat_Axiom(Axiom_Form (f_equivF pr fl fr po))
                   | _ -> assert false)
                 (ofold_list pattern_axiom aux_a e
                    [Axiom_Form h.ef_pr;
                     Axiom_Xpath h.ef_fl;
                     Axiom_Xpath h.ef_fr;
                     Axiom_Form h.ef_po])
            | FequivS h ->
               myomap (function
                   | [Pat_Axiom(Axiom_MemEnv ml);
                      Pat_Axiom(Axiom_MemEnv mr);
                      Pat_Axiom(Axiom_Form pr);
                      Pat_Axiom(Axiom_Stmt sl);
                      Pat_Axiom(Axiom_Stmt sr);
                      Pat_Axiom(Axiom_Form po)] ->
                      Pat_Axiom(Axiom_Form (f_equivS ml mr pr sl sr po))
                   | _ -> assert false)
                 (ofold_list pattern_axiom aux_a e
                    [Axiom_MemEnv h.es_ml;
                     Axiom_MemEnv h.es_mr;
                     Axiom_Form h.es_pr;
                     Axiom_Stmt h.es_sl;
                     Axiom_Stmt h.es_sr;
                     Axiom_Form h.es_po])
            | FeagerF h ->
               myomap (function
                   | [Pat_Axiom(Axiom_Form pr);
                      Pat_Axiom(Axiom_Stmt sl);
                      Pat_Axiom(Axiom_Xpath fl);
                      Pat_Axiom(Axiom_Xpath fr);
                      Pat_Axiom(Axiom_Stmt sr);
                      Pat_Axiom(Axiom_Form po)] ->
                      Pat_Axiom(Axiom_Form (f_eagerF pr sl fl fr sr po))
                   | _ -> assert false)
                 (ofold_list pattern_axiom aux_a e
                    [Axiom_Form h.eg_pr;
                     Axiom_Stmt h.eg_sl;
                     Axiom_Xpath h.eg_fl;
                     Axiom_Xpath h.eg_fr;
                     Axiom_Stmt h.eg_sr;
                     Axiom_Form h.eg_po])
            | Fpr _ when Mid.mem mhr map ->
               raise (Invalid_argument "&hr appears in the matching map so it shouldn't be replaced in a pr formula")
            | Fpr h ->
               myomap (function
                   | [Pat_Axiom(Axiom_Memory mem);
                      Pat_Axiom(Axiom_Xpath f);
                      Pat_Axiom(Axiom_Form args);
                      Pat_Axiom(Axiom_Form event)] ->
                      Pat_Axiom(Axiom_Form (f_pr mem f args event))
                   | _ -> assert false)
                 (ofold_list pattern_axiom aux_a e
                    [Axiom_Memory h.pr_mem;
                     Axiom_Xpath h.pr_fun;
                     Axiom_Form h.pr_args;
                     Axiom_Form h.pr_event])
          end
        | Axiom_Memory m -> begin
            match Mid.find_opt m map with
            | None -> None, e
            | Some (Pat_Axiom (Axiom_Memory m | Axiom_MemEnv (m,_))) ->
               Some (Pat_Axiom(Axiom_Memory m)),e
            | _ -> (* FIXME *) assert false
          end
        | Axiom_MemEnv (m,t) -> begin
            match Mid.find_opt m map with
            | None -> None, e
            | Some (Pat_Axiom (Axiom_Memory m)) ->
               Some (Pat_Axiom(Axiom_MemEnv (m,t))),e
            | Some (Pat_Axiom (Axiom_MemEnv (m,t))) ->
               Some (Pat_Axiom(Axiom_MemEnv (m,t))),e
            | _ -> (* FIXME *) assert false
          end
        | Axiom_Prog_Var p ->
           myomap (function
               | Pat_Axiom(Axiom_Xpath xp) ->
                  Pat_Axiom(Axiom_Prog_Var (pv xp p.pv_kind))
               | _ -> assert false)
             (aux_a e (Axiom_Xpath p.pv_name))
        | Axiom_Op _ -> None, e
        | Axiom_Module mt -> begin
            match mt with
            | `Local id -> begin
                match Mid.find_opt id map with
                | None -> None, e
                | Some (Pat_Axiom (Axiom_Module _) as a) -> Some a,e
                | Some (Pat_Axiom (Axiom_Mpath _) as a)  -> Some a,e
                | _ -> (* FIXME *) assert false
              end
            | _ -> None, e
          end
        | Axiom_Mpath m ->
           myomap (function
               | (Pat_Axiom(Axiom_Module mt))::margs ->
                  Pat_Axiom(Axiom_Mpath (mpath mt (List.map get_mpath margs)))
               | (Pat_Axiom(Axiom_Mpath m))::[] -> Pat_Axiom(Axiom_Mpath m)
               | _ -> assert false)
             (ofold_list id aux e
                ((Pat_Axiom(Axiom_Module m.m_top))::
                   (List.map pattern_mpath m.m_args)))
        | Axiom_Instr i -> begin
            match i.i_node with
            | Sasgn (lv,ex) ->
               myomap (function
                   | [Pat_Axiom(Axiom_Lvalue lv);Pat_Axiom(Axiom_Form f)] ->
                      Pat_Axiom(Axiom_Instr (i_asgn (lv,(expr_of_form f))))
                   | _ -> assert false)
                 (ofold_list id aux e
                    [Pat_Axiom(Axiom_Lvalue lv);
                     Pat_Axiom(Axiom_Form (form_of_expr ex))])
            | Srnd  (lv,ex) ->
               myomap (function
                   | [Pat_Axiom(Axiom_Lvalue lv);Pat_Axiom(Axiom_Form f)] ->
                      Pat_Axiom(Axiom_Instr (i_rnd (lv,(expr_of_form f))))
                   | _ -> assert false)
                 (ofold_list id aux e
                    [Pat_Axiom(Axiom_Lvalue lv);
                     Pat_Axiom(Axiom_Form (form_of_expr ex))])
            | Scall (lvo,f,args) ->
               let l = (Pat_Axiom(Axiom_Xpath f))::
                         (List.map pattern_form(List.map form_of_expr args)) in
               let l = match lvo with
                 | None -> l
                 | Some lv -> (Pat_Axiom(Axiom_Lvalue lv))::l in
               myomap (function
                   | (Pat_Axiom(Axiom_Xpath xp))::args ->
                      Pat_Axiom
                        (Axiom_Instr
                           (i_call
                              (None,xp,
                               List.map expr_of_form (List.map get_form args))))
                   | (Pat_Axiom(Axiom_Lvalue lv))::(Pat_Axiom(Axiom_Xpath xp))::args ->
                      Pat_Axiom
                        (Axiom_Instr
                           (i_call
                              (Some lv,xp,List.map expr_of_form
                                            (List.map get_form args))))
                   | _ -> assert false)
                 (ofold_list id aux e l)
            | Sif (cond,strue,sfalse) ->
               myomap (function
                   | [Pat_Axiom(Axiom_Form f);
                      Pat_Axiom(Axiom_Stmt strue);
                      Pat_Axiom(Axiom_Stmt sfalse)] ->
                      Pat_Axiom
                        (Axiom_Instr
                           (i_if
                              (expr_of_form f,strue,sfalse)))
                   | _ -> assert false)
                 (ofold_list id aux e
                    [Pat_Axiom(Axiom_Form (form_of_expr cond));
                     Pat_Axiom(Axiom_Stmt strue);
                     Pat_Axiom(Axiom_Stmt sfalse)])
            | Swhile (cond,sbody) ->
               myomap (function
                   | [Pat_Axiom(Axiom_Form f);
                      Pat_Axiom(Axiom_Stmt sbody)] ->
                      Pat_Axiom(Axiom_Instr (i_while (expr_of_form f,sbody)))
                   | _ -> assert false)
                 (ofold_list id aux e
                    [Pat_Axiom(Axiom_Form (form_of_expr cond));
                     Pat_Axiom(Axiom_Stmt sbody)])
            | Sassert cond ->
               myomap (fun (f) ->
                   Pat_Axiom(Axiom_Instr
                               (i_assert (expr_of_form (get_form f)))))
                 (aux e (Pat_Axiom(Axiom_Form(form_of_expr cond))))
            | Sabstract id -> begin
                match Mid.find_opt id map with
                | None -> None, e
                | Some (Pat_Axiom (Axiom_Instr _) as a) -> Some a,e
                | _ -> (* FIXME *) assert false
              end
          end
        | Axiom_Stmt s ->
           myomap (fun (l) -> Pat_Axiom(Axiom_Stmt (stmt (List.map get_instr l))))
             (ofold_list id aux e (List.map pattern_instr s.s_node))
        | Axiom_Lvalue lv -> begin
            match lv with
            | LvVar (pv,ty) ->
               myomap (function
                   | Pat_Axiom(Axiom_Prog_Var pv) ->
                      Pat_Axiom(Axiom_Lvalue (LvVar (pv,ty)))
                   | _ -> assert false)
                 (aux e (Pat_Axiom(Axiom_Prog_Var pv)))
            | LvTuple lv ->
               myomap (fun (l) ->
                   Pat_Axiom
                     (Axiom_Lvalue
                        (LvTuple
                           (List.map2
                              (fun (_,ty) lv -> (get_prog_var lv,ty)) lv l))))
                 (ofold_list id aux e
                    (List.map pattern_prog_var (List.map fst lv)))
            | _ -> assert false
          end
        | Axiom_Xpath xp ->
           myomap (function
               | Pat_Axiom(Axiom_Mpath m) ->
                  Pat_Axiom(Axiom_Xpath (xpath m xp.x_sub))
               | _ -> assert false)
             (aux e (Pat_Axiom(Axiom_Mpath xp.x_top)))
        | Axiom_Hoarecmp _ -> None, e
      end
    | Pat_Fun_Symbol (symbol,lp) ->
       match symbol,lp with
       | Sym_Form_If, ([_;_;_] as p) ->
          myomap (function
              | [Pat_Axiom(Axiom_Form fcond);
                 Pat_Axiom(Axiom_Stmt strue);
                 Pat_Axiom(Axiom_Stmt sfalse)] ->
                 Pat_Axiom
                   (Axiom_Instr
                      (i_if
                         (expr_of_form fcond,strue,sfalse)))
              | _ -> assert false)
            (ofold_list id aux e p)
       | Sym_Form_If, _ -> assert false
       | Sym_Form_Tuple, t ->
          myomap (fun (l) ->
              Pat_Axiom(Axiom_Form (f_tuple (List.map get_form l))))
            (ofold_list id aux e t)
       | Sym_Form_Proj i,[p] ->
          myomap (fun (p) ->
              let f = get_form p in
              Pat_Axiom(Axiom_Form(f_proj f i f.f_ty)))
            (aux e p)
       | Sym_Form_Proj _,_ -> assert false
       | Sym_Form_Match ty, p::pargs ->
          myomap (function
              | p::pargs ->
                 Pat_Axiom
                   (Axiom_Form
                      (mk_form
                         (Fmatch (get_form p,List.map get_form pargs,ty)) ty))
              | _ -> assert false)
            (ofold_list id aux e (p::pargs))
       | Sym_Form_Match _,_ -> assert false
       | Sym_Form_Quant (q,bs), [p] ->
          myomap (fun (p) ->
              Pat_Axiom(Axiom_Form(f_quant q bs (get_form p))))
            (aux e p)
       | Sym_Form_Quant _,_ -> assert false
       | Sym_Form_Let lp, ([_;_] as l) ->
          myomap (function
              | [p1;p2] ->
                 Pat_Axiom
                   (Axiom_Form
                      (f_let lp (get_form p1) (get_form p2)))
              | _ -> assert false)
            (ofold_list id aux e l)
       | Sym_Form_Let _,_ -> assert false
       | Sym_Form_Pvar ty, ([_;_] as l) ->
          myomap (function
              | [p1;p2] ->
                 Pat_Axiom(Axiom_Form(f_pvar (get_prog_var p1) ty (get_memory p2)))
              | _ -> assert false)
            (ofold_list id aux e l)
       | Sym_Form_Pvar _,_ -> assert false
       | Sym_Form_Prog_var k, [p] ->
          myomap (fun (p) ->
              Pat_Axiom(Axiom_Prog_Var(EcTypes.pv (get_xpath p) k)))
            (aux e p)
       | Sym_Form_Prog_var _,_ -> assert false
       | Sym_Form_Glob, ([_;_] as l) ->
          myomap (function
              | [pf;pm] ->
                 Pat_Axiom(Axiom_Form(f_glob (get_mpath pf) (get_memory pm)))
              | _ -> assert false)
            (ofold_list id aux e l)
       | Sym_Form_Glob,_ -> assert false
       | Sym_Form_Hoare_F, l ->
          myomap (function
              | [Pat_Axiom(Axiom_Form pr);
                 Pat_Axiom(Axiom_Xpath f);
                 Pat_Axiom(Axiom_Form po)] ->
                 Pat_Axiom(Axiom_Form (f_hoareF pr f po))
              | _ -> assert false)
            (ofold_list id aux e l)
       | Sym_Form_Hoare_S, l ->
          myomap (function
              | [Pat_Axiom(Axiom_MemEnv m);
                 Pat_Axiom(Axiom_Form pr);
                 Pat_Axiom(Axiom_Stmt s);
                 Pat_Axiom(Axiom_Form po)] ->
                 Pat_Axiom(Axiom_Form (f_hoareS m pr s po))
              | _ -> assert false)
            (ofold_list id aux e l)
       | Sym_Form_bd_Hoare_F, l ->
          myomap (function
              | [Pat_Axiom(Axiom_Form pr);
                 Pat_Axiom(Axiom_Xpath f);
                 Pat_Axiom(Axiom_Form po);
                 Pat_Axiom(Axiom_Hoarecmp cmp);
                 Pat_Axiom(Axiom_Form bd)] ->
                 Pat_Axiom(Axiom_Form (f_bdHoareF pr f po cmp bd))
              | _ -> assert false)
            (ofold_list id aux e l)
       | Sym_Form_bd_Hoare_S, l ->
          myomap (function
              | [Pat_Axiom(Axiom_MemEnv m);
                 Pat_Axiom(Axiom_Form pr);
                 Pat_Axiom(Axiom_Stmt s);
                 Pat_Axiom(Axiom_Form po);
                 Pat_Axiom(Axiom_Hoarecmp cmp);
                 Pat_Axiom(Axiom_Form bd)] ->
                 Pat_Axiom(Axiom_Form (f_bdHoareS m pr s po cmp bd))
              | _ -> assert false)
            (ofold_list id aux e l)
       | Sym_Form_Equiv_F, l ->
          myomap (function
              | [Pat_Axiom(Axiom_Form pr);
                 Pat_Axiom(Axiom_Xpath fl);
                 Pat_Axiom(Axiom_Xpath fr);
                 Pat_Axiom(Axiom_Form po)] ->
                 Pat_Axiom(Axiom_Form (f_equivF pr fl fr po))
              | _ -> assert false)
            (ofold_list id aux e l)
       | Sym_Form_Equiv_S, l ->
          myomap (function
              | [Pat_Axiom(Axiom_MemEnv ml);
                 Pat_Axiom(Axiom_MemEnv mr);
                 Pat_Axiom(Axiom_Form pr);
                 Pat_Axiom(Axiom_Stmt sl);
                 Pat_Axiom(Axiom_Stmt sr);
                 Pat_Axiom(Axiom_Form po)] ->
                 Pat_Axiom(Axiom_Form (f_equivS ml mr pr sl sr po))
              | _ -> assert false)
            (ofold_list id aux e l)
       | Sym_Form_Eager_F, l ->
          myomap (function
              | [Pat_Axiom(Axiom_Form pr);
                 Pat_Axiom(Axiom_Stmt sl);
                 Pat_Axiom(Axiom_Xpath fl);
                 Pat_Axiom(Axiom_Xpath fr);
                 Pat_Axiom(Axiom_Stmt sr);
                 Pat_Axiom(Axiom_Form po)] ->
                 Pat_Axiom(Axiom_Form (f_eagerF pr sl fl fr sr po))
              | _ -> assert false)
            (ofold_list id aux e l)
       | Sym_Form_Pr, l ->
          myomap (function
              | [Pat_Axiom(Axiom_Memory mem);
                 Pat_Axiom(Axiom_Xpath f);
                 Pat_Axiom(Axiom_Form args);
                 Pat_Axiom(Axiom_Form event)] ->
                 Pat_Axiom(Axiom_Form (f_pr mem f args event))
              | _ -> assert false)
            (ofold_list id aux e l)
       | Sym_Stmt_Seq, l ->
          myomap (fun (l) ->
              Pat_Axiom(Axiom_Stmt(stmt (List.map get_instr l))))
            (ofold_list id aux e l)
       | Sym_Instr_Assign, ([_;_] as l) ->
          myomap (function
              | [Pat_Axiom(Axiom_Lvalue lv);
                 Pat_Axiom(Axiom_Form f)] ->
                 Pat_Axiom(Axiom_Instr (i_asgn (lv,(expr_of_form f))))
              | _ -> assert false)
            (ofold_list id aux e l)
       | Sym_Instr_Assign, _ -> assert false
       | Sym_Instr_Sample, ([_;_] as l) ->
          myomap (function
              | [Pat_Axiom(Axiom_Lvalue lv);
                 Pat_Axiom(Axiom_Form f)] ->
                 Pat_Axiom(Axiom_Instr (i_rnd (lv,(expr_of_form f))))
              | _ -> assert false)
            (ofold_list id aux e l)
       | Sym_Instr_Sample, _ -> assert false
       | Sym_Instr_Call, (_::_ as l) ->
          myomap (function
              | (Pat_Axiom(Axiom_Xpath xp))::args ->
                 Pat_Axiom
                   (Axiom_Instr
                      (i_call
                         (None,xp,List.map expr_of_form
                                    (List.map get_form args))))
              | _ -> assert false)
            (ofold_list id aux e l)
       | Sym_Instr_Call, _ -> assert false
       | Sym_Instr_Call_Lv, (_::_::_ as l) ->
          myomap (function
              | (Pat_Axiom(Axiom_Lvalue lv))
                ::(Pat_Axiom(Axiom_Xpath xp))
                ::args ->
                 Pat_Axiom
                   (Axiom_Instr
                      (i_call
                         (Some lv,xp,List.map expr_of_form
                                       (List.map get_form args))))
              | _ -> assert false)
            (ofold_list id aux e l)
       | Sym_Instr_Call_Lv, _ -> assert false
       | Sym_Instr_If, ([_;_;_] as l) ->
          myomap (function
              | [Pat_Axiom(Axiom_Form f);
                 Pat_Axiom(Axiom_Stmt strue);
                 Pat_Axiom(Axiom_Stmt sfalse)] ->
                 Pat_Axiom(Axiom_Instr (i_if (expr_of_form f,strue,sfalse)))
              | _ -> assert false)
            (ofold_list id aux e l)
       | Sym_Instr_If, _ -> assert false
       | Sym_Instr_While, ([_;_] as l) ->
          myomap (function
              | [Pat_Axiom(Axiom_Form f);
                 Pat_Axiom(Axiom_Stmt sbody)] ->
                 Pat_Axiom(Axiom_Instr (i_while (expr_of_form f,sbody)))
              | _ -> assert false)
            (ofold_list id aux e l)
       | Sym_Instr_While, _ -> assert false
       | Sym_Instr_Assert, [p] ->
          myomap (fun (f) ->
              Pat_Axiom(Axiom_Instr (i_assert (expr_of_form (get_form f)))))
            (aux e p)
       | Sym_Instr_Assert, _ -> assert false
       | Sym_Xpath, ([_;_] as l) ->
          myomap (function
              | [pm;pf] ->
                 Pat_Axiom(Axiom_Xpath (xpath (get_mpath pm) (get_path pf)))
              | _ -> assert false)
            (ofold_list id aux e l)
       | Sym_Xpath, _ -> assert false
       (* from type mpath *)
       | Sym_Mpath, (_::_ as l) ->
          myomap (function
              | [pm] ->
                 Pat_Axiom(Axiom_Mpath (get_mpath pm))
              | pm::pargs ->
                 Pat_Axiom(Axiom_Mpath(mpath (get_mpath_top pm)
                                         (List.map get_mpath pargs)))
              | _ -> assert false)
            (ofold_list id aux e l)
       | Sym_Mpath, _ -> assert false
       (* generalized *)
       (* | Sym_Form_App ty, (_::_ as l) -> begin
        *     match obeta_reduce e.e_env p with
        *     | None, env ->
        *        myomap (function
        *            | p::l ->
        *               Pat_Axiom
        *                 (Axiom_Form
        *                    (f_app (get_form p)
        *                       (List.map get_form l) ty))
        *            | _ -> assert false)
        *          (ofold_list id aux { e with e_env = restore_environnement env } l)
        *     | Some p,env -> rewrite_pattern_opt { e with e_env = env } p
        *   end *)
       | Sym_Form_App _,_ -> None, e

       (* | Sym_App, _::_ -> begin
        *     match obeta_reduce e.e_env p with
        *     | None,_ -> assert false
        *     | Some p,env -> rewrite_pattern_opt { e with e_env = env } p
        *   end *)
       | Sym_App, _ -> None, e
       | Sym_Quant _,_ -> None, e
  in aux e p

let rewrite_pattern (e : engine) p = match rewrite_pattern_opt e p with
  | None, e -> p, e
  | Some p, e -> p, e

let rewrite_term e f =
  match rewrite_pattern e (Pat_Axiom(Axiom_Form f)) with
  | Pat_Axiom(Axiom_Form f),_ -> f
  | _ -> assert false

(* ---------------------------------------------------------------------- *)
let rec abstract_opt
          (other_args : Sid.t)
          (ep : pattern option * gty Mid.t * engine)
          ((arg,parg) : Name.t * pattern) :
          pattern option * gty Mid.t * engine =
  let id x = x in
  match ep with
  | None, map, e -> None, map, e
  | Some p, map, e ->
     let rec aux ((o,env) : gty Mid.t * environnement)
               (p : pattern) :
               pattern option * (gty Mid.t * environnement) =
       match p with
       | Pat_Anything
         | Pat_Sub _
         | Pat_Or _
         | Pat_Instance _ -> assert false
       | Pat_Meta_Name (_,n) when Sid.mem n other_args -> None, (o,env)
       | Pat_Meta_Name _ -> None, (o,env)
       | Pat_Fun_Symbol (s,lp) ->
          let test = ofold_list id aux (o,env) lp in
          myomap (fun x -> Pat_Fun_Symbol (s,x)) test
       | Pat_Type (p,_) -> aux (o,env) p
       | Pat_Red_Strat (p,x) ->
          myomap (fun p -> Pat_Red_Strat (p,x)) (aux (o,env) p)
       | Pat_Axiom axiom ->
          match parg,axiom with
          | Pat_Anything,_
            | Pat_Sub _,_
            | Pat_Or _,_
            | Pat_Instance _,_
            | Pat_Meta_Name _,_ -> assert false
          | Pat_Red_Strat _,_ ->
             (* FIXME *) assert false
          | Pat_Type (p,GTty ty), Axiom_Form f ->
             let eq_ty, env = eq_type f.f_ty ty env in
             if eq_ty then aux (o,env) p
             else assert false
          | Pat_Type _, Axiom_Form _     -> assert false
          | Pat_Type _, Axiom_Memory _   -> assert false
          | Pat_Type _, Axiom_MemEnv _   -> assert false
          | Pat_Type _, Axiom_Prog_Var _ -> assert false
          | Pat_Type _, Axiom_Op _       -> assert false
          | Pat_Type _, Axiom_Module _   -> assert false
          | Pat_Type _, Axiom_Mpath _    -> assert false
          | Pat_Type _, Axiom_Xpath _    -> assert false
          | Pat_Type _, Axiom_Instr _    -> assert false
          | Pat_Type _, Axiom_Stmt _     -> assert false
          | Pat_Type _, Axiom_Lvalue _   -> assert false
          | Pat_Type _, Axiom_Hoarecmp _ -> assert false
          | Pat_Type _, Axiom_Local _    -> assert false
          | Pat_Fun_Symbol (symbol,_),_ -> begin
              (* FIXME : unification *)
              match rewrite_pattern_opt e parg with
              | None,_ -> begin
                  match symbol with
                  | Sym_Form_If         -> assert false
                  | Sym_Form_App _      -> assert false
                  | Sym_Form_Tuple      -> assert false
                  | Sym_Form_Proj _     -> assert false
                  | Sym_Form_Match _    -> assert false
                  | Sym_Form_Quant _    -> assert false
                  | Sym_Form_Let _      -> assert false
                  | Sym_Form_Pvar _     -> assert false
                  | Sym_Form_Prog_var _ -> assert false
                  | Sym_Form_Glob       -> assert false
                  | Sym_Form_Hoare_F    -> assert false
                  | Sym_Form_Hoare_S    -> assert false
                  | Sym_Form_bd_Hoare_F -> assert false
                  | Sym_Form_bd_Hoare_S -> assert false
                  | Sym_Form_Equiv_F    -> assert false
                  | Sym_Form_Equiv_S    -> assert false
                  | Sym_Form_Eager_F    -> assert false
                  | Sym_Form_Pr         -> assert false
                  | Sym_Stmt_Seq        -> assert false
                  | Sym_Instr_Assign    -> assert false
                  | Sym_Instr_Sample    -> assert false
                  | Sym_Instr_Call      -> assert false
                  | Sym_Instr_Call_Lv   -> assert false
                  | Sym_Instr_If        -> assert false
                  | Sym_Instr_While     -> assert false
                  | Sym_Instr_Assert    -> assert false
                  | Sym_Xpath           -> assert false
                  | Sym_Mpath           -> assert false
                  | Sym_App             -> assert false
                  | Sym_Quant _         -> assert false
                end
              | Some p,eng ->
                 let ep = match ep with
                   | None, map, e ->
                      None, map, e
                   | Some p, map, engine ->
                      Some p, map, { engine with e_env = eng.e_env } in
                 match abstract_opt other_args ep (arg,p) with
                 | None, _, _ -> None, (map, env)
                 | Some p, map, eng -> Some p, (map, eng.e_env)
            end
          (* | Pat_Axiom (Axiom_Form f as axiom2),_
           *      when fst(eq_axiom axiom axiom2 e.e_env) ->
           *    Some (Pat_Axiom(Axiom_Form (f_local arg f.f_ty))),
           *    (Mid.add arg (GTty f.f_ty) map,env)
           * | Pat_Axiom axiom2,_
           *      when fst(eq_axiom axiom axiom2 e.e_env) ->
           *    (\* FIXME *\)
           *    Some (Pat_Meta_Name (Pat_Anything,arg)), (o, env) *)

          | Pat_Axiom axiom2, axiom1 ->
             let eq_ax, env = eq_axiom axiom1 axiom2 e.e_env in
             if eq_ax
             then Some(Pat_Meta_Name(Pat_Anything,arg)), (o,env)
             else
               match axiom1, axiom2 with
               | Axiom_Memory _,_
                 | Axiom_MemEnv _,_
                 | Axiom_Op _,_
                 | Axiom_Hoarecmp _,_
                 -> raise (Invalid_argument "ici")
               | Axiom_Local (id,ty), _ when eq_name id arg ->
                  Some (Pat_Type(Pat_Meta_Name(Pat_Anything,arg),GTty ty)), (o,env)
               | Axiom_Local _,_ -> None, (o,env)
               | Axiom_Module (`Local id),_ when eq_name id arg ->
                  (* FIXME *)
                  Some (Pat_Meta_Name (Pat_Anything,arg)), (o,env)
               | Axiom_Module _,_ -> None, (o,env)
               | Axiom_Mpath mp1, _ ->
                  myomap (fun l -> Pat_Fun_Symbol (Sym_Mpath, l))
                    (ofold_list id aux (o,env)
                       (List.map (fun m -> Pat_Axiom (Axiom_Mpath m)) mp1.m_args))
               | Axiom_Prog_Var pv1, _ ->
                  myomap (fun x -> Pat_Fun_Symbol (Sym_Form_Prog_var pv1.pv_kind, [x]))
                    (aux (o,env) (Pat_Axiom (Axiom_Xpath pv1.pv_name)))
               | Axiom_Xpath xp1, _ ->
                  myomap (fun l -> Pat_Fun_Symbol (Sym_Xpath,l))
                    (ofold_list id aux (o,env)
                       [Pat_Axiom (Axiom_Mpath xp1.x_top);
                        Pat_Axiom (Axiom_Op (xp1.x_sub,[]))])
               | Axiom_Lvalue lv, a -> begin
                   match a, lv with
                   | Axiom_Prog_Var pv1, LvVar (pv2,_) when pv_equal pv1 pv2 ->
                      Some (Pat_Meta_Name (Pat_Anything,arg)), (o,env)
                   | Axiom_Prog_Var _, LvTuple l ->
                      myomap (fun l -> Pat_Fun_Symbol (Sym_Form_Tuple,l))
                        (ofold_list id aux (o,env)
                           (List.map (fun (x,_) -> Pat_Axiom (Axiom_Prog_Var x)) l))
                   | Axiom_Prog_Var _, _ -> (* FIXME *) None, (o,env)
                   | Axiom_Lvalue (LvVar (pv1,ty1)), LvVar (pv2,ty2)
                        when pv_equal pv1 pv2 ->
                      let eq_ty, env = eq_type ty1 ty2 e.e_env in
                      if eq_ty then Some (Pat_Meta_Name (Pat_Anything,arg)), (o,env)
                      else None, (o,env)
                   | Axiom_Lvalue (LvVar (_,_)), LvTuple t ->
                      myomap (fun l -> Pat_Fun_Symbol (Sym_Form_Tuple,l))
                        (ofold_list id aux (o,env)
                           (List.map (fun x -> Pat_Axiom (Axiom_Lvalue (LvVar x))) t))
                   | _,_ -> (* FIXME : LvMap *) None, (o,env)
                 end

               | Axiom_Stmt s1, axiom2 -> begin
                   match myomap (fun l -> Pat_Fun_Symbol (Sym_Stmt_Seq,l))
                           (ofold_list id aux (o,env)
                              (List.map (fun i -> Pat_Axiom (Axiom_Instr i)) s1.s_node)) with
                   | Some _,_ as res -> res
                   | None, (o,env) ->
                      match axiom2 with
                      | Axiom_Stmt s2 -> begin
                          if List.compare_lengths s1.s_node s2.s_node <= 0
                          then None, (o,env)
                          else
                            match
                              aux (o,env)
                                (Pat_Axiom (Axiom_Stmt (stmt (List.tl s1.s_node)))) with
                            | Some _,_ as res -> res
                            | None,(o,env) ->
                               aux (o,env)
                                 (Pat_Axiom
                                    (Axiom_Stmt
                                       (stmt
                                          (List.rev (List.tl (List.rev s1.s_node))))))
                        end
                      |  _ -> None, (o,env)
                 end

               | Axiom_Instr i, a2 -> begin
                   match a2,i.i_node with
                   | Axiom_Hoarecmp _,_
                     | Axiom_Memory _,_
                     | Axiom_MemEnv _,_ -> None, (o,env)
                   | _, Sasgn (lv1,e1) ->
                      myomap (fun l -> Pat_Fun_Symbol (Sym_Instr_Assign,l))
                        (ofold_list id aux (o,env)
                           [Pat_Axiom (Axiom_Lvalue lv1);
                            Pat_Axiom (Axiom_Form (form_of_expr e1))])
                   | _, Srnd (lv1,e1) ->
                      myomap (fun l -> Pat_Fun_Symbol (Sym_Instr_Sample,l))
                        (ofold_list id aux (o,env)
                           [Pat_Axiom (Axiom_Lvalue lv1);
                            Pat_Axiom (Axiom_Form (form_of_expr e1))])
                   | _,Scall (None,f1,args1) ->
                      myomap (fun l -> Pat_Fun_Symbol (Sym_Instr_Call,l))
                        (ofold_list id aux (o,env)
                           ((Pat_Axiom (Axiom_Xpath f1))::
                              (List.map (fun x -> Pat_Axiom (Axiom_Form (form_of_expr x))) args1)))
                   | _,Scall (Some lv1,f1,args1) ->
                      myomap (fun l -> Pat_Fun_Symbol (Sym_Instr_Call,l))
                        (ofold_list id aux (o,env)
                           ((Pat_Axiom (Axiom_Lvalue lv1))::
                              (Pat_Axiom (Axiom_Xpath f1))::
                                (List.map (fun x -> Pat_Axiom (Axiom_Form (form_of_expr x))) args1)))
                   | _,Sassert e1 ->
                      myomap (fun l -> Pat_Fun_Symbol (Sym_Instr_Assert,[l]))
                        (aux (o,env) (Pat_Axiom (Axiom_Form (form_of_expr e1))))
                   | _,Sif (e1,strue1,sfalse1) ->
                      myomap (fun l -> Pat_Fun_Symbol (Sym_Instr_If,l))
                        (ofold_list id aux (o,env)
                           [Pat_Axiom (Axiom_Form (form_of_expr e1));
                            Pat_Axiom (Axiom_Stmt strue1);
                            Pat_Axiom (Axiom_Stmt sfalse1)])
                   | _,Swhile (e1,sbody1) ->
                      myomap (fun l -> Pat_Fun_Symbol (Sym_Instr_While,l))
                        (ofold_list id aux (o,env)
                           [Pat_Axiom (Axiom_Form (form_of_expr e1));
                            Pat_Axiom (Axiom_Stmt sbody1)])
                   | _,Sabstract _ -> None, (o,env)
                 end

               | Axiom_Form f1, _ -> begin
                   match f1.f_node with
                   | Fquant (_,bds,_) when List.exists (fun (a,_) -> id_equal a arg) bds ->
                      raise (Invalid_argument "ici2")
                   | Fquant (q,bds,f1) ->
                      myomap (fun l -> Pat_Fun_Symbol (Sym_Form_Quant (q,bds),[l]))
                        (aux (o,env) (Pat_Axiom (Axiom_Form f1)))
                   | Fif (f1,f2,f3) ->
                      myomap (fun l -> Pat_Fun_Symbol (Sym_Form_If,l))
                        (ofold_list id aux (o,env)
                           [Pat_Axiom (Axiom_Form f1);
                            Pat_Axiom (Axiom_Form f2);
                            Pat_Axiom (Axiom_Form f3)])
                   | Fmatch (f1,matches,_) ->
                      myomap (fun l -> Pat_Fun_Symbol (Sym_Form_Match f1.f_ty,l))
                        (ofold_list id aux (o,env)
                           ((Pat_Axiom (Axiom_Form f1))::
                              (List.map (fun x -> Pat_Axiom (Axiom_Form x)) matches)))
                   | Flet (lv,f1,f2) -> begin
                       if (match lv with
                           | LSymbol (id,_) ->
                              id_equal id arg
                           | LTuple l ->
                              List.exists (fun (a,_) -> id_equal a arg) l
                           | LRecord (_,l) ->
                              List.exists (fun (a,_) -> odfl false (omap (id_equal arg) a)) l)
                       then
                         None, (o,env)
                       else
                         myomap (fun l -> Pat_Fun_Symbol (Sym_Form_Let lv,l))
                           (ofold_list id aux (o,env)
                              [Pat_Axiom (Axiom_Form f1);
                               Pat_Axiom (Axiom_Form f2)])
                     end
                   | Fint _ -> None, (o,env)
                   | Flocal _ -> None, (o,env)
                   | Fpvar (pv,m) ->
                      myomap (fun l -> Pat_Fun_Symbol (Sym_Form_Pvar f1.f_ty,l))
                        (ofold_list id aux (o,env)
                           [Pat_Axiom (Axiom_Prog_Var pv);
                            Pat_Axiom (Axiom_Memory m)])
                   | Fglob (m,mem) ->
                      myomap (fun l -> Pat_Fun_Symbol (Sym_Form_Glob,l))
                        (ofold_list id aux (o,env) [Pat_Axiom (Axiom_Mpath m);Pat_Axiom (Axiom_Memory mem)])
                   | Fop _ -> None, (o,env)
                   | Fapp (f1,fargs) ->
                      myomap (fun l -> Pat_Fun_Symbol (Sym_Form_App f1.f_ty,l))
                        (ofold_list id aux (o,env) (List.map (fun x -> Pat_Axiom (Axiom_Form x)) (f1::fargs)))
                   | Ftuple tuple ->
                      myomap (fun l -> Pat_Fun_Symbol (Sym_Form_Tuple,l))
                        (ofold_list id aux (o,env) (List.map (fun x -> Pat_Axiom (Axiom_Form x)) tuple))
                   | Fproj (f,i) ->
                      myomap (fun l -> Pat_Fun_Symbol (Sym_Form_Proj i,[l]))
                        (aux (o,env) (Pat_Axiom (Axiom_Form f)))
                   | FhoareF h ->
                      myomap (fun l -> Pat_Fun_Symbol (Sym_Form_Hoare_F,l))
                        (ofold_list id aux (o,env)
                           [Pat_Axiom (Axiom_Form h.hf_pr);
                            Pat_Axiom (Axiom_Xpath h.hf_f);
                            Pat_Axiom (Axiom_Form h.hf_po)])
                   | FhoareS h ->
                      myomap (fun l -> Pat_Fun_Symbol (Sym_Form_Hoare_S,l))
                        (ofold_list id aux (o,env)
                           [Pat_Axiom (Axiom_MemEnv h.hs_m);
                            Pat_Axiom (Axiom_Form h.hs_pr);
                            Pat_Axiom (Axiom_Stmt h.hs_s);
                            Pat_Axiom (Axiom_Form h.hs_po)])
                   | FbdHoareF h ->
                      myomap (fun l -> Pat_Fun_Symbol (Sym_Form_bd_Hoare_F,l))
                        (ofold_list id aux (o,env)
                           [Pat_Axiom (Axiom_Form h.bhf_pr);
                            Pat_Axiom (Axiom_Xpath h.bhf_f);
                            Pat_Axiom (Axiom_Form h.bhf_po);
                            Pat_Axiom (Axiom_Hoarecmp h.bhf_cmp);
                            Pat_Axiom (Axiom_Form h.bhf_bd)])
                   | FbdHoareS h ->
                      myomap (fun l -> Pat_Fun_Symbol (Sym_Form_bd_Hoare_S,l))
                        (ofold_list id aux (o,env)
                           [Pat_Axiom (Axiom_MemEnv h.bhs_m);
                            Pat_Axiom (Axiom_Form h.bhs_pr);
                            Pat_Axiom (Axiom_Stmt h.bhs_s);
                            Pat_Axiom (Axiom_Form h.bhs_po);
                            Pat_Axiom (Axiom_Hoarecmp h.bhs_cmp);
                            Pat_Axiom (Axiom_Form h.bhs_bd)])
                   | FequivF h ->
                      myomap (fun l -> Pat_Fun_Symbol (Sym_Form_Equiv_F,l))
                        (ofold_list id aux (o,env)
                           [Pat_Axiom (Axiom_Form h.ef_pr);
                            Pat_Axiom (Axiom_Xpath h.ef_fl);
                            Pat_Axiom (Axiom_Xpath h.ef_fr);
                            Pat_Axiom (Axiom_Form h.ef_po)])
                   | FequivS h ->
                      myomap (fun l -> Pat_Fun_Symbol (Sym_Form_Equiv_S,l))
                        (ofold_list id aux (o,env)
                           [Pat_Axiom (Axiom_MemEnv h.es_ml);
                            Pat_Axiom (Axiom_MemEnv h.es_mr);
                            Pat_Axiom (Axiom_Form h.es_pr);
                            Pat_Axiom (Axiom_Stmt h.es_sl);
                            Pat_Axiom (Axiom_Stmt h.es_sr);
                            Pat_Axiom (Axiom_Form h.es_po)])
                   | FeagerF h ->
                      myomap (fun l -> Pat_Fun_Symbol (Sym_Form_Eager_F,l))
                        (ofold_list id aux (o,env)
                           [Pat_Axiom (Axiom_Form h.eg_pr);
                            Pat_Axiom (Axiom_Stmt h.eg_sl);
                            Pat_Axiom (Axiom_Xpath h.eg_fl);
                            Pat_Axiom (Axiom_Xpath h.eg_fr);
                            Pat_Axiom (Axiom_Stmt h.eg_sr);
                            Pat_Axiom (Axiom_Form h.eg_po)])
                   | Fpr h ->
                      myomap (fun l -> Pat_Fun_Symbol (Sym_Form_Pr,l))
                        (ofold_list id aux (o,env)
                           [Pat_Axiom (Axiom_Memory h.pr_mem);
                            Pat_Axiom (Axiom_Xpath h.pr_fun);
                            Pat_Axiom (Axiom_Form h.pr_args);
                            Pat_Axiom (Axiom_Form h.pr_event)])
                 end

     in
     match aux (map,e.e_env) p with
     | None, (map,env) -> None, map, { e with e_env = restore_environnement env }
     | Some p, (map,env) -> Some p, map, { e with e_env = restore_environnement env }


(* ---------------------------------------------------------------------- *)
let rec process (e : engine) : nengine =
  let binds = e.e_binds in
  let e = match e.e_env.env_red_strat e.e_pattern e.e_head with
    | None -> e
    | Some (p,a) ->
       let e_or = { e with e_pattern = p; e_head = a } in
       { e with e_continuation = Zor (e.e_continuation, [e_or], (e_next e)) }
  in
  match e.e_pattern, e.e_head with
  | Pat_Anything, _ -> next Match e

  | Pat_Meta_Name (p,name), _ ->
     process { e with
         e_pattern = p;
         e_continuation = Znamed(Pat_Axiom e.e_head,name,e.e_continuation);
       }

  | Pat_Sub p, _ ->
     let le = sub_engines e p in
     process { e with
         e_pattern = p;
         e_continuation = Zor (e.e_continuation,le,e_next e);
       }

  | Pat_Type (p,ty), o2 -> begin
      match o2,ty with
      | Axiom_Form f, GTty ty ->
         let eq_ty, env = eq_type ty f.f_ty e.e_env in
         if eq_ty then process { e with e_pattern = p; e_env = env }
         else
           next NoMatch { e with
               e_env = restore_environnement env;
             }
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
     let f p = { e with
                 e_pattern = p;
               } in
     process { e with
         e_pattern = p;
         e_continuation = Zor (e.e_continuation,List.map f pl,e_next e);
       }

  | Pat_Red_Strat (p,f),_ ->
     process { e with
         e_pattern = p;
         e_env = { e.e_env with env_red_strat = f }
       }

  | Pat_Fun_Symbol (Sym_Form_Quant (q1,bs1), [p]),
    Axiom_Form { f_node = Fquant (q2,bs2,f2) } ->
     begin
       (* FIXME : lambda case to be considered in higher order *)
       if not(q1 = q2) then next NoMatch e
       else
         match merge_binds bs1 bs2 binds with
         | None -> next NoMatch e
         | Some (new_binds,[],args) ->
            let p =
              Mid.fold_left
                (fun acc n1 (n2,ty) ->
                  match ty with
                  | GTty ty -> substitution n1 (Pat_Axiom (Axiom_Form (f_local n2 ty))) acc
                  | _ -> acc)
                p new_binds in
            process { e with
                e_pattern = p;
                e_head = Axiom_Form (f_quant q2 args f2);
                e_binds = new_binds;
                e_continuation = Zbinds (e.e_continuation, binds);
              }
         | Some (_new_binds,_args,[]) -> (* FIXME for higher order *)
            (*    let p = *)
            (*      Mid.fold_left *)
            (*        (fun acc n1 (n2,ty) -> *)
            (*          match ty with *)
            (*          | GTty ty -> substitution n1 (Pobject (Oform (f_local n2 ty))) acc *)
            (*          | _ -> acc) *)
            (*        p new_binds in *)
            (*    let p = Pquant (q1,args,p) in *)
            (*    process_higer_order { e with *)
            (*                          e_pattern = p; *)
            (*                          e_head = Oform f2, new_binds; *)
            (*                          e_continuation = Zbinds (e.e_continuation, binds); *)
            (*                        } *)
            next NoMatch e
         | _ -> assert false
     end

  | Pat_Axiom o1, o2 -> begin
      let eq_ty, env = eq_axiom o1 o2 e.e_env in
      if eq_ty then next Match { e with e_env = env }
      else
        match o1 with
        | Axiom_Form f1 -> begin
            match f1.f_node with
            | Flocal id1 -> begin
                match Mid.find_opt id1 e.e_env.env_map with
                | None ->
                   next NoMatch e
                | Some (Pat_Axiom o1' as e_pattern) ->
                   let eq_ax, env = eq_axiom o1 o1' e.e_env in
                   if eq_ax
                   then
                     next NoMatch { e with e_env = restore_environnement env; }
                   else process { e with e_pattern }
                | Some e_pattern ->
                   process { e with e_pattern; e_env = env }
              end
            | _ -> next NoMatch e
          end
        | Axiom_Module (`Local id) -> begin
            match MName.find_opt id e.e_env.env_map with
            | None -> next NoMatch e
            | Some (Pat_Axiom o1' as e_pattern) ->
               let eq_ax, env = eq_axiom o1 o1' e.e_env in
               if eq_ax
               then next NoMatch { e with e_env = restore_environnement env; }
               else process { e with e_pattern ; e_env = env}
            | Some o1 ->
               process { e with e_pattern = o1 }
          end

        | Axiom_Mpath { m_top = `Local id ; m_args = [] } -> begin
            match MName.find_opt id e.e_env.env_map with
            | None -> next NoMatch e
            | Some (Pat_Axiom o1' as e_pattern) ->
               let eq_ax, env = eq_axiom o1 o1' e.e_env in
               if eq_ax
               then next NoMatch { e with e_env = restore_environnement env; }
               else process { e with e_pattern ; e_env = env}
            | Some o1 ->
               process { e with e_pattern = o1 }
          end

        | _ -> next NoMatch e
    end

  (* | Pat_Fun_Symbol (Sym_Form_App,
   *                   [Pat_Meta_Name (Pat_Type (Pat_Anything,_),name);
   *                   (Pat_Axiom (Axiom_Form { f_node = Fint _ }) as arg)]), axiom ->
   *    begin
   *      let arg_name = EcIdent.create (string_of_int 0) in
   *      match abstract_opt (Sid.singleton arg_name) (Some (e,Pat_Axiom axiom)) (arg_name, arg) with
   *      | None -> next NoMatch e
   *      | Some _ ->
   *         process { e with
   *             e_pattern = Pat_Meta_Name (Pat_Anything,name) }
   *    end *)

  | Pat_Fun_Symbol(Sym_App,(Pat_Meta_Name(Pat_Anything,name))::pargs),axiom
    | Pat_Fun_Symbol(Sym_App,(Pat_Meta_Name(Pat_Type(Pat_Anything,_),name))::pargs),axiom
    | Pat_Fun_Symbol(Sym_Form_App _,(Pat_Meta_Name(Pat_Anything,name))::pargs),axiom
    | Pat_Fun_Symbol(Sym_Form_App _,(Pat_Meta_Name(Pat_Type(Pat_Anything,_),name))::pargs),axiom ->
     begin
       (* higher order *)
       let args = List.mapi (fun i x -> EcIdent.create (String.concat "" ["s";string_of_int i]), x) pargs in
       let pat_opt, map, e =
         (* FIXME : add strategies to adapt the order of the arguments *)
         List.fold_left (abstract_opt (Sid.of_list (List.map fst args)))
           (Some (Pat_Axiom axiom),Mid.empty,e) args in
       match pat_opt with
       | None -> next NoMatch e
       | Some pat ->
          (* FIXME : add restrictions according to the types *)
          let f (name,_) = (name,Mid.find_opt name map) in
          let args = List.map f args in
          let pat = Pat_Fun_Symbol(Sym_Quant(Llambda,args),[pat]) in
          let (pat, e) = match rewrite_pattern_opt e pat with
            | Some pat,e -> pat, e
            | None, e -> pat, e in
          let m,e =
            try
              let e = add_match e name pat in
              Match, e
            with
            | CannotUnify -> NoMatch, { e with e_env = restore_environnement e.e_env }
          in
          next m e
     end

  | Pat_Fun_Symbol (symbol, lp), o2 -> begin
      match o2 with
      | Axiom_Local (_id,_ty) ->
         (* this should not appear in o2 *) next NoMatch e
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
             (* FIXME : higher order *)
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
          | Sym_App, (Pat_Meta_Name (p,_))::_,_ -> begin
              match p with
              | Pat_Type _ -> raise (Invalid_argument "pat_type")
              | Pat_Anything -> raise (Invalid_argument "anything")
              | _ -> assert false
            end
          | Sym_Form_Tuple, lp, Ftuple lf
               when 0 = List.compare_lengths lp lf -> begin
              match lp, lf with
              | [], _::_ | _::_,[] -> assert false
              | [], [] -> next Match e
              | p::ptuple, f::ftuple ->
                 let zand = List.map2 (fun x y -> Axiom_Form x, y) ftuple ptuple in
                 let l = (Axiom_Form f, p)::zand in
                 let pat,o,l = match List.rev l with
                   | [] -> assert false
                   | (o,p)::l -> p,o,l
                 in
                 let cont = Zand ([],zand,e.e_continuation) in
                 let or_e = { e with
                              e_pattern = pat;
                              e_head = o;
                              e_continuation = Zand ([],l,e.e_continuation) } in
                 let cont = Zor (cont, [or_e], e_next e) in
                 process { e with
                     e_pattern = p;
                     e_head = Axiom_Form f;
                     e_binds = binds;
                     e_continuation = cont }
            end
          | Sym_Form_Proj i, [e_pattern], Fproj (f,j) when i = j ->
             process { e with e_pattern;
                              e_head = Axiom_Form f }
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
                   e_binds = binds;
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
                   e_binds = binds;
                   e_continuation = Zand ([],[Axiom_Form f,p1],e.e_continuation);
                 }
             else next NoMatch { e with e_env = restore_environnement env }
          | Sym_Form_Prog_var _, [p], Fpvar (x2,_) ->
             process { e with
                 e_pattern = p;
                 e_head = Axiom_Xpath x2.pv_name;
               }
          | Sym_Form_Glob, p1::p2::[], Fglob (x,m) ->
             let zand = [Axiom_Module x.m_top,p1] in
             process { e with
                 e_pattern = p2;
                 e_head = Axiom_Memory m;
                 e_binds = binds;
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
                 e_binds = binds;
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
                 e_binds = binds;
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
                 e_binds = binds;
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
                 e_binds = binds;
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
                 e_binds = binds;
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
                 e_binds = binds;
                 e_continuation = Zand ([],zand,e.e_continuation); }
          | Sym_Form_Pr, [pmem;pf;pargs;pevent], Fpr pr ->
             let fmem,ff,fargs,fevent =
               pr.pr_mem,pr.pr_fun,pr.pr_args,pr.pr_event in
             let zand = [Axiom_Xpath ff,pf;
                         Axiom_Form fargs,pargs;
                         Axiom_Form fevent,pevent] in
             process { e with
                 e_pattern = pmem;
                 e_head = Axiom_Memory fmem;
                 e_binds = binds;
                 e_continuation = Zand ([],zand,e.e_continuation); }
          | _ -> next NoMatch e
        end

      | Axiom_Memory _ | Axiom_MemEnv _ | Axiom_Prog_Var _
        | Axiom_Op _ ->
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
             let (rev_pargs2,rev_pargs1),(rev_margs2,rev_margs1) =
               List.prefix2 (List.rev rest) (List.rev m.m_args) in
             let pargs1,pargs2,margs1,margs2 =
               List.rev rev_pargs1,
               List.rev rev_pargs2,
               List.rev rev_margs1,
               List.rev rev_margs2 in
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
                 e_binds = binds;
                 e_continuation = Zand ([],zand,e.e_continuation); }
          | Sym_Instr_Call, pf::pargs, Scall (None,ff,fargs)
               when 0 = List.compare_lengths pargs fargs ->
             let fmap x y = (Axiom_Form (form_of_expr x),y) in
             let zand = List.map2 fmap fargs pargs in
             process { e with
                 e_pattern = pf;
                 e_head = Axiom_Xpath ff;
                 e_binds = binds;
                 e_continuation = Zand ([],zand,e.e_continuation); }
          | Sym_Instr_Call_Lv, plv::pf::pargs, Scall (Some flv,ff,fargs) ->
             let fmap x y = (Axiom_Form (form_of_expr x),y) in
             let zand = List.map2 fmap fargs pargs in
             let zand = (Axiom_Lvalue flv,plv)::zand in
             process { e with
                 e_pattern = pf;
                 e_head = Axiom_Xpath ff;
                 e_binds = binds;
                 e_continuation = Zand ([],zand,e.e_continuation); }
          | Sym_Instr_If, [pe;ptrue;pfalse], Sif (fe,strue,sfalse) ->
             let zand = [Axiom_Stmt strue,ptrue;
                         Axiom_Stmt sfalse,pfalse] in
             process { e with
                 e_pattern = pe;
                 e_head = Axiom_Form (form_of_expr fe);
                 e_binds = binds;
                 e_continuation = Zand ([],zand,e.e_continuation); }
          | Sym_Instr_While, [pe;pbody], Swhile (fe,fbody) ->
             let zand = [Axiom_Stmt fbody,pbody] in
             process { e with
                 e_pattern = pe;
                 e_head = Axiom_Form (form_of_expr fe);
                 e_binds = binds;
                 e_continuation = Zand ([],zand,e.e_continuation); }
          | Sym_Instr_Assert, [pe], Sassert fe ->
             process { e with
                 e_pattern = pe;
                 e_head = Axiom_Form (form_of_expr fe);
                 e_binds = binds; }
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
                 e_binds = binds;
                 e_continuation = Zand ([],zand,e.e_continuation); }
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
                 e_binds = binds;
                 e_continuation = Zand ([],zand,e.e_continuation); }
          | _ -> next NoMatch e
        end

      | Axiom_Hoarecmp _ -> next NoMatch e


                                 (* | _ -> next NoMatch e *)

    end

  | Pat_Instance (_,_,_,_), _ -> (* FIXME *) assert false

and next (m : ismatch) (e : engine) : nengine = next_n m (e_next e)

and next_n (m : ismatch) (e : nengine) : nengine =
  match m,e.ne_continuation with
  | NoMatch, ZTop -> raise NoMatches

  | Match, ZTop   -> e

  | NoMatch, Znamed (_f, _name, ne_continuation) ->
     next_n NoMatch { e with
         ne_continuation;
         ne_env = restore_environnement e.ne_env;
       }

  | Match, Znamed (f, name, ne_continuation) ->
     let m,e =
       try
         let ne = nadd_match e name f in
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
     process (n_engine f p { e with ne_continuation = Zand ((f,p)::before,after,z)})

  | Match, Zor (ne_continuation, _, _) -> next_n Match { e with ne_continuation }

  | NoMatch, Zor (_, [], ne) ->
     next_n NoMatch { ne with ne_env = restore_environnement e.ne_env; }

  | NoMatch, Zor (_, e'::engines, ne) ->
     process { e' with
         e_continuation = Zor (e'.e_continuation, engines, ne);
         e_env = restore_environnement e'.e_env;
       }

  | Match, Zbinds (ne_continuation, ne_binds) ->
     next_n Match { e with ne_continuation; ne_binds }

  | NoMatch, Zbinds (ne_continuation, ne_binds) ->
     next_n NoMatch { e with
         ne_continuation;
         ne_binds;
         ne_env = restore_environnement e.ne_env;
       }

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
         [sub_engine e p e.e_binds (Axiom_Form (form_of_expr expr))]
      | Scall (_,_,args) ->
         List.map (fun x -> sub_engine e p e.e_binds (Axiom_Form (form_of_expr x))) args
      | Sif (cond,strue,sfalse) ->
         [sub_engine e p e.e_binds (Axiom_Form (form_of_expr cond));
          sub_engine e p e.e_binds (Axiom_Stmt strue);
          sub_engine e p e.e_binds (Axiom_Stmt sfalse)]
      | Swhile (cond,body) ->
         [sub_engine e p e.e_binds (Axiom_Form (form_of_expr cond));
          sub_engine e p e.e_binds (Axiom_Stmt body)]
      | Sassert cond ->
         [sub_engine e p e.e_binds (Axiom_Form (form_of_expr cond))]
      | _ -> []
    end
  | Axiom_Stmt s ->
     List.map (fun x -> sub_engine e p e.e_binds (Axiom_Instr x)) s.s_node
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
         List.map (sub_engine e p e.e_binds) [Axiom_Form cond;Axiom_Form f1;Axiom_Form f2]
      | Fapp (f, args) ->
         List.map (sub_engine e p e.e_binds) ((Axiom_Form f)::(List.map (fun x -> Axiom_Form x) args))
      | Ftuple args ->
         List.map (sub_engine e p e.e_binds) (List.map (fun x -> Axiom_Form x) args)
      | Fproj (f,_) -> [sub_engine e p e.e_binds (Axiom_Form f)]
      | Fmatch (f,fl,_) ->
         List.map (sub_engine e p e.e_binds) ((Axiom_Form f)::(List.map (fun x -> Axiom_Form x) fl))
      | Fpr pr ->
         List.map (sub_engine e p e.e_binds)
           [Axiom_Memory pr.pr_mem;Axiom_Form pr.pr_args;Axiom_Form pr.pr_event]
      | Fquant (_,bs,f) ->
         let binds = Mid.of_list (List.map (fun (x,y) -> (x,(x,y)))bs) in
         [sub_engine e p binds (Axiom_Form f)]
      | Fglob (mp,mem) ->
         List.map (sub_engine e p e.e_binds)
           [Axiom_Module mp.m_top;Axiom_Memory mem]
      | Fpvar (_pv,mem) ->
         [sub_engine e p e.e_binds (Axiom_Memory mem)]
    end


let get_matches (e : engine) : map = e.e_env.env_map
let get_n_matches (e : nengine) : map = e.ne_env.env_map

let search_eng e =
  try Some(process e) with
  | NoMatches -> None

let search (f : form) (p : pattern) (h : LDecl.hyps) (red : reduction_strategy)
      (red_info : EcReduction.reduction_info) (unienv : EcUnify.unienv) =
  try
    let ne = process (mkengine f p h red red_info unienv) in
    Some (get_n_matches ne, ne.ne_env)
  with
  | NoMatches -> None

let pattern_of_axiom (bindings: bindings) (a : axiom) =
  let sbd           = Mid.of_list bindings in
  let pat_axiom x   = Pat_Axiom x in
  let pat_form x    = Pat_Axiom (Axiom_Form x) in
  let axiom_expr e  = Axiom_Form (form_of_expr e) in
  let axiom_mpath m = Axiom_Mpath m in
  let axiom_form f  = Axiom_Form f in
  let pat_instr i   = Pat_Axiom (Axiom_Instr i) in
  let typ ty p      = Pat_Type(p,GTty ty) in

  let rec aux a     = match a with
    | Axiom_Local (id,ty) ->
       if Mid.mem id sbd then Some(Pat_Type(Pat_Meta_Name(Pat_Anything,id),GTty ty))
       else Some (Pat_Axiom a)
    | Axiom_Form f -> begin
        let fty = f.f_ty in
        match f.f_node with
        | Fquant(quant,binds,f) when Mid.set_disjoint (Sid.of_list (List.map fst binds)) sbd ->
           omap (fun fi -> typ fty (Pat_Fun_Symbol(Sym_Form_Quant(quant,binds),[fi])))
             (aux_f f)
        | Fquant _ -> raise (Invalid_argument "quantificator on variables that are aimed to be abstracted as meta-variables.")
        | Fif(f1,f2,f3) ->
           omap (fun l -> typ fty (Pat_Fun_Symbol(Sym_Form_If,l)))
             (omap_list pat_form aux_f [f1;f2;f3])
        | Fmatch(f,args,ty) ->
           omap (fun l -> Pat_Fun_Symbol(Sym_Form_Match ty,l))
             (omap_list pat_form aux_f (f::args))
        | Flet (lp,f1,f2) -> begin
            match lp with
            | LSymbol (id,_) when Mid.mem id sbd ->
               raise (Invalid_argument "let-operation on a variable that is aimed to be abstracted as a meta-variable.")
            | LTuple tuple when not(Mid.set_disjoint (Sid.of_list (List.map fst tuple)) sbd) ->
               raise (Invalid_argument "let-operation on variables that are aimed to be abstracted as meta-variables.")
            | LRecord _ ->
               raise (Invalid_argument "let-operation using the notation of fmap.")
            | _ ->
               omap (fun l -> typ fty (Pat_Fun_Symbol(Sym_Form_Let lp,l)))
                 (omap_list pat_form aux_f [f1;f2])
          end
        | Fint _ -> None
        | Flocal id ->
           if Mid.mem id sbd
           then Some (Pat_Meta_Name (Pat_Type (Pat_Anything,GTty fty), id))
           else if mem_ty_univar fty
           then Some(Pat_Axiom(Axiom_Local(id,fty)))
           else None
        | Fpvar(x,m) ->
           omap (fun l -> Pat_Fun_Symbol (Sym_Form_Pvar fty,l))
             (omap_list pat_axiom aux [Axiom_Prog_Var x;Axiom_Memory m])
        | Fglob(mp, m) ->
           omap (fun l -> Pat_Fun_Symbol (Sym_Form_Glob,l))
             (omap_list pat_axiom aux [Axiom_Mpath mp;Axiom_Memory m])
        | Fop (op,lty) ->
           Some(typ fty (Pat_Axiom(Axiom_Op(op,lty))))
        | Fapp ({ f_node = Flocal id },args) when Mid.mem id sbd ->
           Some
             (typ fty
                (Pat_Fun_Symbol
                   (Sym_App,
                    (Pat_Meta_Name(Pat_Anything,id))::
                      (List.map
                         (fun x ->
                           odfl (Pat_Axiom(Axiom_Form x))
                             (aux_f x))
                         args))))
        | Fapp(fop,args) ->
           if mem_ty_univar fty
           then
             Some
               (typ fty
                  (Pat_Fun_Symbol
                     (Sym_Form_App fty,
                      List.map (fun x -> odfl (Pat_Axiom x) (aux x))
                        (List.map axiom_form (fop::args)))))
           else
             omap (fun l -> typ fty (Pat_Fun_Symbol(Sym_Form_App fty,l)))
               (omap_list pat_form aux_f (fop::args))
        | Ftuple args ->
           omap (fun l -> typ fty (Pat_Fun_Symbol(Sym_Form_Tuple,l)))
             (omap_list pat_form aux_f args)
        | Fproj(f,i) ->
           if mem_ty_univar fty
           then
             Some
               (typ fty
                  (Pat_Fun_Symbol
                     (Sym_Form_Proj i,
                      [odfl (pat_form f) (aux_f f)])))
           else
             omap (fun x -> typ fty (Pat_Fun_Symbol(Sym_Form_Proj i,[x])))
               (aux_f f)
        | FhoareF h ->
           omap (fun l -> Pat_Fun_Symbol(Sym_Form_Hoare_F,l))
             (omap_list pat_axiom aux
                [Axiom_Form h.hf_pr;
                 Axiom_Xpath h.hf_f;
                 Axiom_Form h.hf_po])
        | FhoareS h ->
           omap (fun l -> Pat_Fun_Symbol(Sym_Form_Hoare_S,l))
             (omap_list pat_axiom aux
                [Axiom_MemEnv h.hs_m;
                 Axiom_Form h.hs_pr;
                 Axiom_Stmt h.hs_s;
                 Axiom_Form h.hs_po])
        | FbdHoareF h ->
           omap (fun l -> Pat_Fun_Symbol(Sym_Form_bd_Hoare_F,l))
             (omap_list pat_axiom aux
                [Axiom_Form h.bhf_pr;
                 Axiom_Xpath h.bhf_f;
                 Axiom_Form h.bhf_po;
                 Axiom_Hoarecmp h.bhf_cmp;
                 Axiom_Form h.bhf_bd])
        | FbdHoareS h ->
           omap (fun l -> Pat_Fun_Symbol(Sym_Form_bd_Hoare_S,l))
             (omap_list pat_axiom aux
                [Axiom_MemEnv h.bhs_m;
                 Axiom_Form h.bhs_pr;
                 Axiom_Stmt h.bhs_s;
                 Axiom_Form h.bhs_po;
                 Axiom_Hoarecmp h.bhs_cmp;
                 Axiom_Form h.bhs_bd])
        | FequivF h ->
           omap (fun l -> Pat_Fun_Symbol(Sym_Form_Equiv_F,l))
             (omap_list pat_axiom aux
                [Axiom_Form h.ef_pr;
                 Axiom_Xpath h.ef_fl;
                 Axiom_Xpath h.ef_fr;
                 Axiom_Form h.ef_po])
        | FequivS h ->
           omap (fun l -> Pat_Fun_Symbol(Sym_Form_Equiv_S,l))
             (omap_list pat_axiom aux
                [Axiom_MemEnv h.es_ml;
                 Axiom_MemEnv h.es_mr;
                 Axiom_Form h.es_pr;
                 Axiom_Stmt h.es_sl;
                 Axiom_Stmt h.es_sr;
                 Axiom_Form h.es_po])
        | FeagerF h ->
           omap (fun l -> Pat_Fun_Symbol(Sym_Form_Equiv_F,l))
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
           omap (fun l -> Pat_Fun_Symbol(Sym_Form_Pr,l))
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
        Some (Pat_Meta_Name(Pat_Anything,m))
    | Axiom_MemEnv m when Mid.mem (fst m) sbd ->
       (* let gty = match Mid.find_opt (fst m) sbd with
        *   | Some gty -> gty
        *   | None -> assert false in
        * Some (Pat_Type(Pat_Meta_Name(Pat_Anything, fst m),gty)) *)
       Some (Pat_Meta_Name(Pat_Anything, fst m))
    | Axiom_Prog_Var pv ->
       omap (fun x -> Pat_Fun_Symbol(Sym_Form_Prog_var pv.pv_kind,[x]))
         (aux (Axiom_Xpath pv.pv_name))
    | Axiom_Op _ -> None
    | Axiom_Module mt -> begin
        match mt with
        | `Local id when Mid.mem id sbd ->
           let gty = match Mid.find_opt id sbd with
             | Some gty -> gty
             | None -> assert false in
           Some (Pat_Type(Pat_Meta_Name(Pat_Anything, id),gty))
           (* Some (Pat_Meta_Name(Pat_Anything, id)) *)
        | _ -> None
      end
    | Axiom_Mpath m ->
       omap (fun l -> Pat_Fun_Symbol(Sym_Mpath,l))
         (omap_list pat_axiom aux ((Axiom_Module m.m_top)::(List.map axiom_mpath m.m_args)))
    | Axiom_Instr i -> begin
        match i.i_node with
        | Sasgn (lv,e) ->
           omap (fun l -> Pat_Fun_Symbol (Sym_Instr_Assign,l))
             (omap_list pat_axiom aux [Axiom_Lvalue lv; Axiom_Form (form_of_expr e)])
        | Srnd (lv,e) ->
           omap (fun l -> Pat_Fun_Symbol (Sym_Instr_Sample,l))
             (omap_list pat_axiom aux [Axiom_Lvalue lv; Axiom_Form (form_of_expr e)])
        | Scall (None,f,args) ->
           omap (fun l -> Pat_Fun_Symbol (Sym_Instr_Call,l))
             (omap_list pat_axiom aux ((Axiom_Xpath f)::(List.map axiom_expr args)))
        | Scall (Some lv,f,args) ->
           omap (fun l -> Pat_Fun_Symbol (Sym_Instr_Call_Lv,l))
             (omap_list pat_axiom aux ((Axiom_Lvalue lv)::(Axiom_Xpath f)::(List.map axiom_expr args)))
        | Sif (e,strue,sfalse) ->
           omap (fun l -> Pat_Fun_Symbol (Sym_Instr_If, l))
             (omap_list pat_axiom aux [axiom_expr e;Axiom_Stmt strue;Axiom_Stmt sfalse])
        | Swhile (e,sbody) ->
           omap (fun l -> Pat_Fun_Symbol (Sym_Instr_While, l))
             (omap_list pat_axiom aux [axiom_expr e;Axiom_Stmt sbody])
        | Sassert e ->
           omap (fun x -> Pat_Fun_Symbol (Sym_Instr_Assert,[x]))
             (aux (axiom_expr e))
        | Sabstract id when Mid.mem id sbd ->
           Some (Pat_Meta_Name (Pat_Anything, id))
        | Sabstract _ -> None
      end
    | Axiom_Stmt s ->
       omap (fun l -> Pat_Fun_Symbol (Sym_Stmt_Seq,l))
         (omap_list pat_instr aux_i s.s_node)
    | Axiom_Lvalue lv -> begin
        match lv with
        | LvVar (pv,ty) ->
           omap (fun x -> Pat_Type (x,GTty ty))
             (aux (Axiom_Prog_Var pv))
        | LvTuple l ->
           let default (pv,ty) =
             Pat_Type (Pat_Axiom (Axiom_Prog_Var pv),GTty ty) in
           let aux (pv,ty) =
             omap (fun x -> Pat_Type (x,GTty ty)) (aux (Axiom_Prog_Var pv)) in
           omap (fun l -> Pat_Fun_Symbol (Sym_Form_Tuple,l))
             (omap_list default aux l)
        | LvMap _ -> (* FIXME *) raise (Invalid_argument "bleuh")
      end
    | Axiom_Xpath xp ->
       omap (fun x -> Pat_Fun_Symbol (Sym_Xpath,[x;Pat_Axiom(Axiom_Op (xp.x_sub,[]))]))
         (aux (Axiom_Mpath xp.x_top))
    | Axiom_Hoarecmp _ -> None
    | Axiom_MemEnv _ | Axiom_Memory _ -> None
  and aux_f f = aux (Axiom_Form f)
  and aux_i i = aux (Axiom_Instr i)
  in aux a

let pattern_of_form b f =
  odfl (Pat_Axiom(Axiom_Form f)) (pattern_of_axiom b (Axiom_Form f))




module PReduction = struct
  open EcReduction

  let pat_axiom a = Pat_Axiom a

  let ax_mem m = Axiom_Memory m
  let ax_memenv m = Axiom_MemEnv m
  let ax_pv pv = Axiom_Prog_Var pv
  let ax_op (op,lty) = Axiom_Op (op,lty)
  let ax_mp m = Axiom_Mpath m
  let ax_i i = Axiom_Instr i
  let ax_s s = Axiom_Stmt s
  let ax_lv lv = Axiom_Lvalue lv
  let ax_xp x = Axiom_Xpath x
  let ax_id (id,ty) = Axiom_Local (id,ty)
  let ax_f f = Axiom_Form f

  let pat_form f = pat_axiom (ax_f f)

  let is_record (env : environnement) (f : form) =
    match EcFol.destr_app f with
    | { f_node = Fop (p,_) }, _ ->
       EcEnv.Op.is_record_ctor (LDecl.toenv env.env_hyps) p
    | _ -> false

  let reduce_local_opt (env : environnement) (id : Name.t) : pattern option =
    if env.env_red_info.delta_h id
    then
      match MName.find_opt id env.env_map with
      | Some p -> Some p
      | None ->
         try Some (Pat_Axiom(Axiom_Form(LDecl.unfold id env.env_hyps))) with
         | NotReducible -> None
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
    | Axiom_Module m      -> h_red_mpath_top_opt env (mpath m [])
    | Axiom_Mpath m       -> h_red_mpath_opt env m
    | Axiom_Instr i       -> h_red_instr_opt env i
    | Axiom_Stmt s        -> h_red_stmt_opt env s
    | Axiom_Lvalue lv     -> h_red_lvalue_opt env lv
    | Axiom_Xpath x       -> h_red_xpath_opt env x
    | Axiom_Local (id,ty) -> h_red_local_opt env id ty
    | Axiom_Form f        -> h_red_form_opt env f

  and h_red_mem_opt _env _m = None
  and h_red_memenv_opt _env _m = None
  and h_red_prog_var_opt _env _pv = None
  and h_red_op_opt _env _op _lty = None
  and h_red_mpath_top_opt _env _m = None
  and h_red_mpath_opt _env _m = None
  and h_red_instr_opt _env _i = None
  and h_red_stmt_opt _env _s = None
  and h_red_lvalue_opt _env _lv = None
  and h_red_xpath_opt _env _x = None
  and h_red_local_opt _env _id _ty = None

  and h_red_args_form (env : environnement) l =
    omap_list pat_form (h_red_form_opt env) l

  and h_red_form_opt (env : environnement) (f : form) =
    let ri = env.env_red_info in
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
       EcPattern.p_app_simpl_opt (reduce_local_opt env x) pargs f.f_ty

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
       else Some (p_pvar pv' f.f_ty m)

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
            EcPattern.p_app_simpl_opt op (List.map pat_form args) f.f_ty

         | _ -> Some (pat_form f)
       in
       begin
         match f' with
         | Some (Pat_Axiom(Axiom_Form f')) ->
            if f_equal f f'
            then omap (fun l -> p_app (pat_form fo) l (Some f.f_ty))
                   (h_red_args_form env args)
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
       EcPattern.p_app_simpl_opt op (List.map pat_form args) f.f_ty

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
