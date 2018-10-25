open EcUtils
open EcFol
open EcTypes
open EcPath
open EcIdent
open EcEnv
open EcModules

(* ---------------------------------------------------------------------- *)
exception Matches
exception NoMatches
exception CannotUnify
exception NoNext


module Name = struct
  include EcIdent
  let compare = id_compare
end

module MName = Mid


(* -------------------------------------------------------------------------- *)

module FPattern = struct

  type meta_name = Name.t

  type axiom =
    | Axiom_Form     of form
    | Axiom_Memory   of EcMemory.memory
    | Axiom_MemEnv   of EcMemory.memenv
    | Axiom_Prog_Var of prog_var
    | Axiom_Local    of ident
    | Axiom_Op       of EcPath.path * EcTypes.ty list
    | Axiom_Module   of mpath_top
    | Axiom_Mpath    of mpath
    | Axiom_Instr    of EcModules.instr
    | Axiom_Stmt     of EcModules.stmt
    | Axiom_Lvalue   of EcModules.lvalue
    | Axiom_Xpath    of EcPath.xpath
    | Axiom_Hoarecmp of EcFol.hoarecmp

  type fun_symbol =
    (* from type form *)
    | Sym_Form_If
    | Sym_Form_App
    | Sym_Form_Tuple
    | Sym_Form_Proj         of int
    | Sym_Form_Match
    | Sym_Form_Quant        of quantif * bindings
    | Sym_Form_Let          of lpattern
    | Sym_Form_Pvar
    | Sym_Form_Prog_var     of EcTypes.pvar_kind
    | Sym_Form_Glob
    | Sym_Form_Local
    | Sym_Form_Hoare_F
    | Sym_Form_Hoare_S
    | Sym_Form_bd_Hoare_F
    | Sym_Form_bd_Hoare_S
    | Sym_Form_Equiv_F
    | Sym_Form_Equiv_S
    | Sym_Form_Eager_F
    | Sym_Form_Pr
    (* form type stmt*)
    | Sym_Stmt_Seq
    (* from type instr *)
    | Sym_Instr_Assign
    | Sym_Instr_Sample
    | Sym_Instr_Call
    | Sym_Instr_Call_Lv
    | Sym_Instr_If
    | Sym_Instr_While
    | Sym_Instr_Assert
    (* from type xpath *)
    | Sym_Xpath
    (* from type mpath *)
    | Sym_Mpath
    (* generalized *)
    | Sym_Quant             of quantif * (ident list)

  (* invariant of pattern : if the form is not Pat_Axiom, then there is
     at least one of the first set of patterns *)
  type pattern =
    | Pat_Anything
    | Pat_Meta_Name  of pattern * meta_name
    | Pat_Sub        of pattern
    | Pat_Or         of pattern list
    | Pat_Instance   of pattern option * meta_name * EcPath.path * pattern list
    | Pat_Red_Strat  of pattern * reduction_strategy

    | Pat_Fun_Symbol of fun_symbol * pattern list
    | Pat_Axiom      of axiom
    | Pat_Type       of pattern * ty

  and reduction_strategy = pattern -> axiom -> (pattern * axiom) option


  type environnement = {
      env_hyps      : EcEnv.LDecl.hyps;
      env_unienv    : EcUnify.unienv;
      env_red_strat : reduction_strategy;
      (* FIXME : ajouter ici les stratégies *)
    }

  type map = (pattern * binding Mid.t) MName.t


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
      e_map          : map;
      e_env          : environnement;
    }

  and nengine = {
      ne_continuation : pat_continuation;
      ne_map          : map;
      ne_binds        : binding Mid.t;
      ne_env          : environnement;
    }

  (* val mkengine    : base -> engine *)
  let mkengine (f : form) (p : pattern) (h : LDecl.hyps)
        (strategy : reduction_strategy) : engine = {
      e_head         = Axiom_Form f;
      e_binds        = Mid.empty ;
      e_continuation = ZTop ;
      e_map          = MName.empty ;
      e_pattern      = p ;
      e_env          = {
          env_hyps      = h;
          env_unienv    = EcUnify.UniEnv.create None;
          env_red_strat = strategy;
        } ;
    }

  type ismatch =
    | Match
    | NoMatch

  let my_mem = EcIdent.create "new_mem"

  let form_of_expr = EcFol.form_of_expr my_mem

  let eq_form (f1 : form) (f2 : form) (_env : environnement) =
    match f1.f_node, f2.f_node with
    | Fint i1, Fint i2 -> EcBigInt.equal i1 i2
    | _ -> f_equal f1 f2

  let eq_memory (m1 : EcMemory.memory) (m2 : EcMemory.memory) (_env : environnement) =
    EcMemory.mem_equal m1 m2

  let eq_memenv (m1 : EcMemory.memenv) (m2 : EcMemory.memenv) (_env : environnement) =
    EcMemory.me_equal m1 m2

  let eq_prog_var (x1 : prog_var) (x2 : prog_var) (_env : environnement) =
    pv_equal x1 x2

  let eq_local i1 i2 _ = id_equal i1 i2

  let eq_op
        ((op1, lty1) : EcPath.path * EcTypes.ty list)
        ((op2, lty2) : EcPath.path * EcTypes.ty list)
        (_env : environnement) =
    EcPath.p_equal op1 op2 && List.for_all2 EcTypes.ty_equal lty1 lty2

  let eq_module (m1 : mpath_top) (m2 : mpath_top) (_env : environnement) =
    EcPath.mt_equal m1 m2

  let eq_type (ty1 : ty) (ty2 : ty) (_env : environnement) =
    ty_equal ty1 ty2

  let eq_name (n1 : meta_name) (n2 : meta_name) =
    0 = Name.compare n1 n2

  let eq_instr (i1 : EcModules.instr) (i2 : EcModules.instr) (_env : environnement) =
    EcModules.i_equal i1 i2

  let eq_stmt (s1 : EcModules.stmt) (s2 : EcModules.stmt) (_env : environnement) =
    EcModules.s_equal s1 s2

  let eq_lvalue (lv1 : lvalue) (lv2 :lvalue) (_env : environnement) : bool =
    lv_equal lv1 lv2

  let eq_mpath (m1 : mpath) (m2 : mpath) (_env : environnement) : bool =
    m_equal m1 m2

  let eq_xpath (x1 : xpath) (x2 : xpath) (_env : environnement) : bool =
    x_equal x1 x2

  let eq_hoarecmp (c1 : hoarecmp) (c2 : hoarecmp) (_ : environnement) : bool =
    c1 = c2

  let eq_type (ty1 : ty) (ty2 : ty) (env : environnement) : bool =
    try
      EcUnify.unify (EcEnv.LDecl.toenv env.env_hyps) env.env_unienv ty1 ty2;
      true
    with
    | _ -> false

  let eq_axiom (o1 : axiom) (o2 : axiom) (env : environnement) : bool =
    let aux o1 o2 =
      match o1,o2 with
      | Axiom_Form f1, Axiom_Form f2 ->
         eq_form f1 f2 env
      | Axiom_Memory m1, Axiom_Memory m2 ->
         eq_memory m1 m2 env
      | Axiom_MemEnv m1, Axiom_MemEnv m2 ->
         eq_memenv m1 m2 env
      | Axiom_Prog_Var x1, Axiom_Prog_Var x2 ->
         eq_prog_var x1 x2 env
      | Axiom_Local x1, Axiom_Local x2 ->
         eq_local x1 x2 env
      | Axiom_Op (op1,lty1), Axiom_Op (op2,lty2) ->
         eq_op (op1,lty1) (op2,lty2) env
      | Axiom_Module m1, Axiom_Module m2 ->
         eq_module m1 m2 env
      | Axiom_Mpath m1, Axiom_Mpath m2 ->
         eq_mpath m1 m2 env
      | Axiom_Instr i1, Axiom_Instr i2 ->
         eq_instr i1 i2 env
      | Axiom_Stmt s1, Axiom_Stmt s2 ->
         eq_stmt s1 s2 env
      | Axiom_Lvalue lv1, Axiom_Lvalue lv2 ->
         eq_lvalue lv1 lv2 env
      | Axiom_Xpath x1, Axiom_Xpath x2 ->
         eq_xpath x1 x2 env
      | Axiom_Hoarecmp c1, Axiom_Hoarecmp c2 ->
         eq_hoarecmp c1 c2 env


      | _,_ -> false
    in
    if aux o1 o2 then true
    else
      match env.env_red_strat (Pat_Axiom o1) o2 with
      | None -> false
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
  let add_match (map : map) (name : meta_name) (p : pattern)
        (b : binding Mid.t) h =
    if Mid.set_disjoint b map
    then
      let fv =
        match p with
        | Pat_Axiom a -> begin
            match a with
            | Axiom_Form f     -> Mid.set_inter b (f_fv f)
            | Axiom_Memory m   -> Mid.set_inter b (Sid.singleton m)
            | Axiom_Instr i    -> Mid.set_inter b (i_fv i)
            | Axiom_Stmt s     -> Mid.set_inter b (s_fv s)
            | Axiom_Local id   -> Mid.set_inter b (Sid.singleton id)
            | Axiom_MemEnv m   ->
               Mid.set_union
                 (Mid.set_inter b (EcMemory.mt_fv (snd m)))
                 (Mid.set_inter b (Sid.singleton (fst m)))
            | Axiom_Lvalue lv  ->
               Mid.set_inter b (i_fv (i_asgn (lv,e_int (EcBigInt.of_int 0))))
            | Axiom_Prog_Var _ -> Mid.empty
            | Axiom_Op _       -> Mid.empty
            | Axiom_Module _   -> Mid.empty
            | Axiom_Mpath _    -> Mid.empty
            | Axiom_Xpath _    -> Mid.empty
            | Axiom_Hoarecmp _ -> Mid.empty
          end
        | _ -> (* FIXME *) Mid.empty
      in
      let map = match Mid.find_opt name map with
        | None                  -> Mid.add name (p,fv) map
        | Some (Pat_Axiom o1,_) -> begin
            match p with
            | Pat_Axiom a -> if eq_axiom o1 a h then map
                             else raise CannotUnify
            | _ -> assert false
          end
        | _                     -> (* FIXME *) assert false
      in map
    else raise CannotUnify

  let e_next (e : engine) : nengine =
    { ne_continuation = e.e_continuation;
      ne_map = e.e_map;
      ne_binds = e.e_binds;
      ne_env = e.e_env;
    }

  let n_engine (a : axiom) (e_pattern : pattern) (n : nengine) =
    { e_head = a;
      e_binds = n.ne_binds;
      e_pattern;
      e_continuation = n.ne_continuation;
      e_map = n.ne_map;
      e_env = n.ne_env;
    }


  let sub_engine e p b f =
    { e with e_head = f; e_pattern = Pat_Sub p; e_binds = b }


  let p_app_simpl p subst env =
    let rec aux = function
      | Pat_Anything -> Pat_Anything
      | Pat_Meta_Name (p1,name) -> begin
          match MName.find_opt name subst with
          | None -> Pat_Meta_Name (p1,name)
          | Some (Pat_Type (p2,ty1), GTty ty2) when eq_type ty1 ty2 env -> Pat_Type (p2,ty1)
          | Some (Pat_Type _, GTty _) -> assert false
          | Some (p,GTty ty) -> Pat_Type (p,ty)
          | Some (p,GTmem _) | Some (p, GTmodty _) -> p
        end
      | Pat_Red_Strat (p,f) -> Pat_Red_Strat (aux p,f)
      | Pat_Sub p1 -> Pat_Sub (aux p1)
      | Pat_Or lp -> Pat_Or (List.map aux lp)
      | Pat_Instance (ret,name,fun_name,args) ->
         Pat_Instance (omap aux ret,name,fun_name,List.map aux args)
      | Pat_Fun_Symbol (symbol,lp) -> begin
          match symbol with
          | Sym_Form_Quant (q,binds) when MName.set_disjoint subst (MName.of_list binds) ->
             Pat_Fun_Symbol (Sym_Form_Quant (q,binds), List.map aux lp)
          | Sym_Form_Quant _ ->
             raise (Invalid_argument
                      "in p_app_simpl : invalid argument name, it has been found in a sub quantif.")
          | _ ->
             Pat_Fun_Symbol (symbol, List.map aux lp)
        end
      | Pat_Axiom axiom ->
         Pat_Axiom axiom
      | Pat_Type (p1,ty) -> Pat_Type (aux p1, ty)
    in aux p

  let omap_list (default : 'a -> 'b) (f : 'a -> 'b option) (l : 'a list) : 'b list option =
    let rec aux acc there_is_Some = function
      | [] -> if there_is_Some then Some (List.rev acc) else None
      | x::rest when there_is_Some -> aux ((odfl (default x) (f x))::acc) there_is_Some rest
      | x::rest -> match f x with
                   | None -> aux ((default x)::acc) false rest
                   | Some x -> aux (x::acc) true rest in
    aux [] false l

  let olist f (l : 'a list) = omap_list (fun x -> x) f l

  let replace_id id subst env =
    match Mid.find_opt id subst with
    | None -> None
    | Some (Pat_Type (p,ty1),GTty ty2) when eq_type ty2 ty1 env -> Some (Pat_Type (p,ty1))
    | Some (Pat_Type _, GTty _) -> assert false
    | Some (_,GTty _) -> None
    | Some (p,GTmem _) | Some (p, GTmodty _) -> Some p

  let p_app_simpl_opt p subst env =
    let rec aux = function
      | Pat_Anything -> None
      | Pat_Meta_Name (_,name) -> replace_id name subst env
      | Pat_Sub p1 -> omap (fun x -> Pat_Sub x) (aux p1)
      | Pat_Or lp -> omap (fun x -> Pat_Or x) (olist aux lp)
      | Pat_Fun_Symbol (symbol,lp) -> begin
          match symbol with
          | Sym_Form_Quant (q,binds) when Mid.set_disjoint subst (Mid.of_list binds) ->
             omap (fun x -> Pat_Fun_Symbol (Sym_Form_Quant (q,binds), x)) (olist aux lp)
          | Sym_Form_Quant _ ->
             raise (Invalid_argument
                      "in p_app_simpl_opt : invalid argument name, it has been found in a sub quantif.")
          | _ ->
             omap (fun x -> Pat_Fun_Symbol (symbol, x)) (olist aux lp)
        end
      | Pat_Axiom axiom -> (* FIXME *) Some (Pat_Axiom axiom)
      | Pat_Type (p1,ty) -> omap (fun p -> Pat_Type (p,ty)) (aux p1)
      | Pat_Red_Strat (p,f) -> omap (fun p -> Pat_Red_Strat (p,f)) (aux p)
      | Pat_Instance (opt_lv, name, fun_name, args) -> begin
         match replace_id name subst env with
         | None ->
            omap (fun x -> Pat_Instance (opt_lv, name, fun_name, x)) (olist aux args)
         | Some p -> Some p
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
    in aux p


  let obeta_reduce env = function
    | Pat_Fun_Symbol (Sym_Form_App,
                      (Pat_Fun_Symbol (Sym_Form_Quant (Llambda,binds),[p]))
                      ::pargs) ->
       let (bs1,bs2), (pargs1,pargs2) = List.prefix2 binds pargs in
       let p = match pargs2 with
         | [] -> p
         | _ -> Pat_Fun_Symbol (Sym_Form_App, p::pargs2) in
       let p = match bs2 with
         | [] -> p
         | _ -> Pat_Fun_Symbol (Sym_Form_Quant (Llambda, bs2), [p]) in
       let subst = Mid.empty in
       let subst =
         try List.fold_left2 (fun a (b,t) c -> Mid.add_new Not_found b (c,t) a) subst bs1 pargs1
         with
         | Not_found -> raise (Invalid_argument "beta_reduce : two bindings have got the same name.")
       in
       p_app_simpl_opt p subst env
    | _ -> None


  let beta_reduce env = function
    | Pat_Fun_Symbol (Sym_Form_App,
                      (Pat_Fun_Symbol (Sym_Form_Quant (Llambda,binds),[p]))
                      ::pargs) ->
       let (bs1,bs2), (pargs1,pargs2) = List.prefix2 binds pargs in
       let p = match pargs2 with
         | [] -> p
         | _ -> Pat_Fun_Symbol (Sym_Form_App, p::pargs2) in
       let p = match bs2 with
         | [] -> p
         | _ -> Pat_Fun_Symbol (Sym_Form_Quant (Llambda, bs2), [p]) in
       let subst = Mid.empty in
       let subst =
         try List.fold_left2 (fun a (b,t) c -> Mid.add_new Not_found b (c,t) a) subst bs1 pargs1
         with
         | Not_found -> raise (Invalid_argument "beta_reduce : two bindings have got the same name.")
       in
       p_app_simpl p subst env
    | p -> p

  let rec mpath_to_pattern (m : mpath) =
    Pat_Fun_Symbol (Sym_Mpath, (Pat_Axiom (Axiom_Module m.m_top))
                               ::(List.map mpath_to_pattern m.m_args))


  let subst_name n1 n2 p =
    let rec aux = function
      | Pat_Anything -> Pat_Anything
      | Pat_Meta_Name (p,name) when eq_name n1 name -> Pat_Meta_Name (p,n2)
      | Pat_Meta_Name (p2,name) -> Pat_Meta_Name (aux p2,name)
      | Pat_Sub p2 -> aux p2
      | Pat_Or lp -> Pat_Or (List.map aux lp)

      | Pat_Fun_Symbol (Sym_Form_Quant (q,binds),lp)
           when Mid.mem n1 (Mid.of_list binds) ->
         (* FIXME *) Pat_Fun_Symbol (Sym_Form_Quant (q,binds),lp)
      | Pat_Fun_Symbol (symbol,lp) -> Pat_Fun_Symbol (symbol, List.map aux lp)
      | Pat_Type (p2,ty) -> Pat_Type (aux p2, ty)
      | Pat_Instance (opt_lv, module_name, fun_name, args)
           when 0 = Name.compare module_name n1 ->
         Pat_Instance (opt_lv, n2, fun_name, args)
      | Pat_Instance (a,b,c,args) -> Pat_Instance (a,b,c, List.map aux args)
      | Pat_Red_Strat (p,f) -> Pat_Red_Strat (aux p,f)
      | Pat_Axiom axiom ->
         match axiom with
         | Axiom_Memory m when 0 = Name.compare m n1 -> Pat_Axiom (Axiom_Memory n2)
         | Axiom_MemEnv (m,mt) when 0 = Name.compare m n1 -> Pat_Axiom (Axiom_MemEnv (n2,mt))
         | Axiom_Local id when 0 = Name.compare id n1 -> Pat_Axiom (Axiom_Local n2)
         (* | Axiom_Module mt1 when Name.mt_equal mt1 n1 ->
          *    let p = match n2 with
          *      | Name.Id id -> Pat_Axiom (Axiom_Local id)
          *      | Name.Mpath mp -> Pat_Axiom (Axiom_Module mp)
          *      | Name.Path p -> Pat_Axiom (Axiom_Op (p,[]))
          *    in p *)
         | Axiom_Form f when Mid.mem n1 f.f_fv -> begin
           match f.f_node with
           |  Flocal id when id_equal id n1 ->
               Pat_Fun_Symbol (Sym_Form_Local,[Pat_Axiom (Axiom_Form (f_local n2 f.f_ty))])
           | Fquant (_quant,bs,_f') when Mid.mem n1 (Mid.of_list bs) ->
              (* FIXME *) Pat_Axiom axiom
           | Fquant (quant,bs,f') when Mid.mem n1 f'.f_fv ->
              Pat_Fun_Symbol (Sym_Form_Quant (quant,bs), [aux (Pat_Axiom (Axiom_Form f'))])
           | Fif (f1,f2,f3) ->
              let lp = List.map aux (List.map (fun x -> Pat_Axiom (Axiom_Form x)) [f1;f2;f3]) in
              Pat_Fun_Symbol (Sym_Form_If, lp)
           | Fmatch _ | Flet _-> Pat_Axiom axiom (* FIXME *)
           | Fint _ -> Pat_Axiom axiom
           | Fpvar (pvar,mem) when id_equal mem n1 ->
              Pat_Fun_Symbol (Sym_Form_Pvar,[Pat_Axiom (Axiom_Form (f_pvar pvar f.f_ty n2))])
           | Fglob (mpath,mem) when id_equal mem n1 ->
              Pat_Fun_Symbol (Sym_Form_Glob, [mpath_to_pattern mpath; Pat_Axiom (Axiom_Memory n2)])
           | Fop _ -> Pat_Axiom axiom (* FIXME *)
           | Fapp (f1,fargs) ->
              let lp = f1 :: fargs in
              let lp = List.map (fun x -> Pat_Axiom (Axiom_Form x)) lp in
              let lp = List.map aux lp in
              Pat_Fun_Symbol (Sym_Form_App, lp)
           | Ftuple lp ->
              let lp = List.map (fun x -> Pat_Axiom (Axiom_Form x)) lp in
              let lp = List.map aux lp in
              Pat_Fun_Symbol (Sym_Form_Tuple, lp)
           | Fproj (f1,i) ->
              let p = aux (Pat_Axiom (Axiom_Form f1)) in
              Pat_Fun_Symbol (Sym_Form_Proj i, [p])
           | _ -> (* FIXME *) p
           end
         | Axiom_Lvalue _ -> Pat_Axiom axiom
         | Axiom_Memory _ | Axiom_MemEnv _ | Axiom_Form _ | Axiom_Prog_Var _
           | Axiom_Local _ | Axiom_Op _ | Axiom_Module _ | Axiom_Instr _
           | Axiom_Stmt _ | Axiom_Xpath _ | Axiom_Hoarecmp _ | Axiom_Mpath _ ->
            Pat_Axiom axiom

      (* | Panything -> Panything
       * | Pif (p2,p3,p4) -> Pif (aux p2,aux p3,aux p4)
       * | Papp (p2,pl) -> Papp (aux p2,List.map aux pl)
       * | Ptuple pl -> Ptuple (List.map aux pl)
       * | Pproj (p2,i) -> Pproj (aux p2,i)
       * | Pmatch (p2,pl) -> Pmatch (aux p2,List.map aux pl)
       * | Pquant (q,bs,p2) -> Pquant (q,bs,aux p2)
       * | Ppvar (p2,p3) -> Ppvar (aux p2,aux p3)
       * | Pglob (p2,p3) -> Pglob (aux p2,aux p3)
       * | Ppr (p2,p3,p4,p5) -> Ppr (aux p2,
       *                             aux p3,
       *                             aux p4,
       *                             aux p5)
       * | Pprog_var pv -> Pprog_var pv (\* FIXME *\)
       * | Pxpath xp -> Pxpath xp  (\* FIXME *\)
       * | Pmpath (p2,pl) -> Pmpath (aux p2, List.map aux pl)
       * | Pobject (Omem mem) ->
       *    if id_equal n1 mem then Pobject (Omem n2) else Pobject (Omem n1)
       * | Pobject (Ompath_top _) as p -> p
       * | Pobject (Oform f) as p2 ->
       *    if not(Mid.mem n1 f.f_fv) then p2
       *    else match f.f_node with
       *         |  Flocal id ->
       *             if id_equal id n1 then Pobject (Oform (f_local n2 f.f_ty)) else p2
       *         | Fquant (quant,bs,f') ->
       *            if Mid.mem n1 f'.f_fv then Pquant (quant,bs,aux (Pobject (Oform f')))
       *            else p2
       *         | Fif (f1,f2,f3) ->
       *            Pif (aux (Pobject (Oform f1)),
       *                 aux (Pobject (Oform f2)),
       *                 aux (Pobject (Oform f3)))
       *         | Fmatch _ | Flet _-> Pobject (Oform f) (\* FIXME *\)
       *         | Fint _ -> Pobject (Oform f)
       *         | Fpvar (pvar,mem) ->
       *            if id_equal mem n1 then Ppvar (Pprog_var pvar, Pobject (Omem n2))
       *            else p2
       *         | Fglob (mpath,mem) ->
       *            if id_equal mem n1 then
       *              Pglob (aux_mpath mpath, Pobject (Omem n2))
       *            else p2
       *         | Fop _ -> Pobject (Oform f) (\* FIXME *\)
       *         | Fapp (f1,fargs) ->
       *            Papp (aux (Pobject (Oform f1)),
       *                  List.map (fun f -> aux (Pobject (Oform f))) fargs)
       *         | Ftuple t ->
       *            Ptuple (List.map (fun f -> aux (Pobject (Oform f))) t)
       *         | Fproj (f1,i) -> Pproj (aux (Pobject (Oform f1)),i)
       *         | _ -> (\* FIXME *\) p2
       * and aux_mpath mp =
       *   Pmpath (Pobject (Ompath_top mp.m_top), List.map aux_mpath mp.m_args) *)
    in aux p

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
       | Axiom_Local id when eq_name id n1 -> p1
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
              Pat_Fun_Symbol (Sym_Form_App, lp)
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
         | Axiom_Local _ | Axiom_Op _ | Axiom_Module _ | Axiom_Instr _
         | Axiom_Stmt _ | Axiom_Xpath _ | Axiom_Hoarecmp _ | Axiom_Mpath _ ->
          Pat_Axiom axiom
    in aux p

    (* | Panything -> Panything
     * | Pnamed (_,n2) when id_equal n1 n2 -> p1
     * | Pnamed (p2,n2) -> Pnamed (substitution n1 p1 p2, n2)
     * | Psub p -> Psub (substitution n1 p1 p)
     * | Por pl -> Por (List.map (substitution n1 p1) pl)
     * | Ptype (p,ty) -> Ptype (substitution n1 p1 p, ty)
     * | Pif (p2,p3,p4) -> Pif (substitution n1 p1 p2,
     *                          substitution n1 p1 p3,
     *                          substitution n1 p1 p4)
     * | Papp (p2,pl) -> Papp (substitution n1 p1 p2,
     *                         List.map (substitution n1 p1) pl)
     * | Ptuple pl -> Ptuple (List.map (substitution n1 p1) pl)
     * | Pproj (p2,i) -> Pproj (substitution n1 p1 p2,i)
     * | Pmatch (p2,pl) -> Pmatch (substitution n1 p1 p2,
     *                             List.map (substitution n1 p1) pl)
     * | Pquant (q,bs,p2) -> Pquant (q,bs,substitution n1 p1 p2)
     * | Ppvar (p2,p3) -> Ppvar (substitution n1 p1 p2,substitution n1 p1 p3)
     * | Pglob (p2,p3) -> Pglob (substitution n1 p1 p2,substitution n1 p1 p3)
     * | Ppr (p2,p3,p4,p5) -> Ppr (substitution n1 p1 p2,
     *                             substitution n1 p1 p3,
     *                             substitution n1 p1 p4,
     *                             substitution n1 p1 p5)
     * | Pprog_var pv ->
     *    let xp = pv.pv_name in
     *    let name = xp.x_sub in
     *    if (EcPath.tostring name) = (EcIdent.tostring n1) then p1 else p2
     * | Pxpath xp ->
     *    let name = xp.x_sub in
     *    if (EcPath.tostring name) = (EcIdent.tostring n1) then p1 else p2
     * | Pmpath (p2,pl) -> Pmpath (substitution n1 p1 p2,
     *                             List.map (substitution n1 p1) pl)
     * | Pobject (Omem mem) ->
     *    if id_equal n1 mem then p1 else p2
     * | Pobject (Ompath_top _) -> p2
     * | Pobject (Oform f) ->
     *    if not(Mid.mem n1 f.f_fv) then p2
     *    else match f.f_node with
     *         |  Flocal id ->
     *             if id_equal id n1 then Ptype (p1,f.f_ty) else p2
     *         | Fquant (quant,bs,f') ->
     *            if Mid.mem n1 f'.f_fv then Pquant (quant,bs,substitution n1 p1 (Pobject (Oform f')))
     *            else p2
     *         | Fif (f1,f2,f3) ->
     *            Pif (substitution n1 p1 (Pobject (Oform f1)),
     *                 substitution n1 p1 (Pobject (Oform f2)),
     *                 substitution n1 p1 (Pobject (Oform f3)))
     *         | Fmatch _ | Flet _-> Pobject (Oform f) (\* FIXME *\)
     *         | Fint _ -> Pobject (Oform f)
     *         | Fpvar (pvar,mem) ->
     *            if id_equal mem n1 then Ppvar (Pprog_var pvar,p1)
     *            else p2
     *         | Fglob (mpath,mem) ->
     *            if id_equal mem n1 then Pglob (substitution_mpath n1 p1 mpath, p1)
     *            else p2
     *         | Fop _ -> Pobject (Oform f) (\* FIXME *\)
     *         | Fapp (f1,fargs) ->
     *            Papp (substitution n1 p1 (Pobject (Oform f1)),
     *                  List.map (fun f -> substitution n1 p1 (Pobject (Oform f))) fargs)
     *         | Ftuple t ->
     *            Ptuple (List.map (fun f -> substitution n1 p1 (Pobject (Oform f))) t)
     *         | Fproj (f1,i) -> Pproj (substitution n1 p1 (Pobject (Oform f1)),i)
     *         | _ -> (\* FIXME *\) p2 *)

    (* and substitution_mpath n1 p1 mpath =
     *   Pmpath (Pobject (Ompath_top mpath.m_top),
     *           List.map (substitution_mpath n1 p1) mpath.m_args) *)


  let is_conv (e : environnement) (f1 : form) (f2 : form) =
    EcReduction.is_conv e.env_hyps f1 f2


  (* ---------------------------------------------------------------------- *)
  let rec abstract_opt (other_args : Sid.t) (ep : (engine * pattern) option) ((arg,parg) : Name.t * pattern) =
    match ep with
    | None -> None
    | Some (e,p) ->
       let rec aux = function
         | Pat_Anything
           | Pat_Sub _
           | Pat_Or _
           | Pat_Instance _ -> assert false
         | Pat_Meta_Name (_,n) as p when Sid.mem n other_args -> Some p
         | Pat_Meta_Name _ -> None
         | Pat_Fun_Symbol (s,lp) ->
            omap (fun x -> Pat_Fun_Symbol (s,x)) (olist aux lp)
         | Pat_Type (p,_) -> aux p
         | Pat_Red_Strat (p,x) ->
            omap (fun p -> Pat_Red_Strat (p,x)) (aux p)

         | Pat_Axiom axiom ->
            match parg,axiom with
            | Pat_Anything,_
              | Pat_Sub _,_
              | Pat_Or _,_
              | Pat_Instance _,_
              | Pat_Meta_Name _,_ -> assert false
            | Pat_Red_Strat _,_ ->
               (* FIXME *) assert false
            | Pat_Type (p,ty), Axiom_Form f when eq_type f.f_ty ty e.e_env ->
               aux p
            | Pat_Type _,_ -> assert false
            | Pat_Fun_Symbol _,_ ->
               (* FIXME : unification *)
               assert false
            | Pat_Axiom axiom2,_ when eq_axiom axiom axiom2 e.e_env ->
               Some (Pat_Meta_Name (Pat_Anything,arg))

            | Pat_Axiom axiom2, axiom1 ->
               match axiom1, axiom2 with
               | Axiom_Memory _,_
                 | Axiom_MemEnv _,_
                 | Axiom_Local _,_
                 | Axiom_Op _,_
                 | Axiom_Hoarecmp _,_
                 -> raise (Invalid_argument "ici")
               | Axiom_Module (`Local id),_ when eq_name id arg ->
                  Some (Pat_Meta_Name (Pat_Anything,arg))
               | Axiom_Module _,_ -> None
               | Axiom_Mpath mp1, _ ->
                  omap (fun l -> Pat_Fun_Symbol (Sym_Mpath, l))
                    (olist aux (List.map (fun m -> Pat_Axiom (Axiom_Mpath m)) mp1.m_args))
               | Axiom_Prog_Var pv1, _ ->
                  omap (fun x -> Pat_Fun_Symbol (Sym_Form_Prog_var pv1.pv_kind, [x]))
                    (aux (Pat_Axiom (Axiom_Xpath pv1.pv_name)))
               | Axiom_Xpath xp1, _ ->
                  omap (fun l -> Pat_Fun_Symbol (Sym_Xpath,l))
                    (olist aux [Pat_Axiom (Axiom_Mpath xp1.x_top);
                                Pat_Axiom (Axiom_Op (xp1.x_sub,[]))])
               | Axiom_Lvalue lv, a -> begin
                   match a, lv with
                   | Axiom_Prog_Var pv1, LvVar (pv2,_) when pv_equal pv1 pv2 ->
                      Some (Pat_Meta_Name (Pat_Anything,arg))
                   | Axiom_Prog_Var _, LvTuple l ->
                      omap (fun l -> Pat_Fun_Symbol (Sym_Form_Tuple,l))
                        (olist aux (List.map (fun (x,_) -> Pat_Axiom (Axiom_Prog_Var x)) l))
                   | Axiom_Prog_Var _, _ -> (* FIXME *) None
                   | Axiom_Lvalue (LvVar (pv1,ty1)), LvVar (pv2,ty2)
                        when pv_equal pv1 pv2 && eq_type ty1 ty2 e.e_env ->
                      Some (Pat_Meta_Name (Pat_Anything,arg))
                   | Axiom_Lvalue (LvVar (_,_)), LvTuple t ->
                      omap (fun l -> Pat_Fun_Symbol (Sym_Form_Tuple,l))
                        (olist aux (List.map (fun x -> Pat_Axiom (Axiom_Lvalue (LvVar x))) t))
                   | _,_ -> (* FIXME : LvMap *) None
                 end

               | Axiom_Stmt s1, axiom2 -> begin
                   match omap (fun l -> Pat_Fun_Symbol (Sym_Stmt_Seq,l))
                           (olist aux (List.map (fun i -> Pat_Axiom (Axiom_Instr i)) s1.s_node)) with
                   | Some _ as res -> res
                   | None ->
                      match axiom2 with
                      | Axiom_Stmt s2 -> begin
                          if List.compare_lengths s1.s_node s2.s_node <= 0
                          then None
                          else
                            match aux (Pat_Axiom (Axiom_Stmt (stmt (List.tl s1.s_node)))) with
                            | Some _ as res -> res
                            | None -> aux (Pat_Axiom (Axiom_Stmt (stmt (List.rev (List.tl (List.rev s1.s_node))))))
                        end
                      |  _ -> None
                 end

               | Axiom_Instr i, a2 -> begin
                   match a2,i.i_node with
                   | Axiom_Hoarecmp _,_
                     | Axiom_Memory _,_
                     | Axiom_MemEnv _,_ -> None
                   | _, Sasgn (lv1,e1) ->
                      omap (fun l -> Pat_Fun_Symbol (Sym_Instr_Assign,l))
                        (olist aux [Pat_Axiom (Axiom_Lvalue lv1);
                                    Pat_Axiom (Axiom_Form (form_of_expr e1))])
                   | _, Srnd (lv1,e1) ->
                      omap (fun l -> Pat_Fun_Symbol (Sym_Instr_Sample,l))
                        (olist aux [Pat_Axiom (Axiom_Lvalue lv1);
                                           Pat_Axiom (Axiom_Form (form_of_expr e1))])
                   | _,Scall (None,f1,args1) ->
                      omap (fun l -> Pat_Fun_Symbol (Sym_Instr_Call,l))
                        (olist aux
                           ((Pat_Axiom (Axiom_Xpath f1))::
                              (List.map (fun x -> Pat_Axiom (Axiom_Form (form_of_expr x))) args1)))
                   | _,Scall (Some lv1,f1,args1) ->
                      omap (fun l -> Pat_Fun_Symbol (Sym_Instr_Call,l))
                        (olist aux
                           ((Pat_Axiom (Axiom_Lvalue lv1))::
                              (Pat_Axiom (Axiom_Xpath f1))::
                                (List.map (fun x -> Pat_Axiom (Axiom_Form (form_of_expr x))) args1)))
                   | _,Sassert e1 ->
                      omap (fun l -> Pat_Fun_Symbol (Sym_Instr_Assert,[l]))
                        (aux (Pat_Axiom (Axiom_Form (form_of_expr e1))))
                   | _,Sif (e1,strue1,sfalse1) ->
                      omap (fun l -> Pat_Fun_Symbol (Sym_Instr_If,l))
                        (olist aux
                           [Pat_Axiom (Axiom_Form (form_of_expr e1));
                            Pat_Axiom (Axiom_Stmt strue1);
                            Pat_Axiom (Axiom_Stmt sfalse1)])
                   | _,Swhile (e1,sbody1) ->
                      omap (fun l -> Pat_Fun_Symbol (Sym_Instr_While,l))
                        (olist aux
                           [Pat_Axiom (Axiom_Form (form_of_expr e1));
                            Pat_Axiom (Axiom_Stmt sbody1)])
                   | _,Sabstract _ -> None
                 end

               | Axiom_Form f1, _ -> begin
                   match f1.f_node with
                   | Fquant (_,bds,_) when List.exists (fun (a,_) -> id_equal a arg) bds ->
                      raise (Invalid_argument "ici2")
                   | Fquant (q,bds,f1) ->
                      omap (fun l -> Pat_Fun_Symbol (Sym_Form_Quant (q,bds),[l]))
                        (aux (Pat_Axiom (Axiom_Form f1)))
                   | Fif (f1,f2,f3) ->
                      omap (fun l -> Pat_Fun_Symbol (Sym_Form_If,l))
                        (olist aux [Pat_Axiom (Axiom_Form f1);
                                           Pat_Axiom (Axiom_Form f2);
                                           Pat_Axiom (Axiom_Form f3)])
                   | Fmatch (f1,matches,_) ->
                      omap (fun l -> Pat_Fun_Symbol (Sym_Form_Match,l))
                        (olist aux ((Pat_Axiom (Axiom_Form f1))::
                                             (List.map (fun x -> Pat_Axiom (Axiom_Form x)) matches)))
                   | Flet (lv,f1,f2) -> begin
                       if (match lv with
                           | LSymbol (id,_) -> id_equal id arg
                           | LTuple l -> List.exists (fun (a,_) -> id_equal a arg) l
                           | LRecord (_,l) -> List.exists (fun (a,_) -> odfl false (omap (id_equal arg) a)) l)
                       then
                         None
                       else
                         omap (fun l -> Pat_Fun_Symbol (Sym_Form_Let lv,l))
                           (olist aux [Pat_Axiom (Axiom_Form f1);Pat_Axiom (Axiom_Form f2)])
                     end
                   | Fint _ -> None
                   | Flocal _ -> None
                   | Fpvar (pv,m) ->
                      omap (fun l -> Pat_Fun_Symbol (Sym_Form_Pvar,l))
                        (olist aux [Pat_Axiom (Axiom_Prog_Var pv);Pat_Axiom (Axiom_Memory m)])
                   | Fglob (m,mem) ->
                      omap (fun l -> Pat_Fun_Symbol (Sym_Form_Glob,l))
                        (olist aux [Pat_Axiom (Axiom_Mpath m);Pat_Axiom (Axiom_Memory mem)])
                   | Fop _ -> None
                   | Fapp (f1,fargs) ->
                      omap (fun l -> Pat_Fun_Symbol (Sym_Form_App,l))
                        (olist aux (List.map (fun x -> Pat_Axiom (Axiom_Form x)) (f1::fargs)))
                   | Ftuple tuple ->
                      omap (fun l -> Pat_Fun_Symbol (Sym_Form_Tuple,l))
                        (olist aux (List.map (fun x -> Pat_Axiom (Axiom_Form x)) tuple))
                   | Fproj (f,i) ->
                      omap (fun l -> Pat_Fun_Symbol (Sym_Form_Proj i,[l]))
                        (aux (Pat_Axiom (Axiom_Form f)))
                   | FhoareF h ->
                      omap (fun l -> Pat_Fun_Symbol (Sym_Form_Hoare_F,l))
                        (olist aux [Pat_Axiom (Axiom_Form h.hf_pr);
                                           Pat_Axiom (Axiom_Xpath h.hf_f);
                                           Pat_Axiom (Axiom_Form h.hf_po)])
                   | FhoareS h ->
                      omap (fun l -> Pat_Fun_Symbol (Sym_Form_Hoare_S,l))
                        (olist aux [Pat_Axiom (Axiom_MemEnv h.hs_m);
                                           Pat_Axiom (Axiom_Form h.hs_pr);
                                           Pat_Axiom (Axiom_Stmt h.hs_s);
                                           Pat_Axiom (Axiom_Form h.hs_po)])
                   | FbdHoareF h ->
                      omap (fun l -> Pat_Fun_Symbol (Sym_Form_bd_Hoare_F,l))
                        (olist aux [Pat_Axiom (Axiom_Form h.bhf_pr);
                                           Pat_Axiom (Axiom_Xpath h.bhf_f);
                                           Pat_Axiom (Axiom_Form h.bhf_po);
                                           Pat_Axiom (Axiom_Hoarecmp h.bhf_cmp);
                                           Pat_Axiom (Axiom_Form h.bhf_bd)])
                   | FbdHoareS h ->
                      omap (fun l -> Pat_Fun_Symbol (Sym_Form_bd_Hoare_S,l))
                        (olist aux [Pat_Axiom (Axiom_MemEnv h.bhs_m);
                                           Pat_Axiom (Axiom_Form h.bhs_pr);
                                           Pat_Axiom (Axiom_Stmt h.bhs_s);
                                           Pat_Axiom (Axiom_Form h.bhs_po);
                                           Pat_Axiom (Axiom_Hoarecmp h.bhs_cmp);
                                           Pat_Axiom (Axiom_Form h.bhs_bd)])
                   | FequivF h ->
                      omap (fun l -> Pat_Fun_Symbol (Sym_Form_Equiv_F,l))
                        (olist aux [Pat_Axiom (Axiom_Form h.ef_pr);
                                           Pat_Axiom (Axiom_Xpath h.ef_fl);
                                           Pat_Axiom (Axiom_Xpath h.ef_fr);
                                           Pat_Axiom (Axiom_Form h.ef_po)])
                   | FequivS h ->
                      omap (fun l -> Pat_Fun_Symbol (Sym_Form_Equiv_S,l))
                        (olist aux [Pat_Axiom (Axiom_MemEnv h.es_ml);
                                           Pat_Axiom (Axiom_MemEnv h.es_mr);
                                           Pat_Axiom (Axiom_Form h.es_pr);
                                           Pat_Axiom (Axiom_Stmt h.es_sl);
                                           Pat_Axiom (Axiom_Stmt h.es_sr);
                                           Pat_Axiom (Axiom_Form h.es_po)])
                   | FeagerF h ->
                      omap (fun l -> Pat_Fun_Symbol (Sym_Form_Eager_F,l))
                        (olist aux [Pat_Axiom (Axiom_Form h.eg_pr);
                                           Pat_Axiom (Axiom_Stmt h.eg_sl);
                                           Pat_Axiom (Axiom_Xpath h.eg_fl);
                                           Pat_Axiom (Axiom_Xpath h.eg_fr);
                                           Pat_Axiom (Axiom_Stmt h.eg_sr);
                                           Pat_Axiom (Axiom_Form h.eg_po)])
                   | Fpr h ->
                      omap (fun l -> Pat_Fun_Symbol (Sym_Form_Pr,l))
                        (olist aux [Pat_Axiom (Axiom_Memory h.pr_mem);
                                           Pat_Axiom (Axiom_Xpath h.pr_fun);
                                           Pat_Axiom (Axiom_Form h.pr_args);
                                           Pat_Axiom (Axiom_Form h.pr_event)])
                 end

       in omap (fun x -> e,x) (aux p)


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
        match o2 with
        | Axiom_Form f ->
           if eq_type ty f.f_ty e.e_env then
             process { e with e_pattern = p }
           else next NoMatch e
        | _ -> next NoMatch e
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

    | Pat_Fun_Symbol (Sym_Form_Quant (q1,bs1), [p]), Axiom_Form { f_node = Fquant (q2,bs2,f2) } ->
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

    | Pat_Axiom o1, o2 when eq_axiom o1 o2 e.e_env -> next Match e

    | Pat_Axiom o1, _ -> begin
        match o1 with
        | Axiom_Form f1 -> begin
            match f1.f_node with
            | Flocal id1 -> begin
                match Mid.find_opt id1 e.e_map with
                | None -> next NoMatch e
                | Some (Pat_Axiom o1',_) when eq_axiom o1 o1' e.e_env ->
                   next NoMatch e
                | Some (p1,_) ->
                   process { e with e_pattern = p1 }
              end
            | _ -> next NoMatch e
          end
        | Axiom_Local id1 -> begin
            match MName.find_opt id1 e.e_map with
            | None -> next NoMatch e
            | Some (Pat_Axiom o1',_) when eq_axiom o1 o1' e.e_env -> next NoMatch e
            | Some (o1,b) ->
               process { e with
                   e_pattern = o1;
                   e_binds = b; }
          end
        | Axiom_Module (`Local id) -> begin
            match MName.find_opt id e.e_map with
            | None -> next NoMatch e
            | Some (Pat_Axiom o1',_) when eq_axiom o1 o1' e.e_env -> next NoMatch e
            | Some (o1,b) ->
               process { e with e_pattern = o1; e_binds = b }
          end

        | Axiom_Mpath { m_top = `Local id ; m_args = [] } -> begin
            match MName.find_opt id e.e_map with
            | None -> next NoMatch e
            | Some (Pat_Axiom o1',_) when eq_axiom o1 o1' e.e_env -> next NoMatch e
            | Some (o1,b) ->
               process { e with e_pattern = o1; e_binds = b }
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

    | Pat_Fun_Symbol(Sym_Form_App,(Pat_Meta_Name(Pat_Anything,name))::pargs),axiom
      | Pat_Fun_Symbol(Sym_Form_App,(Pat_Meta_Name(Pat_Type(Pat_Anything,_),name))::pargs),axiom ->
       begin
         (* higher order *)
         let args = List.mapi (fun i x -> EcIdent.create (string_of_int i), x) pargs in
         let pat_opt =
           (* FIXME : add strategies to adapt the order of the arguments *)
           List.fold_left (abstract_opt (Sid.of_list (List.map fst args)))
             (Some (e,Pat_Axiom axiom)) args in
         match pat_opt with
         | None -> next NoMatch e
         | Some (e,pat) ->
            (* FIXME : add restrictions according to the types *)
            let pat = Pat_Fun_Symbol(Sym_Quant(Llambda,List.map fst args),[pat]) in
            let m,e =
              try Match, { e with
                           e_map = add_match e.e_map name pat e.e_binds e.e_env;
                         }
              with
              | CannotUnify -> NoMatch, e
            in
            next m e
       end

    | Pat_Fun_Symbol (symbol, lp), o2 -> begin
        match o2 with
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
            | Sym_Form_App, pop :: pargs, Fapp (fop, fargs) ->
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
                      | _ -> Pat_Fun_Symbol (Sym_Form_App, pop::pargs1) in
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
                    let p = Pat_Fun_Symbol (Sym_Form_App, (pop::pargs1)) in
                    let zand = List.map2 (fun x y -> Axiom_Form x, y) fargs2 pargs2 in
                    Some (fun () ->
                        process { e with
                            e_pattern = p;
                            e_continuation = Zand ([],zand,e.e_continuation)
                          })
               in
               (odfl (fun () -> next NoMatch e) oe) ()
            | Sym_Form_App, (Pat_Meta_Name (p,_))::_,_ -> begin
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
            | Sym_Form_Match, p::pl, Fmatch (f,fl,_)
                 when 0 = List.compare_lengths pl fl ->
               let zand = List.map2 (fun x y -> Axiom_Form x, y) fl pl in
               process {
                   e with
                   e_pattern = p;
                   e_head = Axiom_Form f;
                   e_binds = binds;
                   e_continuation = Zand ([],zand,e.e_continuation);
                 }
            | Sym_Form_Pvar, p1::p2::[], Fpvar (_,m) ->
               process { e with
                   e_pattern = p2;
                   e_head = Axiom_Memory m;
                   e_binds = binds;
                   e_continuation = Zand ([],[Axiom_Form f,p1],e.e_continuation);
                 }
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

        | Axiom_Local id2 -> begin
            match MName.find_opt id2 e.e_map with
            | None -> next NoMatch e
            | Some (Pat_Axiom o1,_) when eq_axiom o1 o2 e.e_env -> next NoMatch e
            | Some (Pat_Axiom o1,b) ->
               process { e with
                   e_head = o1;
                   e_binds = b; }
            | Some _ ->
               (* FIXME : unification of patterns *) assert false
          end

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
       next_n NoMatch { e with ne_continuation }

    | Match, Znamed (f, name, ne_continuation) ->
       let m,e =
         try Match, { e with
                      ne_continuation;
                      ne_map = add_match e.ne_map name f e.ne_binds e.ne_env;
                    }
         with
         | CannotUnify ->
            NoMatch, { e with
                       ne_continuation;
                     } in
       next_n m e

    | NoMatch, Zand (_,_,ne_continuation) ->
       next_n NoMatch { e with ne_continuation }

    | Match, Zand (_before,[],ne_continuation) -> next_n Match { e with ne_continuation }
    | Match, Zand (before,(f,p)::after,z) ->
       process (n_engine f p { e with ne_continuation = Zand ((f,p)::before,after,z)})

    | Match, Zor (ne_continuation, _, _) -> next_n Match { e with ne_continuation }

    | NoMatch, Zor (_, [], ne) ->
       next_n NoMatch ne

    | NoMatch, Zor (_, e'::engines, ne) ->
       process { e' with e_continuation = Zor (e'.e_continuation, engines, ne); }

    | Match, Zbinds (ne_continuation, ne_binds) ->
       next_n Match { e with ne_continuation; ne_binds }

    | NoMatch, Zbinds (ne_continuation, ne_binds) ->
       next_n NoMatch { e with ne_continuation; ne_binds }

  and sub_engines (e : engine) (p : pattern) : engine list =
    match e.e_head with
    | Axiom_Memory _   -> []
    | Axiom_MemEnv _   -> []
    | Axiom_Prog_Var _ -> []
    | Axiom_Local _    -> []
    | Axiom_Op _       -> []
    | Axiom_Module _   -> []
    | Axiom_Lvalue _   -> []
    | Axiom_Xpath _    -> []
    | Axiom_Hoarecmp _ -> []
    | Axiom_Mpath _    -> []
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


  let get_matches (e : engine) : map = e.e_map
  let get_n_matches (e : nengine) : map = e.ne_map

  let search_eng e =
    try Some (process e) with
    | NoMatches -> None

  let search (f : form) (p : pattern) (h : LDecl.hyps) (red : reduction_strategy) =
    try Some (get_n_matches (process (mkengine f p h red))) with
    | NoMatches -> None

  let pattern_of_axiom (bindings: bindings) (a : axiom) =
    let sbd = Sid.of_list (List.map fst bindings) in
    let pat_axiom x = Pat_Axiom x in
    let pat_form x = Pat_Axiom (Axiom_Form x) in
    let axiom_expr e = Axiom_Form (form_of_expr e) in
    let axiom_mpath m = Axiom_Mpath m in
    let pat_instr i = Pat_Axiom (Axiom_Instr i) in
    let rec aux a = match a with
      | Axiom_Form f -> begin
          match f.f_node with
          | Fquant(quant,binds,f) when Sid.disjoint (Sid.of_list (List.map fst binds)) sbd ->
             omap (fun f -> Pat_Fun_Symbol (Sym_Form_Quant (quant,binds), [f]))
               (aux_f f)
          | Fquant _ -> raise (Invalid_argument "quantificator on variables that are aimed to be abstracted as meta-variables.")
          | Fif(f1,f2,f3)      ->
             omap (fun l -> Pat_Fun_Symbol (Sym_Form_If, l))
               (omap_list pat_form aux_f [f1;f2;f3])
          | Fmatch(f,args,_ty) ->
             omap (fun l -> Pat_Fun_Symbol (Sym_Form_Match,l))
               (omap_list pat_form aux_f (f::args))
          | Flet (lp,f1,f2) -> begin
              match lp with
              | LSymbol (id,_) when Sid.mem id sbd ->
                 raise (Invalid_argument "let-operation on a variable that is aimed to be abstracted as a meta-variable.")
              | LTuple tuple when not(Sid.disjoint (Sid.of_list (List.map fst tuple)) sbd) ->
                 raise (Invalid_argument "let-operation on variables that are aimed to be abstracted as meta-variables.")
              | LRecord _ ->
                 raise (Invalid_argument "let-operation using the notation of fmap.")
              | _ ->
                 omap (fun l -> Pat_Fun_Symbol (Sym_Form_Let lp, l))
                   (omap_list pat_form aux_f [f1;f2])
            end
          | Fint _ -> None
          | Flocal id ->
             if Sid.mem id sbd
             then Some (Pat_Meta_Name (Pat_Type (Pat_Anything,f.f_ty), id))
             else None
          | Fpvar(x,m) ->
             omap (fun l -> Pat_Fun_Symbol (Sym_Form_Pvar,l))
               (omap_list pat_axiom aux [Axiom_Prog_Var x;Axiom_Memory m])
          | Fglob(mp, m) ->
             omap (fun l -> Pat_Fun_Symbol (Sym_Form_Glob,l))
               (omap_list pat_axiom aux [Axiom_Mpath mp;Axiom_Memory m])
          | Fop _ -> None
          | Fapp(f,args) ->
             omap (fun l -> Pat_Fun_Symbol (Sym_Form_App,l))
               (omap_list pat_form aux_f (f::args))
          | Ftuple args ->
             omap (fun l -> Pat_Fun_Symbol (Sym_Form_Tuple,l))
               (omap_list pat_form aux_f args)
          | Fproj(f,i) ->
             omap (fun x -> Pat_Fun_Symbol (Sym_Form_Proj i,[x])) (aux_f f)
          | FhoareF h ->
             omap (fun l -> Pat_Fun_Symbol (Sym_Form_Hoare_F,l))
               (omap_list pat_axiom aux [Axiom_Form h.hf_pr;
                                         Axiom_Xpath h.hf_f;
                                         Axiom_Form h.hf_po])
          | FhoareS h ->
             omap (fun l -> Pat_Fun_Symbol (Sym_Form_Hoare_S,l))
               (omap_list pat_axiom aux [Axiom_MemEnv h.hs_m;
                                         Axiom_Form h.hs_pr;
                                         Axiom_Stmt h.hs_s;
                                         Axiom_Form h.hs_po])
          | FbdHoareF h ->
             omap (fun l -> Pat_Fun_Symbol (Sym_Form_bd_Hoare_F,l))
               (omap_list pat_axiom aux [Axiom_Form h.bhf_pr;
                                         Axiom_Xpath h.bhf_f;
                                         Axiom_Form h.bhf_po;
                                         Axiom_Hoarecmp h.bhf_cmp;
                                         Axiom_Form h.bhf_bd])
          | FbdHoareS h ->
             omap (fun l -> Pat_Fun_Symbol (Sym_Form_bd_Hoare_S,l))
               (omap_list pat_axiom aux [Axiom_MemEnv h.bhs_m;
                                         Axiom_Form h.bhs_pr;
                                         Axiom_Stmt h.bhs_s;
                                         Axiom_Form h.bhs_po;
                                         Axiom_Hoarecmp h.bhs_cmp;
                                         Axiom_Form h.bhs_bd])
          | FequivF h ->
             omap (fun l -> Pat_Fun_Symbol (Sym_Form_Equiv_F,l))
               (omap_list pat_axiom aux [Axiom_Form h.ef_pr;
                                         Axiom_Xpath h.ef_fl;
                                         Axiom_Xpath h.ef_fr;
                                         Axiom_Form h.ef_po])
          | FequivS h ->
             omap (fun l -> Pat_Fun_Symbol (Sym_Form_Equiv_S,l))
               (omap_list pat_axiom aux [Axiom_MemEnv h.es_ml;
                                         Axiom_MemEnv h.es_mr;
                                         Axiom_Form h.es_pr;
                                         Axiom_Stmt h.es_sl;
                                         Axiom_Stmt h.es_sr;
                                         Axiom_Form h.es_po])
          | FeagerF h ->
             omap (fun l -> Pat_Fun_Symbol (Sym_Form_Equiv_F,l))
               (omap_list pat_axiom aux [Axiom_Form h.eg_pr;
                                         Axiom_Stmt h.eg_sl;
                                         Axiom_Xpath h.eg_fl;
                                         Axiom_Xpath h.eg_fr;
                                         Axiom_Stmt h.eg_sr;
                                         Axiom_Form h.eg_po])
          | Fpr pr ->
             let pr_event = pr.pr_event in
             (* let mhr,memty = EcMemory.empty_local mhr pr.pr_fun in
              * let pr_event = mk_form (Fquant (Llambda,[mhr, GTmem memty],pr_event)) pr_event.f_ty in *)
             omap (fun l -> Pat_Fun_Symbol (Sym_Form_Pr,l))
               (omap_list pat_axiom aux [Axiom_Memory pr.pr_mem;
                                         Axiom_Xpath pr.pr_fun;
                                         Axiom_Form pr.pr_args;
                                         Axiom_Form pr_event])
        end
      | Axiom_Memory m when  Sid.mem m sbd ->
         Some (Pat_Meta_Name (Pat_Anything, m))
      | Axiom_MemEnv m when Sid.mem (fst m) sbd ->
         Some (Pat_Meta_Name (Pat_Anything, fst m))
      | Axiom_Prog_Var pv ->
         omap (fun x -> Pat_Fun_Symbol (Sym_Form_Prog_var pv.pv_kind,[x]))
           (aux (Axiom_Xpath pv.pv_name))
      | Axiom_Local id when Sid.mem id sbd ->
         Some (Pat_Meta_Name (Pat_Anything, id))
      | Axiom_Op _ -> None
      | Axiom_Module mt -> begin
          match mt with
          | `Local id when Sid.mem id sbd ->
             Some (Pat_Meta_Name (Pat_Anything, id))
          | _ -> None
        end
      | Axiom_Mpath m ->
         omap (fun l -> Pat_Fun_Symbol (Sym_Mpath, l))
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
          | Sabstract id when Sid.mem id sbd ->
             Some (Pat_Meta_Name (Pat_Anything, id))
          | Sabstract _ -> None
        end
      | Axiom_Stmt s ->
         omap (fun l -> Pat_Fun_Symbol (Sym_Stmt_Seq,l))
           (omap_list pat_instr aux_i s.s_node)
      | Axiom_Lvalue lv -> begin
          match lv with
          | LvVar (pv,ty) ->
             omap (fun x -> Pat_Type (x,ty))
               (aux (Axiom_Prog_Var pv))
          | LvTuple l ->
             let default (pv,ty) = Pat_Type (Pat_Axiom (Axiom_Prog_Var pv),ty) in
             let aux (pv,ty) = omap (fun x -> Pat_Type (x,ty)) (aux (Axiom_Prog_Var pv)) in
             omap (fun l -> Pat_Fun_Symbol (Sym_Form_Tuple,l))
               (omap_list default aux l)
          | LvMap _ -> (* FIXME *) raise (Invalid_argument "bleuh")
        end
      | Axiom_Xpath xp ->
         omap (fun x -> Pat_Fun_Symbol (Sym_Xpath,[x;Pat_Axiom(Axiom_Op (xp.x_sub,[]))]))
           (aux (Axiom_Mpath xp.x_top))
      | Axiom_Hoarecmp _ -> None
      | Axiom_Local _ | Axiom_MemEnv _ | Axiom_Memory _ -> None

    and aux_f f = aux (Axiom_Form f)

    and aux_i i = aux (Axiom_Instr i)

    in

    aux a

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

  let pattern_of_form b f =
    odfl (Pat_Axiom(Axiom_Form f)) (pattern_of_axiom b (Axiom_Form f))

  let rewrite_axiom (map: map) (a : axiom) =
    let smap = Sid.of_list (Mid.keys map) in
    let get_form = function
      | Axiom_Form f -> f
      | _ -> assert false in
    let get_mpath = function
      | Axiom_Mpath m -> m
      | _ -> assert false in
    let get_instr = function
      | Axiom_Instr i -> i
      | _ -> assert false in
    let get_prog_var = function
      | Axiom_Prog_Var pv -> pv
      | _ -> assert false in
    let axiom_form f = Axiom_Form f in
    let axiom_mpath m = Axiom_Mpath m in
    let axiom_instr i = Axiom_Instr i in
    let axiom_prog_var pv = Axiom_Prog_Var pv in
    let rec aux_f f : axiom option = aux (Axiom_Form f)
    and aux (a : axiom) : axiom option =
      match a with
      | Axiom_Form f -> begin
          match f.f_node with
          | Fquant (quant,bs,f')
               when Sid.disjoint (Sid.of_list (List.map fst bs)) smap ->
             omap (fun f -> Axiom_Form (f_quant quant bs (get_form f))) (aux_f f')
          | Fquant _ ->
             raise (Invalid_argument "in rewrite_term, a quantifier appeares in the matching map")
          | Fif (f1,f2,f3) ->
             omap (function
                 | f1::f2::f3::[] ->
                    Axiom_Form (f_if (get_form f1) (get_form f2) (get_form f3))
                 | _ -> assert false)
               (omap_list axiom_form aux_f [f1;f2;f3])
          | Fmatch (fop,fargs,ty) ->
             omap (function fop::fargs -> Axiom_Form (mk_form (Fmatch (get_form fop,List.map get_form fargs,ty)) ty) | _ -> assert false)
               (omap_list axiom_form aux_f (fop::fargs))
          | Flet (lv,f1,f2) -> begin
              match lv with
              | LSymbol (id,_) when Mid.mem id map ->
                 raise (Invalid_argument "in rewrite_term, a let-lvalue appeares in the matching map")
              | LTuple l when not(Sid.disjoint smap (Sid.of_list (List.map fst l))) ->
                 raise (Invalid_argument "in rewrite_term, one of the let-lvalues appear in the matching map")
              | _ ->
                 omap (function f1::f2::[] -> Axiom_Form(f_let lv (get_form f1) (get_form f2)) | _ -> assert false)
                   (omap_list axiom_form aux_f [f1;f2])
            end
          | Fint _ -> None
          | Flocal id -> begin
              match Mid.find_opt id map with
              | None -> None
              | Some (Pat_Axiom (Axiom_Form f'), _) -> begin
                  match aux_f f' with
                  | None -> Some (Axiom_Form f')
                  | Some a -> Some a
                end
              | _ -> (* FIXME *) assert false
            end
          | Fpvar (pvar,mem) ->
             omap (function
                 | (Axiom_Prog_Var pvar)::(Axiom_Memory mem)::[] ->
                    Axiom_Form (f_pvar pvar f.f_ty mem)
                 | _ -> assert false)
               (olist aux [Axiom_Prog_Var pvar;Axiom_Memory mem])
          | Fglob (mpath,mem) ->
             omap (function
                 | (Axiom_Mpath mpath)::(Axiom_Memory mem)::[] ->
                    Axiom_Form (f_glob mpath mem)
                 | _ -> assert false)
               (olist aux [Axiom_Mpath mpath;Axiom_Memory mem])
          | Fop _ -> None
          | Fapp (f1,fargs) ->
             omap (function
                 | fop::fargs ->
                    Axiom_Form (f_app (get_form fop) (List.map get_form fargs) f.f_ty)
                 | _ -> assert false)
               (omap_list axiom_form aux_f (f1::fargs))
          | Ftuple t ->
             omap (fun l -> Axiom_Form (f_tuple (List.map get_form l)))
               (omap_list axiom_form aux_f t)
          | Fproj (f1,i) ->
             omap (fun fi -> Axiom_Form (f_proj (get_form fi) i f.f_ty)) (aux_f f1)
          | FhoareF h ->
             omap (function
                 | (Axiom_Form pr)::(Axiom_Xpath f)::(Axiom_Form po)::[] ->
                    Axiom_Form (f_hoareF pr f po)
                 | _ -> assert false)
               (olist aux [Axiom_Form h.hf_po;Axiom_Xpath h.hf_f;Axiom_Form h.hf_po])
          | FhoareS h ->
             omap (function
                 | [Axiom_MemEnv m;
                    Axiom_Form pr;
                    Axiom_Stmt s;
                    Axiom_Form po] ->
                    Axiom_Form (f_hoareS m pr s po)
                 | _ -> assert false)
               (olist aux [Axiom_MemEnv h.hs_m;
                           Axiom_Form h.hs_pr;
                           Axiom_Stmt h.hs_s;
                           Axiom_Form h.hs_po])
          | FbdHoareF h ->
             omap (function
                 | [Axiom_Form pr;
                    Axiom_Xpath f;
                    Axiom_Form po;
                    Axiom_Hoarecmp cmp;
                    Axiom_Form bd] ->
                    Axiom_Form (f_bdHoareF pr f po cmp bd)
                 | _ -> assert false)
               (olist aux [Axiom_Form h.bhf_pr;
                           Axiom_Xpath h.bhf_f;
                           Axiom_Form h.bhf_po;
                           Axiom_Hoarecmp h.bhf_cmp;
                           Axiom_Form h.bhf_bd])
          | FbdHoareS h ->
             omap (function
                 | [Axiom_MemEnv m;
                    Axiom_Form pr;
                    Axiom_Stmt s;
                    Axiom_Form po;
                    Axiom_Hoarecmp cmp;
                    Axiom_Form bd] ->
                    Axiom_Form (f_bdHoareS m pr s po cmp bd)
                 | _ -> assert false)
               (olist aux [Axiom_MemEnv h.bhs_m;
                           Axiom_Form h.bhs_pr;
                           Axiom_Stmt h.bhs_s;
                           Axiom_Form h.bhs_po;
                           Axiom_Hoarecmp h.bhs_cmp;
                           Axiom_Form h.bhs_bd])
          | FequivF h ->
             omap (function
                 | [Axiom_Form pr;
                    Axiom_Xpath fl;
                    Axiom_Xpath fr;
                    Axiom_Form po] ->
                    Axiom_Form (f_equivF pr fl fr po)
                 | _ -> assert false)
               (olist aux [Axiom_Form h.ef_pr;
                           Axiom_Xpath h.ef_fl;
                           Axiom_Xpath h.ef_fr;
                           Axiom_Form h.ef_po])
          | FequivS h ->
             omap (function
                 | [Axiom_MemEnv ml;
                    Axiom_MemEnv mr;
                    Axiom_Form pr;
                    Axiom_Stmt sl;
                    Axiom_Stmt sr;
                    Axiom_Form po] ->
                    Axiom_Form (f_equivS ml mr pr sl sr po)
                 | _ -> assert false)
               (olist aux [Axiom_MemEnv h.es_ml;
                           Axiom_MemEnv h.es_mr;
                           Axiom_Form h.es_pr;
                           Axiom_Stmt h.es_sl;
                           Axiom_Stmt h.es_sr;
                           Axiom_Form h.es_po])
          | FeagerF h ->
             omap (function
                 | [Axiom_Form pr;
                    Axiom_Stmt sl;
                    Axiom_Xpath fl;
                    Axiom_Xpath fr;
                    Axiom_Stmt sr;
                    Axiom_Form po] ->
                    Axiom_Form (f_eagerF pr sl fl fr sr po)
                 | _ -> assert false)
               (olist aux [Axiom_Form h.eg_pr;
                           Axiom_Stmt h.eg_sl;
                           Axiom_Xpath h.eg_fl;
                           Axiom_Xpath h.eg_fr;
                           Axiom_Stmt h.eg_sr;
                           Axiom_Form h.eg_po])
          | Fpr _ when Mid.mem mhr map ->
             raise (Invalid_argument "&hr appears in the matching map si it shouldn't be replaced in a pr formula")
          | Fpr h ->
             omap (function
                 | [Axiom_Memory mem;
                    Axiom_Xpath f;
                    Axiom_Form args;
                    Axiom_Form event] ->
                    Axiom_Form (f_pr mem f args event)
                 | _ -> assert false)
               (olist aux [Axiom_Memory h.pr_mem;
                           Axiom_Xpath h.pr_fun;
                           Axiom_Form h.pr_args;
                           Axiom_Form h.pr_event])
        end
      | Axiom_Memory m -> begin
          match Mid.find_opt m map with
          | None -> None
          | Some (Pat_Axiom (Axiom_Memory m | Axiom_MemEnv (m,_)),_) -> Some (Axiom_Memory m)
          | _ -> (* FIXME *) assert false
        end
      | Axiom_MemEnv (m,t) -> begin
          match Mid.find_opt m map with
          | None -> None
          | Some (Pat_Axiom (Axiom_Memory m),_) -> Some (Axiom_MemEnv (m,t))
          | Some (Pat_Axiom (Axiom_MemEnv (m,t)),_) -> Some (Axiom_MemEnv (m,t))
          | _ -> (* FIXME *) assert false
        end
      | Axiom_Prog_Var p ->
         omap (function Axiom_Xpath xp -> Axiom_Prog_Var (pv xp p.pv_kind) | _ -> assert false)
           (aux (Axiom_Xpath p.pv_name))
      | Axiom_Local id -> begin
          match Mid.find_opt id map with
          | None -> None
          | Some (Pat_Axiom a,_) -> Some a
          | _ -> (* FIXME *) assert false
        end
      | Axiom_Op _ -> None
      | Axiom_Module mt -> begin
          match mt with
          | `Local id -> begin
              match Mid.find_opt id map with
              | None -> None
              | Some (Pat_Axiom (Axiom_Module _ as a),_) -> Some a
              | Some (Pat_Axiom (Axiom_Mpath _ as a),_)  -> Some a
              | _ -> (* FIXME *) assert false
            end
          | _ -> None
        end
      | Axiom_Mpath m ->
         omap (function
             | (Axiom_Module mt)::margs ->
                Axiom_Mpath (mpath mt (List.map get_mpath margs))
             | (Axiom_Mpath m)::[] -> Axiom_Mpath m
             | _ -> assert false)
           (olist aux ((Axiom_Module m.m_top)::(List.map axiom_mpath m.m_args)))
      | Axiom_Instr i -> begin
          match i.i_node with
          | Sasgn (lv,e) ->
             omap (function
                 | [Axiom_Lvalue lv;Axiom_Form f] -> Axiom_Instr (i_asgn (lv,(expr_of_form f)))
                 | _ -> assert false)
               (olist aux [Axiom_Lvalue lv;Axiom_Form (form_of_expr e)])
          | Srnd  (lv,e) ->
             omap (function
                 | [Axiom_Lvalue lv;Axiom_Form f] -> Axiom_Instr (i_rnd (lv,(expr_of_form f)))
                 | _ -> assert false)
               (olist aux [Axiom_Lvalue lv;Axiom_Form (form_of_expr e)])
          | Scall (lvo,f,args) ->
             let l = (Axiom_Xpath f)::(List.map axiom_form (List.map form_of_expr args)) in
             let l = match lvo with
               | None -> l
               | Some lv -> (Axiom_Lvalue lv)::l in
             omap (function
                 | (Axiom_Xpath xp)::args ->
                    Axiom_Instr (i_call (None,xp,List.map expr_of_form (List.map get_form args)))
                 | (Axiom_Lvalue lv)::(Axiom_Xpath xp)::args ->
                    Axiom_Instr (i_call (Some lv,xp,List.map expr_of_form (List.map get_form args)))
                 | _ -> assert false)
               (olist aux l)
          | Sif (e,strue,sfalse) ->
             omap (function
                 | [Axiom_Form f;Axiom_Stmt strue;Axiom_Stmt sfalse] ->
                    Axiom_Instr (i_if (expr_of_form f,strue,sfalse))
                 | _ -> assert false)
               (olist aux [Axiom_Form (form_of_expr e);Axiom_Stmt strue;Axiom_Stmt sfalse])
          | Swhile (e,sbody) ->
             omap (function
                 | [Axiom_Form f;Axiom_Stmt sbody] ->
                    Axiom_Instr (i_while (expr_of_form f,sbody))
                 | _ -> assert false)
               (olist aux [Axiom_Form (form_of_expr e);Axiom_Stmt sbody])
          | Sassert e ->
             omap (fun f -> Axiom_Instr (i_assert (expr_of_form (get_form f))))
               (aux (Axiom_Form (form_of_expr e)))
          | Sabstract id -> begin
              match Mid.find_opt id map with
              | None -> None
              | Some (Pat_Axiom (Axiom_Instr _ as a),_) -> Some a
              | _ -> (* FIXME *) assert false
            end
        end
      | Axiom_Stmt s ->
         omap (fun l -> Axiom_Stmt (stmt (List.map get_instr l)))
           (olist aux (List.map axiom_instr s.s_node))
      | Axiom_Lvalue lv -> begin
          match lv with
          | LvVar (pv,ty) ->
             omap (function
                 | Axiom_Prog_Var pv -> Axiom_Lvalue (LvVar (pv,ty))
                 | _ -> assert false)
               (aux (Axiom_Prog_Var pv))
          | LvTuple lv ->
             omap (fun l ->
                 Axiom_Lvalue
                   (LvTuple
                      (List.map2
                         (fun (_,ty) lv -> (get_prog_var lv,ty)) lv l)))
               (olist aux (List.map axiom_prog_var (List.map fst lv)))
          | _ -> assert false
        end
      | Axiom_Xpath xp ->
         omap (function
             | Axiom_Mpath m -> Axiom_Xpath (xpath m xp.x_sub)
             | _ -> assert false)
           (aux (Axiom_Mpath xp.x_top))

      | Axiom_Hoarecmp _ -> None
    in
    odfl a (aux a)

  let rewrite_term map f = match rewrite_axiom map (Axiom_Form f) with
    | Axiom_Form f -> f
    | _ -> assert false

end
