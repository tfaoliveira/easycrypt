(* -------------------------------------------------------------------- *)
open EcUtils
open EcFol
open EcTypes
open EcPath
open EcIdent
open EcEnv
open EcModules
open EcPattern
open Psubst

(* ---------------------------------------------------------------------- *)
exception Matches
exception NoMatches
exception CannotUnify
exception NoNext

type match_env = {
    me_unienv    : EcUnify.unienv;
    me_meta_vars : ogty Mid.t;
    me_matches   : pattern Mid.t;
  }

type environment = {
    env_hyps             : EcEnv.LDecl.hyps;
    env_match            : match_env;
    env_red_info_p       : EcReduction.reduction_info;
    env_red_info_a       : EcReduction.reduction_info;
    env_restore_unienv   : EcUnify.unienv option ref;
    env_current_binds    : pbindings;
    env_meta_restr_binds : pbindings Mid.t;
    env_fmt              : Format.formatter;
    env_ppe              : EcPrinting.PPEnv.t;
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
    e_env          : environment;
  }

and nengine = {
    ne_continuation : pat_continuation;
    ne_env          : environment;
  }

(* -------------------------------------------------------------------------- *)
let h_red_strat hyps s rp ra p a =
  match PReduction.h_red_pattern_opt hyps rp s p with
  | Some p -> Some (p, a)
  | None ->
     match a with
     | Axiom_Form f -> begin
         match EcReduction.h_red_opt ra hyps f with
         | Some f -> Some (p, axiom_form f)
         | None -> None
       end
     | _ ->
        match PReduction.h_red_axiom_opt hyps ra s a with
        | Some (Pat_Axiom a) -> Some (p, a)
        | _ -> None

let saturate (me : match_env) =
  let ue    = me.me_unienv in
  let mtch  = me.me_matches in
  let sty   = { EcTypes.ty_subst_id with ts_u = EcUnify.UniEnv.assubst ue } in
  let subst = { ps_patloc = mtch; ps_sty = sty } in
  let seen  = ref Sid.empty in

  let rec for_ident x binding subst =
    if Sid.mem x !seen then subst else begin
        seen := Sid.add x !seen;
        let subst =
          Mid.fold2_inter (fun x bdx _ -> for_ident x bdx)
            subst.ps_patloc (pat_fv binding) subst in
        { subst with ps_patloc = Mid.add x (Psubst.p_subst subst binding) subst.ps_patloc }
      end
  in
  let subst = Mid.fold_left (fun acc x bd -> for_ident x bd acc)
                subst subst.ps_patloc in
  { me with me_matches = subst.ps_patloc }


let saturate env = { env with env_match = saturate env.env_match }

let psubst_of_env env =
  let sty   = { EcTypes.ty_subst_id with
                ts_u = EcUnify.UniEnv.assubst env.me_unienv } in
  { ps_patloc = env.me_matches; ps_sty = sty }

(* -------------------------------------------------------------------------- *)

let restore_environment (env : environment) : unit =
  match !(env.env_restore_unienv) with
  | None -> ()
  | Some unienv ->
     let dst = env.env_match.me_unienv in
     let src = unienv in
     EcUnify.UniEnv.restore dst src

let add_binds (env : environment) (env_current_binds : pbindings) : environment =
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


let is_modty (env : EcEnv.env) (m : mpath) (mt : module_type) (mr : mod_restr) =
  let ms = EcEnv.Mod.by_mpath_opt m env in
  match ms with
  | None -> false
  | Some ms ->
    let ms = ms.me_sig in
    try EcTyping.check_modtype_with_restrictions env m ms mt mr; true
    with EcTyping.TymodCnvFailure _ -> false

(* -------------------------------------------------------------------------- *)
module Translate = struct

  exception Invalid_Type of string

  let rec form_of_pattern env (p : pattern) = match p with
    | Pat_Anything            -> raise (Invalid_Type "formula")
    | Pat_Meta_Name (_,_,_)   -> raise (Invalid_Type "formula")
    | Pat_Sub _               -> raise (Invalid_Type "sub in form")
    | Pat_Or [p]              -> form_of_pattern env p
    | Pat_Or _                -> raise (Invalid_Type "formula")
    | Pat_Instance _          -> assert false
    | Pat_Red_Strat (p,_)     -> form_of_pattern env p
    | Pat_Type (p,OGTty (Some ty)) ->
       let f = form_of_pattern env p in
       if ty_equal ty f.f_ty then f
       else raise (Invalid_Type "formula")
    | Pat_Type (p, OGTty None)-> form_of_pattern env p
    | Pat_Type _              -> raise (Invalid_Type "formula")
    | Pat_Axiom (Axiom_Form f)        -> f
    | Pat_Axiom (Axiom_Local (id,ty)) -> f_local id ty
    | Pat_Axiom _             -> raise (Invalid_Type "formula")
    | Pat_Fun_Symbol (s, lp)  ->
    match s, lp with
    | Sym_Form_If, [p1;p2;p3]   -> f_if (form_of_pattern env p1)
                                     (form_of_pattern env p2)
                                     (form_of_pattern env p3)
    | Sym_Form_App ty, p::lp    -> f_app (form_of_pattern env p)
                                     (List.map (form_of_pattern env) lp) ty
    | Sym_Form_Tuple, t         -> f_tuple (List.map (form_of_pattern env) t)
    | Sym_Form_Proj (i,ty), [p] -> f_proj (form_of_pattern env p) i ty
    | Sym_Form_Match ty, p::lp  -> mk_form (Fmatch (form_of_pattern env p,
                                                    List.map (form_of_pattern env) lp,
                                                    ty)) ty
    | Sym_Form_Quant (q,b), [p] -> f_quant q b (form_of_pattern env p)
    | Sym_Form_Let lp, [p1;p2]  -> f_let lp (form_of_pattern env p1)
                                     (form_of_pattern env p2)
    | Sym_Form_Pvar ty, [pv;pm] -> f_pvar (prog_var_of_pattern env pv) ty
                                     (memory_of_pattern pm)
    | Sym_Form_Prog_var _, _    -> raise (Invalid_Type "formula")
    | Sym_Form_Glob, [mp;mem]   -> f_glob (mpath_of_pattern env mp) (memory_of_pattern mem)
    | Sym_Form_Hoare_F, [pr;xp;po] ->
       f_hoareF (form_of_pattern env pr) (xpath_of_pattern env xp) (form_of_pattern env po)
    | Sym_Form_Hoare_S, [pm;pr;s;po] ->
       f_hoareS (memenv_of_pattern pm) (form_of_pattern env pr) (stmt_of_pattern env s)
         (form_of_pattern env po)
    | Sym_Form_bd_Hoare_F, [pr;xp;po;cmp;bd] ->
       f_bdHoareF (form_of_pattern env pr) (xpath_of_pattern env xp) (form_of_pattern env po)
         (cmp_of_pattern cmp) (form_of_pattern env bd)
    | Sym_Form_bd_Hoare_S, [pm;pr;s;po;cmp;bd] ->
       f_bdHoareS (memenv_of_pattern pm) (form_of_pattern env pr) (stmt_of_pattern env s)
         (form_of_pattern env po) (cmp_of_pattern cmp) (form_of_pattern env bd)
    | Sym_Form_Equiv_F, [pr;f1;f2;po] ->
       f_equivF (form_of_pattern env pr) (xpath_of_pattern env f1) (xpath_of_pattern env f2)
         (form_of_pattern env po)
    | Sym_Form_Equiv_S, [pm1;pm2;pr;s1;s2;po] ->
       f_equivS (memenv_of_pattern pm1) (memenv_of_pattern pm2) (form_of_pattern env pr)
         (stmt_of_pattern env s1) (stmt_of_pattern env s2) (form_of_pattern env po)
    | Sym_Form_Eager_F, [po;s1;f1;f2;s2;pr] ->
       f_eagerF (form_of_pattern env po) (stmt_of_pattern env s1) (xpath_of_pattern env f1)
         (xpath_of_pattern env f2) (stmt_of_pattern env s2) (form_of_pattern env pr)
    | Sym_Form_Pr, [pm;f;args;event] ->
       f_pr (memory_of_pattern pm) (xpath_of_pattern env f) (form_of_pattern env args)
         (form_of_pattern env event)
    | Sym_App, pop::pargs ->
       f_ty_app env (form_of_pattern env pop) (List.map (form_of_pattern env) pargs)
    | Sym_Quant (q,pb), [p] ->
       let f (id,ogt) = match ogt with
         | OGTty (Some ty) -> id, GTty ty
         | OGTmem (Some t) -> id, GTmem t
         | OGTmodty (Some (t,r)) -> id, GTmodty (t,r)
         | _ -> raise (Invalid_Type "formula") in
       f_quant q (List.map f pb) (form_of_pattern env p)
    | _ -> raise (Invalid_Type "formula")

  and memory_of_pattern = function
    | Pat_Axiom (Axiom_Memory m) -> m
    | Pat_Type (p, OGTmem None) -> memory_of_pattern p
    | _ -> raise (Invalid_Type "memory")

  and prog_var_of_pattern env = function
    | Pat_Axiom (Axiom_Prog_Var pv) -> pv
    | Pat_Fun_Symbol (Sym_Form_Prog_var k, [xp]) ->
       pv (xpath_of_pattern env xp) k
    | _ -> raise (Invalid_Type "prog_var")

  and xpath_of_pattern env = function
    | Pat_Axiom (Axiom_Xpath xp) -> xp
    | Pat_Fun_Symbol (Sym_Xpath, [mp;p]) ->
       EcPath.xpath (mpath_of_pattern env mp) (path_of_pattern p)
    | _ -> raise (Invalid_Type "xpath")

  and path_of_pattern = function
    | Pat_Axiom (Axiom_Op (p,[])) -> p
    | _ -> raise (Invalid_Type "path")

  and mpath_of_pattern env = function
    | Pat_Axiom (Axiom_Mpath mp) -> mp
    | Pat_Fun_Symbol (Sym_Mpath, mp::margs) ->
       mpath (mpath_top_of_pattern env mp) (List.map (mpath_of_pattern env) margs)
    | Pat_Type (p, OGTmodty (Some (mt, mr))) ->
       let mp = mpath_of_pattern env p in
       if is_modty env mp mt mr then mp
       else raise (Invalid_Type "mpath's type does not match")
    | _ -> raise (Invalid_Type "mpath")

  and mpath_top_of_pattern _env = function
    | Pat_Axiom (Axiom_Module m) -> m
    | _ -> raise (Invalid_Type "mpath_top")

  and memenv_of_pattern = function
    | Pat_Axiom (Axiom_MemEnv m) -> m
    | Pat_Type (p, OGTmem (Some mt)) -> begin
        try (memory_of_pattern p, mt) with
        | Invalid_Type "memory" ->
           let (m,mt') = memenv_of_pattern p in
           if EcMemory.mt_equal mt mt' then (m,mt)
           else raise (Invalid_Type "memenv")
      end
    | _ -> raise (Invalid_Type "memenv")

  and stmt_of_pattern env = function
    | Pat_Axiom (Axiom_Stmt s) -> s
    | Pat_Fun_Symbol (Sym_Stmt_Seq, l) ->
       stmt (List.flatten (List.map (instr_of_pattern env) l))
    | _ -> raise (Invalid_Type "stmt")

  and instr_of_pattern env = function
    | Pat_Axiom (Axiom_Instr i) -> [i]
    | Pat_Axiom (Axiom_Stmt s) -> s.s_node
    | Pat_Fun_Symbol (Sym_Instr_Assign, [lv;e]) ->
       [i_asgn (lvalue_of_pattern env lv, expr_of_pattern env e)]
    | Pat_Fun_Symbol (Sym_Instr_Sample, [lv;e]) ->
       [i_rnd  (lvalue_of_pattern env lv, expr_of_pattern env e)]
    | Pat_Fun_Symbol (Sym_Instr_Call, f::args) ->
       [i_call (None, xpath_of_pattern env f, List.map (expr_of_pattern env) args)]
    | Pat_Fun_Symbol (Sym_Instr_Call_Lv, lv::f::args) ->
       [i_call (Some (lvalue_of_pattern env lv), xpath_of_pattern env f,
                List.map (expr_of_pattern env) args)]
    | Pat_Fun_Symbol (Sym_Instr_If, [cond;s1;s2]) ->
       [i_if (expr_of_pattern env cond, stmt_of_pattern env s1, stmt_of_pattern env s2)]
    | Pat_Fun_Symbol (Sym_Instr_While, [cond;s]) ->
       [i_while (expr_of_pattern env cond, stmt_of_pattern env s)]
    | Pat_Fun_Symbol (Sym_Instr_Assert, [e]) ->
       [i_assert (expr_of_pattern env e)]
    | Pat_Fun_Symbol (Sym_Stmt_Seq, lp) ->
       List.flatten (List.map (instr_of_pattern env) lp)
    | _ -> raise (Invalid_Type "instr")

  and lvalue_of_pattern env = function
    | Pat_Axiom (Axiom_Lvalue lv) -> lv
    | Pat_Type (pv, OGTty (Some ty)) ->
       LvVar (prog_var_of_pattern env pv, ty)
    | Pat_Fun_Symbol (Sym_Form_Tuple, t) ->
       let t = List.map (lvalue_of_pattern env) t in
       let t = List.map (function LvVar (x,t) -> (x,t)
                                | _ -> raise (Invalid_Type "lvalue tuple")) t in
       LvTuple t
    | _ -> raise (Invalid_Type "lvalue")

  and expr_of_pattern env p =
    try match expr_of_form (form_of_pattern env p) with
        | Some e -> e
        | None -> raise (Invalid_Type "expr from form")
    with
    | Invalid_Type s -> raise (Invalid_Type (String.concat " in " [s;"expr"]))

  and cmp_of_pattern = function
    | Pat_Axiom (Axiom_Hoarecmp cmp) -> cmp
    | _ -> raise (Invalid_Type "hoarecmp")

  let form_of_pattern env p = match p with
    | Pat_Sub p -> begin
        try form_of_pattern env p with
        | Invalid_Type "sub in form" -> assert false
      end
    | _ -> form_of_pattern env p

end

module EQ : sig
  val ty        : environment -> ty -> ty -> bool
  val memtype   : environment -> EcMemory.memtype -> EcMemory.memtype -> bool
  val memory    : environment -> EcMemory.memory -> EcMemory.memory -> bool
  val memenv    : environment -> EcMemory.memenv -> EcMemory.memenv -> bool
  val mpath     : environment -> mpath -> mpath -> bool
  val mpath_top : environment -> mpath_top -> mpath_top -> bool
  val xpath     : environment -> xpath -> xpath -> bool
  val name      :                meta_name -> meta_name -> bool
  val instr     : environment -> instr -> instr -> bool
  val stmt      : environment -> stmt -> stmt -> bool
  val lvalue    : environment -> lvalue -> lvalue -> bool
  val op        : environment -> path * ty list -> path * ty list -> bool
  val prog_var  : environment -> prog_var -> prog_var -> bool
  val hoarecmp  : environment -> hoarecmp -> hoarecmp -> bool
  val gty       : environment -> gty -> gty -> bool
  val binding   : environment -> binding -> binding -> bool
  val pbinding  : environment -> pbinding -> pbinding -> bool
  val symbol    : environment -> fun_symbol -> fun_symbol -> bool
  val is_gty    : environment -> pattern -> gty -> bool
  val is_ogty   : environment -> pattern -> ogty -> bool
  val form      : environment -> form -> form -> bool
  val axiom     : environment -> axiom -> axiom -> bool
  val pattern   : environment -> pattern -> pattern -> bool
end = struct
  let rec ty (env : environment) (ty1 : ty) (ty2 : ty) : bool =
    if None = !(env.env_restore_unienv)
    then begin
        let unienv = EcUnify.UniEnv.copy env.env_match.me_unienv in
        env.env_restore_unienv := Some unienv
      end;
    try EcUnify.unify (EcEnv.LDecl.toenv env.env_hyps) env.env_match.me_unienv ty1 ty2;
        true
    with EcUnify.UnificationFailure _ -> false

  let memtype (_env : environment) (m1 : EcMemory.memtype) (m2 : EcMemory.memtype) =
    EcMemory.mt_equal m1 m2

  let memory (_env : environment) (m1 : EcMemory.memory) (m2 : EcMemory.memory) =
    EcMemory.mem_equal m1 m2

  let memenv (_env : environment) (m1 : EcMemory.memenv) (m2 : EcMemory.memenv) =
    EcMemory.me_equal m1 m2

  let mpath (env : environment) (m1 : mpath) (m2 : mpath) : bool =
    EcReduction.EqTest.for_mp (EcEnv.LDecl.toenv env.env_hyps) m1 m2

  let mpath_top (_env : environment) (mt1 : mpath_top) (mt2 : mpath_top) =
    EcPath.mt_equal mt1 mt2

  let xpath (env : environment) (x1 : xpath) (x2 : xpath) : bool =
    EcReduction.EqTest.for_xp (EcEnv.LDecl.toenv env.env_hyps) x1 x2
    || (if EcPath.p_equal x1.x_sub x2.x_sub then mpath env x1.x_top x2.x_top
        else false)

  let name (n1 : meta_name) (n2 : meta_name) = 0 = id_compare n1 n2

  let instr (env : environment) (i1 : EcModules.instr) (i2 : EcModules.instr) =
    EcReduction.EqTest.for_instr (EcEnv.LDecl.toenv env.env_hyps) i1 i2

  let stmt (env : environment) (s1 : EcModules.stmt) (s2 : EcModules.stmt) =
    EcReduction.EqTest.for_stmt (EcEnv.LDecl.toenv env.env_hyps) s1 s2

  let lvalue (_env : environment) (lv1 : lvalue) (lv2 :lvalue) : bool =
    lv_equal lv1 lv2

  let op (env : environment)
        ((op1, lty1) : EcPath.path * EcTypes.ty list)
        ((op2, lty2) : EcPath.path * EcTypes.ty list) =
    if EcPath.p_equal op1 op2
    then List.for_all2 (ty env) lty1 lty2
    else false

  let prog_var (env : environment) (x1 : prog_var) (x2 : prog_var) =
    pv_equal x1 x2
    || (x1.pv_kind = x2.pv_kind && xpath env x1.pv_name x2.pv_name)

  let hoarecmp (_env : environment) (c1 : hoarecmp) (c2 : hoarecmp) : bool =
    c1 = c2


  let gty (env : environment) (gty1 : gty) (gty2 : gty) : bool =
    match gty1, gty2 with
    | GTty ty1, GTty ty2 -> ty env ty1 ty2
    | _,_ -> EcCoreFol.gty_equal gty1 gty2

  let ogty (env : environment) (gty1 : ogty) (gty2 : ogty) : bool =
    match gty1, gty2 with
    | OGTty (Some ty1), OGTty (Some ty2) -> ty env ty1 ty2
    | _,_ -> ogty_equal gty1 gty2

  let binding env (id1,gt1) (id2,gt2) =
    if not (id_equal id1 id2) then false
    else gty env gt1 gt2

  let pbinding env (id1,ogt1) (id2,ogt2) =
    match ogt1,ogt2 with
    | OGTty (Some gt1), OGTty (Some gt2) ->
       binding env (id1,GTty gt1) (id2,GTty gt2)
    | OGTty _, OGTty _ -> id_equal id1 id2
    | OGTty _, _ | _, OGTty _ -> false
    | OGTmem (Some t1), OGTmem (Some t2) ->
       binding env (id1,GTmem t1) (id2, GTmem t2)
    | OGTmem _, OGTmem _ -> id_equal id1 id2
    | OGTmem _, _ | _, OGTmem _ -> false
    | OGTmodty (Some (t1,r1)), OGTmodty (Some (t2,r2)) ->
       binding env (id1, GTmodty (t1,r1)) (id2, GTmodty (t2,r2))
    | OGTmodty _, OGTmodty _ -> true

  let symbol (env : environment) (s1 : fun_symbol) (s2 : fun_symbol) : bool =
    match s1,s2 with
    | Sym_Form_Proj (i1,t1), Sym_Form_Proj (i2,t2) ->
       if not (i1 = i2) then false
       else ty env t1 t2
    | Sym_Form_Pvar t1, Sym_Form_Pvar t2 | Sym_Form_App t1, Sym_Form_App t2
      | Sym_Form_Match t1, Sym_Form_Match t2 -> ty env t1 t2
    | Sym_Form_Quant (q1, b1), Sym_Form_Quant (q2, b2) ->
       if not (q1 = q2) then false
       else List.for_all2 (binding env) b1 b2
    | Sym_Form_Let lp1, Sym_Form_Let lp2 -> lp_equal lp1 lp2
    | Sym_Form_Prog_var k1, Sym_Form_Prog_var k2 -> k1 = k2
    | Sym_Quant (q1,b1), Sym_Quant (q2,b2) ->
       if not (q1 = q2) then false
       else List.for_all2 (pbinding env) b1 b2
    | _,_ -> s1 = s2


  let is_gty env (p : pattern) (gty1 : gty) = match gty1, p with
    | _, Pat_Type (_,OGTty (Some ty2)) -> gty env gty1 (GTty ty2)
    | _, Pat_Type (_, OGTmem (Some m)) -> gty env gty1 (GTmem m)
    | _, Pat_Type (_, OGTmodty (Some (mt, mr))) -> gty env gty1 (GTmodty (mt,mr))
    | GTty ty1, (Pat_Axiom (Axiom_Form { f_ty = ty2 }
                            | Axiom_Local (_,ty2))
                 | Pat_Fun_Symbol ((Sym_Form_App ty2
                                    | Sym_Form_Proj (_,ty2)
                                    | Sym_Form_Match ty2
                                    | Sym_Form_Pvar ty2),_)) ->
       ty env ty1 ty2
    | GTmem _, Pat_Axiom (Axiom_MemEnv (_,mt2)) ->
       gty env gty1 (GTmem mt2)
    | GTmodty (mt,mr), Pat_Axiom (Axiom_Mpath m) ->
       let env = LDecl.toenv env.env_hyps in
       is_modty env m mt mr
    | _ -> false

  let is_ogty env (p : pattern) (ogty1 : ogty) = match ogty1, p with
    | _, Pat_Type (_,ogty2) -> ogty env ogty1 ogty2
    | OGTty None, Pat_Axiom (Axiom_Form _
                             | Axiom_Op _
                             | Axiom_Local _) -> true
    | OGTty (Some ty1), p -> is_gty env p (GTty ty1)
    | OGTmem _, Pat_Axiom (Axiom_MemEnv (_,mt2)) ->
       ogty env ogty1 (OGTmem (Some mt2))
    | OGTmodty (Some (mt, mr)), Pat_Axiom (Axiom_Mpath m) ->
       let env = LDecl.toenv env.env_hyps in
       is_modty env m mt mr
    | _ -> false


  let form (env : environment) (f1 : form) (f2 : form) =
    let env_restore_unienv = !(env.env_restore_unienv) in
    env.env_restore_unienv := None;
    let eq = ty env f1.f_ty f2.f_ty in
    if eq
    then
      let sty    = { EcTypes.ty_subst_id with
                     ts_u = EcUnify.UniEnv.assubst env.env_match.me_unienv } in
      let sf     = Fsubst.f_subst_init ~sty () in
      let f1, f2 = Fsubst.f_subst sf f1, Fsubst.f_subst sf f2 in
      let ri     = env.env_red_info_a in
      env.env_restore_unienv := env_restore_unienv;
      EcReduction.is_conv_param ri env.env_hyps f1 f2
    else
      let _ = restore_environment env in
      false

  let rec axiom (env : environment) (o1 : axiom) (o2 : axiom) : bool =
    let aux o1 o2 =
      match o1,o2 with
      | Axiom_Form f1, Axiom_Form f2 ->
         form env f1 f2
      | Axiom_Memory m1, Axiom_Memory m2 ->
         memory env m1 m2
      | Axiom_MemEnv m1, Axiom_MemEnv m2 ->
         memenv env m1 m2
      | Axiom_Prog_Var x1, Axiom_Prog_Var x2 ->
         prog_var env x1 x2
      | Axiom_Op (op1,lty1), Axiom_Op (op2,lty2) ->
         op env (op1,lty1) (op2,lty2)
      | Axiom_Module m1, Axiom_Module m2 ->
         mpath_top env m1 m2
      | Axiom_Mpath m1, Axiom_Mpath m2 ->
         mpath env m1 m2
      | Axiom_Mpath { m_top = mt1 ; m_args = [] }, Axiom_Module mt2
        | Axiom_Module mt1, Axiom_Mpath { m_top = mt2 ; m_args = [] } ->
         mpath_top env mt1 mt2
      | Axiom_Instr i1, Axiom_Instr i2 ->
         instr env i1 i2
      | Axiom_Stmt s1, Axiom_Stmt s2 ->
         stmt env s1 s2
      | Axiom_Lvalue lv1, Axiom_Lvalue lv2 ->
         lvalue env lv1 lv2
      | Axiom_Xpath x1, Axiom_Xpath x2 ->
         xpath env x1 x2
      | Axiom_Hoarecmp c1, Axiom_Hoarecmp c2 ->
         hoarecmp env c1 c2
      | Axiom_Local (id1,ty1), Axiom_Local (id2,ty2) ->
         if ty env ty1 ty2 then name id1 id2 else false
      | Axiom_Op (op1,lty1), Axiom_Form { f_node = Fop (op2,lty2) } ->
         op env (op1,lty1) (op2,lty2)
      | Axiom_Form { f_node = Fop (op1,lty1) }, Axiom_Op (op2,lty2) ->
         op env (op1,lty1) (op2,lty2)
      | Axiom_Local (id1,ty1), Axiom_Form { f_node = Flocal id2; f_ty = ty2 } ->
         if ty env ty1 ty2 then name id1 id2 else false
      | Axiom_Form { f_node = Flocal id1; f_ty = ty1 }, Axiom_Local (id2,ty2) ->
         if ty env ty1 ty2 then name id1 id2 else false
      | _,_ -> false
    in
    aux o1 o2

  and pattern (env : environment) (p1 : pattern) (p2 : pattern) : bool =
    let env_restore_unienv = !(env.env_restore_unienv) in
    env.env_restore_unienv := None;
    let eq = match p1, p2 with
      | Pat_Anything, _ | _, Pat_Anything -> true
      | Pat_Instance _, _ | _, Pat_Instance _ -> assert false
      | Pat_Red_Strat (p1,red1), Pat_Red_Strat (p2,red2) ->
         if red1 == red2 then pattern env p1 p2 else false
      | Pat_Or lp1, Pat_Or lp2 ->
         List.for_all2 (pattern env) lp1 lp2
      | Pat_Sub p1, Pat_Sub p2 -> pattern env p1 p2
      | Pat_Type (p1,gt1), Pat_Type (p2,gt2) ->
         if ogty env gt1 gt2 then pattern env p1 p2 else false
      | Pat_Type (p1, gt1), p2 | p2, Pat_Type (p1, gt1) ->
         if is_ogty env p2 gt1 then pattern env p1 p2
         else false
      | Pat_Axiom a1, Pat_Axiom a2 ->
         axiom env a1 a2
      | Pat_Fun_Symbol (s1, lp1), Pat_Fun_Symbol (s2, lp2) ->
         if symbol env s1 s2 then List.for_all2 (pattern env) lp1 lp2
         else false
      | Pat_Meta_Name (p1,n1,b1), Pat_Meta_Name (p2,n2,b2) when name n1 n2 ->
         let eq = match b1, b2 with
           | Some b1, Some b2 -> List.for_all2 (pbinding env) b1 b2
           | _                -> true in
         if eq then pattern env p1 p2 else false
      | Pat_Meta_Name (_,n1,_), p2' | p2', Pat_Meta_Name (_,n1,_) -> begin
          match Mid.find_opt n1 (saturate env).env_match.me_matches with
          | Some p1' -> pattern env p1' p2'
          | None -> false
        end

      | Pat_Axiom a, Pat_Fun_Symbol (s,lp)
        | Pat_Fun_Symbol (s,lp), Pat_Axiom a -> begin
          match s, lp, a with
          | Sym_Form_If, [p1;p2;p3],
            Axiom_Form { f_node = Fif (f1,f2,f3) } ->
             if not (pattern env p1 (pat_form f1)) then false
             else if not (pattern env p2 (pat_form f2)) then false
             else pattern env p3 (pat_form f3)

          | Sym_Form_App pty, pop::pargs,
            Axiom_Form { f_node = Fapp (_,_) ; f_ty = fty } ->
             if not (ty env pty fty) then false
             else pattern env (Pat_Fun_Symbol(Sym_App,pop::pargs)) p2

          | Sym_Form_Tuple, pt,
            Axiom_Form { f_node = Ftuple ft } ->
             List.for_all2 (pattern env) pt (List.map pat_form ft)

          | Sym_Form_Proj (pi,pty), [p1],
            Axiom_Form { f_node = Fproj (f1,fi) ; f_ty = fty } when pi = fi ->
             if not (ty env pty fty) then false
             else pattern env p1 (pat_form f1)

          | Sym_Form_Match pty, pop::pargs,
            Axiom_Form { f_node = Fmatch (fop,fargs,fty) }
               when 0 = List.compare_lengths pargs fargs ->
             if not (ty env pty fty) then false
             else if not (pattern env pop (pat_form fop)) then false
             else List.for_all2 (pattern env) pargs (List.map pat_form fargs)

          | Sym_Form_Quant (pq,pb), [p1],
            Axiom_Form { f_node = Fquant (fq,fb,f1) }
               when pq = fq ->
             if not (List.for_all2 (binding env) pb fb) then false
             else pattern env p1 (pat_form f1)

          | Sym_Form_Let plp, [p1;p2],
            Axiom_Form { f_node = Flet (flp,f1,f2) } ->
             if not (lp_equal plp flp) then false
             else if not (pattern env p1 (pat_form f1)) then false
             else pattern env p2 (pat_form f2)

          | Sym_Form_Pvar pty, [ppv;pm],
            Axiom_Form { f_node = Fpvar (fpv,fm) ; f_ty = fty } ->
             if not (ty env pty fty) then false
             else if not (pattern env pm (pat_memory fm)) then false
             else pattern env ppv (pat_pv fpv)

          | Sym_Form_Prog_var k1, [p1],
            Axiom_Prog_Var { pv_name = xp ; pv_kind = k2 } when k1 = k2 ->
             pattern env p1 (pat_xpath xp)

          | Sym_Form_Glob, [pmp;pm],
            Axiom_Form { f_node = Fglob (fmp,fm) } ->
             if not (pattern env pm (pat_memory fm)) then false
             else pattern env pmp (pat_mpath fmp)

          | Sym_Form_Hoare_F, [pr1;xp1;po1],
            Axiom_Form { f_node = FhoareF { hf_pr = pr2;
                                            hf_f  = xp2;
                                            hf_po = po2; } } ->
             List.for_all2 (pattern env) [pr1;xp1;po1]
               [pat_form pr2; pat_xpath xp2; pat_form po2]

          | Sym_Form_Hoare_S, [m1;pr1;s1;po1],
            Axiom_Form { f_node = FhoareS { hs_m  = m2;
                                            hs_pr = pr2;
                                            hs_s  = s2;
                                            hs_po = po2; } } ->
             List.for_all2 (pattern env) [m1;pr1;s1;po1]
               [pat_memenv m2; pat_form pr2; pat_stmt s2; pat_form po2]

          | Sym_Form_bd_Hoare_F, [pr1;xp1;po1;cmp1;bd1],
            Axiom_Form { f_node = FbdHoareF { bhf_pr  = pr2;
                                              bhf_f   = xp2;
                                              bhf_po  = po2;
                                              bhf_cmp = cmp2;
                                              bhf_bd  = bd2; } } ->
             List.for_all2 (pattern env) [pr1;xp1;po1;cmp1;bd1]
               [pat_form pr2; pat_xpath xp2; pat_form po2; pat_cmp cmp2;
                pat_form bd2]

          | Sym_Form_bd_Hoare_S, [m1;pr1;s1;po1;cmp1;bd1],
            Axiom_Form { f_node = FbdHoareS { bhs_m   = m2;
                                              bhs_pr  = pr2;
                                              bhs_s   = s2;
                                              bhs_po  = po2;
                                              bhs_cmp = cmp2;
                                              bhs_bd  = bd2; } } ->
             List.for_all2 (pattern env) [m1;pr1;s1;po1;cmp1;bd1]
               [pat_memenv m2; pat_form pr2; pat_stmt s2; pat_form po2;
                pat_cmp cmp2; pat_form bd2]

          | Sym_Form_Equiv_F, [pr1;xpl1;xpr1;po1],
            Axiom_Form { f_node = FequivF { ef_pr = pr2;
                                            ef_fl = xpl2;
                                            ef_fr = xpr2;
                                            ef_po = po2; } } ->
             List.for_all2 (pattern env) [pr1;xpl1;xpr1;po1]
               [pat_form pr2; pat_xpath xpl2; pat_xpath xpr2; pat_form po2]

          | Sym_Form_Equiv_S, [ml1;mr1;pr1;sl1;sr1;po1],
            Axiom_Form { f_node = FequivS { es_ml = ml2;
                                            es_mr = mr2;
                                            es_pr = pr2;
                                            es_sl = sl2;
                                            es_sr = sr2;
                                            es_po = po2; } } ->
             List.for_all2 (pattern env) [ml1;mr1;pr1;sl1;sr1;po1]
               [pat_memenv ml2; pat_memenv mr2; pat_form pr2; pat_stmt sl2; pat_stmt sr2; pat_form po2]

          | Sym_Form_Eager_F, [pr1;sl1;xpl1;xpr1;sr1;po1],
            Axiom_Form { f_node = FeagerF { eg_pr = pr2;
                                            eg_sl = sl2;
                                            eg_fl = xpl2;
                                            eg_fr = xpr2;
                                            eg_sr = sr2;
                                            eg_po = po2; } } ->
             List.for_all2 (pattern env) [pr1;sl1;xpl1;xpr1;sr1;po1]
               [pat_form pr2; pat_stmt sl2; pat_xpath xpl2; pat_xpath xpr2; pat_stmt sr2; pat_form po2]

          | Sym_Form_Pr, [m1;xp1;args1;event1],
            Axiom_Form { f_node = Fpr { pr_mem   = m2;
                                        pr_fun   = xp2;
                                        pr_args  = args2;
                                        pr_event = event2; } } ->
             List.for_all2 (pattern env) [m1;xp1;args1;event1]
               [pat_memory m2; pat_xpath xp2; pat_form args2; pat_form event2]

          | Sym_Stmt_Seq, s1, Axiom_Stmt { s_node = s2 }
               when 0 = List.compare_lengths s1 s2 ->
             List.for_all2 (pattern env) s1 (List.map pat_instr s2)

          | Sym_Instr_Assign, [lv1;e1],
            Axiom_Instr { i_node = Sasgn (lv2,e2) }
            | Sym_Instr_Sample, [lv1;e1],
              Axiom_Instr { i_node = Srnd (lv2,e2) } ->
             List.for_all2 (pattern env) [lv1;e1]
               [pat_lvalue lv2; pat_form (form_of_expr e2)]

          | Sym_Instr_Call, xp1::args1,
            Axiom_Instr { i_node = Scall (None,xp2,args2) } ->
             List.for_all2 (pattern env) (xp1::args1)
               ((pat_xpath xp2)::
                  (List.map (fun x -> pat_form (form_of_expr x)) args2))

          | Sym_Instr_Call_Lv, lv1::xp1::args1,
            Axiom_Instr { i_node = Scall (Some lv2,xp2,args2) } ->
             List.for_all2 (pattern env) (lv1::xp1::args1)
               ((pat_lvalue lv2)::(pat_xpath xp2)::
                  (List.map (fun x -> pat_form (form_of_expr x)) args2))

          | Sym_Instr_If, [cond1;st1;sf1],
            Axiom_Instr { i_node = Sif (cond2,st2,sf2) } ->
             List.for_all2 (pattern env) [cond1;st1;sf1]
               [pat_form (form_of_expr cond2); pat_stmt st2; pat_stmt sf2]

          | Sym_Instr_While, [cond1;s1],
            Axiom_Instr { i_node = Swhile (cond2,s2) } ->
             List.for_all2 (pattern env) [cond1;s1]
               [pat_form (form_of_expr cond2); pat_stmt s2]

          | Sym_Instr_Assert, [cond1],
            Axiom_Instr { i_node = Sassert cond2 } ->
             pattern env cond1 (pat_form (form_of_expr cond2))

          | Sym_Xpath, [mp1;p1],
            Axiom_Xpath { x_top = mp2; x_sub = p2 } ->
             if not (pattern env p1 (pat_op p2 [])) then false
             else pattern env mp1 (pat_mpath mp2)

          | Sym_Mpath, [m1], Axiom_Mpath _ ->
             pattern env m1 p2

          | Sym_Mpath, [mtop1], Axiom_Module _ ->
             pattern env mtop1 p2

          | Sym_Mpath, mtop1::margs1,
            Axiom_Mpath { m_top = mtop2; m_args = margs2 } ->
             let (margs11,margs12), (margs21,margs22) = suffix2 margs1 margs2 in
             let mtop1 = p_mpath mtop1 margs11 in
             let mtop2 = if margs21 = [] then pat_mpath_top mtop2
                         else pat_mpath (EcPath.mpath mtop2 margs21) in
             List.for_all2 (pattern env) (mtop1::margs12)
               (mtop2::(List.map pat_mpath margs22))

          | Sym_Mpath, _, _ -> false

          | Sym_App, op1::args1,
            Axiom_Form { f_node = Fapp (op2,args2) } ->
             let (args11,args12), (args21,args22) = suffix2 args1 args2 in
             let op1 = p_app op1 args11 None in
             let op2 = f_app op2 args21
                         (EcTypes.toarrow (List.map f_ty args22) (f_ty op2)) in
             List.for_all2 (pattern env) (op1::args12) (List.map pat_form (op2::args22))

          | Sym_Quant (q1,pb1), [p1],
            Axiom_Form { f_node = Fquant (q2,b2,f1) } when q1 = q2 ->
             if not (List.for_all2 (pbinding env) pb1
                             (List.map (snd_map ogty_of_gty) b2))
             then false
             else pattern env p1 (pat_form f1)

          | _ -> false

        end
      | _, _ -> false
    in
    if not eq then let _ = restore_environment env in eq
    else let _ = env.env_restore_unienv := env_restore_unienv in eq

end


let rec merge_binds bs1 bs2 env = match bs1,bs2 with
  | [], _ | _,[] -> Some (env,bs1,bs2)
  | (x,_)::_, (y,_)::_
       when List.mem_assoc x env.env_current_binds
            || List.mem_assoc y env.env_current_binds ->
     None
  | (x,ty1)::r1, (y,ty2)::r2 when EQ.name x y && EQ.gty env ty1 ty2 ->
     let env = { env with env_current_binds = env.env_current_binds @ [y, ogty_of_gty ty2]; }
     in merge_binds r1 r2 env
  | _ -> None

(* -------------------------------------------------------------------------- *)
module FV : sig
  type fv = int Mid.t

  val add_fv   : fv -> ident -> fv
  val union    : fv -> fv -> fv
  val lvalue   : match_env -> LDecl.hyps -> fv -> lvalue -> fv
  val axiom    : match_env -> LDecl.hyps -> fv -> axiom -> fv
  val pattern  : match_env -> LDecl.hyps -> fv -> pattern -> fv
  val lvalue0  : match_env -> LDecl.hyps -> lvalue -> fv
  val axiom0   : match_env -> LDecl.hyps -> axiom -> fv
  val pattern0 : match_env -> LDecl.hyps -> pattern -> fv
end = struct
  type fv = int Mid.t

  let add_fv (m: fv) (x : ident) =
    Mid.change (fun i -> Some (odfl 0 i + 1)) x m

  let union (m1 : fv) (m2 : fv) =
    Mid.union (fun _ i1 i2 -> Some (i1 + i2)) m1 m2

  let rec lvalue (env : match_env) h (map : fv) =
    function
    | LvVar (pv,_) ->
        pattern env h map (pat_pv pv)
    | LvTuple t ->
        List.fold_left (pattern env h) map (List.map (fun (x,_) -> pat_pv x) t)
    | LvMap ((_,_),pv,e,_) ->
        pattern env h (union map e.e_fv) (pat_pv pv)

  and axiom (env : match_env) h =
    let rec aux (map : fv) (a : axiom) =
      match a with
      | Axiom_Form f -> union f.f_fv map
      | Axiom_Memory m -> add_fv map m
      | Axiom_Instr i -> union map i.i_fv
      | Axiom_Stmt s -> union map s.s_fv
      | Axiom_MemEnv (m, _) -> add_fv map m
      | Axiom_Prog_Var pv -> pattern env h map (pat_xpath pv.pv_name)
      | Axiom_Xpath xp -> pattern env h map (pat_mpath xp.x_top)
      | Axiom_Mpath mp ->
          let env0 = LDecl.toenv h in
          if is_none (EcEnv.Mod.by_mpath_opt mp env0) then map else
          List.fold_left (pattern env h)
            (pattern env h map (pat_mpath_top mp.m_top))
            (List.map pat_mpath mp.m_args)

      | Axiom_Module (`Local id) -> add_fv map id
      | Axiom_Module _ -> map
      | Axiom_Local (id,_) -> add_fv map id
      | Axiom_Op _ -> map
      | Axiom_Hoarecmp _ -> map
      | Axiom_Lvalue lv -> lvalue env h map lv

    in fun m a -> aux m a

  and pattern env h =
    let rec aux (map : int Mid.t) = function
      | Pat_Anything -> map
      | Pat_Meta_Name (p,n,_) -> aux (add_fv map n) p
      | Pat_Sub p -> aux map p
      | Pat_Or lp -> List.fold_left aux map lp
      | Pat_Red_Strat (p,_) -> aux map p
      | Pat_Type (p,_) -> aux map p
      | Pat_Fun_Symbol (Sym_Form_Quant (_,b),lp) ->
         let map' = List.fold_left aux Mid.empty lp in
         let map' =
           Mid.filter
             (fun x _ -> not (List.exists (fun (y,_) -> id_equal x y) b))
             map' in
         union map map'
      | Pat_Fun_Symbol (Sym_Quant (_,b),lp) ->
         let map' = List.fold_left aux Mid.empty lp in
         let map' =
           Mid.filter
             (fun x _ -> not (List.exists (fun (y,_) -> id_equal x y) b))
             map' in
         union map map'
      | Pat_Fun_Symbol (_,lp) -> List.fold_left aux map lp
      | Pat_Axiom a -> axiom env h map a
      | Pat_Instance _ -> assert false (* FIXME: instance *)

    in fun m p -> aux m p

  (* ------------------------------------------------------------------ *)
  let lvalue0  env h = lvalue  env h Mid.empty
  let axiom0   env h = axiom   env h Mid.empty
  let pattern0 env h = pattern env h Mid.empty
end

(* --------------------------------------------------------------------- *)
let restr_bds_check (env : environment) (p : pattern) (restr : pbindings) =
  let mr = Sid.of_list (List.map fst restr) in
  let m = Mid.set_diff (FV.pattern0 env.env_match env.env_hyps p) mr in
  Mid.for_all (fun x _ -> LDecl.has_id x env.env_hyps) m


(* add_match can raise the exception : CannotUnify *)
let nadd_match (e : nengine) (name : meta_name) (p : pattern)
      (orb : pbindings option) : nengine =
  let env = e.ne_env in
  let env = saturate env in
  let subst = psubst_of_env env.env_match in
  let p = Psubst.p_subst subst p in
  if odfl true (omap (fun r -> restr_bds_check env p r) orb)
  then
    let me_matches =
      match Mid.find_opt name e.ne_env.env_match.me_matches with
      | None -> Mid.add name p e.ne_env.env_match.me_matches
      | Some p' -> if EQ.pattern e.ne_env p p'
                   then e.ne_env.env_match.me_matches
                   else raise CannotUnify in
    { e with ne_env = { env with env_match = { env.env_match with me_matches; }; }; }
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

let rewrite_term e f =
  let env   = saturate e.e_env in
  let subst = psubst_of_env env.env_match in
  Psubst.p_subst subst (pat_form f)

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
let add_ogty (id : ident) (p : pattern) (m : ogty Mid.t) =
  match p with
  | Pat_Type (_,gty) -> Mid.add id gty m
  | Pat_Axiom (Axiom_Local (_,ty))
    | Pat_Axiom (Axiom_Form { f_ty = ty })
    | Pat_Fun_Symbol (Sym_Form_App ty,_)
    | Pat_Fun_Symbol (Sym_Form_Proj (_,ty),_)
    | Pat_Fun_Symbol (Sym_Form_Match ty,_)
    | Pat_Fun_Symbol (Sym_Form_Pvar ty,_)
    -> Mid.add id (OGTty (Some ty)) m
  | Pat_Axiom (Axiom_MemEnv (_,mt)) -> Mid.add id (OGTmem (Some mt)) m
  | _ -> m

let rec abstract_opt
          (other_args : Sid.t)
          (ep : pattern option * ogty Mid.t * engine)
          ((arg,parg) : Name.t * pattern) :
          pattern option * ogty Mid.t * engine =
  match ep with
  | None, map, e -> None, map, e
  | Some p, map, e ->
     let eq_pat' env mgty p pp =
       match p, pp with
       | Pat_Meta_Name (_,n,_), _
            when Mid.mem n other_args -> false, mgty
       | _, Pat_Meta_Name (_,n,_)
            when Mid.mem n other_args -> false, mgty
       | _,_ ->
          if EQ.pattern env p pp
          then true, (add_ogty arg pp (add_ogty arg p mgty))
          else false, mgty
     in
     let aux (mgty,env) p a =
       let rec f (mgty,env) p =
         let eq, mgty = eq_pat' env mgty p a in
         if eq then (mgty,env), Pat_Meta_Name(Pat_Anything,arg,None)
         else
         (mgty,env), p in
       let (mgty,env), p' = p_map_fold f (mgty,env) p in
       if   p = p'
       then
         None, (mgty,env)
       else
         Some p', (mgty,env)
     in
     let env   = saturate e.e_env in
     let subst = psubst_of_env env.env_match in
     let p     = Psubst.p_subst subst p in
     let parg  = Psubst.p_subst subst parg in
     match aux (map,e.e_env) p parg with
     | None, (map,_env) ->
        None, map, e
     | Some p, (map,_env) ->
        Some p, map, e


(* ---------------------------------------------------------------------- *)
let rec process (e : engine) : nengine =
  (* let _ =
   *   let fmt, ppe = e.e_env.env_fmt, e.e_env.env_ppe in
   *   Format.fprintf fmt "[W]-- %a =? %a\n"
   *     (EcPrinting.pp_pattern ppe) e.e_pattern
   *     (EcPrinting.pp_pat_axiom ppe) e.e_head
   * in *)
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

  | Pat_Type (p,ty), o2 when EQ.is_ogty e.e_env (pat_axiom o2) ty ->
     process { e with e_pattern = p; }

  | Pat_Type _, _ -> next NoMatch e

  | Pat_Or [], _ -> next NoMatch e

  | Pat_Or (p::pl), _ ->
     let f p = { e with
                 e_pattern = p;
                 e_env = { e.e_env with
                           env_restore_unienv =
                             ref !(e.e_env.env_restore_unienv); }; } in
     process { e with
         e_pattern = p;
         e_continuation = Zor (e.e_continuation,List.map f pl,e_next e);
       }

  | Pat_Red_Strat (e_pattern,f),_ ->
     let env_red_info_p, env_red_info_a =
       f e.e_env.env_red_info_p e.e_env.env_red_info_a in
     let e_env = { e.e_env with env_red_info_a; env_red_info_p } in
     process { e with e_pattern; e_env }

  | Pat_Fun_Symbol(Sym_App,(Pat_Meta_Name(Pat_Anything,name,ob))::pargs),axiom
    | Pat_Fun_Symbol(Sym_App,(Pat_Meta_Name(Pat_Type(Pat_Anything,_),name,ob))::pargs),axiom
    | Pat_Fun_Symbol(Sym_Form_App _,(Pat_Meta_Name(Pat_Anything,name,ob))::pargs),axiom
    | Pat_Fun_Symbol(Sym_Form_App _,(Pat_Meta_Name(Pat_Type(Pat_Anything,_),name,ob))::pargs),axiom ->
     begin
       (* higher order *)
       let env = saturate e.e_env in
       let subst = psubst_of_env env.env_match in
       let add_ident i x =
         EcIdent.create (String.concat "$" ["s";string_of_int i]),
         Psubst.p_subst subst x in
       let args = List.mapi add_ident pargs in
       let env_meta_restr_binds =
         odfl env.env_meta_restr_binds
           (omap (fun b -> Mid.add name b env.env_meta_restr_binds) ob) in
       let e = { e with e_env = { env with env_meta_restr_binds } } in
       let abstract m (p,m2,e) arg =
         let op,m,e = abstract_opt m (Some p,m2,e) arg in
         odfl p op, m, e in
       let pat, map, e =
         (* FIXME : add strategies to adapt the order of the arguments *)
         List.fold_left (abstract (Sid.of_list (List.map fst args)))
           (Psubst.p_subst subst (Pat_Axiom axiom),Mid.empty,e) args in
       let f (name,_) = (name,Mid.find name map) in
       let args = List.map f args in
       (* let pat = omap (p_quant Llambda args) pat in *)
       let pat = p_quant Llambda args pat in
       let pat = Psubst.p_subst subst pat in
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
         | CannotUnify -> NoMatch, e
       in
       next m e
     end

  | Pat_Axiom o1, o2 when EQ.axiom e.e_env o1 o2 -> next Match e

  | Pat_Axiom _, _ -> next NoMatch e

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
          | Sym_Form_Proj (i,ty), [e_pattern], Fproj (f1,j)
               when i = j  && EQ.ty e.e_env ty f.f_ty ->
             process { e with e_pattern; e_head = Axiom_Form f1 }
          | Sym_Form_Match ty, p::pl, Fmatch (fmatch,fl,_)
               when 0 = List.compare_lengths pl fl && EQ.ty e.e_env ty f.f_ty ->
             let zand = List.map2 (fun x y -> Axiom_Form x, y) fl pl in
             process { e with
                 e_pattern = p;
                 e_head = Axiom_Form fmatch;
                 e_continuation = Zand ([],zand,e.e_continuation);
               }
          | Sym_Form_Quant (q1,bs1), [p], Fquant (q2,bs2,f2)
               when q1 = q2 && 0 > List.compare_lengths bs1 bs2 -> begin
              (* FIXME : lambda case to be considered in higher order *)
              let (pbs1,_), (fbs1,fbs2) = List.prefix2 bs1 bs2 in
              if not (List.for_all2 (EQ.gty e.e_env) (List.map snd pbs1) (List.map snd fbs1))
              then  next NoMatch e
              else
              let f s (id1,gty1) (id2,_) = Psubst.p_bind_gty s id1 id2 gty1 in
              let e_env = saturate e.e_env in
              let subst = psubst_of_env e_env.env_match in
              let s     = List.fold_left2 f subst pbs1 fbs1 in
              let e_pattern = Psubst.p_subst s p in
              process { e with
                  e_pattern; e_env; e_head = Axiom_Form (f_quant q2 fbs2 f2);
                }
            end

          | Sym_Form_Pvar ty, p1::p2::[], Fpvar (_,m)
               when EQ.ty e.e_env f.f_ty ty ->
             process { e with
                 e_pattern = p2;
                 e_head = Axiom_Memory m;
                 e_continuation = Zand ([],[Axiom_Form f,p1],e.e_continuation);
               }
          | Sym_Form_Prog_var k, [p], Fpvar (x2,_) when k = x2.pv_kind ->
             process { e with e_pattern = p; e_head = Axiom_Xpath x2.pv_name; }
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

and next (m : ismatch) (e : engine) : nengine = match m with
  | NoMatch -> begin
      let i_red_p, i_red_a =
        e.e_env.env_red_info_p, e.e_env.env_red_info_a in
      let e_env = saturate e.e_env in
      let e = { e with e_env } in
      let subst = psubst_of_env e_env.env_match in
      match h_red_strat e.e_env.env_hyps subst i_red_p i_red_a
              (Psubst.p_subst subst e.e_pattern) e.e_head with
      | None -> next_n m (e_next e)
      | Some (p,a) ->
         let e_or = { e with e_pattern = p; e_head = a } in
         match e.e_continuation with
         | Zor (cont,(_::_ as l),nomatch_cont) ->
            process { e with e_continuation = Zor (cont,l@[e_or],nomatch_cont) }
         | _ -> process e_or
    end
  | _ ->
     next_n m (e_next e)

and next_n (m : ismatch) (e : nengine) : nengine =
  match m,e.ne_continuation with
  | NoMatch, ZTop -> raise NoMatches

  | Match, ZTop   -> e

  | NoMatch, Znamed (_f, _name, _ob, ne_continuation) ->
     let _ = restore_environment e.ne_env in
     next_n NoMatch { e with ne_continuation; }

  | Match, Znamed (f, name, ob, ne_continuation) ->
     let m,e =
       try
         let ne = nadd_match e name f ob in
         Match, { ne with ne_continuation; }
       with
       | CannotUnify ->
          let _ = restore_environment e.ne_env in
          NoMatch, { e with ne_continuation; } in
     next_n m e

  | NoMatch, Zand (_,_,ne_continuation) ->
     let _ = restore_environment e.ne_env in
     next_n NoMatch { e with ne_continuation; }

  | Match, Zand (_before,[],ne_continuation) ->
     next_n Match { e with ne_continuation }

  | Match, Zand (before,(f,p)::after,z) ->
     let ne_env = saturate e.ne_env in
     let e      = { e with ne_env } in
     let subst  = psubst_of_env ne_env.env_match in
     let p      = Psubst.p_subst subst p in
     process (n_engine f p
                { e with ne_continuation = Zand ((f,p)::before,after,z)})

  | Match, Zor (ne_continuation, _, _) -> next_n Match { e with ne_continuation }

  | NoMatch, Zor (_, [], ne) ->
     let _ = restore_environment e.ne_env in
     next_n NoMatch ne

  | NoMatch, Zor (_, e'::engines, ne) ->
     let _ = restore_environment e'.e_env in
     process { e' with e_continuation = Zor (e'.e_continuation, engines, ne); }

  | Match, Zbinds (ne_continuation, env_current_binds) ->
     next_n Match { e with ne_continuation; ne_env = { e.ne_env with env_current_binds } }

  | NoMatch, Zbinds (ne_continuation, env_current_binds) ->
     let _ = restore_environment e.ne_env in
     let ne_env = { e.ne_env with env_current_binds } in
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
      | Fint _
        | Flocal _
        | Fop _-> []

      | Flet (_,f1,f2) ->
         List.map (sub_engine e p e.e_env.env_current_binds)
           [axiom_form f1;axiom_form f2]
      | FhoareF h ->
         List.map (sub_engine e p e.e_env.env_current_binds)
           [axiom_form h.hf_pr; Axiom_Xpath h.hf_f; Axiom_Form h.hf_po]
      | FhoareS h ->
         List.map (sub_engine e p e.e_env.env_current_binds)
           [Axiom_MemEnv h.hs_m; axiom_form h.hs_pr; Axiom_Stmt h.hs_s;
            axiom_form h.hs_po]
      | FbdHoareF h ->
         List.map (sub_engine e p e.e_env.env_current_binds)
           [axiom_form h.bhf_pr; Axiom_Xpath h.bhf_f; Axiom_Form h.bhf_po;
            Axiom_Hoarecmp h.bhf_cmp; Axiom_Form h.bhf_bd]
      | FbdHoareS h ->
         List.map (sub_engine e p e.e_env.env_current_binds)
           [Axiom_MemEnv h.bhs_m; axiom_form h.bhs_pr; Axiom_Stmt h.bhs_s;
            axiom_form h.bhs_po; Axiom_Hoarecmp h.bhs_cmp; Axiom_Form h.bhs_bd]
      | FequivF h ->
         List.map (sub_engine e p e.e_env.env_current_binds)
           [Axiom_Form h.ef_pr; Axiom_Xpath h.ef_fl; Axiom_Xpath h.ef_fr;
            Axiom_Form h.ef_po]
      | FequivS h ->
         List.map (sub_engine e p e.e_env.env_current_binds)
           [Axiom_MemEnv h.es_ml; Axiom_MemEnv h.es_mr; Axiom_Form h.es_pr;
            Axiom_Stmt h.es_sl; Axiom_Stmt h.es_sr; Axiom_Form h.es_po]
      | FeagerF h ->
         List.map (sub_engine e p e.e_env.env_current_binds)
           [Axiom_Form h.eg_pr; Axiom_Stmt h.eg_sl; Axiom_Xpath h.eg_fl;
            Axiom_Xpath h.eg_fr; Axiom_Stmt h.eg_sr; Axiom_Form h.eg_po]
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
         [sub_engine e p (List.map (snd_map ogty_of_gty) bs) (Axiom_Form f)]
      | Fglob (mp,mem) ->
         List.map (sub_engine e p e.e_env.env_current_binds)
           [Axiom_Module mp.m_top;Axiom_Memory mem]
      | Fpvar (_pv,mem) ->
         [sub_engine e p e.e_env.env_current_binds (Axiom_Memory mem)]
    end


let get_matches (e : engine) : match_env = (saturate e.e_env).env_match
let get_n_matches (e : nengine) : match_env = (saturate e.ne_env).env_match

let search_eng e =
  try
    Some (process e)
  with
  | NoMatches -> None

let pattern_of_axiom (sbd: ogty Mid.t) (a : axiom) =
  let pat_axiom x   = Pat_Axiom x in
  let pat_form x    = Pat_Axiom (Axiom_Form x) in
  let axiom_expr e  = Axiom_Form (form_of_expr e) in
  let axiom_mpath m = Axiom_Mpath m in
  let pat_instr i   = Pat_Axiom (Axiom_Instr i) in
  let typ ty p      = Pat_Type(p,OGTty (Some ty)) in

  let rec aux a     = match a with
    | Axiom_Local (id,ty) ->
       if Mid.mem id sbd
       then Some (typ ty (Pat_Meta_Name(Pat_Anything,id,None)))
       else Some (pat_axiom a)
    | Axiom_Form f -> begin
        let fty = f.f_ty in
        match f.f_node with
        | Fquant(quant,binds,f)
             when Mid.set_disjoint (Sid.of_list (List.map fst binds)) sbd ->
           omap (fun fi -> typ fty (p_f_quant quant binds fi)) (aux_f f)
        | Fquant _ -> assert false
        | Fif(f1,f2,f3) ->
           omap (function [p1;p2;p3] -> typ fty (p_if p1 p2 p3) | _ -> assert false)
             (omap_list pat_form aux_f [f1;f2;f3])
        | Fmatch(f,args,ty) ->
           omap (function op::l -> p_match op ty l | _ -> assert false)
             (omap_list pat_form aux_f (f::args))
        | Flet (lp,f1,f2) -> begin
            match lp with
            | LSymbol (id,_) when Mid.mem id sbd -> assert false
            | LTuple tuple
                 when not(Mid.set_disjoint (Sid.of_list (List.map fst tuple)) sbd) ->
               assert false
            | LRecord _ -> assert false
            | _ ->
               omap (function [p1;p2] -> typ fty (p_let lp p1 p2) | _ -> assert false)
                 (omap_list pat_form aux_f [f1;f2])
          end
        | Fint _ -> None
        | Flocal id ->
           if Mid.mem id sbd
           then Some (typ fty (Pat_Meta_Name(Pat_Anything,id,None)))
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
           Some(typ fty (pat_op op lty))
        | Fapp ({ f_node = Flocal id },args) when Mid.mem id sbd ->
           let p =
             p_app (Pat_Meta_Name(Pat_Anything,id,None))
               (List.map (fun x ->  odfl (pat_form x) (aux_f x)) args) (Some fty) in
           Some (typ fty p)
        | Fapp(fop,args) ->
           if mem_ty_univar fty
           then
             let pargs = List.map (fun arg -> odfl (pat_form arg) (aux_f arg)) args in
             let pop = odfl (pat_form fop) (aux_f fop) in
             Some (typ fty (p_app pop pargs (Some fty)))
           else
             omap (function
                 | pop::pargs ->
                    typ fty (p_app pop pargs (Some fty))
                 | _ -> assert false)
               (omap_list pat_form aux_f (fop::args))
        | Ftuple args ->
           omap (fun l -> typ fty (p_tuple l))
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
       Some (p_type (Pat_Meta_Name(Pat_Anything, fst m, None)) (OGTmem (Some (snd m))))
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
           omap (fun x -> typ ty x) (aux (Axiom_Prog_Var pv))
        | LvTuple l ->
           let default (pv,ty) = typ ty (pat_pv pv) in
           let aux (pv,ty) =
             omap (fun x -> typ ty x) (aux (Axiom_Prog_Var pv)) in
           omap (fun l -> p_tuple l) (omap_list default aux l)
        | LvMap _ -> (* FIXME *) assert false
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
  | (x,ty1)::r1, (y,ty2)::r2 when EQ.name x y && gty_equal ty1 ty2 ->
     aux ((x,ty1)::acc) r1 r2
  | _ -> List.rev acc
  in aux [] bs1 bs2

let rec prefix_pbinds bs1 bs2 =
  let rec aux acc bs1 bs2 = match bs1,bs2 with
  | (x,OGTty (Some ty1))::r1, (y,OGTty (Some ty2))::r2
       when EQ.name x y && gty_equal (GTty ty1) (GTty ty2) ->
     aux ((x,OGTty (Some ty1))::acc) r1 r2
  | (x,OGTty t1)::r1, (y,OGTty t2)::r2 when EQ.name x y ->
     let t = match t1 with
       | Some _ -> t1
       | None ->
       match t2 with
       | Some _ -> t2
       | None -> None in
     aux ((x,OGTty t)::acc) r1 r2
  | (x,OGTmem (Some ty1))::r1, (y,OGTmem (Some ty2))::r2
       when EQ.name x y && gty_equal (GTmem ty1) (GTmem ty2) ->
     aux ((x,OGTmem (Some ty1))::acc) r1 r2
  | (x,OGTmem t1)::r1, (y,OGTmem t2)::r2 when EQ.name x y ->
     let t = match t1 with
       | Some _ -> t1
       | None ->
       match t2 with
       | Some _ -> t2
       | None -> None in
     aux ((x,OGTmem t)::acc) r1 r2
  | (x,OGTmodty (Some (t1,mr1)))::r1, (y,OGTmodty (Some (t2,mr2)))::r2
       when EQ.name x y && gty_equal (GTmodty (t1,mr1)) (GTmodty (t2,mr2)) ->
     aux ((x,OGTmodty (Some (t1,mr1)))::acc) r1 r2
  | (x,OGTmodty t1)::r1, (y,OGTmodty t2)::r2 when EQ.name x y ->
     let t = match t1 with
       | Some _ -> t1
       | None ->
       match t2 with
       | Some _ -> t2
       | None -> None in
     aux ((x,OGTmodty t)::acc) r1 r2
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
     let b = List.map (snd_map ogty_of_gty) b in
     aux (current_bds @ b) meta_bds (pat_form f)
  | Pat_Axiom _ -> meta_bds
  | Pat_Fun_Symbol (Sym_Form_Quant (_,b),[p]) ->
     let b = List.map (snd_map ogty_of_gty) b in
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

let pattern_of_form me f = pattern_of_axiom me.me_meta_vars (Axiom_Form f)

let pattern_of_memory me m = pattern_of_axiom me.me_meta_vars (Axiom_Memory m)

let init_match_env ?mtch ?unienv ?metas () =
  { me_matches   = odfl Mid.empty mtch;
    me_unienv    = odfl (EcUnify.UniEnv.create None) unienv;
    me_meta_vars = odfl Mid.empty metas;
  }

(* val mkengine    : base -> engine *)
let mkenv ?ppe ?fmt ?mtch (h : LDecl.hyps)
      (red_info_p : EcReduction.reduction_info)
      (red_info_a : EcReduction.reduction_info)
    : environment = {
    env_hyps             = h;
    env_red_info_p       = red_info_p;
    env_red_info_a       = red_info_a;
    env_restore_unienv   = ref None;
    env_current_binds    = [] ;
    env_meta_restr_binds = Mid.empty;
    env_ppe              = odfl (EcPrinting.PPEnv.ofenv (LDecl.toenv h)) ppe;
    env_fmt              = odfl Format.std_formatter fmt;
    env_match            = odfl {
                               me_matches   = Mid.empty;
                               me_unienv    = EcUnify.UniEnv.create None;
                               me_meta_vars = Mid.empty;
                             } mtch;
  }

let mkengine (a : axiom) (p : pattern) (env : environment) : engine =
  { e_head = a;
    e_pattern = p;
    e_env = env;
    e_continuation = ZTop;
  }

let mk_engine ?ppe ?fmt ?mtch f e_pattern env_hyps env_red_info_p env_red_info_a =
  let e = {
      e_pattern;
      e_head         = axiom_form f;
      e_continuation = ZTop;
      e_env          = {
          env_hyps;
          env_red_info_p;
          env_red_info_a;
          env_restore_unienv   = ref None;
          env_current_binds    = [];
          env_meta_restr_binds = Mid.empty;
          env_ppe              = odfl (EcPrinting.PPEnv.ofenv (LDecl.toenv env_hyps)) ppe;
          env_fmt              = odfl Format.std_formatter fmt;
          env_match            = odfl {
                                     me_matches   = Mid.empty;
                                     me_meta_vars = Mid.empty;
                                     me_unienv    = EcUnify.UniEnv.create None;
                                   } mtch
        }
    } in e

let search ?ppe ?fmt ?mtch (f : form) (p : pattern) (h : LDecl.hyps)
      (red_info_p : EcReduction.reduction_info)
      (red_info_a : EcReduction.reduction_info) =
  try
    let env = mkenv ?ppe ?fmt ?mtch h red_info_p red_info_a in
    let ne = process (mkengine (axiom_form f) p env) in
    Some (get_n_matches ne, ne.ne_env)
  with
  | NoMatches -> None


let match_is_full (e : match_env) h =
  let matches   = e.me_matches in
  let meta_vars = e.me_meta_vars in

  let f n _ = match Mid.find_opt n matches with
    | None   -> false
    | Some p -> let fv = FV.pattern0 e h p in
                Mid.for_all (fun n _ -> not (Mid.mem n meta_vars)) fv in

  Mid.for_all f meta_vars


let add_meta_var (n : Name.t) (ogty : ogty) (me : match_env) : match_env =
  { me with me_meta_vars = Mid.add n ogty me.me_meta_vars }


let fsubst_of_env (me : match_env) (env : env) =
  let ps = psubst_of_env me in
  let fs = Fsubst.f_subst_init ~sty:ps.ps_sty () in
  let bind_pattern id p s =
    try Fsubst.f_bind_local s id (Translate.form_of_pattern env p)
    with Translate.Invalid_Type _ ->
    try Fsubst.f_bind_mem s id (Translate.memory_of_pattern p)
    with Translate.Invalid_Type _ ->
    try Fsubst.f_bind_mod s id (Translate.mpath_of_pattern env p)
    with Translate.Invalid_Type _ -> s in

  Mid.fold bind_pattern me.me_matches fs
