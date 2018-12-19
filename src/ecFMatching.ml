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

let verbose = false

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
    env_hyps               : EcEnv.LDecl.hyps;
    env_match              : match_env;
    env_red_info_match     : EcReduction.reduction_info;
    env_red_info_same_meta : EcReduction.reduction_info;
    env_restore_unienv     : EcUnify.unienv option ref;
    env_current_binds      : pbindings;
    env_meta_restr_binds   : pbindings Mid.t;
    env_fmt                : Format.formatter;
    env_ppe                : EcPrinting.PPEnv.t;
    env_verbose            : bool;
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

type ismatch =
  | Match
  | NoMatch
  | NoMatch_NoRed

(* -------------------------------------------------------------------- *)
let menv_copy (me : match_env) =
  { me with me_unienv = EcUnify.UniEnv.copy me.me_unienv }

(* -------------------------------------------------------------------- *)
let menv_of_hyps (hy : LDecl.hyps) =
  { me_unienv    = EcProofTyping.unienv_of_hyps hy;
    me_meta_vars = Mid.empty;
    me_matches   = Mid.empty; }

(* -------------------------------------------------------------------- *)
let menv_add_form x ty menv =
  assert (not (Mid.mem x menv.me_meta_vars));
  { menv with
      me_meta_vars = Mid.add x (OGTty (Some ty)) menv.me_meta_vars; }

(* -------------------------------------------------------------------- *)
let menv_add_mem x menv =
  assert (not (Mid.mem x menv.me_meta_vars));
  { menv with
      me_meta_vars = Mid.add x (OGTmem None) menv.me_meta_vars; }

(* -------------------------------------------------------------------------- *)
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

let psubst_of_menv env =
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

  let rec form_of_pattern env (p : pattern) = match p.p_node with
    | Pat_Anything            -> raise (Invalid_Type "formula")
    | Pat_Meta_Name (_,_,_)   -> raise (Invalid_Type "formula")
    | Pat_Sub _               -> raise (Invalid_Type "sub in form")
    | Pat_Or [p]              -> form_of_pattern env p
    | Pat_Or _                -> raise (Invalid_Type "formula")
    | Pat_Red_Strat (p,_)     -> form_of_pattern env p
    | Pat_Axiom (Axiom_Form f)        -> f
    | Pat_Axiom (Axiom_Local (id,ty)) -> f_local id ty
    | Pat_Axiom _             -> raise (Invalid_Type "formula")
    | Pat_Fun_Symbol (s, lp)  ->
    match s, lp with
    | Sym_Form_If, [p1;p2;p3]   -> f_if (form_of_pattern env p1)
                                     (form_of_pattern env p2)
                                     (form_of_pattern env p3)
    | Sym_Form_App _, p::lp    -> f_ty_app env (form_of_pattern env p)
                                     (List.map (form_of_pattern env) lp)
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
    | Sym_Quant (q,pb), [p] ->
       let f (id,ogt) = match ogt with
         | OGTty (Some ty) -> id, GTty ty
         | OGTmem (Some t) -> id, GTmem t
         | OGTmodty (Some (t,r)) -> id, GTmodty (t,r)
         | _ -> raise (Invalid_Type "formula") in
       f_quant q (List.map f pb) (form_of_pattern env p)
    | _ -> raise (Invalid_Type "formula")

  and memory_of_pattern p = match p.p_node with
    | Pat_Axiom (Axiom_Memory m) -> m
    | _ -> raise (Invalid_Type "memory")

  and prog_var_of_pattern env p = match p.p_node with
    | Pat_Axiom (Axiom_Prog_Var pv) -> pv
    | Pat_Fun_Symbol (Sym_Form_Prog_var k, [xp]) ->
       pv (xpath_of_pattern env xp) k
    | _ -> raise (Invalid_Type "prog_var")

  and xpath_of_pattern env p = match p.p_node with
    | Pat_Axiom (Axiom_Xpath xp) -> xp
    | Pat_Fun_Symbol (Sym_Xpath, [mp;p]) ->
       EcPath.xpath (mpath_of_pattern env mp) (path_of_pattern p)
    | _ -> raise (Invalid_Type "xpath")

  and path_of_pattern p = match p.p_node with
    | Pat_Axiom (Axiom_Op (p,[])) -> p
    | _ -> raise (Invalid_Type "path")

  and mpath_of_pattern env p = match p.p_node with
    | Pat_Axiom (Axiom_Mpath mp) -> mp
    | Pat_Fun_Symbol (Sym_Mpath, mp::margs) ->
       mpath (mpath_top_of_pattern env mp) (List.map (mpath_of_pattern env) margs)
    | _ -> raise (Invalid_Type "mpath")

  and mpath_top_of_pattern _env p = match p.p_node with
    | Pat_Axiom (Axiom_Mpath_top m) -> m
    | _ -> raise (Invalid_Type "mpath_top")

  and memenv_of_pattern p = match p.p_node with
    | Pat_Axiom (Axiom_MemEnv m) -> m
    | _ -> raise (Invalid_Type "memenv")

  and stmt_of_pattern env p = match p.p_node with
    | Pat_Axiom (Axiom_Stmt s) -> s
    | Pat_Fun_Symbol (Sym_Stmt_Seq, l) ->
       stmt (List.flatten (List.map (instr_of_pattern env) l))
    | _ -> raise (Invalid_Type "stmt")

  and instr_of_pattern env p = match p.p_node with
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

  and lvalue_of_pattern env p = match p.p_node with
    | Pat_Axiom (Axiom_Lvalue lv) -> lv
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

  and cmp_of_pattern p = match p.p_node with
    | Pat_Axiom (Axiom_Hoarecmp cmp) -> cmp
    | _ -> raise (Invalid_Type "hoarecmp")

  let form_of_pattern env p = match p.p_node with
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
  val ogty      : environment -> ogty -> ogty -> bool
  val binding   : environment -> binding -> binding -> bool
  val pbinding  : environment -> pbinding -> pbinding -> bool
  val symbol    : environment -> fun_symbol -> fun_symbol -> bool
  val form      : environment -> EcReduction.reduction_info -> form -> form -> bool
  val axiom     : environment -> EcReduction.reduction_info -> axiom -> axiom -> bool
  val pattern   : environment -> EcReduction.reduction_info -> pattern -> pattern -> bool
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
    EcPath.p_equal op1 op2 && List.for_all2 (ty env) lty1 lty2

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
    | _ when name id1 id2 -> ogty_equal ogt1 ogt2
    | _ -> false

  let symbol (env : environment) (s1 : fun_symbol) (s2 : fun_symbol) : bool =
    match s1,s2 with
    | Sym_Form_Proj (i1,t1), Sym_Form_Proj (i2,t2) ->
       if not (i1 = i2) then false
       else ty env t1 t2
    | Sym_Form_Pvar t1, Sym_Form_Pvar t2
      | Sym_Form_App (Some t1, _), Sym_Form_App (Some t2, _)
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

  let form (env : environment) ri (f1 : form) (f2 : form) =
    let env_restore_unienv = !(env.env_restore_unienv) in
    env.env_restore_unienv := None;
    let eq = ty env f1.f_ty f2.f_ty in
    if eq
    then
      let _ = if env.env_verbose then
                Format.fprintf env.env_fmt
                  "[W] === types are unified %a in %a\n"
                  (EcPrinting.pp_type env.env_ppe) f1.f_ty
                  (EcPrinting.pp_type env.env_ppe) f2.f_ty in
      let sty    = { EcTypes.ty_subst_id with
                     ts_u = EcUnify.UniEnv.assubst env.env_match.me_unienv } in
      let sf     = Fsubst.f_subst_init ~sty () in
      let f1, f2 = Fsubst.f_subst sf f1, Fsubst.f_subst sf f2 in
      if EcReduction.is_conv_param ri env.env_hyps f1 f2 then
        let _ = env.env_restore_unienv := env_restore_unienv in true
      else
        let _ = restore_environment env in
        let _ = env.env_restore_unienv := env_restore_unienv in false
    else
      let _ = restore_environment env in
      let _ = env.env_restore_unienv := env_restore_unienv in
      false

  let rec axiom (env : environment) ri (o1 : axiom) (o2 : axiom) : bool =
    let aux o1 o2 =
      match o1,o2 with
      | Axiom_Form f1, Axiom_Form f2 ->
         form env ri f1 f2
      | Axiom_Memory m1, Axiom_Memory m2 ->
         memory env m1 m2
      | Axiom_MemEnv m1, Axiom_MemEnv m2 ->
         memenv env m1 m2
      | Axiom_Prog_Var x1, Axiom_Prog_Var x2 ->
         prog_var env x1 x2
      | Axiom_Op (op1,lty1), Axiom_Op (op2,lty2) ->
         op env (op1,lty1) (op2,lty2)
      | Axiom_Mpath_top m1, Axiom_Mpath_top m2 ->
         mpath_top env m1 m2
      | Axiom_Mpath m1, Axiom_Mpath m2 ->
         mpath env m1 m2
      | Axiom_Mpath { m_top = mt1 ; m_args = [] }, Axiom_Mpath_top mt2
        | Axiom_Mpath_top mt1, Axiom_Mpath { m_top = mt2 ; m_args = [] } ->
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

  and pattern (env : environment) ri (p1 : pattern) (p2 : pattern) : bool =
    let env_restore_unienv = !(env.env_restore_unienv) in
    env.env_restore_unienv := None;
    let try_translate_eq eq trans p1 p2 =
      try eq (trans p1) (trans p2) with Translate.Invalid_Type _ -> false in
    let eq =
      if      (try_translate_eq (form env ri)
                 (Translate.form_of_pattern (EcEnv.LDecl.toenv env.env_hyps)) p1 p2)
      then true
      else if (try_translate_eq (memory env) Translate.memory_of_pattern p1 p2)
      then true
      else if (try_translate_eq (mpath env)
                 (Translate.mpath_of_pattern (EcEnv.LDecl.toenv env.env_hyps)) p1 p2)
      then true
      else
      match p1.p_node, p2.p_node with
      | Pat_Anything, _ | _, Pat_Anything -> true
      | Pat_Red_Strat (p1,red1), Pat_Red_Strat (p2,red2) ->
         if red1 == red2 then pattern env ri p1 p2 else false
      | Pat_Or lp1, Pat_Or lp2 ->
         List.for_all2 (pattern env ri) lp1 lp2
      | Pat_Sub p1, Pat_Sub p2 -> pattern env ri p1 p2
      | Pat_Axiom a1, Pat_Axiom a2 ->
         axiom env ri a1 a2
      | Pat_Fun_Symbol (s1, lp1), Pat_Fun_Symbol (s2, lp2) ->
         if symbol env s1 s2 then List.for_all2 (pattern env ri) lp1 lp2
         else false
      | Pat_Meta_Name (p1,n1,b1), Pat_Meta_Name (p2,n2,b2) ->
         if not (name n1 n2) then false
         else
         let eq = match b1, b2 with
           | Some b1, Some b2 -> List.for_all2 (pbinding env) b1 b2
           | _                -> true in
         if eq then pattern env ri p1 p2 else false
      | Pat_Meta_Name (_,n1,_), _ -> begin
          match Mid.find_opt n1 (saturate env).env_match.me_matches with
          | Some p1' ->
             if pattern env ri p1 p1' then false
             else pattern env ri p1' p2
          | None -> false
        end
      | _, Pat_Meta_Name (_,n2,_) -> begin
          match Mid.find_opt n2 (saturate env).env_match.me_matches with
          | Some p2' ->
             if pattern env ri p2 p2' then false
             else pattern env ri p1 p2'
          | None -> false
        end
      | Pat_Axiom a, Pat_Fun_Symbol (s,lp)
        | Pat_Fun_Symbol (s,lp), Pat_Axiom a -> begin
          match s, lp, a with
          | Sym_Form_If, [p1;p2;p3],
            Axiom_Form { f_node = Fif (f1,f2,f3) } ->
             pattern env ri p1 (pat_form f1)
             && pattern env ri p2 (pat_form f2)
             &&pattern env ri p3 (pat_form f3)

          | Sym_Form_App (Some pty, i), pop::pargs,
            Axiom_Form { f_node = Fapp (_,_) ; f_ty = fty } ->
             ty env pty fty
             && pattern env ri (pat_fun_symbol (Sym_Form_App (None,i)) (pop::pargs)) p2

          | Sym_Form_App (None, _), op1::args1,
            Axiom_Form { f_node = Fapp (op2,args2) } ->
             let (args11,args12), (args21,args22) = suffix2 args1 args2 in
             let op1 = p_app op1 args11 None in
             let op2 = f_app op2 args21
                         (EcTypes.toarrow (List.map f_ty args22) (f_ty op2)) in
             List.for_all2 (pattern env ri) (op1::args12) (List.map pat_form (op2::args22))

          | Sym_Form_Tuple, pt,
            Axiom_Form { f_node = Ftuple ft } ->
             List.for_all2 (pattern env ri) pt (List.map pat_form ft)

          | Sym_Form_Proj (pi,pty), [p1],
            Axiom_Form { f_node = Fproj (f1,fi) ; f_ty = fty } when pi = fi ->
             if not (ty env pty fty) then false
             else pattern env ri p1 (pat_form f1)

          | Sym_Form_Match pty, pop::pargs,
            Axiom_Form { f_node = Fmatch (fop,fargs,fty) }
               when 0 = List.compare_lengths pargs fargs ->
             if not (ty env pty fty) then false
             else if not (pattern env ri pop (pat_form fop)) then false
             else List.for_all2 (pattern env ri) pargs (List.map pat_form fargs)

          | Sym_Form_Quant (pq,pb), [p1],
            Axiom_Form { f_node = Fquant (fq,fb,f1) }
               when pq = fq ->
             if not (List.for_all2 (binding env) pb fb) then false
             else pattern env ri p1 (pat_form f1)

          | Sym_Form_Let plp, [p1;p2],
            Axiom_Form { f_node = Flet (flp,f1,f2) } ->
             if not (lp_equal plp flp) then false
             else if not (pattern env ri p1 (pat_form f1)) then false
             else pattern env ri p2 (pat_form f2)

          | Sym_Form_Pvar pty, [ppv;pm],
            Axiom_Form { f_node = Fpvar (fpv,fm) ; f_ty = fty } ->
             if not (ty env pty fty) then false
             else if not (pattern env ri pm (pat_memory fm)) then false
             else pattern env ri ppv (pat_pv fpv)

          | Sym_Form_Prog_var k1, [p1],
            Axiom_Prog_Var { pv_name = xp ; pv_kind = k2 } when k1 = k2 ->
             pattern env ri p1 (pat_xpath xp)

          | Sym_Form_Glob, [pmp;pm],
            Axiom_Form { f_node = Fglob (fmp,fm) } ->
             if not (pattern env ri pm (pat_memory fm)) then false
             else pattern env ri pmp (pat_mpath fmp)

          | Sym_Form_Hoare_F, [pr1;xp1;po1],
            Axiom_Form { f_node = FhoareF { hf_pr = pr2;
                                            hf_f  = xp2;
                                            hf_po = po2; } } ->
             List.for_all2 (pattern env ri) [pr1;xp1;po1]
               [pat_form pr2; pat_xpath xp2; pat_form po2]

          | Sym_Form_Hoare_S, [m1;pr1;s1;po1],
            Axiom_Form { f_node = FhoareS { hs_m  = m2;
                                            hs_pr = pr2;
                                            hs_s  = s2;
                                            hs_po = po2; } } ->
             List.for_all2 (pattern env ri) [m1;pr1;s1;po1]
               [pat_memenv m2; pat_form pr2; pat_stmt s2; pat_form po2]

          | Sym_Form_bd_Hoare_F, [pr1;xp1;po1;cmp1;bd1],
            Axiom_Form { f_node = FbdHoareF { bhf_pr  = pr2;
                                              bhf_f   = xp2;
                                              bhf_po  = po2;
                                              bhf_cmp = cmp2;
                                              bhf_bd  = bd2; } } ->
             List.for_all2 (pattern env ri) [pr1;xp1;po1;cmp1;bd1]
               [pat_form pr2; pat_xpath xp2; pat_form po2; pat_cmp cmp2;
                pat_form bd2]

          | Sym_Form_bd_Hoare_S, [m1;pr1;s1;po1;cmp1;bd1],
            Axiom_Form { f_node = FbdHoareS { bhs_m   = m2;
                                              bhs_pr  = pr2;
                                              bhs_s   = s2;
                                              bhs_po  = po2;
                                              bhs_cmp = cmp2;
                                              bhs_bd  = bd2; } } ->
             List.for_all2 (pattern env ri) [m1;pr1;s1;po1;cmp1;bd1]
               [pat_memenv m2; pat_form pr2; pat_stmt s2; pat_form po2;
                pat_cmp cmp2; pat_form bd2]

          | Sym_Form_Equiv_F, [pr1;xpl1;xpr1;po1],
            Axiom_Form { f_node = FequivF { ef_pr = pr2;
                                            ef_fl = xpl2;
                                            ef_fr = xpr2;
                                            ef_po = po2; } } ->
             List.for_all2 (pattern env ri) [pr1;xpl1;xpr1;po1]
               [pat_form pr2; pat_xpath xpl2; pat_xpath xpr2; pat_form po2]

          | Sym_Form_Equiv_S, [ml1;mr1;pr1;sl1;sr1;po1],
            Axiom_Form { f_node = FequivS { es_ml = ml2;
                                            es_mr = mr2;
                                            es_pr = pr2;
                                            es_sl = sl2;
                                            es_sr = sr2;
                                            es_po = po2; } } ->
             List.for_all2 (pattern env ri) [ml1;mr1;pr1;sl1;sr1;po1]
               [pat_memenv ml2; pat_memenv mr2; pat_form pr2; pat_stmt sl2; pat_stmt sr2; pat_form po2]

          | Sym_Form_Eager_F, [pr1;sl1;xpl1;xpr1;sr1;po1],
            Axiom_Form { f_node = FeagerF { eg_pr = pr2;
                                            eg_sl = sl2;
                                            eg_fl = xpl2;
                                            eg_fr = xpr2;
                                            eg_sr = sr2;
                                            eg_po = po2; } } ->
             List.for_all2 (pattern env ri) [pr1;sl1;xpl1;xpr1;sr1;po1]
               [pat_form pr2; pat_stmt sl2; pat_xpath xpl2; pat_xpath xpr2; pat_stmt sr2; pat_form po2]

          | Sym_Form_Pr, [m1;xp1;args1;event1],
            Axiom_Form { f_node = Fpr { pr_mem   = m2;
                                        pr_fun   = xp2;
                                        pr_args  = args2;
                                        pr_event = event2; } } ->
             List.for_all2 (pattern env ri) [m1;xp1;args1;event1]
               [pat_memory m2; pat_xpath xp2; pat_form args2; pat_form event2]

          | Sym_Stmt_Seq, s1, Axiom_Stmt { s_node = s2 }
               when 0 = List.compare_lengths s1 s2 ->
             List.for_all2 (pattern env ri) s1 (List.map pat_instr s2)

          | Sym_Instr_Assign, [lv1;e1],
            Axiom_Instr { i_node = Sasgn (lv2,e2) }
            | Sym_Instr_Sample, [lv1;e1],
              Axiom_Instr { i_node = Srnd (lv2,e2) } ->
             List.for_all2 (pattern env ri) [lv1;e1]
               [pat_lvalue lv2; pat_form (form_of_expr e2)]

          | Sym_Instr_Call, xp1::args1,
            Axiom_Instr { i_node = Scall (None,xp2,args2) } ->
             List.for_all2 (pattern env ri) (xp1::args1)
               ((pat_xpath xp2)::
                  (List.map (fun x -> pat_form (form_of_expr x)) args2))

          | Sym_Instr_Call_Lv, lv1::xp1::args1,
            Axiom_Instr { i_node = Scall (Some lv2,xp2,args2) } ->
             List.for_all2 (pattern env ri) (lv1::xp1::args1)
               ((pat_lvalue lv2)::(pat_xpath xp2)::
                  (List.map (fun x -> pat_form (form_of_expr x)) args2))

          | Sym_Instr_If, [cond1;st1;sf1],
            Axiom_Instr { i_node = Sif (cond2,st2,sf2) } ->
             List.for_all2 (pattern env ri) [cond1;st1;sf1]
               [pat_form (form_of_expr cond2); pat_stmt st2; pat_stmt sf2]

          | Sym_Instr_While, [cond1;s1],
            Axiom_Instr { i_node = Swhile (cond2,s2) } ->
             List.for_all2 (pattern env ri) [cond1;s1]
               [pat_form (form_of_expr cond2); pat_stmt s2]

          | Sym_Instr_Assert, [cond1],
            Axiom_Instr { i_node = Sassert cond2 } ->
             pattern env ri cond1 (pat_form (form_of_expr cond2))

          | Sym_Xpath, [mp1;p1],
            Axiom_Xpath { x_top = mp2; x_sub = p2 } ->
             pattern env ri p1 (pat_op p2 [] None)
             && pattern env ri mp1 (pat_mpath mp2)

          | Sym_Mpath, [m1], Axiom_Mpath _ ->
             pattern env ri m1 p2

          | Sym_Mpath, [mtop1], Axiom_Mpath_top _ ->
             pattern env ri mtop1 p2

          | Sym_Mpath, mtop1::margs1,
            Axiom_Mpath { m_top = mtop2; m_args = margs2 } ->
             let (margs11,margs12), (margs21,margs22) = suffix2 margs1 margs2 in
             let mtop1 = p_mpath mtop1 margs11 in
             let mtop2 = if margs21 = [] then pat_mpath_top mtop2
                         else pat_mpath (EcPath.mpath mtop2 margs21) in
             List.for_all2 (pattern env ri) (mtop1::margs12)
               (mtop2::(List.map pat_mpath margs22))

          | Sym_Mpath, _, _ -> false

          | Sym_Quant (q1,pb1), [p1],
            Axiom_Form { f_node = Fquant (q2,b2,f1) } when q1 = q2 ->
             if not (List.for_all2 (pbinding env) pb1
                             (List.map (snd_map ogty_of_gty) b2))
             then false
             else pattern env ri p1 (pat_form f1)

          | _ -> false

        end
      | _, _ -> false
    in
    if not eq then let _ = restore_environment env in eq
    else let _ = env.env_restore_unienv := env_restore_unienv in eq

end


(* -------------------------------------------------------------------------- *)
let h_red_strat hyps s rp _ p a =
  let op = match PReduction.h_red_pattern_opt hyps rp s p with
    | Some p' -> if p = p' then None else Some (p', a)
    | None -> None in
  match op with
  | Some _ -> op
  | None ->
  match PReduction.h_red_axiom_opt hyps rp s a with
  | Some { p_node = Pat_Axiom a } -> Some (p, a)
  | Some p' -> begin
      match p'.p_ogty with
      | OGTty _ -> begin
          (* try  *)
          let _ =
            Some (p, axiom_form (Translate.form_of_pattern (EcEnv.LDecl.toenv hyps) p'))
          in None
          (* with Translate.Invalid_Type _ -> None *)
        end
      | OGTmem _ -> begin
          (* try *)
            let _ =
              Some (p, Axiom_Memory (Translate.memory_of_pattern p'))
            in None
          (* with Translate.Invalid_Type _ -> None *)
        end
      | OGTmodty _ -> begin
          (* try *)
          let _ =
            Some (p, Axiom_Mpath (Translate.mpath_of_pattern (EcEnv.LDecl.toenv hyps) p'))
          in None
          (* with Translate.Invalid_Type _ -> None *)
        end
      | _ -> None
    end
  | _ -> None


(* -------------------------------------------------------------------------- *)
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

(* --------------------------------------------------------------------- *)
let restr_bds_check (env : environment) (p : pattern) (restr : pbindings) =
  let mr = Sid.of_list (List.map fst restr) in
  let m = Mid.set_diff (FV.pattern0 env.env_hyps p) mr in
  Mid.for_all (fun x _ ->
      if LDecl.has_id x env.env_hyps then true
      else if is_some (EcEnv.Mod.by_mpath_opt (mpath (`Local x) [])
                         (LDecl.toenv env.env_hyps))
      then true
      else
        let _ =
          if env.env_verbose then
            Format.fprintf env.env_fmt
              "[W] Binding restrictions prevents using : %s\n"
              (EcIdent.tostring x) in
        false) m


(* add_match can raise the exception : CannotUnify *)
let nadd_match (e : nengine) (name : meta_name) (p : pattern)
      (orb : pbindings option) : nengine =
  let env = e.ne_env in
  let env = saturate env in
  let subst = psubst_of_menv env.env_match in
  let p = Psubst.p_subst subst p in
  if odfl true (omap (fun r -> restr_bds_check env p r) orb)
  then
    let me_matches =
      match Mid.find_opt name e.ne_env.env_match.me_matches with
      | None ->
         if env.env_verbose then
           Format.fprintf e.ne_env.env_fmt "[W] adding %a <- %a\n"
             (EcPrinting.pp_pattern e.ne_env.env_ppe)
             (meta_var name None OGTany)
             (EcPrinting.pp_pattern e.ne_env.env_ppe) p;
         Mid.add name p e.ne_env.env_match.me_matches
      | Some p' ->
         (* raise CannotUnify *)
         if EQ.pattern e.ne_env e.ne_env.env_red_info_same_meta p p'
         then e.ne_env.env_match.me_matches
         else
         (if env.env_verbose then
            Format.fprintf e.ne_env.env_fmt "[W] cannot unify (%a) and (%a)\n"
              (EcPrinting.pp_pattern e.ne_env.env_ppe) p
              (EcPrinting.pp_pattern e.ne_env.env_ppe) p';
          raise CannotUnify)
    in
    { e with ne_env = { env with env_match = { env.env_match with me_matches; }; }; }
  else
    (if env.env_verbose then
       Format.fprintf e.ne_env.env_fmt
         "[W] cannot add because of binding restrictions : %a\n"
         (EcPrinting.pp_pattern env.env_ppe) p;
     raise CannotUnify)

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
  { e with e_head = f; e_pattern = mk_pattern (Pat_Sub p) OGTany;
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
 *   Pat_Fun_Symbol (Sym_Mpath, (Pat_Axiom (Axiom_Mpath_top m.m_top))
 *                              ::(List.map mpath_to_pattern m.m_args))
 *
 * let rec pat_of_mpath (m : mpath) =
 *   let args = List.map pat_of_mpath m.m_args in
 *   let m = Pat_Axiom (Axiom_Mpath_top m.m_top) in
 *   Pat_Fun_Symbol (Sym_Mpath, m::args)
 *
 * let rec pat_of_xpath (x : xpath) =
 *   Pat_Fun_Symbol (Sym_Xpath, [Pat_Axiom (Axiom_Op (x.x_sub,[])); pat_of_mpath x.x_top]) *)

let rewrite_term e f =
  let env   = saturate e.e_env in
  let subst = psubst_of_menv env.env_match in
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
let rec abstract_opt
          (other_args : Sid.t)
          (e : engine)
          (ep : pattern option)
          ((arg,parg) : Name.t * pattern) :
          pattern option =
  match ep with
  | None -> None
  | Some p ->
     let eq_pat' env p pp =
       match p.p_node, pp.p_node with
       | Pat_Meta_Name (_,n,_), _
            when Mid.mem n other_args -> false
       | _, Pat_Meta_Name (_,n,_)
            when Mid.mem n other_args -> false
       | _,_ ->
          let _ = if e.e_env.env_verbose then
                    Format.fprintf e.e_env.env_fmt
                      "[W] === try abstract %a in %a\n"
                      (EcPrinting.pp_pattern e.e_env.env_ppe) pp
                      (EcPrinting.pp_pattern e.e_env.env_ppe) p in
          EQ.pattern env env.env_red_info_match p pp
     in
     let aux env p a =
       let rec f env p =
         if eq_pat' env p a then
           match p.p_ogty, a.p_ogty with
           | OGTty (Some ty), _ | _, OGTty (Some ty)->
              pat_form (f_local arg ty)
           | _ -> meta_var arg None p.p_ogty
         else p_map (f env) p in
       let p' = f env p in
       if EQ.pattern env env.env_red_info_match p p' then None else Some p'
     in
     let env   = saturate e.e_env in
     let subst = psubst_of_menv env.env_match in
     let p     = Psubst.p_subst subst p in
     let parg  = Psubst.p_subst subst parg in
     aux e.e_env p parg


let try_reduce (e : engine) : engine =
  let i_red_match, i_red_same_meta =
    e.e_env.env_red_info_match, e.e_env.env_red_info_same_meta in
  let e_env = saturate e.e_env in
  let e = { e with e_env } in
  let subst = psubst_of_menv e_env.env_match in
  let o = try h_red_strat e.e_env.env_hyps subst i_red_match i_red_same_meta
                e.e_pattern e.e_head
          with Translate.Invalid_Type _ ->
                if e.e_env.env_verbose then
                  Format.fprintf e.e_env.env_fmt
                    "[W] Axiom has been reduced to pattern without being able to convert\n";
                None in
  match o with
  | None -> e
  | Some (p,a) ->
     let l = match e.e_continuation with
       | Zor (_,l,_) -> List.map (fun e -> e.e_pattern,e.e_head) (e::l)
       | _ -> [e.e_pattern,e.e_head] in
     if   List.mem (p,a) l
     then
       (if e.e_env.env_verbose then
          Format.fprintf e.e_env.env_fmt
            "[W] something was found but not reduced.\n";
        e)
     else
       (if e.e_env.env_verbose then
          Format.fprintf e.e_env.env_fmt "[W] something is reduced : (%a,%a).\n"
            (EcPrinting.pp_pattern e.e_env.env_ppe) p
            (EcPrinting.pp_pat_axiom e.e_env.env_ppe) a;
        (* let p = match p.p_ogty with
         *   | OGTty (Some _) -> mk_pattern p.p_node (OGTty None)
         *   | _ -> p in *)
        let e_or = { e with e_pattern = p; e_head = a } in
        match e.e_continuation with
        | Zor (cont,(_::_ as l),nomatch_cont) ->
           { e with e_continuation = Zor (cont,e_or::l,nomatch_cont) }
        | _ -> { e with e_continuation = Zor (e.e_continuation,[e_or],e_next e)})

(* ---------------------------------------------------------------------- *)
let rec process (e : engine) : nengine =
  (if e.e_env.env_verbose then
     let ppe = e.e_env.env_ppe in
     Format.fprintf e.e_env.env_fmt "[W]?? (%i left) : %a =? %a\n"
       (match e.e_continuation with
        | Zand (_,l,_) -> List.length l
        | _ -> 0)
       (* (if e.e_env.env_red_info_match.EcReduction.delta_p
        *       (match e.e_pattern with
        *        | Pat_Fun_Symbol
        *          (Sym_Form_App _,
        *           (Pat_Axiom (Axiom_Form { f_node = Fop (op,_)}))::_) -> op
        *        | _ -> EcPath.psymbol "foobar")
        *  then "with" else "without") *)
       (* (if e.e_env.env_red_info_same_meta.EcReduction.delta_p
        *       (match e.e_head with
        *        | Axiom_Form { f_node = Fapp ({ f_node = Fop (op,_)}, _)} -> op
        *        | _ -> EcPath.psymbol "foobar")
        *  then "with" else "without") *)
       (EcPrinting.pp_pattern ppe) e.e_pattern
       (EcPrinting.pp_pat_axiom ppe) e.e_head);
  if   not (EQ.ogty e.e_env e.e_pattern.p_ogty (pat_axiom e.e_head).p_ogty)
  then
    ((if e.e_env.env_verbose then
       let ppe = e.e_env.env_ppe in
       Format.fprintf e.e_env.env_fmt "[W] wrong type %a <> %a\n"
         (EcPrinting.pp_ogty ppe) e.e_pattern.p_ogty
         (EcPrinting.pp_ogty ppe) (pat_axiom e.e_head).p_ogty);
       next NoMatch e)
  else
  match e.e_pattern.p_node, e.e_head with
  | Pat_Anything, _ -> next Match e

  | Pat_Meta_Name (_,n1,_), (Axiom_Form { f_node = Flocal n2 }
                             | Axiom_Local (n2,_))
       when EQ.name n1 n2 -> next Match e

  | Pat_Meta_Name (p,name,ob), _ ->
     let env_meta_restr_binds =
       odfl e.e_env.env_meta_restr_binds
         (omap (fun b -> Mid.add name b e.e_env.env_meta_restr_binds) ob) in
     let e_env = { e.e_env with env_meta_restr_binds; } in
     let e = { e with e_env } in
     let e = try_reduce e in
     let _ = if e.e_env.env_verbose then
       Format.fprintf e.e_env.env_fmt "[W] rule : meta variable\n" in
     process { e with
         e_pattern = p; e_env;
         e_continuation = Znamed(pat_axiom e.e_head,name,ob,e.e_continuation);
       }

  | Pat_Sub p, _ ->
     let le = sub_engines e p in
     let _ = if e.e_env.env_verbose then
       Format.fprintf e.e_env.env_fmt "[W] rule : sub\n" in
     let e_continuation = match e.e_continuation with
       | Zor (c1, l, c2) -> Zor (c1, le @ l, c2)
       | _ -> Zor (e.e_continuation,le,e_next e) in
     process { e with e_pattern = p; e_continuation; }

  | Pat_Or [], _ -> next NoMatch e

  | Pat_Or (p::pl), _ ->
     let _ = if e.e_env.env_verbose then
       Format.fprintf e.e_env.env_fmt "[W] rule : or\n" in
     let f p = { e with
                 e_pattern = p;
                 e_env = { e.e_env with
                           env_restore_unienv =
                             ref !(e.e_env.env_restore_unienv); }; } in
     let e_continuation = match e.e_continuation with
       | Zor (c1, l, c2) -> Zor (c1, (List.map f pl) @ l, c2)
       | _ -> Zor (e.e_continuation,List.map f pl,e_next e) in
     process { e with e_pattern = p; e_continuation; }

  | Pat_Red_Strat (e_pattern,f),_ ->
     let _ = if e.e_env.env_verbose then
       Format.fprintf e.e_env.env_fmt "[W] rule : reduction strategy\n" in
     let env_red_info_match, env_red_info_same_meta =
       f e.e_env.env_red_info_match e.e_env.env_red_info_same_meta in
     let e_env = { e.e_env with env_red_info_match; env_red_info_same_meta } in
     process { e with e_pattern; e_env }

  | Pat_Axiom o1, o2
       when EQ.axiom e.e_env e.e_env.env_red_info_match o1 o2 ->
     let _ = if e.e_env.env_verbose then
       Format.fprintf e.e_env.env_fmt "[W] rule : same axiom\n" in
     next Match e

  | Pat_Axiom _, _ ->
     let _ = if e.e_env.env_verbose then
       Format.fprintf e.e_env.env_fmt "[W] rule : different axiom\n" in
     let e = try_reduce e in
     next NoMatch e

  | Pat_Fun_Symbol (Sym_Form_If, p1::p2::p3::[]),
    Axiom_Form { f_node = Fif (f1,f2,f3) } ->
     let _ = if e.e_env.env_verbose then
       Format.fprintf e.e_env.env_fmt "[W] rule : form : if\n" in
     let zand = [(Axiom_Form f2,p2);(Axiom_Form f3,p3)] in
     let e = try_reduce e in
     let e =
       { e with
         e_head = Axiom_Form f1;
         e_pattern = p1;
         e_continuation = Zand ([],zand,e.e_continuation);
       }
     in process e

  | Pat_Fun_Symbol (Sym_Form_App (_, MaybeHO), pop :: pargs), _ ->
     let _ = if e.e_env.env_verbose then
       Format.fprintf e.e_env.env_fmt "[W] rule : form : application : test both without and with higher order\n" in
     let e_pattern = pat_fun_symbol (Sym_Form_App (None, HO)) (pop::pargs) in
     let e_or = { e with e_pattern; } in
     let e_pattern = pat_fun_symbol (Sym_Form_App (None, NoHO)) (pop::pargs) in
     let e_continuation = match e.e_continuation with
       | Zor (c1,l,c2) -> Zor (c1,e_or::l,c2)
       | c -> Zor (c, [e_or], e_next e) in
     process { e with e_pattern; e_continuation; }

  | Pat_Fun_Symbol (Sym_Form_App (_, NoHO), pop :: pargs),
    Axiom_Form { f_node = Fapp (fop, fargs) } ->
     let _ = if e.e_env.env_verbose then
       Format.fprintf e.e_env.env_fmt "[W] rule : form : application : without higher order \n" in
     let e = try_reduce e in
     (* let _ = Format.fprintf e.e_env.env_fmt "[W] ?? application matched.\n" in *)
     let (fargs1,fargs2),(pargs1,pargs2) = suffix2 fargs pargs in
     if fargs2 = [] && pargs2 = [] then assert false;
     let zand = List.map2 (fun x y -> Axiom_Form x, y) fargs2 pargs2 in
     (* let _ = Format.fprintf e.e_env.env_fmt "[W] op = %a\n[W]arg length = %i\n"
      *           (EcPrinting.pp_pattern e.e_env.env_ppe) (pat_form fop)
      *           (List.length fargs1) in *)
     let fop' = f_ty_app (EcEnv.LDecl.toenv e.e_env.env_hyps) fop fargs1 in
     let pop = p_app pop pargs1 None in
     let e_head, e_pattern, zand = Axiom_Form fop', pop, List.rev zand in
     let e_continuation = Zand ([e_head,e_pattern],zand,e.e_continuation) in
     process { e with e_pattern; e_head; e_continuation; }

  | Pat_Fun_Symbol (Sym_Form_App (_, HO),
                    { p_node = Pat_Meta_Name({ p_node = Pat_Anything },name,ob)}
                    ::pargs), axiom ->
     begin
       let _ = if e.e_env.env_verbose then
                 Format.fprintf e.e_env.env_fmt
                   "[W] rule : form : application : with higher order \n" in
       (if e.e_env.env_verbose then
          Format.fprintf e.e_env.env_fmt "[W] higher order : %a\n"
            (EcPrinting.pp_pat_axiom e.e_env.env_ppe) axiom);
       let e = try_reduce e in
       (* higher order *)
       let env = saturate e.e_env in
       let add_ident i x =
         EcIdent.create (String.concat "$" ["s";string_of_int i]), x in
       let args = List.mapi add_ident pargs in
       let env_meta_restr_binds =
         odfl env.env_meta_restr_binds
           (omap (fun b -> Mid.add name b env.env_meta_restr_binds) ob) in
       let e = { e with e_env = { env with env_meta_restr_binds } } in
       let abstract m e p arg =
         let _ = if e.e_env.env_verbose then
                   Format.fprintf e.e_env.env_fmt
                     "[W] try to abstract (%a) in : %a\n"
                     (EcPrinting.pp_pattern e.e_env.env_ppe) (snd arg)
                     (EcPrinting.pp_pattern e.e_env.env_ppe) p in
         let op = abstract_opt m e (Some p) arg in odfl p op in
       let pat =
         (* FIXME : add strategies to adapt the order of the arguments *)
         List.fold_left (abstract (Sid.of_list (List.map fst args)) e)
           (pat_axiom axiom) args in
       let f (name,p) = (name,p.p_ogty) in
       let args = List.map f args in
       (* let pat = omap (p_quant Llambda args) pat in *)
       let pat = p_quant Llambda args pat in
       (* let (pat, e) = match rewrite_pattern_opt e pat with
        *   | Some pat,e -> pat, e
        *   | None, e -> pat, e in *)
       let m,e =
         try let e = add_match e name pat ob in Match, e
         with CannotUnify -> NoMatch, e
       in next m e
     end

  | Pat_Fun_Symbol (Sym_Form_Tuple, lp),
    Axiom_Form { f_node = Ftuple lf }
       when 0 = List.compare_lengths lp lf -> begin
       let _ = if e.e_env.env_verbose then
                 Format.fprintf e.e_env.env_fmt
                   "[W] rule : form : tuple \n" in
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

  | Pat_Fun_Symbol (Sym_Form_Tuple, lp),
    Axiom_Lvalue (LvTuple lv) when 0 = List.compare_lengths lp lv ->
       let _ = if e.e_env.env_verbose then
                 Format.fprintf e.e_env.env_fmt
                   "[W] rule : lvalue : tuple \n" in
     let zand = List.map2 (fun x y -> Axiom_Lvalue (LvVar x), y) lv lp in
     let e_continuation = Zand ([], zand, e.e_continuation) in
     next Match { e with e_continuation }

  | Pat_Fun_Symbol (Sym_Form_Proj (i,ty), [e_pattern]),
    Axiom_Form ({ f_node = Fproj (f1,j) } as f)
       when i = j  && EQ.ty e.e_env ty f.f_ty ->
       let _ = if e.e_env.env_verbose then
                 Format.fprintf e.e_env.env_fmt
                   "[W] rule : form : proj \n" in
     process { e with e_pattern; e_head = Axiom_Form f1 }

  | Pat_Fun_Symbol (Sym_Form_Match ty, p::pl),
    Axiom_Form ({ f_node = Fmatch (fmatch,fl,_) } as f)
       when 0 = List.compare_lengths pl fl && EQ.ty e.e_env ty f.f_ty ->
       let _ = if e.e_env.env_verbose then
                 Format.fprintf e.e_env.env_fmt
                   "[W] rule : form : match \n" in
     let e = try_reduce e in
     let zand = List.map2 (fun x y -> Axiom_Form x, y) fl pl in
     process { e with
         e_pattern = p;
         e_head = Axiom_Form fmatch;
         e_continuation = Zand ([],zand,e.e_continuation);
       }

  | Pat_Fun_Symbol (Sym_Form_Quant (q1,bs1), [p]),
    Axiom_Form { f_node = Fquant (q2,bs2,f2) }
       when q1 = q2 && 0 >= List.compare_lengths bs1 bs2 -> begin
       let _ = if e.e_env.env_verbose then
                 Format.fprintf e.e_env.env_fmt
                   "[W] rule : form : quantif \n" in
      let e = try_reduce e in
      let (pbs1,_), (fbs1,fbs2) = List.prefix2 bs1 bs2 in
      if not (List.for_all2 (EQ.gty e.e_env) (List.map snd pbs1) (List.map snd fbs1))
      then  next NoMatch e
      else
        (* let f s (id,gty) =
         *   if List.exists (fun (id2,_) -> id_equal id id2) e.e_env.env_current_binds
         *   then match gty with
         *        | GTty ty -> Fsubst.f_bind_rename s id (EcIdent.fresh id) ty
         *        | GTmem _ -> Fsubst.f_bind_mem s id (EcIdent.fresh id)
         *        | GTmodty _ -> s
         *   else s in *)
        let fs = Fsubst.f_subst_id in
        (* let fs = List.fold_left f fs bs2 in *)
        let f s (id1,gty1) (id2,_) = Psubst.p_bind_gty s id1 id2 gty1 in
        let e_env = saturate e.e_env in
        let subst = Psubst.p_subst_id in
        let s     = List.fold_left2 f subst pbs1 fbs1 in
        let e_pattern = Psubst.p_subst s p in
        process { e with
            e_pattern; e_env; e_head = Axiom_Form (f_quant q2 fbs2 (Fsubst.f_subst fs f2));
          }
    end

  | Pat_Fun_Symbol (Sym_Form_Pvar ty, p1::p2::[]),
    Axiom_Form ({ f_node = Fpvar (_,m) } as f) when EQ.ty e.e_env f.f_ty ty ->
       let _ = if e.e_env.env_verbose then
                 Format.fprintf e.e_env.env_fmt
                   "[W] rule : form : pvar \n" in
     let e = try_reduce e in
     process { e with
         e_pattern = p2;
         e_head = Axiom_Memory m;
         e_continuation = Zand ([],[Axiom_Form f,p1],e.e_continuation);
       }

  | Pat_Fun_Symbol (Sym_Form_Prog_var k, [p]),
    Axiom_Form { f_node = Fpvar (x2,_) } when k = x2.pv_kind ->
       let _ = if e.e_env.env_verbose then
                 Format.fprintf e.e_env.env_fmt
                   "[W] rule : form : prog_var \n" in
     let e = try_reduce e in
     process { e with e_pattern = p; e_head = Axiom_Xpath x2.pv_name; }

  | Pat_Fun_Symbol (Sym_Form_Glob, p1::p2::[]),
    Axiom_Form { f_node = Fglob (x,m) } ->
       let _ = if e.e_env.env_verbose then
                 Format.fprintf e.e_env.env_fmt
                   "[W] rule : form : glob \n" in
     let e = try_reduce e in
     let zand = [Axiom_Mpath x,p1] in
     process { e with
         e_pattern = p2;
         e_head = Axiom_Memory m;
         e_continuation = Zand ([],zand,e.e_continuation);
       }

  | Pat_Fun_Symbol (Sym_Form_Hoare_F, [ppre;px;ppost]),
    Axiom_Form { f_node = FhoareF hF } ->
       let _ = if e.e_env.env_verbose then
                 Format.fprintf e.e_env.env_fmt
                   "[W] rule : form : hoareF \n" in
     let fpre,fx,fpost = hF.hf_pr,hF.hf_f,hF.hf_po in
     let zand = [Axiom_Form fpre,ppre;
                 Axiom_Form fpost,ppost] in
     process { e with
         e_pattern = px;
         e_head = Axiom_Xpath fx;
         e_continuation = Zand ([],zand,e.e_continuation);
       }

  | Pat_Fun_Symbol (Sym_Form_Hoare_S, [pmem;ppre;ps;ppost]),
    Axiom_Form { f_node = FhoareS hs } ->
       let _ = if e.e_env.env_verbose then
                 Format.fprintf e.e_env.env_fmt
                   "[W] rule : form : hoareS \n" in
     let fmem,fpre,fs,fpost = hs.hs_m,hs.hs_pr,hs.hs_s,hs.hs_po in
     let zand = [Axiom_Form fpre,ppre;
                 Axiom_Form fpost,ppost;
                 Axiom_Stmt fs,ps] in
     process { e with
         e_pattern = pmem;
         e_head = Axiom_MemEnv fmem;
         e_continuation = Zand ([],zand,e.e_continuation); }

  | Pat_Fun_Symbol (Sym_Form_bd_Hoare_F, [ppre;pf;ppost;pcmp;pbd]),
    Axiom_Form { f_node = FbdHoareF bhf } ->
       let _ = if e.e_env.env_verbose then
                 Format.fprintf e.e_env.env_fmt
                   "[W] rule : form : bd hoareF \n" in
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

  | Pat_Fun_Symbol (Sym_Form_bd_Hoare_S, [pmem;ppre;ps;ppost;pcmp;pbd]),
    Axiom_Form { f_node = FbdHoareS bhs } ->
       let _ = if e.e_env.env_verbose then
                 Format.fprintf e.e_env.env_fmt
                   "[W] rule : form : bd hoareS \n" in
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

  | Pat_Fun_Symbol (Sym_Form_Equiv_F, [ppre;pf1;pf2;ppost]),
    Axiom_Form { f_node = FequivF ef } ->
       let _ = if e.e_env.env_verbose then
                 Format.fprintf e.e_env.env_fmt
                   "[W] rule : form : equivF \n" in
     let fpre,ff1,ff2,fpost =
       ef.ef_pr,ef.ef_fl,ef.ef_fr,ef.ef_po in
     let zand = [Axiom_Xpath ff2,pf2;
                 Axiom_Form fpre,ppre;
                 Axiom_Form fpost,ppost] in
     process { e with
         e_pattern = pf1;
         e_head = Axiom_Xpath ff1;
         e_continuation = Zand ([],zand,e.e_continuation); }

  | Pat_Fun_Symbol (Sym_Form_Equiv_S, [pmem1;pmem2;ppre;ps1;ps2;ppost]),
    Axiom_Form { f_node = FequivS es } ->
       let _ = if e.e_env.env_verbose then
                 Format.fprintf e.e_env.env_fmt
                   "[W] rule : form : equivS \n" in
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

  | Pat_Fun_Symbol (Sym_Form_Eager_F, [ppre;ps1;pf1;pf2;ps2;ppost]),
    Axiom_Form { f_node = FeagerF eg } ->
       let _ = if e.e_env.env_verbose then
                 Format.fprintf e.e_env.env_fmt
                   "[W] rule : form : eagerF \n" in
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

  | Pat_Fun_Symbol (Sym_Form_Pr, [pmem;pf;pargs;pevent]),
    Axiom_Form { f_node = Fpr pr } ->
       let _ = if e.e_env.env_verbose then
                 Format.fprintf e.e_env.env_fmt
                   "[W] rule : form : pr \n" in
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

  | Pat_Fun_Symbol (Sym_Mpath, [p]), Axiom_Mpath_top _ ->
       let _ = if e.e_env.env_verbose then
                 Format.fprintf e.e_env.env_fmt
                   "[W] rule : mpath_top \n" in
     process { e with e_pattern = p }

  | Pat_Fun_Symbol (Sym_Mpath, p::rest), Axiom_Mpath m ->
       let _ = if e.e_env.env_verbose then
                 Format.fprintf e.e_env.env_fmt
                   "[W] rule : mpath \n" in
     let e = try_reduce e in
     let (pargs1,pargs2),(margs1,margs2) = suffix2 rest m.m_args in
     let zand = List.map2 (fun x y -> (Axiom_Mpath x),y) margs2 pargs2 in
     let e_continuation = match zand with
       | [] -> e.e_continuation
       | _  -> Zand ([],zand,e.e_continuation) in
     let m = match margs1 with
       | [] ->
          Axiom_Mpath_top m.m_top
       | _  -> if margs2 = [] then Axiom_Mpath m
               else Axiom_Mpath (mpath m.m_top margs1)
     in
     let p = match pargs1 with
       | [] -> p
       | _ -> pat_fun_symbol Sym_Mpath (p::pargs1)
     in
     process { e with e_pattern = p; e_head = m; e_continuation; }

  | Pat_Fun_Symbol (Sym_Instr_Assign, [plv;prv]),
    Axiom_Instr { i_node = Sasgn (flv,fe) }
    | Pat_Fun_Symbol (Sym_Instr_Sample, [plv;prv]),
      Axiom_Instr { i_node = Srnd (flv,fe) } ->
       let _ = if e.e_env.env_verbose then
                 Format.fprintf e.e_env.env_fmt
                   "[W] rule : instr : assign / rnd \n" in
     let e = try_reduce e in
     let frv = form_of_expr fe in
     let zand = [Axiom_Form frv,prv] in
     process { e with
         e_pattern = plv;
         e_head = Axiom_Lvalue flv;
         e_continuation = Zand ([],zand,e.e_continuation); }

  | Pat_Fun_Symbol (Sym_Instr_Call, pf::pargs),
    Axiom_Instr { i_node = Scall (None,ff,fargs) }
       when 0 = List.compare_lengths pargs fargs ->
       let _ = if e.e_env.env_verbose then
                 Format.fprintf e.e_env.env_fmt
                   "[W] rule : instr : call no lv \n" in
     let e = try_reduce e in
     let fmap x y = (Axiom_Form (form_of_expr x),y) in
     let zand = List.map2 fmap fargs pargs in
     process { e with
         e_pattern = pf;
         e_head = Axiom_Xpath ff;
         e_continuation = Zand ([],zand,e.e_continuation); }

  | Pat_Fun_Symbol (Sym_Instr_Call_Lv, plv::pf::pargs),
    Axiom_Instr { i_node = Scall (Some flv,ff,fargs) } ->
       let _ = if e.e_env.env_verbose then
                 Format.fprintf e.e_env.env_fmt
                   "[W] rule : instr : call with lv \n" in
     let e = try_reduce e in
     let fmap x y = (Axiom_Form (form_of_expr x),y) in
     let zand = List.map2 fmap fargs pargs in
     let zand = (Axiom_Lvalue flv,plv)::zand in
     process { e with
         e_pattern = pf;
         e_head = Axiom_Xpath ff;
         e_continuation = Zand ([],zand,e.e_continuation); }

  | Pat_Fun_Symbol (Sym_Instr_If, [pe;ptrue;pfalse]),
    Axiom_Instr { i_node = Sif (fe,strue,sfalse) } ->
       let _ = if e.e_env.env_verbose then
                 Format.fprintf e.e_env.env_fmt
                   "[W] rule : instr : if \n" in
     let e = try_reduce e in
     let zand = [Axiom_Stmt strue,ptrue;
                 Axiom_Stmt sfalse,pfalse] in
     process { e with
         e_pattern = pe;
         e_head = Axiom_Form (form_of_expr fe);
         e_continuation = Zand ([],zand,e.e_continuation); }

  | Pat_Fun_Symbol (Sym_Instr_While, [pe;pbody]),
    Axiom_Instr { i_node = Swhile (fe,fbody) } ->
       let _ = if e.e_env.env_verbose then
                 Format.fprintf e.e_env.env_fmt
                   "[W] rule : instr : while \n" in
     let e = try_reduce e in
     let zand = [Axiom_Stmt fbody,pbody] in
     process { e with
         e_pattern = pe;
         e_head = Axiom_Form (form_of_expr fe);
         e_continuation = Zand ([],zand,e.e_continuation); }

  | Pat_Fun_Symbol (Sym_Instr_Assert, [pe]),
    Axiom_Instr { i_node = Sassert fe } ->
       let _ = if e.e_env.env_verbose then
                 Format.fprintf e.e_env.env_fmt
                   "[W] rule : instr : assert \n" in
     let e = try_reduce e in
     process { e with e_pattern = pe; e_head = Axiom_Form (form_of_expr fe); }

  | Pat_Fun_Symbol (Sym_Stmt_Seq,[]), Axiom_Stmt { s_node = [] } ->
       let _ = if e.e_env.env_verbose then
                 Format.fprintf e.e_env.env_fmt
                   "[W] rule : stmt : empty \n" in
     next Match e

  | Pat_Fun_Symbol (Sym_Stmt_Seq,pi::pl), Axiom_Stmt { s_node = fi::fl } ->
       let _ = if e.e_env.env_verbose then
                 Format.fprintf e.e_env.env_fmt
                   "[W] rule : stmt : to instr \n" in
     let e = try_reduce e in
     let pl = pat_fun_symbol Sym_Stmt_Seq pl in
     let zand = [Axiom_Stmt (stmt fl),pl] in
     process { e with
         e_pattern = pi;
         e_head = Axiom_Instr fi;
         e_continuation = Zand ([],zand,e.e_continuation);
       }

  | Pat_Fun_Symbol (Sym_Xpath, [pm;pf]), Axiom_Xpath x ->
       let _ = if e.e_env.env_verbose then
                 Format.fprintf e.e_env.env_fmt
                   "[W] rule : xpath \n" in
     let e = try_reduce e in
     let zand = [Axiom_Mpath x.x_top,pm] in
     process { e with
         e_pattern = pf;
         e_head = Axiom_Op (x.x_sub,[]);
         e_continuation = Zand ([],zand,e.e_continuation); }

  | Pat_Fun_Symbol _, _ ->
       let _ = if e.e_env.env_verbose then
                 Format.fprintf e.e_env.env_fmt
                   "[W] rule : default \n" in
     next NoMatch_NoRed e

and next (m : ismatch) (e : engine) : nengine =
  (if e.e_env.env_verbose then
     let ppe = e.e_env.env_ppe in
     Format.fprintf e.e_env.env_fmt "[W] %s (%i left) %a %s %a\n"
       (if m = Match then "++" else "--")
       (match e.e_continuation with
        | Zand (_,l,_) -> List.length l
        | _ -> 0)
       (EcPrinting.pp_pattern ppe) e.e_pattern
       (if m = Match then "=" else "<>")
       (EcPrinting.pp_pat_axiom ppe) e.e_head);
  let e = if m = NoMatch then try_reduce e else e in
  next_n m (e_next e)

and next_n (m : ismatch) (e : nengine) : nengine =
  match m,e.ne_continuation with
  | (NoMatch | NoMatch_NoRed), ZTop -> raise NoMatches

  | Match, ZTop   -> e

  | (NoMatch | NoMatch_NoRed), Znamed (_f, _name, _ob, ne_continuation) ->
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

  | (NoMatch | NoMatch_NoRed), Zand (_,_,ne_continuation) ->
     let _ = restore_environment e.ne_env in
     next_n NoMatch { e with ne_continuation; }

  | Match, Zand (_before,[],ne_continuation) ->
     next_n Match { e with ne_continuation }

  | Match, Zand (before,(f,p)::after,z) ->
     let ne_env = saturate e.ne_env in
     let e      = { e with ne_env } in
     process (n_engine f p
                { e with ne_continuation = Zand ((f,p)::before,after,z)})

  | Match, Zor (ne_continuation, _, _) -> next_n Match { e with ne_continuation }

  | (NoMatch | NoMatch_NoRed), Zor (_, [], ne) ->
     let _ = restore_environment e.ne_env in
     next_n NoMatch ne

  | (NoMatch | NoMatch_NoRed), Zor (_, e'::engines, ne) ->
     let _ = restore_environment e'.e_env in
     process { e' with e_continuation = Zor (e'.e_continuation, engines, ne); }

  | Match, Zbinds (ne_continuation, env_current_binds) ->
     next_n Match { e with ne_continuation; ne_env = { e.ne_env with env_current_binds } }

  | (NoMatch | NoMatch_NoRed), Zbinds (ne_continuation, env_current_binds) ->
     let _ = restore_environment e.ne_env in
     let ne_env = { e.ne_env with env_current_binds } in
     next_n NoMatch { e with ne_continuation; ne_env; }

and sub_engines (e : engine) (p : pattern) : engine list =
  match e.e_head with
  | Axiom_Memory _   -> []
  | Axiom_MemEnv _   -> []
  | Axiom_Prog_Var _ -> []
  | Axiom_Op _       -> []
  | Axiom_Mpath_top _   -> []
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
           [Axiom_Mpath_top mp.m_top;Axiom_Memory mem]
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
  let axiom_expr e  = Axiom_Form (form_of_expr e) in
  let axiom_mpath m = Axiom_Mpath m in

  let rec aux a     = match a with
    | Axiom_Local (id,ty) ->
       if Mid.mem id sbd
       then Some (meta_var id None (OGTty (Some ty)))
       else Some (pat_axiom a)
    | Axiom_Form f -> begin
        let fty = f.f_ty in
        match f.f_node with
        | Fquant(quant,binds,f)
             when Mid.set_disjoint (Sid.of_list (List.map fst binds)) sbd ->
           omap (fun fi -> p_f_quant quant binds fi) (aux_f f)
        | Fquant _ -> assert false
        | Fif(f1,f2,f3) ->
           omap (function [p1;p2;p3] -> p_if p1 p2 p3 | _ -> assert false)
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
               omap (function [p1;p2] -> p_let lp p1 p2 | _ -> assert false)
                 (omap_list pat_form aux_f [f1;f2])
          end
        | Fint _ -> None
        | Flocal id ->
           if Mid.mem id sbd
           then Some (meta_var id None (OGTty (Some fty)))
           else if mem_ty_univar fty
           then Some (pat_local id fty)
           else None
        | Fpvar(x,m) ->
           omap (function [p1;p2] -> p_pvar p1 fty p2 | _ -> assert false)
             (omap_list pat_axiom aux [Axiom_Prog_Var x;Axiom_Memory m])
        | Fglob(mp, m) ->
           omap (function [p1;p2] -> p_glob p1 p2 | _ -> assert false)
             (omap_list pat_axiom aux [Axiom_Mpath mp;Axiom_Memory m])
        | Fop (_,_) ->
           Some (pat_form f)
        | Fapp ({ f_node = Flocal id },args) when Mid.mem id sbd ->
           let p =
             p_app (meta_var id None (OGTty (Some fty)))
               (List.map (fun x ->  odfl (pat_form x) (aux_f x)) args) (Some fty) in
           Some p
        | Fapp(fop,args) ->
           if mem_ty_univar fty
           then
             let pargs = List.map (fun arg -> odfl (pat_form arg) (aux_f arg)) args in
             let pop = odfl (pat_form fop) (aux_f fop) in
             Some (p_app pop pargs (Some fty))
           else
             omap (function
                 | pop::pargs -> p_app pop pargs (Some fty)
                 | _ -> assert false)
               (omap_list pat_form aux_f (fop::args))
        | Ftuple args ->
           omap (fun l -> p_tuple l) (omap_list pat_form aux_f args)
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
        Some (meta_var m None (OGTmem None))

    | Axiom_MemEnv m when Mid.mem (fst m) sbd ->
        Some (meta_var (fst m) None (OGTmem (Some (snd m))))

    | Axiom_Prog_Var pv ->
       omap (fun x -> p_prog_var x pv.pv_kind) (aux (Axiom_Xpath pv.pv_name))

    | Axiom_Op _ -> None
    | Axiom_Mpath_top mt -> begin
        match mt with
        | `Local id when Mid.mem id sbd ->
           let ogty = match Mid.find_opt id sbd with
             | Some gty -> gty
             | None -> assert false in
           Some (meta_var id None ogty)
        | _ -> None
      end
    | Axiom_Mpath m ->
       omap (function mt::margs -> p_mpath mt margs | _ -> assert false)
         (omap_list pat_axiom aux ((Axiom_Mpath_top m.m_top)::(List.map axiom_mpath m.m_args)))
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
           Some (meta_var id None OGTstmt)
        | Sabstract _ -> None
      end
    | Axiom_Stmt s ->
       omap (fun l -> p_stmt l) (omap_list pat_instr aux_i s.s_node)
    | Axiom_Lvalue lv -> begin
        match lv with
        | LvVar (pv,ty) -> begin
            match aux (Axiom_Prog_Var pv) with
            | Some { p_node = Pat_Axiom (Axiom_Prog_Var pv) } ->
               Some (pat_lvalue (LvVar (pv,ty)))
            | Some p -> Some (mk_pattern p.p_node (OGTty (Some ty)))
            | None   -> None
          end
        | LvTuple l ->
           let default (pv,ty) = pat_lvalue (LvVar (pv,ty)) in
           let aux (pv,ty) =
             omap (fun p -> mk_pattern p.p_node (OGTty (Some ty)))
               (aux (Axiom_Prog_Var pv)) in
           omap (fun l -> p_tuple l) (omap_list default aux l)
        | LvMap _ -> (* FIXME *) assert false
      end
    | Axiom_Xpath xp ->
       omap (fun mp -> p_xpath mp (pat_op xp.x_sub [] None))
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
  let rec aux current_bds meta_bds p = match p.p_node with
  | Pat_Anything -> meta_bds
  | Pat_Meta_Name (p,n,_) ->
     aux current_bds (add_meta_bindings n current_bds meta_bds) p
  | Pat_Sub p -> aux current_bds meta_bds p
  | Pat_Or lp -> List.fold_left (aux current_bds) meta_bds lp
  | Pat_Red_Strat (p,_) -> aux current_bds meta_bds p
  | Pat_Axiom (Axiom_Form { f_node = Fquant (_,b,f) } ) ->
     let b = List.map (snd_map ogty_of_gty) b in
     aux (current_bds @ b) meta_bds (pat_form f)
  | Pat_Axiom _ -> meta_bds
  | Pat_Fun_Symbol (Sym_Form_Quant (_,b),[p]) ->
     let b = List.map (snd_map ogty_of_gty) b in
     aux (current_bds @ b) meta_bds p
  | Pat_Fun_Symbol (_,lp) -> List.fold_left (aux current_bds) meta_bds lp
  in aux [] Mid.empty p

let rec write_meta_bindings (m : pbindings Mid.t) (p : pattern) =
  let aux = write_meta_bindings m in
  match p.p_node with
  | Pat_Anything          -> p
  | Pat_Meta_Name (p,n,_) -> pat_meta (aux p) n (Mid.find_opt n m)
  | Pat_Sub p             -> mk_pattern (Pat_Sub (aux p)) OGTany
  | Pat_Or lp             -> mk_pattern (Pat_Or (List.map aux lp)) OGTany
  | Pat_Red_Strat (p,f)   -> let p = aux p in
                             mk_pattern (Pat_Red_Strat (p,f)) p.p_ogty
  | Pat_Axiom _           -> p
  | Pat_Fun_Symbol (s,lp) -> pat_fun_symbol s (List.map aux lp)

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
      (red_info_match : EcReduction.reduction_info)
      (red_info_same_meta : EcReduction.reduction_info)
    : environment = {
    env_hyps               = h;
    env_red_info_match     = red_info_match;
    env_red_info_same_meta = red_info_same_meta;
    env_restore_unienv     = ref None;
    env_current_binds      = [] ;
    env_meta_restr_binds   = Mid.empty;
    env_ppe                = odfl (EcPrinting.PPEnv.ofenv (LDecl.toenv h)) ppe;
    env_fmt                = odfl Format.std_formatter fmt;
    env_match              = odfl {
                                 me_matches   = Mid.empty;
                                 me_unienv    = EcUnify.UniEnv.create None;
                                 me_meta_vars = Mid.empty;
                               } mtch;
    env_verbose            = verbose;
  }

let mkengine (a : axiom) (p : pattern) (env : environment) : engine =
  { e_head = a;
    e_pattern = p;
    e_env = env;
    e_continuation = ZTop;
  }

let mk_engine ?ppe ?fmt ?mtch f e_pattern env_hyps
      env_red_info_match env_red_info_same_meta =
  let e = {
      e_pattern;
      e_head         = axiom_form f;
      e_continuation = ZTop;
      e_env          = {
          env_hyps;
          env_red_info_match;
          env_red_info_same_meta;
          env_restore_unienv   = ref None;
          env_current_binds    = [];
          env_meta_restr_binds = Mid.empty;
          env_ppe              = odfl (EcPrinting.PPEnv.ofenv (LDecl.toenv env_hyps)) ppe;
          env_fmt              = odfl Format.std_formatter fmt;
          env_match            = odfl {
                                     me_matches   = Mid.empty;
                                     me_meta_vars = Mid.empty;
                                     me_unienv    = EcUnify.UniEnv.create None;
                                   } mtch;
          env_verbose          = verbose;
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


(* -------------------------------------------------------------------- *)
let menv_is_full (e : match_env) h =
  let matches   = e.me_matches in
  let meta_vars = e.me_meta_vars in

  let f n _ = match Mid.find_opt n matches with
    | None   -> false
    | Some p -> let fv = FV.pattern0 h p in
                Mid.for_all (fun n _ -> not (Mid.mem n meta_vars)) fv in

  Mid.for_all f meta_vars

(* -------------------------------------------------------------------- *)
let fsubst_of_menv (me : match_env) (env : env) =
  let ps = psubst_of_menv me in
  let fs = Fsubst.f_subst_init ~sty:ps.ps_sty () in
  let bind_pattern id p s =
    try Fsubst.f_bind_local s id (Translate.form_of_pattern env p)
    with Translate.Invalid_Type _ ->
    try Fsubst.f_bind_mem s id (Translate.memory_of_pattern p)
    with Translate.Invalid_Type _ ->
    try Fsubst.f_bind_mod s id (Translate.mpath_of_pattern env p)
    with Translate.Invalid_Type _ -> s in

  Mid.fold bind_pattern me.me_matches fs

(* -------------------------------------------------------------------- *)
let menv_get_form x env menv =
  obind
    (fun p ->
      try  Some (Translate.form_of_pattern env p)
      with Translate.Invalid_Type _ -> None)
    (Mid.find_opt x menv.me_matches)

(* -------------------------------------------------------------------- *)
let menv_has_form x menv =
  match Mid.find_opt x menv.me_meta_vars with
  | Some (OGTty _) -> true | _ -> false

(* -------------------------------------------------------------------- *)
let menv_has_memory x menv =
  match Mid.find_opt x menv.me_meta_vars with
  | Some (OGTmem _) -> true | _ -> false
