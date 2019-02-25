(* ------------------------------------------------------------------------------ *)
open EcUtils
open EcFol
open EcTypes
open EcPath
open EcMemory
open EcIdent
open EcModules

module Name  = EcIdent
module MName = Mid

(* -------------------------------------------------------------------------- *)
type meta_name = Name.t

type ogty =
  | OGTty    of ty option
  | OGTmodty of (module_type * mod_restr) option
  | OGTmem   of EcMemory.memtype option
  | OGTpv
  | OGTxpath
  | OGTinstr
  | OGTstmt
  | OGTlv
  | OGThcmp
  | OGTpath
  | OGTany


type pbinding  = ident * ogty
type pbindings = pbinding list

type reduction_strategy =
  EcReduction.reduction_info -> EcReduction.reduction_info ->
  EcReduction.reduction_info * EcReduction.reduction_info

type axiom =
  | Axiom_Form      of form
  | Axiom_Memory    of memory
  | Axiom_MemEnv    of memenv
  | Axiom_Prog_Var  of prog_var
  | Axiom_Op        of path * ty list
  | Axiom_Mpath_top of mpath_top
  | Axiom_Mpath     of mpath
  | Axiom_Instr     of instr
  | Axiom_Stmt      of stmt
  | Axiom_Lvalue    of lvalue
  | Axiom_Xpath     of xpath
  | Axiom_Hoarecmp  of hoarecmp
  | Axiom_Local     of ident * ty

type is_higher_order =
  | MaybeHO
  | NoHO
  | HO

type fun_symbol =
  (* from type form *)
  | Sym_Form_If
  | Sym_Form_App          of ty option * is_higher_order
  | Sym_Form_Tuple
  | Sym_Form_Proj         of int * ty
  | Sym_Form_Match        of ty
  | Sym_Form_Let          of lpattern
  | Sym_Form_Pvar         of ty
  | Sym_Form_Prog_var     of pvar_kind
  | Sym_Form_Glob
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
  | Sym_Quant             of quantif * pbindings


(* invariant of pattern : if the form is not Pat_Axiom, then there is
     at least one of the first set of patterns *)
type p_node =
  | Pat_Anything
  | Pat_Meta_Name  of pattern * meta_name * pbindings option
  | Pat_Sub        of pattern
  | Pat_Or         of pattern list
  | Pat_Red_Strat  of pattern * reduction_strategy

  | Pat_Fun_Symbol of fun_symbol * pattern list
  | Pat_Axiom      of axiom

and pattern = {
    p_node : p_node;
    p_ogty : ogty;
  }


(* This is for EcTransMatching ---------------------------------------- *)
let default_start_name = "$start"
let default_end_name = "$end"
let default_name = "$default"


(* -------------------------------------------------------------------------- *)
let olist_all (f : 'a -> 'b option) (l : 'a list) : 'b list option =
  let rec aux accb = function
    | []     -> Some (List.rev accb)
    | a :: r -> match f a with
                | None -> None
                | Some b -> aux (b::accb) r
  in aux [] l


(* -------------------------------------------------------------------------- *)

type map = pattern MName.t


(* -------------------------------------------------------------------------- *)
let my_mem = EcIdent.create "my_mem"
let form_of_expr e = form_of_expr my_mem e

let ogty_of_gty (gty : gty) = match gty with
  | GTty ty -> OGTty (Some ty)
  | GTmem t -> OGTmem (Some t)
  | GTmodty (t,r) -> OGTmodty (Some (t,r))

let gty_of_ogty (ogty : ogty) = match ogty with
  | OGTty (Some ty) -> Some (GTty ty)
  | OGTmem (Some t) -> Some (GTmem t)
  | OGTmodty (Some (t,r)) -> Some (GTmodty (t,r))
  | _ -> None



(* -------------------------------------------------------------------------- *)

let rec p_equal = (=)

let ogty_equal o1 o2 = match o1, o2 with
  | OGTany, _ | _, OGTany -> true
  | OGTty (Some t1), OGTty (Some t2) -> ty_equal t1 t2
  | OGTty _, OGTty _ -> true
  | OGTmem (Some mt1), OGTmem (Some mt2) -> EcMemory.mt_equal mt1 mt2
  | OGTmem _, OGTmem _ -> true
  | OGTmodty (Some (mt1,mr1)), OGTmodty (Some (mt2,mr2)) ->
     EcModules.mty_equal mt1 mt2 && EcModules.mr_equal mr1 mr2
  | OGTmodty _, OGTmodty _ -> true
  | _ -> o1 = o2

let op_equal (p1 : pattern) (op : form) =
  match p1, op with
  | { p_node = Pat_Axiom (Axiom_Form { f_node = Fop (op1, lty1) ; f_ty = ty1 }) },
    { f_node = Fop (op2, lty2); f_ty = ty2 } ->
     ty_equal ty1 ty2 && EcPath.p_equal op1 op2
                      && List.for_all2 ty_equal lty1 lty2
  | { p_node = Pat_Axiom (Axiom_Op (op1, lty1)); p_ogty = OGTty (Some ty1) },
    { f_node = Fop (op2, lty2); f_ty = ty2 } ->
     ty_equal ty1 ty2 && EcPath.p_equal op1 op2
                      && List.for_all2 ty_equal lty1 lty2
  | { p_node = Pat_Axiom (Axiom_Op (op1, lty1)); p_ogty = OGTty None },
    { f_node = Fop (op2, lty2) } ->
     EcPath.p_equal op1 op2 && List.for_all2 ty_equal lty1 lty2
  | _ -> false

let axiom_equal (a1 : axiom) (a2 : axiom) =
  match a1, a2 with
  | Axiom_Form f1, Axiom_Form f2 -> f_equal f1 f2
  | Axiom_Memory m1, Axiom_Memory m2 -> EcMemory.mem_equal m1 m2
  | Axiom_MemEnv m1, Axiom_MemEnv m2 -> EcMemory.me_equal m1 m2
  | Axiom_Prog_Var pv1, Axiom_Prog_Var pv2 -> pv_equal pv1 pv2
  | Axiom_Op (op1,lty1), Axiom_Op (op2,lty2) ->
     EcPath.p_equal op1 op2 && List.for_all2 ty_equal lty1 lty2
  | Axiom_Mpath_top mt1, Axiom_Mpath_top mt2 ->
     EcPath.mt_equal mt1 mt2
  | Axiom_Mpath m1, Axiom_Mpath m2 -> EcPath.m_equal m1 m2
  | Axiom_Instr i1, Axiom_Instr i2 -> i_equal i1 i2
  | Axiom_Stmt s1, Axiom_Stmt s2 -> s_equal s1 s2
  | Axiom_Lvalue lv1, Axiom_Lvalue lv2 -> lv_equal lv1 lv2
  | Axiom_Xpath xp1, Axiom_Xpath xp2 -> x_equal xp1 xp2
  | Axiom_Hoarecmp cmp1, Axiom_Hoarecmp cmp2 -> cmp1 = cmp2
  | Axiom_Local (id1,ty1), Axiom_Local (id2,ty2) ->
     id_equal id1 id2 && ty_equal ty1 ty2
  | _ -> false

let symbol_equal (s1 : fun_symbol) (s2 : fun_symbol) = match s1, s2 with
  | Sym_Form_App (Some ty1, i1), Sym_Form_App (Some ty2, i2) ->
     i1 = i2 && ty_equal ty1 ty2
  | Sym_Form_Proj (i1,ty1), Sym_Form_Proj (i2,ty2) ->
     i1 = i2 && ty_equal ty1 ty2
  | Sym_Form_Match ty1, Sym_Form_Match ty2 ->
     ty_equal ty1 ty2
  | Sym_Form_Let lp1, Sym_Form_Let lp2 ->
     lp_equal lp1 lp2
  | Sym_Form_Pvar ty1, Sym_Form_Pvar ty2 ->
     ty_equal ty1 ty2
  | Sym_Form_Prog_var k1, Sym_Form_Prog_var k2 -> k1 = k2
  | Sym_Quant (q1,pb1), Sym_Quant (q2,pb2) ->
     q1 = q2
    && List.for_all2 (fun (i1,t1) (i2,t2) ->
           id_equal i1 i2 && ogty_equal t1 t2) pb1 pb2
  | _ -> s1 = s2

(* -------------------------------------------------------------------------- *)

let mk_pattern (p_node : p_node) (p_ogty : ogty) = { p_node; p_ogty; }

let pat_form f      = mk_pattern (Pat_Axiom (Axiom_Form f))        (OGTty (Some f.f_ty))
let pat_memory m    = mk_pattern (Pat_Axiom (Axiom_Memory m))      (OGTmem None)
let pat_memenv m    = mk_pattern (Pat_Axiom (Axiom_MemEnv m))      (OGTmem (Some (snd m)))
let pat_mpath m     = mk_pattern (Pat_Axiom (Axiom_Mpath m))       (OGTmodty None)
let pat_mpath_top m = mk_pattern (Pat_Axiom (Axiom_Mpath_top m))   (OGTmodty None)
let pat_xpath x     = mk_pattern (Pat_Axiom (Axiom_Xpath x))       OGTxpath
let pat_op op lty o = mk_pattern (Pat_Axiom (Axiom_Op (op,lty)))   (OGTty o)
let pat_lvalue lv   = mk_pattern (Pat_Axiom (Axiom_Lvalue lv))     OGTlv
let pat_instr i     = mk_pattern (Pat_Axiom (Axiom_Instr i))       OGTinstr
let pat_stmt s      = mk_pattern (Pat_Axiom (Axiom_Stmt s))        OGTstmt
let pat_local id ty = mk_pattern (Pat_Axiom (Axiom_Local (id,ty))) (OGTty (Some ty))
let pat_cmp cmp     = mk_pattern (Pat_Axiom (Axiom_Hoarecmp cmp))  OGThcmp
let pat_pv pv       = mk_pattern (Pat_Axiom (Axiom_Prog_Var pv))   OGTpv

let axiom_form f    = Axiom_Form f
let axiom_mpath m   = Axiom_Mpath m

let pat_meta p name ob =
  mk_pattern (Pat_Meta_Name (p,name,ob)) p.p_ogty

let meta_var name ob ogty = pat_meta (mk_pattern Pat_Anything ogty) name ob


let pat_axiom x = match x with
  | Axiom_Form      f      -> pat_form f
  | Axiom_Memory    m      -> pat_memory m
  | Axiom_MemEnv    m      -> pat_memenv m
  | Axiom_Prog_Var  pv     -> pat_pv pv
  | Axiom_Op        (op,l) -> pat_op op l None
  | Axiom_Mpath_top mt     -> pat_mpath_top mt
  | Axiom_Mpath     m      -> pat_mpath m
  | Axiom_Instr     i      -> pat_instr i
  | Axiom_Stmt      s      -> pat_stmt s
  | Axiom_Lvalue    lv     -> pat_lvalue lv
  | Axiom_Xpath     xp     -> pat_xpath xp
  | Axiom_Hoarecmp  cmp    -> pat_cmp cmp
  | Axiom_Local     (x,t)  -> pat_local x t

let get_tys (b : bindings) =
  let rec aux acc = function
    | [] -> Some (List.rev acc)
    | (_, GTty ty)::rest -> aux (ty::acc) rest
    | _ -> None in
  aux [] b

let pat_fun_symbol s lp = match s, lp with
  (* from type form *)
  | Sym_Form_If, [_;p2;p3]   -> begin
     match p2.p_ogty, p3.p_ogty with
     | OGTty (Some t), _
       | _, (OGTty (Some t)) -> mk_pattern (Pat_Fun_Symbol(s,lp)) (OGTty (Some t))
     | _                     -> mk_pattern (Pat_Fun_Symbol(s,lp)) (OGTty None)
    end
  | Sym_Form_App (t,_), _::_ -> mk_pattern (Pat_Fun_Symbol(s,lp)) (OGTty t)
  | Sym_Form_Tuple, _        -> mk_pattern (Pat_Fun_Symbol(s,lp)) (OGTty None)
  | Sym_Form_Proj _, [_]     -> mk_pattern (Pat_Fun_Symbol(s,lp)) (OGTty None)
  | Sym_Form_Match t, _::_   -> mk_pattern (Pat_Fun_Symbol(s,lp)) (OGTty (Some t))
  | Sym_Form_Let _, [_;p2]   -> mk_pattern (Pat_Fun_Symbol(s,lp)) p2.p_ogty
  | Sym_Form_Pvar t, [_;_]   -> mk_pattern (Pat_Fun_Symbol(s,lp)) (OGTty (Some t))
  | Sym_Form_Prog_var _, [_] -> mk_pattern (Pat_Fun_Symbol(s,lp)) OGTpv
  | Sym_Form_Glob, [_;_]     -> mk_pattern (Pat_Fun_Symbol(s,lp)) (OGTty None)
  | Sym_Form_Hoare_F, _
    | Sym_Form_Hoare_S, _
    | Sym_Form_bd_Hoare_F, _
    | Sym_Form_bd_Hoare_S, _
    | Sym_Form_Equiv_F, _
    | Sym_Form_Equiv_S, _
    | Sym_Form_Eager_F, _    -> mk_pattern (Pat_Fun_Symbol(s,lp)) (OGTty (Some tbool))
  | Sym_Form_Pr, _           -> mk_pattern (Pat_Fun_Symbol(s,lp)) (OGTty (Some treal))
  (* form type stmt*)
  | Sym_Stmt_Seq, _          -> mk_pattern (Pat_Fun_Symbol(s,lp)) OGTstmt
  (* from type instr *)
  | (Sym_Instr_Assign
    | Sym_Instr_Sample
    | Sym_Instr_Call
    | Sym_Instr_Call_Lv
    | Sym_Instr_If
    | Sym_Instr_While
    | Sym_Instr_Assert), _  -> mk_pattern (Pat_Fun_Symbol(s,lp)) OGTinstr
  (* from type xpath *)
  | Sym_Xpath, _            -> mk_pattern (Pat_Fun_Symbol(s,lp)) OGTxpath
  (* from type mpath *)
  | Sym_Mpath, _            -> mk_pattern (Pat_Fun_Symbol(s,lp)) (OGTmodty None)
  (* generalized *)
  | Sym_Quant (Lforall, _), _ -> mk_pattern (Pat_Fun_Symbol(s,lp)) (OGTty (Some tbool))
  | Sym_Quant (Lexists, _), _ -> mk_pattern (Pat_Fun_Symbol(s,lp)) (OGTty (Some tbool))
  | Sym_Quant _, _          -> mk_pattern (Pat_Fun_Symbol(s,lp)) OGTany
  | _ -> assert false


(* -------------------------------------------------------------------------- *)

let p_destr_app p = match p.p_node with
  | Pat_Axiom(Axiom_Form f) ->
     let p,lp = EcFol.destr_app f in
     pat_form p, List.map pat_form lp
  | Pat_Fun_Symbol(Sym_Form_App _,p::lp) -> p,lp
  | _ -> p, []


(* -------------------------------------------------------------------------- *)

let pat_add_fv map (n : ident) =
  match Mid.find_opt n map with
  | None -> Mid.add n 1 map
  | Some i -> Mid.add n (i+1) map

let pat_fv_union m1 m2 =
  Mid.fold_left (fun m n _ -> pat_add_fv m n) m1 m2

let pat_fv p =
  let rec aux (map : int Mid.t) p = match p.p_node with
    | Pat_Anything -> map
    | Pat_Meta_Name (p,n,_) ->
       aux (pat_add_fv map n) p
    | Pat_Sub p -> aux map p
    | Pat_Or lp -> List.fold_left aux map lp
    | Pat_Red_Strat (p,_) -> aux map p
    | Pat_Fun_Symbol (Sym_Quant (_,b),lp) ->
       let map = List.fold_left aux Mid.empty lp in
       Mid.filter (fun x _ -> List.exists (fun (y,_) -> id_equal x y) b) map
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
          List.fold_left aux (aux map (pat_mpath_top mp.m_top))
            (List.map pat_mpath mp.m_args)
       | Axiom_Mpath_top (`Local id) -> pat_add_fv map id
       | Axiom_Mpath_top _ -> map
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

(* -------------------------------------------------------------------------- *)
let p_mpath (p : pattern) (args : pattern list) =
  if args = [] then p
  else
  (* let rec oget_mpaths acc = function
   *   | [] -> Some (List.rev acc)
   *   | ({ p_node = Pat_Axiom(Axiom_Mpath m)})::r ->
   *      oget_mpaths (m::acc) r
   *   | ({ p_node = Pat_Axiom(Axiom_Mpath_top mt)})::r ->
   *      oget_mpaths ((mpath mt [])::acc) r
   *   | _ -> None in
   * let oget_mpaths l = oget_mpaths [] l in
   * let oget_mpath =
   *   match p.p_node with
   *   | Pat_Axiom(Axiom_Mpath_top mt) -> Some (mpath mt [])
   *   | Pat_Axiom(Axiom_Mpath m)   -> Some m
   *   | _ -> None in
   * match oget_mpath, oget_mpaths args with
   * | Some m, Some args ->
   *    pat_mpath (mpath m.m_top (m.m_args @ args))
   * | _,_ -> *)
     mk_pattern (Pat_Fun_Symbol(Sym_Mpath,p::args)) (OGTmodty None)

let p_xpath (p : pattern) (f : pattern) =
  (* match p.p_node, f.p_node with
   * | Pat_Axiom(Axiom_Mpath m), Pat_Axiom(Axiom_Op (op,[])) ->
   *    pat_xpath (EcPath.xpath m op)
   * | _ ->  *)
     pat_fun_symbol Sym_Xpath [p;f]

let p_prog_var (p : pattern) (k : pvar_kind) =
  (* match p.p_node with
   * | Pat_Axiom (Axiom_Xpath x) -> pat_pv (pv x k)
   * | _ -> *)
     pat_fun_symbol (Sym_Form_Prog_var k) [p]

let p_lvalue_var (p : pattern) (ty : ty) =
  match p.p_node with
  | Pat_Axiom(Axiom_Prog_Var pv) -> pat_lvalue (LvVar(pv,ty))
  | p ->
     mk_pattern p (OGTty (Some ty))

let p_lvalue_tuple (p : pattern list) =
  (* let rec oget_pv acc = function
   *   | [] -> Some (List.rev acc)
   *   | a :: r ->
   *      match a with
   *      | { p_node = Pat_Axiom (Axiom_Prog_Var pv); p_ogty = OGTty (Some ty) }
   *        | { p_node = Pat_Axiom (Axiom_Lvalue (LvVar (pv,ty))) ; p_ogty = OGTlv } ->
   *         oget_pv ((pv,ty)::acc) r
   *      | _ -> None
   * in
   * match oget_pv [] p with
   * | Some l -> pat_lvalue (LvTuple l)
   * | None ->  *)
     mk_pattern (Pat_Fun_Symbol(Sym_Form_Tuple,p)) OGTlv

let p_pvar (pv : pattern) (ty : ty) (m : pattern) =
  (* match pv.p_node, m.p_node with
   * | Pat_Axiom (Axiom_Prog_Var pv),Pat_Axiom (Axiom_Memory m) ->
   *    pat_form (f_pvar pv ty m)
   * | _ -> *)
     pat_fun_symbol (Sym_Form_Pvar ty) [pv;m]

let p_glob (mp : pattern) (m : pattern) =
  (* match mp.p_node, m.p_node  with
   * | Pat_Axiom (Axiom_Mpath mp), Pat_Axiom (Axiom_Memory m) ->
   *    pat_form (f_glob mp m)
   * | _ -> *)
     pat_fun_symbol Sym_Form_Glob [mp;m]

let p_if (p1 : pattern) (p2 : pattern) (p3 : pattern) =
  pat_fun_symbol Sym_Form_If [p1;p2;p3]

let p_match (p : pattern) (ty : ty) (lp : pattern list) =
  (* match p.p_node,
   *       olist_all (function { p_node = Pat_Axiom(Axiom_Form f) } -> Some f
   *                         | _ -> None) lp with
   * | Pat_Axiom(Axiom_Form op), Some lf ->
   *    pat_form (mk_form (Fmatch (op,lf,ty)) ty)
   * | _ -> *)
     pat_fun_symbol (Sym_Form_Match ty) (p::lp)

let p_tuple (lp : pattern list) =
  (* match olist_all
   *         (function { p_node = Pat_Axiom (Axiom_Form f) } -> Some f
   *                 | _ -> None) lp with
   * | Some l -> pat_form (f_tuple l)
   * | None ->  *)
     pat_fun_symbol Sym_Form_Tuple lp

let p_proj (p1 : pattern) (i : int) (ty : ty) =
  match p1.p_node with
  | Pat_Fun_Symbol(Sym_Form_Tuple,lp) when 0 <= i && i < List.length lp ->
     List.nth lp i
  | _ -> pat_fun_symbol (Sym_Form_Proj (i,ty)) [p1]

let p_let (l : lpattern) (p1 : pattern) (p2 : pattern) =
  (* match p1.p_node, p2.p_node with
   * | Pat_Axiom (Axiom_Form f1), Pat_Axiom (Axiom_Form f2) ->
   *    pat_form (EcFol.f_let l f1 f2)
   * | _ ->  *)
     pat_fun_symbol (Sym_Form_Let l) [p1;p2]

let is_higher_order (p : pattern) = match p.p_node with
  | Pat_Meta_Name ({ p_node = Pat_Anything }, _, _) -> true
  | _ -> false

let is_form (p : pattern) = match p.p_node with
  | Pat_Axiom (Axiom_Form _) -> true
  | Pat_Axiom (Axiom_Local _) -> true
  | _ -> false

let form_of_pattern (p : pattern) = match p.p_ogty with
  | OGTany | OGTty _ -> begin
      match p.p_node with
      | Pat_Axiom (Axiom_Form f) -> f
      | Pat_Axiom (Axiom_Local (id,t)) -> f_local id t
      | _ -> raise Not_found
    end
  | _ -> raise Not_found

let p_app ?ho (p : pattern) (args : pattern list) (ty : ty option) =
  let p, args1 = p_destr_app p in
  match args1 @ args with
  | [] -> p
  | args ->
  match ho with
  | None ->
     if is_higher_order p then
       pat_fun_symbol (Sym_Form_App (ty,MaybeHO)) (p::args)
     else pat_fun_symbol (Sym_Form_App (ty,NoHO)) (p::args)
  | Some ho -> pat_fun_symbol (Sym_Form_App (ty,ho)) (p::args)

let p_quant q bs p =
  match bs with
  | [] -> p
  | _  -> pat_fun_symbol (Sym_Quant (q,bs)) [p]

let p_forall b p = p_quant Lforall b p

let p_exists b p = p_quant Lexists b p

let p_stmt (lp : pattern list) =
  (* match olist_all (function { p_node = Pat_Axiom (Axiom_Instr i) } -> Some i
   *                         | _ -> None) lp with
   * | Some l -> pat_stmt (stmt l)
   * | None ->  *)
     mk_pattern (Pat_Fun_Symbol(Sym_Stmt_Seq,lp)) OGTstmt

let p_var_form x ty =
  let t = OGTty (Some ty) in
  mk_pattern (Pat_Meta_Name (mk_pattern Pat_Anything t, x, None)) t

let p_assign (plv : pattern) (pe : pattern) =
  (* match plv.p_node, pe.p_node with
   * | Pat_Axiom (Axiom_Lvalue lv),Pat_Axiom (Axiom_Form f) -> begin
   *     match expr_of_form f with
   *     | None -> pat_fun_symbol Sym_Instr_Assign [plv;pe]
   *     | Some e -> pat_instr (i_asgn (lv,e))
   *   end
   * | _ -> *)
     pat_fun_symbol Sym_Instr_Assign [plv;pe]

let p_sample (plv : pattern) (pe : pattern) =
  (* match plv.p_node, pe.p_node with
   * | Pat_Axiom (Axiom_Lvalue lv), Pat_Axiom (Axiom_Form f) -> begin
   *     match expr_of_form f with
   *     | None -> pat_fun_symbol Sym_Instr_Sample [plv;pe]
   *     | Some e -> pat_instr (i_rnd (lv,e))
   *   end
   * | _ ->  *)
     pat_fun_symbol Sym_Instr_Sample [plv;pe]

let p_call (olv : pattern option) (f : pattern) (args : pattern list) =
  (* let get_expr = function
   *   | { p_node = Pat_Axiom(Axiom_Form f) } -> expr_of_form f
   *   | _ -> None in *)
  match olv, f.p_node with
  (* | None, Pat_Axiom (Axiom_Xpath proc) -> begin
   *     match olist_all get_expr args with
   *     | Some args -> pat_instr (i_call(None,proc,args))
   *     | None -> pat_fun_symbol Sym_Instr_Call (f::args)
   *   end
   * | Some({ p_node = Pat_Axiom (Axiom_Lvalue lv) } as olv),
   *   Pat_Axiom (Axiom_Xpath proc) ->
   *    begin
   *      match olist_all get_expr args with
   *      | Some args -> pat_instr (i_call(Some lv,proc,args))
   *      | None -> pat_fun_symbol Sym_Instr_Call_Lv (olv::f::args)
   *    end *)
  | None,_ ->
     pat_fun_symbol  Sym_Instr_Call (f::args)
  | Some lv,_ ->
     pat_fun_symbol Sym_Instr_Call_Lv (lv::f::args)

let p_instr_if (pcond : pattern) (ps1 : pattern) (ps2 : pattern) =
  (* match pcond.p_node, ps1.p_node, ps2.p_node with
   * | Pat_Axiom (Axiom_Form f), Pat_Axiom (Axiom_Stmt s1), Pat_Axiom (Axiom_Stmt s2) ->
   *    odfl (pat_fun_symbol Sym_Instr_If [pcond;ps1;ps2])
   *      (omap (fun cond -> pat_instr (i_if(cond,s1,s2))) (expr_of_form f))
   * | _ ->  *)
     pat_fun_symbol Sym_Instr_If [pcond;ps1;ps2]

let p_while (pcond : pattern) (ps : pattern) =
  (* match pcond.p_node, ps.p_node with
   * | Pat_Axiom (Axiom_Form f), Pat_Axiom (Axiom_Stmt s) ->
   *    odfl (pat_fun_symbol Sym_Instr_While [pcond;ps])
   *      (omap (fun cond -> pat_instr (i_while(cond,s)))
   *         (expr_of_form f))
   * | _ ->  *)
     pat_fun_symbol Sym_Instr_While [pcond;ps]

let p_assert (p : pattern) =
  (* match p.p_node with
   * | Pat_Axiom(Axiom_Form f) ->
   *    odfl (pat_fun_symbol Sym_Instr_Assert [p])
   *      (omap (fun e -> pat_instr (i_assert e)) (expr_of_form f))
   * | _ -> *)
     pat_fun_symbol Sym_Instr_Assert [p]


let p_hoareF (pr : pattern) (f : pattern) (po : pattern) =
  (* match pr.p_node, f.p_node, po.p_node with
   * | Pat_Axiom(Axiom_Form pr),
   *   Pat_Axiom(Axiom_Xpath f),
   *   Pat_Axiom(Axiom_Form po) ->
   *    pat_form (f_hoareF pr f po)
   * | _ -> *)
     pat_fun_symbol Sym_Form_Hoare_F [pr;f;po]

let p_hoareS (m : pattern) (pr : pattern) (s : pattern) (po : pattern) =
  (* match m.p_node, pr.p_node, s.p_node, po.p_node with
   * | Pat_Axiom(Axiom_MemEnv m),
   *   Pat_Axiom(Axiom_Form pr),
   *   Pat_Axiom(Axiom_Stmt s),
   *   Pat_Axiom(Axiom_Form po) ->
   *    pat_form (f_hoareS m pr s po)
   * | _ ->  *)
     pat_fun_symbol Sym_Form_Hoare_F [m;pr;s;po]

let p_bdHoareF (pr : pattern) (f : pattern) (po : pattern) (cmp : pattern)
      (bd : pattern) =
  (* match pr.p_node, f.p_node, po.p_node, cmp.p_node, bd.p_node with
   * | Pat_Axiom(Axiom_Form pr),
   *   Pat_Axiom(Axiom_Xpath f),
   *   Pat_Axiom(Axiom_Form po),
   *   Pat_Axiom(Axiom_Hoarecmp cmp),
   *   Pat_Axiom(Axiom_Form bd) ->
   *    pat_form(f_bdHoareF pr f po cmp bd)
   * | _ -> *)
     pat_fun_symbol Sym_Form_bd_Hoare_F [pr;f;po;cmp;bd]

let p_bdHoareS (m : pattern) (pr : pattern) (s : pattern) (po : pattern)
      (cmp : pattern) (bd : pattern) =
  (* match m.p_node, pr.p_node, s.p_node, po.p_node, cmp.p_node, bd.p_node with
   * | Pat_Axiom(Axiom_MemEnv m),
   *   Pat_Axiom(Axiom_Form pr),
   *   Pat_Axiom(Axiom_Stmt s),
   *   Pat_Axiom(Axiom_Form po),
   *   Pat_Axiom(Axiom_Hoarecmp cmp),
   *   Pat_Axiom(Axiom_Form bd) ->
   *    pat_form(f_bdHoareS m pr s po cmp bd)
   * | _ -> *)
     pat_fun_symbol Sym_Form_bd_Hoare_F [m;pr;s;po;cmp;bd]

let p_equivF (pr : pattern) (fl : pattern) (fr : pattern) (po : pattern) =
  (* match pr.p_node, fl.p_node, fr.p_node, po.p_node with
   * | Pat_Axiom(Axiom_Form pr),
   *   Pat_Axiom(Axiom_Xpath fl),
   *   Pat_Axiom(Axiom_Xpath fr),
   *   Pat_Axiom(Axiom_Form po) ->
   *    pat_form (f_equivF pr fl fr po)
   * | _ -> *)
     pat_fun_symbol Sym_Form_Equiv_F [pr;fl;fr;po]

let p_equivS (ml : pattern) (mr : pattern) (pr : pattern) (sl : pattern)
      (sr : pattern) (po : pattern) =
  (* match ml.p_node, mr.p_node, pr.p_node, sl.p_node, sr.p_node, po.p_node with
   * | Pat_Axiom(Axiom_MemEnv ml),
   *   Pat_Axiom(Axiom_MemEnv mr),
   *   Pat_Axiom(Axiom_Form pr),
   *   Pat_Axiom(Axiom_Stmt sl),
   *   Pat_Axiom(Axiom_Stmt sr),
   *   Pat_Axiom(Axiom_Form po) ->
   *    pat_form (f_equivS ml mr pr sl sr po)
   * | _ -> *)
     pat_fun_symbol Sym_Form_Equiv_F [ml;mr;pr;sl;sr;po]

let p_eagerF (pr : pattern) (sl : pattern) (fl : pattern)
      (fr : pattern) (sr : pattern) (po : pattern) =
  (* match pr.p_node, sl.p_node, fl.p_node, fr.p_node, sr.p_node, po.p_node with
   * | Pat_Axiom(Axiom_Form pr),
   *   Pat_Axiom(Axiom_Stmt sl),
   *   Pat_Axiom(Axiom_Xpath fl),
   *   Pat_Axiom(Axiom_Xpath fr),
   *   Pat_Axiom(Axiom_Stmt sr),
   *   Pat_Axiom(Axiom_Form po) ->
   *    pat_form (f_eagerF pr sl fl fr sr po)
   * | _ -> *)
     pat_fun_symbol Sym_Form_Eager_F [pr;sl;fl;fr;sr;po]

let p_pr (pm : pattern) (pf : pattern) (pargs : pattern) (pevent : pattern) =
  (* match pm.p_node, pf.p_node, pargs.p_node, pevent.p_node with
   * | Pat_Axiom(Axiom_Memory m),
   *   Pat_Axiom(Axiom_Xpath f),
   *   Pat_Axiom(Axiom_Form args),
   *   Pat_Axiom(Axiom_Form event) ->
   *    pat_form (f_pr m f args event)
   * | _ ->  *)
     pat_fun_symbol Sym_Form_Pr [pm;pf;pargs;pevent]

(* -------------------------------------------------------------------------- *)
let lv_ty (f_ty : ty -> ty) = function
  | LvVar (pv,ty) -> LvVar (pv,f_ty ty)
  | LvTuple l -> LvTuple (List.map (fun (x,ty)->(x,f_ty ty)) l)
  | LvMap ((op,lty),pv,e,ty) ->
     LvMap ((op,List.map f_ty lty),pv,e_map f_ty (fun x->x) e,f_ty ty)


let p_map (f : pattern -> pattern) (p : pattern) : pattern =
  match p.p_node with
  | Pat_Anything -> p
  | Pat_Meta_Name (p,n,ob) ->
     let p = f p in mk_pattern (Pat_Meta_Name (p,n,ob)) p.p_ogty
  | Pat_Sub p ->
     let p = f p in mk_pattern (Pat_Sub p) OGTany
  | Pat_Or lp ->
     let lp = List.map f lp in mk_pattern (Pat_Or lp) OGTany
  | Pat_Red_Strat (p, red) ->
     let p = f p in mk_pattern (Pat_Red_Strat (p, red)) p.p_ogty
  | Pat_Fun_Symbol (s, lp) ->
     let lp = List.map f lp in pat_fun_symbol s lp
  | Pat_Axiom axiom ->
     match axiom with
     | Axiom_Form fo -> begin
         match fo.f_node with
         | Fquant (q,b,f') ->
            let p' = f (pat_form f') in
            let p' = match p.p_node with
              | Pat_Axiom(Axiom_Form f'') ->
                 pat_form (EcFol.FSmart.f_quant (fo, (q,b,f')) (q, b, f''))
              | _ -> p_quant q (List.map (fun (id,t) -> id, ogty_of_gty t) b) p' in
            p'
         | Fif (f1,f2,f3) ->
            let p1 = f (pat_form f1) in
            let p2 = f (pat_form f2) in
            let p3 = f (pat_form f3) in
            let p  = match p1.p_node, p2.p_node, p3.p_node with
              | Pat_Axiom (Axiom_Form f1'),
                Pat_Axiom (Axiom_Form f2'),
                Pat_Axiom (Axiom_Form f3') ->
                 pat_form (EcFol.FSmart.f_if (fo, (f1,f2,f3)) (f1',f2',f3'))
              | _ -> p_if p1 p2 p3
            in p
         | Fmatch (f1,fargs,ty) ->
            let p1   = f (pat_form f1) in
            let args = List.map f (List.map pat_form fargs) in
            let oargs   =
              olist_all (function { p_node = Pat_Axiom (Axiom_Form f) } -> Some f
                                | _ -> None) args in
            let p = match p1.p_node, oargs with
              | Pat_Axiom(Axiom_Form f1'),Some fargs' ->
                 pat_form (EcFol.FSmart.f_match (fo,(f1,fargs,ty)) (f1',fargs',ty))
              | _ -> p_match p1 ty args in
            p
         | Flet (lp,f1,f2) ->
            let p1 = f (pat_form f1) in
            let p2 = f (pat_form f2) in
            let p  = match p1.p_node, p2.p_node with
              | Pat_Axiom (Axiom_Form f1'),Pat_Axiom (Axiom_Form f2') ->
                 pat_form (EcFol.FSmart.f_let (fo,(lp,f1,f2)) (lp,f1',f2'))
              | _ -> p_let lp p1 p2 in
            p
         | Fpvar (pv,m) ->
            let p1 = f (pat_pv pv) in
            let p2 = f (pat_memory m) in
            let p  = match p1.p_node, p2.p_node with
              | Pat_Axiom (Axiom_Prog_Var pv'), Pat_Axiom (Axiom_Memory m') ->
                 pat_form (EcFol.FSmart.f_pvar (fo,(pv,fo.f_ty,m)) (pv',fo.f_ty,m'))
              | _ -> p_pvar p1 fo.f_ty p2
            in p
         | Fglob (mp,m) ->
            let p1 = f (pat_mpath mp) in
            let p2 = f (pat_memory m) in
            let p  = match p1.p_node, p2.p_node with
              | Pat_Axiom (Axiom_Mpath mp'), Pat_Axiom (Axiom_Memory m') ->
                 pat_form (EcFol.FSmart.f_glob (fo,(mp,m)) (mp',m'))
              | _ -> p_glob p1 p2 in
            p
         | Fapp (fop,fargs) ->
            let pop   = f (pat_form fop) in
            let pargs = List.map f (List.map pat_form fargs) in
            let oargs    =
              olist_all (function { p_node = Pat_Axiom(Axiom_Form f) } -> Some f
                                | _ -> None) pargs in
            let p = match pop.p_node, oargs with
              | Pat_Axiom (Axiom_Form fop'), Some fargs' ->
                 pat_form (EcFol.FSmart.f_app (fo,(fop,fargs,fo.f_ty)) (fop',fargs',fo.f_ty))
              | _ -> p_app pop pargs (Some fo.f_ty) in
            p
         | Ftuple t ->
            let pt = List.map f (List.map pat_form t) in
            let ot    =
              olist_all (function { p_node = Pat_Axiom (Axiom_Form f) } -> Some f
                                | _ -> None) pt in
            let p = match ot with
              | Some t' -> pat_form (EcFol.FSmart.f_tuple (fo,t) t')
              | None    -> p_tuple pt in
            p
         | Fproj (f1,i) ->
            let p1 = f (pat_form f1) in
            let p = match p1.p_node with
              | Pat_Axiom(Axiom_Form f1') ->
                 pat_form (EcFol.FSmart.f_proj (fo,(f1,fo.f_ty)) (f1',fo.f_ty) i)
              | _ -> p_proj p1 i fo.f_ty in
            p
         | FhoareF h ->
            let pr = f (pat_form h.hf_pr) in
            let xp = f (pat_xpath h.hf_f) in
            let po = f (pat_form h.hf_po) in
            let p = match pr.p_node, xp.p_node, po.p_node with
              | Pat_Axiom(Axiom_Form hf_pr),
                Pat_Axiom(Axiom_Xpath hf_f),
                Pat_Axiom(Axiom_Form hf_po) ->
                 pat_form (EcFol.FSmart.f_hoareF (fo,h) { hf_pr ; hf_f ; hf_po })
              | _ -> p_hoareF pr xp po in
            p
         | FhoareS h ->
            let mem = f (pat_memenv h.hs_m) in
            let pr  = f (pat_form h.hs_pr) in
            let s   = f (pat_stmt h.hs_s) in
            let po  = f (pat_form h.hs_po) in
            let p = match mem.p_node, pr.p_node, s.p_node, po.p_node with
              | Pat_Axiom(Axiom_MemEnv hs_m),
                Pat_Axiom(Axiom_Form hs_pr),
                Pat_Axiom(Axiom_Stmt hs_s),
                Pat_Axiom(Axiom_Form hs_po) ->
                 pat_form (EcFol.FSmart.f_hoareS (fo,h) { hs_m ; hs_pr ; hs_s ; hs_po })
              | _ -> p_hoareS mem pr s po in
            p
         | FbdHoareF h ->
            let pr  = f (pat_form h.bhf_pr) in
            let xp  = f (pat_xpath h.bhf_f) in
            let po  = f (pat_form h.bhf_po) in
            let cmp = f (pat_cmp h.bhf_cmp) in
            let bd  = f (pat_form h.bhf_bd) in
            let p = match pr.p_node, xp.p_node, po.p_node, cmp.p_node, bd.p_node with
              | Pat_Axiom(Axiom_Form bhf_pr),
                Pat_Axiom(Axiom_Xpath bhf_f),
                Pat_Axiom(Axiom_Form bhf_po),
                Pat_Axiom(Axiom_Hoarecmp bhf_cmp),
                Pat_Axiom(Axiom_Form bhf_bd) ->
                 pat_form (EcFol.FSmart.f_bdHoareF (fo,h) { bhf_pr ; bhf_f ; bhf_po ; bhf_cmp ; bhf_bd })
              | _ -> p_bdHoareF pr xp po cmp bd in
            p
         | FbdHoareS h ->
            let mem = f (pat_memenv h.bhs_m) in
            let pr  = f (pat_form h.bhs_pr) in
            let s   = f (pat_stmt h.bhs_s) in
            let po  = f (pat_form h.bhs_po) in
            let cmp = f (pat_cmp h.bhs_cmp) in
            let bd  = f (pat_form h.bhs_bd) in
            let p = match mem.p_node, pr.p_node, s.p_node, po.p_node, cmp.p_node, bd.p_node with
              | Pat_Axiom(Axiom_MemEnv bhs_m),
                Pat_Axiom(Axiom_Form bhs_pr),
                Pat_Axiom(Axiom_Stmt bhs_s),
                Pat_Axiom(Axiom_Form bhs_po),
                Pat_Axiom(Axiom_Hoarecmp bhs_cmp),
                Pat_Axiom(Axiom_Form bhs_bd) ->
                 pat_form (EcFol.FSmart.f_bdHoareS (fo,h) { bhs_m ; bhs_pr ; bhs_s ; bhs_po ; bhs_cmp; bhs_bd })
              | _ -> p_bdHoareS mem pr s po cmp bd in
            p
         | FequivF h ->
            let pr = f (pat_form h.ef_pr) in
            let xl = f (pat_xpath h.ef_fl) in
            let xr = f (pat_xpath h.ef_fr) in
            let po = f (pat_form h.ef_po) in
            let p = match pr.p_node, xl.p_node, xr.p_node, po.p_node with
              | Pat_Axiom(Axiom_Form ef_pr),
                Pat_Axiom(Axiom_Xpath ef_fl),
                Pat_Axiom(Axiom_Xpath ef_fr),
                Pat_Axiom(Axiom_Form ef_po) ->
                 pat_form (EcFol.FSmart.f_equivF (fo,h) { ef_pr ; ef_fl ; ef_fr ; ef_po })
              | _ -> p_equivF pr xl xr po in
            p
         | FequivS h ->
            let ml = f (pat_memenv h.es_ml) in
            let mr = f (pat_memenv h.es_mr) in
            let pr = f (pat_form h.es_pr) in
            let sl = f (pat_stmt h.es_sl) in
            let sr = f (pat_stmt h.es_sr) in
            let po = f (pat_form h.es_po) in
            let p = match ml.p_node, mr.p_node, pr.p_node, sl.p_node, sr.p_node, po.p_node with
              | Pat_Axiom(Axiom_MemEnv es_ml),
                Pat_Axiom(Axiom_MemEnv es_mr),
                Pat_Axiom(Axiom_Form es_pr),
                Pat_Axiom(Axiom_Stmt es_sl),
                Pat_Axiom(Axiom_Stmt es_sr),
                Pat_Axiom(Axiom_Form es_po) ->
                 pat_form (EcFol.FSmart.f_equivS (fo,h) { es_ml; es_mr ; es_pr ; es_sl ; es_sr ; es_po })
              | _ -> p_equivS ml mr pr sl sr po in
            p
         | FeagerF h ->
            let pr = f (pat_form h.eg_pr) in
            let sl = f (pat_stmt h.eg_sl) in
            let fl = f (pat_xpath h.eg_fl) in
            let fr = f (pat_xpath h.eg_fr) in
            let sr = f (pat_stmt h.eg_sr) in
            let po = f (pat_form h.eg_po) in
            let p = match pr.p_node, sl.p_node, fl.p_node, fr.p_node, sr.p_node, po.p_node with
              | Pat_Axiom(Axiom_Form eg_pr),
                Pat_Axiom(Axiom_Stmt eg_sl),
                Pat_Axiom(Axiom_Xpath eg_fl),
                Pat_Axiom(Axiom_Xpath eg_fr),
                Pat_Axiom(Axiom_Stmt eg_sr),
                Pat_Axiom(Axiom_Form eg_po) ->
                 pat_form (EcFol.FSmart.f_eagerF (fo,h) { eg_pr ; eg_sl; eg_fl ; eg_fr ; eg_sr ; eg_po })
              | _ -> p_eagerF pr sl fl fr sr po in
            p
         | Fpr h ->
            let m    = f (pat_memory h.pr_mem) in
            let xp   = f (pat_xpath h.pr_fun) in
            let args = f (pat_form h.pr_args) in
            let ev   = f (pat_form h.pr_event) in
            let p = match m.p_node, xp.p_node, args.p_node, ev.p_node with
              | Pat_Axiom(Axiom_Memory pr_mem),
                Pat_Axiom(Axiom_Xpath pr_fun),
                Pat_Axiom(Axiom_Form pr_args),
                Pat_Axiom(Axiom_Form pr_event) ->
                 pat_form (EcFol.FSmart.f_pr (fo,h) { pr_mem ; pr_fun ; pr_args; pr_event })
              | _ -> p_pr m xp args ev in
            p
         | Fint _ | Flocal _ | Fop _ -> p
       end
     | Axiom_Instr i -> begin
         match i.i_node with
         | Sasgn (lv,e) ->
            let plv = f (pat_lvalue lv) in
            let pe  = f (pat_form (form_of_expr e)) in
            p_assign plv pe
         | Srnd (lv,e) ->
            let plv = f (pat_lvalue lv) in
            let pe  = f (pat_form (form_of_expr e)) in
            p_sample plv pe
         | Scall (olv,xp,args) ->
            let olv = match olv with
              | Some lv -> let p = f (pat_lvalue lv) in Some p
              | None -> None in
            let xp = f (pat_xpath xp) in
            let args =
              List.map f (List.map (fun arg -> pat_form (form_of_expr arg)) args) in
            p_call olv xp args
         | Sif (e,s1,s2) ->
            let pe = f (pat_form (form_of_expr e)) in
            let s1 = f (pat_stmt s1) in
            let s2 = f (pat_stmt s2) in
            p_instr_if pe s1 s2
         | Swhile (e,s) ->
            let pe = f (pat_form (form_of_expr e)) in
            let s  = f (pat_stmt s) in
            p_while pe s
         | Sassert e ->
            let p = f (pat_form (form_of_expr e)) in
            p_assert p
         | Sabstract _ -> p
       end
     | Axiom_Stmt s ->
        let s = List.map f (List.map pat_instr s.s_node) in
        p_stmt s
     | Axiom_Lvalue lv -> begin
         match lv with
         | LvVar (pv,ty) ->
            let p = f (pat_pv pv) in p_lvalue_var p ty
         | LvTuple t ->
            let t = List.map f (List.map (fun (pv,ty) -> pat_lvalue (LvVar (pv,ty))) t) in
            p_lvalue_tuple t
         | LvMap _ -> p
       end
     | Axiom_Prog_Var pv ->
        let p = f (pat_xpath pv.pv_name) in
        p_prog_var p pv.pv_kind
     | Axiom_Xpath xp ->
        let p = f (pat_mpath xp.x_top) in
        p_xpath p (pat_op xp.x_sub [] None)
     | Axiom_Mpath mp ->
        let m = f (pat_mpath_top mp.m_top) in
        let margs = List.map f (List.map pat_mpath mp.m_args) in
        p_mpath m margs
     | Axiom_Op _ | Axiom_Local _ | Axiom_Memory _ | Axiom_MemEnv _
       | Axiom_Mpath_top _ | Axiom_Hoarecmp _ -> p

(* -------------------------------------------------------------------------- *)
module Simplify = struct

  let ps_app ?ho p1 pargs ot = match ot with
    | None -> p_app ?ho p1 pargs ot
    | Some t ->
       if List.for_all is_form (p1::pargs)
       then pat_form (f_app (form_of_pattern p1)
                        (List.map form_of_pattern pargs) t)
       else p_app ?ho p1 pargs ot

  let ps_quant q b p =
    if is_form p then
      let o (id,t) = omap (fun x -> id,x) (gty_of_ogty t) in
      match olist_all o b with
      | None -> p_quant q b p
      | Some b -> pat_form (f_quant q b (form_of_pattern p))
    else p_quant q b p

  let ps_mpath (p : pattern) (args : pattern list) =
    if args = [] then p
    else
      let rec oget_mpaths acc = function
        | [] -> Some (List.rev acc)
        | ({ p_node = Pat_Axiom(Axiom_Mpath m)})::r ->
           oget_mpaths (m::acc) r
        | ({ p_node = Pat_Axiom(Axiom_Mpath_top mt)})::r ->
           oget_mpaths ((mpath mt [])::acc) r
        | _ -> None in
      let oget_mpaths l = oget_mpaths [] l in
      let oget_mpath =
        match p.p_node with
        | Pat_Axiom(Axiom_Mpath_top mt) -> Some (mpath mt [])
        | Pat_Axiom(Axiom_Mpath m)   -> Some m
        | _ -> None in
      match oget_mpath, oget_mpaths args with
      | Some m, Some args ->
         pat_mpath (mpath m.m_top (m.m_args @ args))
      | _,_ -> p_mpath p args

  let ps_xpath (p : pattern) (f : pattern) =
    match p.p_node, f.p_node with
    | Pat_Axiom(Axiom_Mpath m), Pat_Axiom(Axiom_Op (op,[])) ->
       pat_xpath (EcPath.xpath m op)
    | _ -> p_xpath p f

  let ps_prog_var (p : pattern) (k : pvar_kind) =
    match p.p_node with
    | Pat_Axiom (Axiom_Xpath x) -> pat_pv (pv x k)
    | _ ->
       pat_fun_symbol (Sym_Form_Prog_var k) [p]

  let ps_lvalue_var (p : pattern) (ty : ty) =
    match p.p_node with
    | Pat_Axiom(Axiom_Prog_Var pv) -> pat_lvalue (LvVar(pv,ty))
    | _ -> p_lvalue_var p ty

  let ps_lvalue_tuple (p : pattern list) =
    let rec oget_pv acc = function
      | [] -> Some (List.rev acc)
      | a :: r ->
         match a with
         | { p_node = Pat_Axiom (Axiom_Prog_Var pv); p_ogty = OGTty (Some ty) }
           | { p_node = Pat_Axiom (Axiom_Lvalue (LvVar (pv,ty))) ; p_ogty = OGTlv } ->
            oget_pv ((pv,ty)::acc) r
         | _ -> None
    in
    match oget_pv [] p with
    | Some l -> pat_lvalue (LvTuple l)
    | None -> p_lvalue_tuple p

  let ps_pvar (pv : pattern) (ty : ty) (m : pattern) =
    match pv.p_node, m.p_node with
    | Pat_Axiom (Axiom_Prog_Var pv),Pat_Axiom (Axiom_Memory m) ->
       pat_form (f_pvar pv ty m)
    | _ -> p_pvar pv ty m

  let ps_glob (mp : pattern) (m : pattern) =
    match mp.p_node, m.p_node  with
    | Pat_Axiom (Axiom_Mpath mp), Pat_Axiom (Axiom_Memory m) ->
       pat_form (f_glob mp m)
    | _ -> p_glob mp m

  let ps_if (p1 : pattern) (p2 : pattern) (p3 : pattern) =
    let l = [p1;p2;p3] in
    if List.for_all is_form l then
      let f1, f2, f3 = as_seq3 (List.map form_of_pattern l) in
      pat_form (f_if f1 f2 f3)
    else p_if p1 p2 p3

  let ps_match (p : pattern) (ty : ty) (lp : pattern list) =
    if List.for_all is_form (p::lp) then
      let op, lf = form_of_pattern p, List.map form_of_pattern lp in
      pat_form (mk_form (Fmatch (op,lf,ty)) ty)
    else p_match p ty lp

  let ps_tuple (lp : pattern list) =
    if List.for_all is_form lp then
      pat_form (f_tuple (List.map form_of_pattern lp))
    else p_tuple lp

  let ps_proj (p1 : pattern) (i : int) (ty : ty) =
    if is_form p1 then
      pat_form (f_proj (form_of_pattern p1) i ty)
    else p_proj p1 i ty

  let ps_let (l : lpattern) (p1 : pattern) (p2 : pattern) =
    if is_form p1 && is_form p2 then
      pat_form (EcFol.f_let l (form_of_pattern p1) (form_of_pattern p2))
    else p_let l p1 p2

  let ps_stmt (lp : pattern list) =
    match olist_all (function { p_node = Pat_Axiom (Axiom_Instr i) } -> Some i
                            | _ -> None) lp with
    | Some l -> pat_stmt (stmt l)
    | None -> p_stmt lp

  let ps_assign (plv : pattern) (pe : pattern) =
    match plv.p_node with
    | Pat_Axiom (Axiom_Lvalue lv) when is_form pe -> begin
        match expr_of_form (form_of_pattern pe) with
        | None -> p_assign plv pe
        | Some e -> pat_instr (i_asgn (lv,e))
      end
    | _ -> p_assign plv pe

  let ps_sample (plv : pattern) (pe : pattern) =
    match plv.p_node with
    | Pat_Axiom (Axiom_Lvalue lv) when is_form pe -> begin
        match expr_of_form (form_of_pattern pe) with
        | None -> p_sample plv pe
        | Some e -> pat_instr (i_rnd (lv,e))
      end
    | _ -> p_sample plv pe

  let ps_call (olv : pattern option) (f : pattern) (args : pattern list) =
    let get_expr p =
      if is_form p then expr_of_form (form_of_pattern p) else None
    in
    match olv, f.p_node with
    | None, Pat_Axiom (Axiom_Xpath proc) -> begin
        match olist_all get_expr args with
        | Some args -> pat_instr (i_call(None,proc,args))
        | None -> pat_fun_symbol Sym_Instr_Call (f::args)
      end
    | Some({ p_node = Pat_Axiom (Axiom_Lvalue lv) } as olv),
      Pat_Axiom (Axiom_Xpath proc) ->
       begin
         match olist_all get_expr args with
         | Some args -> pat_instr (i_call(Some lv,proc,args))
         | None -> pat_fun_symbol Sym_Instr_Call_Lv (olv::f::args)
       end
    | _ -> p_call olv f args

  let ps_instr_if (pcond : pattern) (ps1 : pattern) (ps2 : pattern) =
    match ps1.p_node, ps2.p_node with
    | Pat_Axiom (Axiom_Stmt s1), Pat_Axiom (Axiom_Stmt s2)
         when is_form pcond ->
       odfl (p_instr_if pcond ps1 ps2)
         (omap (fun cond -> pat_instr (i_if(cond,s1,s2)))
            (expr_of_form (form_of_pattern pcond)))
    | _ -> p_instr_if pcond ps1 ps2

  let ps_while (pcond : pattern) (ps : pattern) =
    match pcond.p_node, ps.p_node with
    | Pat_Axiom (Axiom_Form f), Pat_Axiom (Axiom_Stmt s) ->
       odfl (p_while pcond ps)
         (omap (fun cond -> pat_instr (i_while(cond,s)))
            (expr_of_form f))
    | _ -> p_while pcond ps

  let ps_assert (p : pattern) =
    if is_form p then
      odfl (p_assert p) (omap (fun e -> pat_instr (i_assert e))
                           (expr_of_form (form_of_pattern p)))
    else p_assert p

  let ps_hoareF (pr : pattern) (f : pattern) (po : pattern) =
    match pr.p_node, f.p_node, po.p_node with
    | Pat_Axiom(Axiom_Form pr),
      Pat_Axiom(Axiom_Xpath f),
      Pat_Axiom(Axiom_Form po) ->
       pat_form (f_hoareF pr f po)
    | _ ->
       pat_fun_symbol Sym_Form_Hoare_F [pr;f;po]

  let ps_hoareS (m : pattern) (pr : pattern) (s : pattern) (po : pattern) =
    match m.p_node, pr.p_node, s.p_node, po.p_node with
    | Pat_Axiom(Axiom_MemEnv m),
      Pat_Axiom(Axiom_Form pr),
      Pat_Axiom(Axiom_Stmt s),
      Pat_Axiom(Axiom_Form po) ->
       pat_form (f_hoareS m pr s po)
    | _ ->
       pat_fun_symbol Sym_Form_Hoare_F [m;pr;s;po]

  let ps_bdHoareF (pr : pattern) (f : pattern) (po : pattern) (cmp : pattern)
        (bd : pattern) =
    match pr.p_node, f.p_node, po.p_node, cmp.p_node, bd.p_node with
    | Pat_Axiom(Axiom_Form pr),
      Pat_Axiom(Axiom_Xpath f),
      Pat_Axiom(Axiom_Form po),
      Pat_Axiom(Axiom_Hoarecmp cmp),
      Pat_Axiom(Axiom_Form bd) ->
       pat_form(f_bdHoareF pr f po cmp bd)
    | _ ->
       pat_fun_symbol Sym_Form_bd_Hoare_F [pr;f;po;cmp;bd]

  let ps_bdHoareS (m : pattern) (pr : pattern) (s : pattern) (po : pattern)
        (cmp : pattern) (bd : pattern) =
    match m.p_node, pr.p_node, s.p_node, po.p_node, cmp.p_node, bd.p_node with
    | Pat_Axiom(Axiom_MemEnv m),
      Pat_Axiom(Axiom_Form pr),
      Pat_Axiom(Axiom_Stmt s),
      Pat_Axiom(Axiom_Form po),
      Pat_Axiom(Axiom_Hoarecmp cmp),
      Pat_Axiom(Axiom_Form bd) ->
       pat_form(f_bdHoareS m pr s po cmp bd)
    | _ ->
       pat_fun_symbol Sym_Form_bd_Hoare_F [m;pr;s;po;cmp;bd]

  let ps_equivF (pr : pattern) (fl : pattern) (fr : pattern) (po : pattern) =
    match pr.p_node, fl.p_node, fr.p_node, po.p_node with
    | Pat_Axiom(Axiom_Form pr),
      Pat_Axiom(Axiom_Xpath fl),
      Pat_Axiom(Axiom_Xpath fr),
      Pat_Axiom(Axiom_Form po) ->
       pat_form (f_equivF pr fl fr po)
    | _ ->
       pat_fun_symbol Sym_Form_Equiv_F [pr;fl;fr;po]

  let ps_equivS (ml : pattern) (mr : pattern) (pr : pattern) (sl : pattern)
        (sr : pattern) (po : pattern) =
    match ml.p_node, mr.p_node, pr.p_node, sl.p_node, sr.p_node, po.p_node with
    | Pat_Axiom(Axiom_MemEnv ml),
      Pat_Axiom(Axiom_MemEnv mr),
      Pat_Axiom(Axiom_Form pr),
      Pat_Axiom(Axiom_Stmt sl),
      Pat_Axiom(Axiom_Stmt sr),
      Pat_Axiom(Axiom_Form po) ->
       pat_form (f_equivS ml mr pr sl sr po)
    | _ ->
       pat_fun_symbol Sym_Form_Equiv_F [ml;mr;pr;sl;sr;po]

  let ps_eagerF (pr : pattern) (sl : pattern) (fl : pattern)
        (fr : pattern) (sr : pattern) (po : pattern) =
    match pr.p_node, sl.p_node, fl.p_node, fr.p_node, sr.p_node, po.p_node with
    | Pat_Axiom(Axiom_Form pr),
      Pat_Axiom(Axiom_Stmt sl),
      Pat_Axiom(Axiom_Xpath fl),
      Pat_Axiom(Axiom_Xpath fr),
      Pat_Axiom(Axiom_Stmt sr),
      Pat_Axiom(Axiom_Form po) ->
       pat_form (f_eagerF pr sl fl fr sr po)
    | _ ->
       pat_fun_symbol Sym_Form_Eager_F [pr;sl;fl;fr;sr;po]

  let ps_pr (pm : pattern) (pf : pattern) (pargs : pattern) (pevent : pattern) =
    match pm.p_node, pf.p_node, pargs.p_node, pevent.p_node with
    | Pat_Axiom(Axiom_Memory m),
      Pat_Axiom(Axiom_Xpath f),
      Pat_Axiom(Axiom_Form args),
      Pat_Axiom(Axiom_Form event) ->
       pat_form (f_pr m f args event)
    | _ ->
       pat_fun_symbol Sym_Form_Pr [pm;pf;pargs;pevent]

  let mem_ty_univar (ty : ty) =
    try ty_check_uni ty; true
    with
    | FoundUnivar -> false

(* -------------------------------------------------------------------------- *)
  let rec p_simplify p =
    match p.p_ogty with
    | OGTty (Some ty) when mem_ty_univar ty -> p
    | _ ->
    match p.p_node with
    | Pat_Anything -> p
    | Pat_Axiom (Axiom_Local (n, ty)) -> pat_form (f_local n ty)
    | Pat_Meta_Name (p1,n,ob) ->
       let p2 = p_simplify p1 in
       if p_equal p1 p2 then p else pat_meta p2 n ob
    | Pat_Sub p1 ->
       let p2 = p_simplify p1 in
       if p_equal p1 p2 then p else mk_pattern (Pat_Sub p2) OGTany
    | Pat_Or [] -> p
    | Pat_Or [p] -> p_simplify p
    | Pat_Or l ->
       let l1 = List.map p_simplify l in
       if List.for_all2 p_equal l l1 then p else mk_pattern (Pat_Or l1) p.p_ogty
    | Pat_Red_Strat (p1,f) ->
       let p2 = p_simplify p1 in
       if p_equal p1 p2 then p else mk_pattern (Pat_Red_Strat (p2,f)) p.p_ogty
    | Pat_Axiom _ -> p
    | Pat_Fun_Symbol (s, lp) ->
       match s, lp with
       | Sym_Form_If, _ ->
          let l = List.map p_simplify lp in
          if List.for_all2 p_equal l lp then p
          else let p1, p2, p3 = as_seq3 l in ps_if p1 p2 p3
       | Sym_Form_App (t,_), _ ->
          let l = List.map p_simplify lp in
          if List.for_all2 p_equal l lp then p
          else let p1, args = List.hd l, List.tl l in ps_app p1 args t
       | Sym_Form_Tuple, l ->
          let l1 = List.map p_simplify l in
          if List.for_all2 p_equal l l1 then p
          else ps_tuple l1
       | Sym_Form_Proj (i,ty), [p1] ->
          let p2 = p_simplify p1 in
          if p_equal p2 p1 then p
          else ps_proj p2 i ty
       | Sym_Form_Match ty, _ ->
          let l = List.map p_simplify lp in
          if List.for_all2 p_equal l lp then p
          else ps_match (List.hd l) ty (List.tl l)
       | Sym_Form_Let lp, [p1;p2] ->
          let p3, p4 = p_simplify p1, p_simplify p2 in
          if p_equal p1 p3 && p_equal p2 p4 then p
          else ps_let lp p3 p4
       | Sym_Form_Pvar ty, [pv;mem] ->
          let p1, p2 = p_simplify pv, p_simplify mem in
          if p_equal pv p1 && p_equal mem p2 then p
          else ps_pvar p1 ty p2
       | Sym_Form_Prog_var k, [xp] ->
          let p1 = p_simplify xp in
          if p_equal xp p1 then p
          else ps_prog_var p1 k
       | Sym_Form_Glob, [mp;mem] ->
          let p1, p2 = p_simplify mp, p_simplify mem in
          if p_equal mp p1 && p_equal p2 mem then p
          else ps_glob p1 p2
       | Sym_Form_Hoare_F, _ ->
          let l = List.map p_simplify lp in
          if List.for_all2 p_equal l lp then p
          else let p1, p2, p3 = as_seq3 l in ps_hoareF p1 p2 p3
       | Sym_Form_Hoare_S, _ ->
          let l = List.map p_simplify lp in
          if List.for_all2 p_equal l lp then p
          else let p1, p2, p3, p4 = as_seq4 l in ps_hoareS p1 p2 p3 p4
       | Sym_Form_bd_Hoare_F, _ ->
          let l = List.map p_simplify lp in
          if List.for_all2 p_equal l lp then p
          else let p1, p2, p3, p4, p5 = as_seq5 l in ps_bdHoareF p1 p2 p3 p4 p5
       | Sym_Form_bd_Hoare_S, _ ->
          let l = List.map p_simplify lp in
          if List.for_all2 p_equal l lp then p
          else let p1, p2, p3, p4, p5, p6 = as_seq6 l in ps_bdHoareS p1 p2 p3 p4 p5 p6
       | Sym_Form_Equiv_F, _ ->
          let l = List.map p_simplify lp in
          if List.for_all2 p_equal l lp then p
          else let p1, p2, p3, p4 = as_seq4 l in ps_equivF p1 p2 p3 p4
       | Sym_Form_Equiv_S, _ ->
          let l = List.map p_simplify lp in
          if List.for_all2 p_equal l lp then p
          else let p1, p2, p3, p4, p5, p6 = as_seq6 l in ps_equivS p1 p2 p3 p4 p5 p6
       | Sym_Form_Eager_F, _ ->
          let l = List.map p_simplify lp in
          if List.for_all2 p_equal l lp then p
          else let p1, p2, p3, p4, p5, p6 = as_seq6 l in ps_eagerF p1 p2 p3 p4 p5 p6
       | Sym_Form_Pr, _ ->
          let l = List.map p_simplify lp in
          if List.for_all2 p_equal l lp then p
          else let p1, p2, p3, p4 = as_seq4 l in ps_pr p1 p2 p3 p4
       | Sym_Stmt_Seq, _ ->
          let l = List.map p_simplify lp in
          if List.for_all2 p_equal l lp then p else ps_stmt l
       | Sym_Instr_Assign, _ ->
          let l = List.map p_simplify lp in
          if List.for_all2 p_equal l lp then p
          else let p1, p2 = as_seq2 l in ps_assign p1 p2
       | Sym_Instr_Sample, _ ->
          let l = List.map p_simplify lp in
          if List.for_all2 p_equal l lp then p
          else let p1, p2 = as_seq2 l in ps_sample p1 p2
       | Sym_Instr_Call, _ ->
          let l = List.map p_simplify lp in
          if List.for_all2 p_equal l lp then p
          else let p1, args = List.hd l, List.tl l in ps_call None p1 args
       | Sym_Instr_Call_Lv, _ ->
          let l = List.map p_simplify lp in
          if List.for_all2 p_equal l lp then p
          else let p1, l    = List.hd l, List.tl l in
               let p2, args = List.hd l, List.tl l in ps_call (Some p1) p2 args
       | Sym_Instr_If, _ ->
          let l = List.map p_simplify lp in
          if List.for_all2 p_equal l lp then p
          else let p1, p2, p3 = as_seq3 l in ps_instr_if p1 p2 p3
       | Sym_Instr_While, _ ->
          let l = List.map p_simplify lp in
          if List.for_all2 p_equal l lp then p
          else let p1, p2 = as_seq2 l in ps_while p1 p2
       | Sym_Instr_Assert, [p1] ->
          let p2 = p_simplify p1 in
          if p_equal p1 p2 then p else ps_assert p2
       | Sym_Xpath, _ ->
          let l = List.map p_simplify lp in
          if List.for_all2 p_equal l lp then p
          else let p1, p2 = as_seq2 l in ps_xpath p1 p2
       | Sym_Mpath, _ ->
          let l = List.map p_simplify lp in
          if List.for_all2 p_equal l lp then p
          else let p1, args = List.hd l, List.tl l in ps_mpath p1 args
       | Sym_Quant (q, b), [p1] ->
          let p2 = p_simplify p1 in
          if p_equal p1 p2 then p else ps_quant q b p2
       | _ -> assert false
end


let p_simplify = Simplify.p_simplify

(* -------------------------------------------------------------------------- *)
module Psubst = struct

  type p_subst = {
      ps_patloc : pattern Mid.t;
      ps_sty    : ty_subst;
    }

  let p_subst_id = {
      ps_patloc = Mid.empty;
      ps_sty    = ty_subst_id;
    }

  let is_subst_id s =
       is_ty_subst_id s.ps_sty
    && Mid.is_empty   s.ps_patloc

  let p_subst_init ?sty () =
    { p_subst_id with ps_sty = odfl ty_subst_id sty; }

  let p_bind_local (s : p_subst) (id : ident) (p : pattern) =
    let merge o = assert (o = None); Some p in
    { s with ps_patloc = Mid.change merge id s.ps_patloc }

  let p_bind_mem (s : p_subst) (m1 : memory) (m2 : memory) =
    let merge o = assert (o = None); Some (pat_memory m2) in
    { s with ps_patloc = Mid.change merge m1 s.ps_patloc }

  let p_bind_mod (s : p_subst) (x : ident) (m : mpath) =
    let merge o = assert (o = None); Some (pat_mpath m) in
    { s with ps_patloc = Mid.change merge x s.ps_patloc }

  let p_bind_rename (s : p_subst) (nfrom : ident) (nto : ident) (ty : ty) =
    let np = pat_local nto ty in
    p_bind_local s nfrom np

  let p_bind_gty (s : p_subst) (nfrom : ident) (nto : ident) (gty : gty) =
    match gty with
    | GTty ty -> p_bind_rename s nfrom nto ty
    | GTmem _ -> p_bind_mem s nfrom nto
    | GTmodty (_,_) -> p_bind_mod s nfrom (mpath (`Local nto) [])

  (* ------------------------------------------------------------------------ *)
  let p_rem_local (s : p_subst) (n : ident) =
    { s with ps_patloc = Mid.remove n s.ps_patloc; }

  let p_rem_mem (s : p_subst) (m : memory) =
    { s with ps_patloc = Mid.remove m s.ps_patloc }

  let p_rem_mod (s : p_subst) (m : ident) =
    let ps_patloc = Mid.remove m s.ps_patloc in
    let sty = s.ps_sty in
    let smp = Mid.map_filter (function { p_node = Pat_Axiom(Axiom_Mpath m) } -> Some m
                                     | _ -> None) ps_patloc in
    let sty = { sty with ts_mp = EcPath.m_subst sty.ts_p smp } in
    let ps_patloc =
      Mid.mapi (fun id a -> odfl a (omap pat_mpath (Mid.find_opt id smp)))
        ps_patloc in
    { s with ps_patloc = ps_patloc; ps_sty = sty; }

  (* ------------------------------------------------------------------------ *)
  let add_local (s : p_subst) (n,t as nt : ident * ty) =
    let t' = (ty_subst s.ps_sty) t in
    if   t == t'
    then (s, nt)
    else s, (n,t')

  let add_locals = List.Smart.map_fold add_local

  let subst_lpattern (s : p_subst) (lp : lpattern) =
    match lp with
    | LSymbol x ->
        let (s, x') = add_local s x in
          if x == x' then (s, lp) else (s, LSymbol x')

    | LTuple xs ->
        let (s, xs') = add_locals s xs in
          if xs == xs' then (s, lp) else (s, LTuple xs')

    | LRecord (p, xs) ->
        let (s, xs') =
          List.Smart.map_fold
            (fun s ((x, t) as xt) ->
              match x with
              | None ->
                  let t' = (ty_subst s.ps_sty) t in
                    if t == t' then (s, xt) else (s, (x, t'))
              | Some x ->
                  let (s, (x', t')) = add_local s (x, t) in
                    if   x == x' && t == t'
                    then (s, xt)
                     else (s, (Some x', t')))
            s xs
        in
          if xs == xs' then (s, lp) else (s, LRecord (p, xs'))

  let gty_subst (s : p_subst) (gty : gty) =
    if is_subst_id s then gty else

    match gty with
    | GTty ty ->
        let ty' = (ty_subst s.ps_sty) ty in
        if ty == ty' then gty else GTty ty'

    | GTmodty (p, (rx, r)) ->
        let sub  = s.ps_sty.ts_mp in
        let mp   = Mid.map_filter (function { p_node = Pat_Axiom(Axiom_Mpath m) } -> Some m
                                          | _ -> None) s.ps_patloc in
        let xsub = EcPath.x_substm s.ps_sty.ts_p mp in
        let p'   = mty_subst s.ps_sty.ts_p sub p in
        let rx'  = Sx.fold (fun m rx' -> Sx.add (xsub m) rx') rx Sx.empty in
        let r'   = Sm.fold (fun m r' -> Sm.add (sub m) r') r Sm.empty in

        if   p == p' && Sx.equal rx rx' && Sm.equal r r'
        then gty
        else GTmodty (p', (rx', r'))

    | GTmem mt ->
        let mp  = Mid.map_filter (function { p_node = Pat_Axiom(Axiom_Mpath m) } -> Some m
                                         | _ -> None) s.ps_patloc in
        let mt' = EcMemory.mt_substm s.ps_sty.ts_p mp
                    (ty_subst s.ps_sty) mt in
        if mt == mt' then gty else GTmem mt'

  let ogty_subst (s : p_subst) (ogty : ogty) =
    match ogty with
    | OGTty ty -> OGTty (omap (fun ty -> ty_subst s.ps_sty ty) ty)
    | OGTmem mt -> OGTmem (omap (fun mt -> gty_as_mem (gty_subst s (GTmem mt))) mt)
    | OGTmodty (Some (mt, mr)) ->
       let mt, mr = gty_as_mod (gty_subst s (GTmodty (mt,mr))) in
       OGTmodty (Some (mt, mr))
    | OGTmodty None -> ogty
    | _ -> ogty

  (* ------------------------------------------------------------------------ *)
  let add_binding (s : p_subst) (x,gty as xt : binding) =
    let gty' = gty_subst s gty in
    if   gty == gty'
    then
      let s = match gty with
        | GTty _    -> p_rem_local s x
        | GTmodty _ -> p_rem_mod   s x
        | GTmem _   -> p_rem_mem   s x in
      (s,xt)
    else
      (s, (x, gty'))

  let add_bindings = List.map_fold add_binding

  (* ------------------------------------------------------------------------ *)
  let add_pbinding (s : p_subst) (x,ogty as xt : pbinding) =
    let gty' = ogty_subst s ogty in
    if   ogty == gty'
    then
      let s = match ogty with
        | OGTty _    -> p_rem_local s x
        | OGTmodty _ -> p_rem_mod   s x
        | OGTmem _   -> p_rem_mem   s x
        | _ -> s
      in (s,xt)
    else
      (s, (x, gty'))

  let add_pbindings = List.map_fold add_pbinding

  (* ------------------------------------------------------------------------ *)
  let rec p_subst (s : p_subst) (p : pattern) =
    let p = mk_pattern p.p_node (ogty_subst s p.p_ogty) in
    let p = match p.p_node with
      | Pat_Anything -> mk_pattern Pat_Anything p.p_ogty
      | Pat_Sub p -> mk_pattern (Pat_Sub (p_subst s p)) p.p_ogty
      | Pat_Or lp -> mk_pattern (Pat_Or (List.map (p_subst s) lp)) p.p_ogty
      | Pat_Red_Strat (p,f) ->
         let p = p_subst s p in mk_pattern (Pat_Red_Strat (p,f)) p.p_ogty
      | Pat_Meta_Name (p,name,ob) -> begin
          match Mid.find_opt name s.ps_patloc with
          | Some p -> p
          | None ->
             let p = p_subst s p in mk_pattern (Pat_Meta_Name (p,name,ob)) p.p_ogty
        end
      | Pat_Axiom a -> begin
          match a with
          | Axiom_Form fp -> begin
              match fp.f_node with
              | Fquant (q, b, f) ->
                 let s, b' = add_bindings s b in
                 let p     = p_subst s (pat_form f) in
                 Simplify.ps_quant q (List.map (fun (id,t) -> id, ogty_of_gty t) b') p
              | Flet (lp, f1, f2) ->
                 let f1'    = p_subst s (pat_form f1) in
                 let s, lp' = subst_lpattern s lp in
                 let f2'    = p_subst s (pat_form f2) in
                 Simplify.ps_let lp' f1' f2'
              | Flocal id -> begin
                  match Mid.find_opt id s.ps_patloc with
                  | Some ({ p_node = Pat_Axiom (Axiom_Local (id,ty))}) ->
                     pat_form (f_local id ty)
                  | Some p -> p
                  | None ->
                     let ty = ty_subst s.ps_sty fp.f_ty in
                     pat_form (FSmart.f_local (fp, (id, fp.f_ty)) (id, ty))
                end
              | Fop (op, lty) ->
                 let ty'  = ty_subst s.ps_sty fp.f_ty in
                 let lty' = List.Smart.map (ty_subst s.ps_sty) lty in
                 let op'  = s.ps_sty.ts_p op in
                 pat_form (FSmart.f_op (fp, (op, lty, fp.f_ty)) (op', lty', ty'))
              | Fpvar (pv, m) ->
                 let pv' = pv_subst s pv in
                 let m'  = mem_subst s m in
                 let ty' = ty_subst s.ps_sty fp.f_ty in
                 Simplify.ps_pvar pv' ty' m'
              (* pat_form (FSmart.f_pvar (fp, (pv, fp.f_ty, m)) (pv', ty', m')) *)
              | Fglob (mp, m) ->
                 let m'  = mem_subst s m in
                 let mp' = mp_subst s mp in
                 Simplify.ps_glob mp' m'
              (* pat_form (FSmart.f_glob (fp, (mp, m)) (mp', m')) *)
              | FhoareF hf ->
                 assert (not (Mid.mem mhr s.ps_patloc)
                         && not (Mid.mem mhr s.ps_patloc));
                 let pr' = p_subst s (pat_form hf.hf_pr) in
                 let po' = p_subst s (pat_form hf.hf_po) in
                 let mp' = xp_subst s hf.hf_f in
                 Simplify.ps_hoareF pr' mp' po'
              (* FSmart.f_hoareF (fp, hf) { hf_pr = pr'; hf_po = po'; hf_f = mp'; } *)
              | FhoareS hs ->
                 assert (not (Mid.mem (fst hs.hs_m) s.ps_patloc));
                 let pr' = p_subst s (pat_form hs.hs_pr) in
                 let po' = p_subst s (pat_form hs.hs_po) in
                 let st' = stmt_subst s hs.hs_s in
                 let me' = memenv_subst s hs.hs_m in
                 Simplify.ps_hoareS  me' pr' st' po'
              (* FSmart.f_hoareS (fp, hs)
               *   { hs_pr = pr'; hs_po = po'; hs_s = st'; hs_m = me'; } *)
              | FbdHoareF bhf ->
                 assert (not (Mid.mem mhr s.ps_patloc)
                         && not (Mid.mem mhr s.ps_patloc));
                 let pr' = p_subst s (pat_form bhf.bhf_pr) in
                 let po' = p_subst s (pat_form bhf.bhf_po) in
                 let mp' = xp_subst s bhf.bhf_f in
                 let bd' = p_subst s (pat_form bhf.bhf_bd) in
                 Simplify.ps_bdHoareF pr' mp' po' (pat_cmp bhf.bhf_cmp) bd'
              (* FSmart.f_bdHoareF (fp, bhf)
               *   { bhf with bhf_pr = pr'; bhf_po = po';
               *              bhf_f  = mp'; bhf_bd = bd'; } *)
              | FbdHoareS bhs ->
                 assert (not (Mid.mem (fst bhs.bhs_m) s.ps_patloc));
                 let pr' = p_subst s (pat_form bhs.bhs_pr) in
                 let po' = p_subst s (pat_form bhs.bhs_po) in
                 let st' = stmt_subst s bhs.bhs_s in
                 let me' = memenv_subst s bhs.bhs_m in
                 let bd' = p_subst s (pat_form bhs.bhs_bd) in
                 Simplify.ps_bdHoareS me' pr' st' po'
                   (pat_cmp bhs.bhs_cmp) bd'
              (* FSmart.f_bdHoareS (fp, bhs)
               *   { bhs with bhs_pr = pr'; bhs_po = po'; bhs_s = st';
               *              bhs_bd = bd'; bhs_m  = me'; } *)
              | FequivF ef ->
                 assert (not (Mid.mem mleft s.ps_patloc)
                         && not (Mid.mem mright s.ps_patloc));
                 let pr' = p_subst s (pat_form ef.ef_pr) in
                 let po' = p_subst s (pat_form ef.ef_po) in
                 let fl' = xp_subst s ef.ef_fl in
                 let fr' = xp_subst s ef.ef_fr in
                 Simplify.ps_equivF pr' fl' fr' po'
              (* FSmart.f_equivF (fp, ef)
               *   { ef_pr = pr'; ef_po = po'; ef_fl = fl'; ef_fr = fr'; } *)
              | FequivS eqs ->
                 assert (not (Mid.mem (fst eqs.es_ml) s.ps_patloc)
                         && not (Mid.mem (fst eqs.es_mr) s.ps_patloc));
                 let pr' = p_subst s (pat_form eqs.es_pr) in
                 let po' = p_subst s (pat_form eqs.es_po) in
                 let sl' = stmt_subst s eqs.es_sl in
                 let sr' = stmt_subst s eqs.es_sr in
                 let ml' = memenv_subst s eqs.es_ml in
                 let mr' = memenv_subst s eqs.es_mr in
                 Simplify.ps_equivS ml' mr' pr' sl' sr' po'
              (* FSmart.f_equivS (fp, eqs)
               *   { es_ml = ml'; es_mr = mr';
               *     es_pr = pr'; es_po = po';
               *     es_sl = sl'; es_sr = sr'; } *)
              | FeagerF eg ->
                 assert (not (Mid.mem mleft s.ps_patloc)
                         && not (Mid.mem mright s.ps_patloc));
                 let pr' = p_subst s (pat_form eg.eg_pr) in
                 let po' = p_subst s (pat_form eg.eg_po) in
                 let fl' = xp_subst s eg.eg_fl in
                 let fr' = xp_subst s eg.eg_fr in
                 let sl' = stmt_subst s eg.eg_sl in
                 let sr' = stmt_subst s eg.eg_sr in
                 Simplify.ps_eagerF pr' sl' fl' fr' sr' po'
              (* FSmart.f_eagerF (fp, eg)
               *   { eg_pr = pr'; eg_sl = sl';eg_fl = fl';
               *     eg_fr = fr'; eg_sr = sr'; eg_po = po'; } *)
              | Fpr pr ->
                 assert (not (Mid.mem mhr s.ps_patloc));
                 let pr_mem   = mem_subst s pr.pr_mem in
                 let pr_fun   = xp_subst s pr.pr_fun in
                 let pr_args  = p_subst s (pat_form pr.pr_args) in
                 let pr_event = p_subst s (pat_form pr.pr_event) in
                 Simplify.ps_pr pr_mem pr_fun pr_args pr_event
              (* FSmart.f_pr (fp, pr) { pr_mem; pr_fun; pr_args; pr_event; } *)
              | Fif (f1, f2, f3) ->
                 Simplify.ps_if (p_subst s (pat_form f1)) (p_subst s (pat_form f2))
                   (p_subst s (pat_form f3))
              | Fmatch (f1, fargs, ty) ->
                 Simplify.ps_match (p_subst s (pat_form f1)) (ty_subst s.ps_sty ty)
                   (List.map (fun x -> p_subst s (pat_form x)) fargs)
              | Fint _ -> pat_form fp
              | Fapp (op,args) ->
                 let p = Simplify.ps_app (p_subst s (pat_form op))
                           (List.map (fun x -> p_subst s (pat_form x)) args)
                           (Some (ty_subst s.ps_sty fp.f_ty)) in
                 odfl p (p_betared_opt p)
              | Ftuple t ->
                 Simplify.ps_tuple (List.map (fun x -> p_subst s (pat_form x)) t)
              | Fproj (f1,i) ->
                 Simplify.ps_proj (p_subst s (pat_form f1)) i (ty_subst s.ps_sty fp.f_ty)
            end (* axiom_form *)
          | Axiom_Mpath_top mtop -> mtop_subst s mtop
          | Axiom_Mpath m -> mp_subst s m
          | Axiom_Xpath xp -> xp_subst s xp
          | Axiom_Memory m -> mem_subst s m
          | Axiom_MemEnv m -> memenv_subst s m
          | Axiom_Prog_Var pv -> pv_subst s pv
          | Axiom_Op (op,lty) ->
             let lty = List.Smart.map (ty_subst s.ps_sty) lty in
             let oty = match p.p_ogty with
               | OGTty (Some ty) -> Some (ty_subst s.ps_sty ty)
               | _ -> None in
             pat_op op lty oty
          | Axiom_Instr i -> i_subst s i
          | Axiom_Stmt st -> stmt_subst s st
          | Axiom_Lvalue lv -> lv_subst s lv
          | Axiom_Hoarecmp _ -> p
          | Axiom_Local (id,ty) ->
             match Mid.find_opt id s.ps_patloc with
             | None -> p
             | Some p' ->
                match p'.p_ogty with
                | OGTty (Some ty2) -> if ty_equal ty ty2 then p'
                                      else assert false
                | _ -> mk_pattern p'.p_node (OGTty (Some ty))
        end
      | Pat_Fun_Symbol (sym,lp) -> begin
          match sym,lp with
          | Sym_Form_If, [cond;p1;p2] ->
             let cond, p1, p2 = p_subst s cond, p_subst s p1, p_subst s p2 in
             p_if cond p1 p2
          | Sym_Form_App (ty,ho), op::args ->
             p_app ~ho (p_subst s op) (List.map (p_subst s) args) (omap (ty_subst s.ps_sty) ty)
          | Sym_Form_Tuple, t ->
             p_tuple (List.map (p_subst s) t)
          | Sym_Form_Proj (i,ty), [p] ->
             p_proj (p_subst s p) i (ty_subst s.ps_sty ty)
          | Sym_Form_Match ty, op::args ->
             p_match (p_subst s op) (ty_subst s.ps_sty ty) (List.map (p_subst s) args)
          | Sym_Form_Let lp, [p1;p2] ->
             let p1'    = p_subst s p1 in
             let s, lp' = subst_lpattern s lp in
             let p2'    = p_subst s p2 in
             p_let lp' p1' p2'
          | Sym_Form_Pvar ty, [p;m] ->
             p_pvar (p_subst s p) (ty_subst s.ps_sty ty) (p_subst s m)
          | Sym_Form_Prog_var k, [p] ->
             p_prog_var (p_subst s p) k
          | Sym_Form_Glob, [mp;m] ->
             p_glob (p_subst s mp) (p_subst s m)
          | Sym_Form_Hoare_F, [pr;pf;po] ->
             p_hoareF (p_subst s pr) (p_subst s pf) (p_subst s po)
          | Sym_Form_Hoare_S, [m;pr;ps;po] ->
             p_hoareS (p_subst s m) (p_subst s pr) (p_subst s ps) (p_subst s po)
          | Sym_Form_bd_Hoare_F, [pr;pf;po;cmp;bd] ->
             p_bdHoareF (p_subst s pr) (p_subst s pf) (p_subst s po)
               (p_subst s cmp) (p_subst s bd)
          | Sym_Form_bd_Hoare_S, [pm;pr;ps;po;cmp;bd] ->
             p_bdHoareS (p_subst s pm) (p_subst s pr)
               (p_subst s ps) (p_subst s po)
               (p_subst s cmp) (p_subst s bd)
          | Sym_Form_Equiv_F, [pr;fl;fr;po] ->
             p_equivF (p_subst s pr) (p_subst s fl)
               (p_subst s fr) (p_subst s po)
          | Sym_Form_Equiv_S, [ml;mr;pr;sl;sr;po] ->
             p_equivS (p_subst s ml) (p_subst s mr)
               (p_subst s pr) (p_subst s sl)
               (p_subst s sr) (p_subst s po)
          | Sym_Form_Eager_F, [pr;sl;fl;fr;sr;po] ->
             p_eagerF (p_subst s pr) (p_subst s sl)
               (p_subst s fl) (p_subst s fr)
               (p_subst s sr) (p_subst s po)
          | Sym_Form_Pr, [pm;pf;pargs;pevent] ->
             p_pr (p_subst s pm) (p_subst s pf)
               (p_subst s pargs) (p_subst s pevent)
          | Sym_Stmt_Seq, lp -> p_stmt (List.map (p_subst s) lp)
          | Sym_Instr_Assign, [lv;e] ->
             p_assign (p_subst s lv) (p_subst s e)
          | Sym_Instr_Sample, [lv;e] ->
             p_sample (p_subst s lv) (p_subst s e)
          | Sym_Instr_Call, p::args ->
             p_call None (p_subst s p) (List.map (p_subst s) args)
          | Sym_Instr_Call_Lv, lv::p::args ->
             p_call (Some (p_subst s lv)) (p_subst s p) (List.map (p_subst s) args)
          | Sym_Instr_If, [cond;s1;s2] ->
             p_instr_if (p_subst s cond) (p_subst s s1) (p_subst s s2)
          | Sym_Instr_While, [cond;body] ->
             p_while (p_subst s cond) (p_subst s body)
          | Sym_Instr_Assert, [cond] ->
             p_assert (p_subst s cond)
          | Sym_Xpath, [mp;p] ->
             p_xpath (p_subst s mp) (p_subst s p)
          | Sym_Mpath, mtop::margs ->
             p_mpath (p_subst s mtop) (List.map (p_subst s) margs)
          | Sym_Quant (q,bs), [p] ->
             let s, b' = add_pbindings s bs in
             let p'    = p_subst s p in
             p_quant q b' p'
          | _ -> assert false
        end (* pat_fun_symbol *)
    in p

    and pv_subst s pv =
      (* FIXME *)
      let mp = Mid.map_filter
                 (function { p_node = Pat_Axiom(Axiom_Mpath m) } -> Some m
                         | _ -> None) s.ps_patloc in
      let pv = EcTypes.pv_subst (EcPath.x_substm s.ps_sty.ts_p mp) pv in
      match xp_subst s pv.pv_name with
      | { p_node = Pat_Axiom (Axiom_Xpath xp) }
           when x_equal xp pv.pv_name -> pat_pv pv
      | p -> p_prog_var p pv.pv_kind


    and mtop_subst s mtop = match mtop with
      | `Local id when Mid.mem id s.ps_patloc ->
         Mid.find id s.ps_patloc
      | _ -> pat_mpath_top (s.ps_sty.ts_mp (mpath mtop [])).m_top

    and mp_subst s mp =
      let mp = s.ps_sty.ts_mp mp in
      match mp.m_top with
      | `Local id when Mid.mem id s.ps_patloc ->
         p_mpath (Mid.find id s.ps_patloc)
           (List.map (mp_subst s) mp.m_args)
      | _ ->
       let margs = List.map (mp_subst s) mp.m_args in
       let m_is_eq m1 = function
         | { p_node = Pat_Axiom(Axiom_Mpath m2) } -> m_equal m1 m2
         | _ -> false in
       if List.for_all2 m_is_eq mp.m_args margs
       then pat_mpath mp
       else p_mpath (pat_mpath_top mp.m_top) margs

    and mem_subst s m =
      match Mid.find_opt m s.ps_patloc with
      | Some p -> p
      | _ -> pat_memory m

    and xp_subst s xp =
      let mp = Mid.map_filter
                 (function { p_node = Pat_Axiom(Axiom_Mpath m) } -> Some m
                         | _ -> None) s.ps_patloc in
      let xp = EcPath.x_substm s.ps_sty.ts_p mp xp in
      match mp_subst s xp.x_top with
      | { p_node = Pat_Axiom (Axiom_Mpath mp) }
           when m_equal mp xp.x_top -> pat_xpath xp
      | p -> p_xpath p (pat_op xp.x_sub [] None)

    and memenv_subst s m =
      let mp  = Mid.map_filter
                  (function { p_node = Pat_Axiom(Axiom_Mpath m) } -> Some m
                            | _ -> None) s.ps_patloc in
      let mem = Mid.map_filter
                  (function { p_node = Pat_Axiom(Axiom_Memory m) } -> Some m
                          | _ -> None) s.ps_patloc in
      (* FIXME *)
      pat_memenv (EcMemory.me_substm s.ps_sty.ts_p mp mem (ty_subst s.ps_sty) m)

    and e_subst s e = p_subst s (pat_form (form_of_expr e))

    and i_subst s i =
      let e_s = e_subst s in
      let lv_subst lv = lv_subst s lv in
      match i.i_node with
      | Sasgn (lv, e) ->
         p_assign (lv_subst lv) (e_s e)
      | Srnd (lv, e) ->
         p_sample (lv_subst lv) (e_s e)
      | Scall (olv, xp, le) ->
         p_call (omap (lv_subst) olv) (xp_subst s xp) (List.map e_s le)
      | Sif (e, s1, s2) ->
         p_instr_if (e_s e) (stmt_subst s s1) (stmt_subst s s2)
      | Swhile (e, st) ->
         p_while (e_s e) (stmt_subst s st)
      | Sassert e ->
         p_assert (e_s e)
      | Sabstract id ->
         odfl (pat_instr i) (Mid.find_opt id s.ps_patloc)


    and stmt_subst s stmt =
      (* ISmart.s_stmt s (List.Smart.map i_subst s.s_node) *)
      p_stmt (List.map (i_subst s) stmt.s_node)

      (* (\* FIXME *\)
       * let es  = e_subst_init s.ps_freshen s.ps_sty.ts_p
       *             (ty_subst s.ps_sty) s.ps_opdef s.ps_mp s.ps_exloc in
       * pat_stmt (EcModules.s_subst es stmt) *)

    and lv_subst (s : p_subst) (lv : lvalue) = match lv with
      | LvVar (pv,ty) ->
         p_lvalue_var (p_subst s (pat_pv pv)) (ty_subst s.ps_sty ty)
      | LvTuple l ->
         p_lvalue_tuple (List.map (fun x -> lv_subst s (LvVar x)) l)
      | LvMap ((op,lty),pv,e,ty) ->
      match pv_subst s pv with
      | { p_node = Pat_Axiom(Axiom_Prog_Var pv) } ->
         pat_lvalue
           (LvMap
              ((op,List.map (ty_subst s.ps_sty) lty),
               pv, e_map (ty_subst s.ps_sty) (fun x->x) e, ty_subst s.ps_sty ty))
      | _ -> assert false

    and p_betared_opt p =
      match p.p_node with
      | Pat_Anything -> None
      | Pat_Meta_Name (p,n,ob) ->
         omap (fun p -> pat_meta p n ob) (p_betared_opt p)
      | Pat_Sub p ->
         omap (fun p -> mk_pattern (Pat_Sub p) p.p_ogty) (p_betared_opt p)
      | Pat_Or [p] -> p_betared_opt p
      | Pat_Or _ -> None
      | Pat_Red_Strat (p,f) ->
         omap (fun p -> mk_pattern (Pat_Red_Strat (p,f)) p.p_ogty) (p_betared_opt p)
      | Pat_Axiom (Axiom_Form f) ->
         let f2 = try EcFol.f_betared f with
                  | _ -> f in
         if f_equal f f2 then None
         else Some (pat_form f2)
      | Pat_Axiom _ -> None
      | Pat_Fun_Symbol (s,lp) ->
      match s,lp with
      | Sym_Form_App (ty,ho),
        ({ p_node = Pat_Fun_Symbol(Sym_Quant(Llambda, bds),[p])})::pargs ->
         let (bs1,bs2),(pargs1,pargs2) = List.prefix2 bds pargs in
         let subst = p_subst_id in
         let subst =
           List.fold_left2 (fun s (id,_) p -> p_bind_local s id p) subst bs1 pargs1 in
         Some (p_app ~ho (p_quant Llambda bs2 (p_subst subst p)) pargs2 ty)
      | Sym_Form_App (ty,ho),
        ({ p_node = Pat_Axiom (Axiom_Form { f_node = Fquant (Llambda,bds,f) })})::pargs ->
         let (bs1,bs2), (pargs1,pargs2) = List.prefix2 bds pargs in
         let subst = p_subst_id in
         let subst =
           List.fold_left2 (fun s (id,_) p -> p_bind_local s id p) subst bs1 pargs1 in
         let bs2 = List.map (snd_map ogty_of_gty) bs2 in
         Some (p_app ~ho (p_quant Llambda bs2 (p_subst subst (pat_form f))) pargs2 ty)
      | _ -> None

end

(* -------------------------------------------------------------------------- *)

let p_betared_opt = Psubst.p_betared_opt

(* -------------------------------------------------------------------------- *)
let fop_real_of_int = f_op EcCoreLib.CI_Real.p_real_of_int [] (tfun tint treal)

(* -------------------------------------------------------------------------- *)
let p_true  = pat_form EcFol.f_true
let p_false = pat_form EcFol.f_false

let p_op (p : path) (lty : ty list) (ty : ty) = pat_form (f_op p lty ty)

let pop_eq ty = p_op EcCoreLib.CI_Bool.p_eq [ty] (toarrow [ty; ty] tbool)

let p_is_true = function
  | { p_node = Pat_Axiom(Axiom_Form f) } -> EcCoreFol.is_true f
  | _ -> false

let p_is_false = function
  | { p_node = Pat_Axiom(Axiom_Form f) } -> EcCoreFol.is_false f
  | _ -> false

let p_bool_val p =
  if p_is_true p then Some true
  else if p_is_false p then Some false
  else None

let p_eq ty (p1 : pattern) (p2 : pattern) =
  match p1.p_node, p2.p_node with
  | Pat_Axiom(Axiom_Form f1), Pat_Axiom (Axiom_Form f2) ->
     pat_form (f_eq f1 f2)
  | _ ->
     p_app (pop_eq ty) [p1;p2] (Some tbool)

let p_not p =
  match p with
  | { p_node = Pat_Axiom(Axiom_Form f) } -> pat_form (EcFol.f_not f)
  | p ->
     p_app (pat_form EcFol.fop_not) [p] (Some EcTypes.tbool)

let p_imp (p1 : pattern) (p2 : pattern) =
  match p1.p_node,p2.p_node with
  | Pat_Axiom(Axiom_Form f1),
    Pat_Axiom(Axiom_Form f2) ->
     pat_form (EcFol.f_imp f1 f2)
  | _ ->
     p_app (pat_form EcFol.fop_imp) [p1;p2] (Some EcTypes.tbool)

let p_anda (p1 : pattern) (p2 : pattern) =
  match p1.p_node,p2.p_node with
  | Pat_Axiom(Axiom_Form f1),
    Pat_Axiom(Axiom_Form f2) ->
     pat_form  (EcFol.f_anda f1 f2)
  | _ ->
     p_app (pat_form EcFol.fop_anda) [p1;p2]
       (Some EcTypes.tbool)

let p_ora (p1 : pattern) (p2 : pattern) =
  match p1.p_node, p2.p_node with
  | Pat_Axiom (Axiom_Form f1), Pat_Axiom (Axiom_Form f2) ->
     pat_form (EcFol.f_ora f1 f2)
  | _ ->
     p_app (pat_form EcFol.fop_ora) [p1;p2] (Some EcTypes.tbool)

let p_iff (p1 : pattern) (p2 : pattern) =
  match p1.p_node, p2.p_node with
  | Pat_Axiom (Axiom_Form f1), Pat_Axiom (Axiom_Form f2) ->
     pat_form (EcFol.f_iff f1 f2)
  | _ ->
     p_app (pat_form EcFol.fop_iff) [p1;p2] (Some EcTypes.tbool)

let p_and (p1 : pattern) (p2 : pattern) =
  match p1.p_node, p2.p_node with
  | Pat_Axiom (Axiom_Form f1), Pat_Axiom (Axiom_Form f2) ->
     pat_form (EcFol.f_and f1 f2)
  | _ ->
     p_app (pat_form EcFol.fop_and) [p1;p2] (Some EcTypes.tbool)

let p_or (p1 : pattern) (p2 : pattern) =
  match p1.p_node, p2.p_node with
  | Pat_Axiom (Axiom_Form f1), Pat_Axiom (Axiom_Form f2) ->
     pat_form (EcFol.f_or f1 f2)
  | _ ->
     p_app (pat_form EcFol.fop_or) [p1;p2] (Some EcTypes.tbool)

let p_ands (ps : pattern list) = match List.rev ps with
  | [] -> p_true
  | p::ps -> List.fold_left ((^~) p_and) p ps

(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
 (* CORELIB *)
let pop_real_mul    = pat_form fop_real_mul
let pop_real_inv    = pat_form fop_real_inv
let pop_real_of_int = p_op EcCoreLib.CI_Real.p_real_of_int [] (tfun tint treal)

let p_int (i : EcBigInt.zint) = pat_form (f_int i)


let p_real_of_int p  = p_app pop_real_of_int [p] (Some treal)
let p_rint n         = p_real_of_int (p_int n)

let p_i0 = pat_form f_i0
let p_i1 = pat_form f_i1

let p_r0 = pat_form f_r0
let p_r1 = pat_form f_r1

let p_destr_int (p : pattern) = match p.p_node with
  | Pat_Axiom (Axiom_Form { f_node = Fint x } ) -> x
  | Pat_Axiom (Axiom_Form { f_node = Fapp (op, [{f_node = Fint n}])})
       when f_equal op fop_int_opp ->
     EcBigInt.neg n
  | _ -> destr_error "p_destr_int"

let p_destr_rint p =
  match p_destr_app p with
  | op, [p1] when op_equal op fop_real_of_int ->
     begin try p_destr_int p1 with DestrError _ -> destr_error "destr_rint" end

  | _ -> destr_error "destr_rint"

let p_int_le (p1 : pattern) (p2 : pattern) =
  match p1.p_node, p2.p_node with
  | Pat_Axiom (Axiom_Form f1), Pat_Axiom (Axiom_Form f2) ->
     pat_form (EcFol.f_int_le f1 f2)
  | _ ->
     p_app (pat_form fop_int_le) [p1;p2] (Some EcTypes.tbool)

let p_int_lt (p1 : pattern) (p2 : pattern) =
  match p1.p_node, p2.p_node with
  | Pat_Axiom (Axiom_Form f1), Pat_Axiom (Axiom_Form f2) ->
     pat_form (EcFol.f_int_lt f1 f2)
  | _ ->
     p_app (pat_form fop_int_lt) [p1;p2] (Some EcTypes.tbool)

let p_int_add (p1 : pattern) (p2 : pattern) =
  match p1.p_node, p2.p_node with
  | Pat_Axiom (Axiom_Form f1), Pat_Axiom (Axiom_Form f2) ->
     pat_form (EcFol.f_int_add f1 f2)
  | _ ->
     p_app (pat_form fop_int_add) [p1;p2] (Some EcTypes.tint)

let p_int_opp (p : pattern) =
  match p.p_node with
  | Pat_Axiom (Axiom_Form f) -> pat_form (EcFol.f_int_opp f)
  | _ ->
     p_app (pat_form fop_int_opp) [p] (Some EcTypes.tint)

let p_int_mul (p1 : pattern) (p2 : pattern) =
  match p1.p_node, p2.p_node with
  | Pat_Axiom (Axiom_Form f1), Pat_Axiom (Axiom_Form f2) ->
     pat_form (EcFol.f_int_mul f1 f2)
  | _ ->
     p_app (pat_form fop_int_mul) [p1;p2] (Some EcTypes.tint)

let get_real_of_int (p : pattern) =
  try Some (p_destr_rint p) with DestrError _ -> None


let p_real_le (p1 : pattern) (p2 : pattern) = match p1.p_node, p2.p_node with
  | Pat_Axiom (Axiom_Form f1), Pat_Axiom (Axiom_Form f2) ->
     pat_form (EcFol.f_real_le f1 f2)
  | _ -> p_app (pat_form fop_real_le) [p1;p2] (Some EcTypes.tbool)

let p_real_lt (p1 : pattern) (p2 : pattern) = match p1.p_node, p2.p_node with
  | Pat_Axiom (Axiom_Form f1), Pat_Axiom (Axiom_Form f2) ->
     pat_form (EcFol.f_real_lt f1 f2)
  | _ -> p_app (pat_form fop_real_lt) [p1;p2] (Some EcTypes.tbool)

let p_real_add (p1 : pattern) (p2 : pattern) = match p1.p_node, p2.p_node with
  | Pat_Axiom (Axiom_Form f1), Pat_Axiom (Axiom_Form f2) ->
     pat_form (EcFol.f_real_add f1 f2)
  | _ -> p_app (pat_form fop_real_add) [p1;p2] (Some EcTypes.treal)

let p_real_opp (p : pattern) = match p.p_node with
  | Pat_Axiom (Axiom_Form f) -> pat_form (EcFol.f_int_opp f)
  | _ -> p_app (pat_form fop_real_opp) [p] (Some EcTypes.treal)

let p_real_mul (p1 : pattern) (p2 : pattern) = match p1.p_node, p2.p_node with
  | Pat_Axiom (Axiom_Form f1), Pat_Axiom (Axiom_Form f2) ->
     pat_form (EcFol.f_real_mul f1 f2)
  | _ -> p_app (pat_form fop_real_mul) [p1;p2] (Some EcTypes.treal)

let p_real_inv (p : pattern) = match p.p_node with
  | Pat_Axiom (Axiom_Form f) -> pat_form (EcFol.f_real_inv f)
  | _ -> p_app (pat_form fop_real_inv) [p] (Some EcTypes.treal)

let p_real_div (p1 : pattern) (p2 : pattern) =
  p_real_mul p1 (p_real_inv p2)

(* -------------------------------------------------------------------------- *)
let p_is_not = function
  | { p_node = Pat_Axiom(Axiom_Form f) } -> EcFol.is_not f
  | _ -> false

let p_destr_not = function
  | { p_node = Pat_Axiom(Axiom_Form f) } -> pat_form (EcFol.destr_not f)
  | _ -> assert false

(* -------------------------------------------------------------------------- *)
let p_not_simpl (p : pattern) =
  if p_is_not p then p_destr_not p
  else if p_is_true p then p_false
  else if p_is_false p then p_true
  else p_not p

let p_imp_simpl (p1 : pattern) (p2 : pattern) =
  match p_bool_val p1, p_bool_val p2 with
  | Some true, _ -> p2
  | Some false, _ | _, Some true -> p_true
  | _, Some false -> p_not_simpl p1
  | _ -> if p_equal p1 p2 then p_true
         else p_imp p1 p2

let p_anda_simpl (p1 : pattern) (p2 : pattern) =
  match p_bool_val p1, p_bool_val p2 with
  | Some true, _ -> p2
  | Some false, _ -> p_false
  | _, Some true -> p1
  | _, Some false -> p_false
  | _ -> p_anda p1 p2

let p_ora_simpl (p1 : pattern) (p2 : pattern) =
  match p_bool_val p1, p_bool_val p2 with
  | Some true, _ -> p_true
  | Some false, _ -> p2
  | _, Some true -> p_true
  | _, Some false -> p1
  | _ -> p_ora p1 p2

let rec p_iff_simpl (p1 : pattern) (p2 : pattern) =
  if p_equal  p1 p2 then p_true
  else
  match p_bool_val p1, p_bool_val p2 with
  | Some true, _ -> p2
  | Some false, _ -> p_not_simpl p2
  | _, Some true -> p1
  | _, Some false -> p_not_simpl p1
  | _ ->
  match p_destr_app p1, p_destr_app p2 with
  | (op1, [p1]), (op2, [p2])
       when (op_equal op1 fop_not && op_equal op2 fop_not) ->
     p_iff_simpl p1 p2
  | _ -> p_iff p1 p2

let p_and_simpl (p1 : pattern) (p2 : pattern) =
  match p_bool_val p1, p_bool_val p2 with
  | Some false, _ | _, Some false -> p_false
  | Some true, _ -> p2
  | _, Some true -> p1
  | _ -> p_and p1 p2

let p_or_simpl (p1 : pattern) (p2 : pattern) =
  match p_bool_val p1, p_bool_val p2 with
  | Some true, _ | _, Some true -> p_true
  | Some false, _ -> p2
  | _, Some false -> p1
  | _ -> p_or p1 p2

let p_andas_simpl = List.fold_right p_anda_simpl

let rec p_eq_simpl ty (p1 : pattern) (p2 : pattern) =
  if p_equal p1 p2 then p_true
  else match p1.p_node, p2.p_node with
  | Pat_Axiom (Axiom_Form { f_node = Fint _ } ),
    Pat_Axiom (Axiom_Form { f_node = Fint _ } ) -> p_false

  | Pat_Axiom (Axiom_Form { f_node = Fapp (op1, [{f_node = Fint _}]) }),
    Pat_Axiom (Axiom_Form { f_node = Fapp (op2, [{f_node = Fint _}]) })
      when f_equal op1 fop_real_of_int &&
           f_equal op2 fop_real_of_int
    -> p_false

  | Pat_Axiom (Axiom_Form { f_node = Fop (op1, []) } ),
    Pat_Axiom (Axiom_Form { f_node = Fop (op2, []) } )
       when
         (EcPath.p_equal op1 EcCoreLib.CI_Bool.p_true  &&
          EcPath.p_equal op2 EcCoreLib.CI_Bool.p_false  )
      || (EcPath.p_equal op2 EcCoreLib.CI_Bool.p_true  &&
          EcPath.p_equal op1 EcCoreLib.CI_Bool.p_false  )
    -> p_false

  | Pat_Axiom (Axiom_Form { f_node = Ftuple fs1 } ),
    Pat_Axiom (Axiom_Form { f_node = Ftuple fs2 } )
       when List.length fs1 = List.length fs2 ->
      p_andas_simpl (List.map2 (fun x y -> pat_form (f_eq_simpl x y)) fs1 fs2) p_true

  | _ -> p_eq ty p1 p2


(* -------------------------------------------------------------------------- *)
let p_int_le_simpl (p1 : pattern) (p2 : pattern) =
  if p_equal p1 p2 then p_true
  else
    try pat_form (f_bool (EcBigInt.compare (p_destr_int p1) (p_destr_int p2) <= 0))
    with DestrError _ -> p_int_le p1 p2

let p_int_lt_simpl (p1 : pattern) (p2 : pattern) =
  if p_equal p1 p2 then p_true
  else
    try pat_form (f_bool (EcBigInt.compare (p_destr_int p1) (p_destr_int p2) < 0))
    with DestrError _ -> p_int_lt p1 p2

let p_int_opp_simpl (p : pattern) =
  match p_destr_app p with
  | op, [p] when op_equal op fop_int_opp -> p
  | _ -> if p_equal p_i0 p then p_i0 else p_int_opp p

let p_int_add_simpl =
  let try_add_opp p1 p2 =
    try
      let p2 = match p_destr_app p2 with
        | op, [p] when op_equal op fop_int_opp -> p
        | _ -> destr_error "" in
      if p_equal p1 p2 then Some p_i0 else None
    with DestrError _ -> None in

  let try_addc i p =
    try
      let c1, c2 = match p_destr_app p with
        | op, [p1; p2] when op_equal op fop_int_add -> p1, p2
        | _ -> destr_error "" in

      try  let c = p_destr_int c1 in
           Some (p_int_add (p_int (EcBigInt.add c i)) c2)
      with DestrError _ ->
      try  let c = p_destr_int c2 in
           Some (p_int_add c1 (p_int (EcBigInt.add c i)))
      with DestrError _ -> None

    with DestrError _ -> None in

  fun p1 p2 ->
    let i1 = try Some (p_destr_int p1) with DestrError _ -> None in
    let i2 = try Some (p_destr_int p2) with DestrError _ -> None in

    match i1, i2 with
    | Some i1, Some i2 -> p_int (EcBigInt.add i1 i2)

    | Some i1, _ when EcBigInt.equal i1 EcBigInt.zero -> p2
    | _, Some i2 when EcBigInt.equal i2 EcBigInt.zero -> p1

    | _, _ ->
        let simpls = [
           (fun () -> try_add_opp p1 p2);
           (fun () -> try_add_opp p2 p1);
           (fun () -> i1 |> obind (try_addc^~ p2));
           (fun () -> i2 |> obind (try_addc^~ p1));
        ] in

        ofdfl
          (fun () -> p_int_add p1 p2)
          (List.Exceptionless.find_map (fun f -> f ()) simpls)

let p_int_mul_simpl (p1 : pattern) (p2 : pattern) =
  try  p_int (EcBigInt.mul (p_destr_int p1) (p_destr_int p2))
  with DestrError _ ->
    if p_equal p_i0 p1 || p_equal p_i0 p2 then p_i0
    else if p_equal p_i1 p1 then p2
    else if p_equal p_i1 p2 then p1
    else p_int_mul p1 p2

(* -------------------------------------------------------------------- *)
let p_real_le_simpl (p1 : pattern) (p2 : pattern) =
  if p_equal p1 p2 then p_true else
    match get_real_of_int p1, get_real_of_int p2 with
    | Some x1, Some x2 -> pat_form (f_bool (EcBigInt.compare x1 x2 <= 0))
    | _ -> p_real_le p1 p2

let p_real_lt_simpl (p1 : pattern) (p2 : pattern) =
  if p_equal p1 p2 then p_true else
    match get_real_of_int p1, get_real_of_int p2 with
    | Some x1, Some x2 -> pat_form (f_bool (EcBigInt.compare x1 x2 < 0))
    | _ -> p_real_lt p1 p2

let p_remove_opp (p : pattern) =
  match p_destr_app p with
  | op, [p] when op_equal op fop_real_opp -> Some p
  | _ -> None

let p_remove_add (p : pattern) =
  match p_destr_app p with
  | op, [p1;p2] when op_equal op fop_real_add -> p1, p2
  | _ -> destr_error "p_remove_add"

let p_destr_rdivint (p : pattern) =
  let rec aux isneg p =
    let renorm n d =
      if isneg then (EcBigInt.neg n, d) else (n, d)
    in
    match p_destr_app p with
    | op, [p1;p2] when op_equal op fop_real_mul -> begin
        match p_destr_app p2 with
        | op2, [p2] when op_equal op2 fop_real_inv ->
           let n1, n2 =
             try (p_destr_rint p1, p_destr_rint p2)
             with DestrError _ -> destr_error "p_rdivint"
           in renorm n1 n2
        | _ ->
           try  renorm (p_destr_rint p) EcBigInt.one
           with DestrError _ -> destr_error "p_rdivint"
      end

    | op, [p1] when op_equal op fop_real_inv -> begin
        try  renorm EcBigInt.one (p_destr_rint p1)
        with DestrError _ -> destr_error "p_rdivint"
      end

    | op, [p1] when op_equal op fop_real_opp ->
       aux (not isneg) p1

    | _ ->
       try  renorm (p_destr_rint p) EcBigInt.one
       with DestrError _ -> destr_error "p_rdivint"

  in aux false p

let rec p_real_split p =
  match p.p_node with
  | Pat_Axiom (Axiom_Form { f_node = Fapp (op, [f1; { f_node = Fapp (subop, [f2]) }]) })
      when f_equal    op fop_real_mul
        && f_equal subop fop_real_inv  -> (pat_form f1, pat_form f2)
  | Pat_Fun_Symbol (Sym_Form_App _,
                    [op;p1;{ p_node =
                               Pat_Axiom (Axiom_Form { f_node = Fapp (subop, [f2])})}])
       when op_equal    op fop_real_mul
         &&  f_equal subop fop_real_inv -> (p1, pat_form f2)
  | Pat_Fun_Symbol (Sym_Form_App _,
                    [op;p1;{ p_node =
                               Pat_Fun_Symbol (Sym_Form_App _, [subop;p2])}])
       when op_equal    op fop_real_mul
         &&  p_equal subop pop_real_inv -> (p1, p2)

  | Pat_Axiom (Axiom_Form { f_node = Fapp (op, [{ f_node = Fapp (subop, [f1]) }; f2]) })
      when f_equal    op fop_real_mul
        && f_equal subop fop_real_inv -> (pat_form f2, pat_form f1)
  | Pat_Fun_Symbol (Sym_Form_App _,
                    [op;{ p_node = Pat_Axiom (Axiom_Form { f_node = Fapp (subop, [f1])})};
                     p2])
       when op_equal    op fop_real_mul
         &&  f_equal subop fop_real_inv -> (p2, pat_form f1)
  | Pat_Fun_Symbol (Sym_Form_App _,
                    [op;{ p_node = Pat_Fun_Symbol (Sym_Form_App _, [subop;p1])};
                     p2])
       when op_equal    op fop_real_mul
         &&  p_equal subop pop_real_inv -> (p2, p1)

  | Pat_Axiom (Axiom_Form { f_node = Fapp (op, [f]) })
       when f_equal op fop_real_inv -> (p_r1, pat_form f)
  | Pat_Fun_Symbol (Sym_Form_App _, [op;p])
       when op_equal op fop_real_inv -> (p_r1, p)

  | _ -> (p, p_r1)

let p_norm_real_int_div n1 n2 =
  let module BI = EcBigInt in
  let s1 = BI.sign n1 and s2 = BI.sign n2 in
  if s1 = 0 || s2 = 0 then p_r0
  else
    let n1 = BI.abs n1 and n2 = BI.abs n2 in
    let n1, n2 =
      match BI.gcd n1 n2 with
      | n when BI.equal n BI.one -> (n1, n2)
      | n -> (BI.div n1 n, BI.div n2 n)
    in
    let n1 = if (s1 * s2) < 0 then BI.neg n1 else n1 in
    if BI.equal n2 BI.one then p_rint n1
    else p_real_div (p_rint n1) (p_rint n2)

let p_real_add_simpl (p1 : pattern) (p2 : pattern) =
  let module BI = EcBigInt in
  let try_add_opp p1 p2 =
    match p_remove_opp p2 with
    | None -> None
    | Some p2 -> if p_equal p1 p2 then Some p_r0 else None in

  let try_addc i p =
    try
      let c1, c2 = p_remove_add p in
      try let c = p_destr_rint c1 in Some (p_real_add (p_rint (EcBigInt.add c i)) c2)
      with DestrError _ ->
      try let c = p_destr_rint c2 in Some (p_real_add c1 (p_rint (EcBigInt.add c i)))
      with DestrError _ -> None

    with DestrError _ -> None in

  let try_norm_rintdiv p1 p2 =
    try
      let (n1, d1) = p_destr_rdivint p1 in
      let (n2, d2) = p_destr_rdivint p2 in

      Some (p_norm_real_int_div (BI.add (BI.mul n1 d2) (BI.mul n2 d1)) (BI.mul d1 d2))

    with DestrError _ -> None in

  let r1 = try Some (p_destr_rint p1) with DestrError _ -> None in
  let r2 = try Some (p_destr_rint p2) with DestrError _ -> None in

  match r1, r2 with
  | Some i1, Some i2 -> p_rint (BI.add i1 i2)

  | Some i1, _ when BI.equal i1 BI.zero -> p2
  | _, Some i2 when BI.equal i2 BI.zero -> p1

  | _ ->
     let simpls = [
         (fun () -> try_norm_rintdiv p1 p2);
         (fun () -> try_add_opp p1 p2);
         (fun () -> try_add_opp p2 p1);
         (fun () -> r1 |> obind (try_addc^~ p2));
         (fun () -> r2 |> obind (try_addc^~ p1));
       ] in

     ofdfl
       (fun () -> p_real_add p1 p2)
       (List.Exceptionless.find_map (fun f -> f ()) simpls)

let p_real_opp_simpl (p : pattern) =
  match p_destr_app p with
  | op, [p] when op_equal op fop_real_opp -> p
  | _ -> p_real_opp p

let p_real_is_zero p =
  try  EcBigInt.equal EcBigInt.zero (p_destr_rint p)
  with DestrError _ -> false

let p_real_is_one p =
  try  EcBigInt.equal EcBigInt.one (p_destr_rint p)
  with DestrError _ -> false


let rec p_real_mul_simpl p1 p2 =
  let (n1, d1) = p_real_split p1 in
  let (n2, d2) = p_real_split p2 in

  p_real_div_simpl_r
    (p_real_mul_simpl_r n1 n2)
    (p_real_mul_simpl_r d1 d2)

and p_real_div_simpl p1 p2 =
  let (n1, d1) = p_real_split p1 in
  let (n2, d2) = p_real_split p2 in

  p_real_div_simpl_r
    (p_real_mul_simpl_r n1 d2)
    (p_real_mul_simpl_r d1 n2)

and p_real_mul_simpl_r p1 p2 =
  if p_real_is_zero p1 || p_real_is_zero p2 then p_r0 else

  if p_real_is_one p1 then p2 else
  if p_real_is_one p2 then p1 else

  try
    p_rint (EcBigInt.Notations.( *^ ) (p_destr_rint p1) (p_destr_rint p2))
  with DestrError _ ->
    p_real_mul p1 p2

and p_real_div_simpl_r p1 p2 =
  let (p1, p2) =
    try
      let n1 = p_destr_rint p1 in
      let n2 = p_destr_rint p2 in
      let gd = EcBigInt.gcd n1 n2 in

      p_rint (EcBigInt.div n1 gd), p_rint (EcBigInt.div n2 gd)

    with
    | DestrError _ -> (p1, p2)
    | Division_by_zero -> (p_r0, p_r1)

  in p_real_mul_simpl_r p1 (p_real_inv_simpl p2)

and p_real_inv_simpl p =
  match p.p_node with
  | Pat_Axiom (Axiom_Form { f_node = Fapp (op, [f]) })
       when f_equal op fop_real_inv -> pat_form f
  | Pat_Fun_Symbol (Sym_Form_App _,
                    [{ p_node = Pat_Axiom (Axiom_Form op) };p])
       when f_equal op fop_real_inv -> p

  | _ ->
     try
       match p_destr_rint p with
       | n when EcBigInt.equal n EcBigInt.zero -> p_r0
       | n when EcBigInt.equal n EcBigInt.one  -> p_r1
       | _ -> destr_error "destr_rint/inv"
     with DestrError _ -> p_app pop_real_inv [p] (Some treal)

(* -------------------------------------------------------------------------- *)
let rec reduce_pat p = match p.p_node with
  | Pat_Anything | Pat_Red_Strat _ | Pat_Sub _ | Pat_Or _ -> p
  | Pat_Meta_Name ({ p_node = Pat_Anything }, id, None) -> begin
      match p.p_ogty with
      | OGTty (Some ty) -> pat_form (f_local id ty)
      | _ -> p
    end
  | Pat_Meta_Name _ -> p
  | Pat_Axiom _ -> p
  | Pat_Fun_Symbol (Sym_Form_If, [p1;p2;p3]) ->
     p_if (reduce_pat p1) (reduce_pat p2) (reduce_pat p3)
  | Pat_Fun_Symbol (Sym_Form_App (ty,ho), pop::pargs) ->
     p_app ~ho (reduce_pat pop) (List.map reduce_pat pargs) ty
  | Pat_Fun_Symbol (Sym_Form_Tuple, t) ->
     p_tuple (List.map reduce_pat t)
  | Pat_Fun_Symbol (Sym_Form_Proj (i,ty), [p]) ->
     p_proj (reduce_pat p) i ty
  | Pat_Fun_Symbol (Sym_Form_Match ty, pop::l) ->
     p_match (reduce_pat pop) ty (List.map reduce_pat l)
  | Pat_Fun_Symbol (Sym_Form_Let lp, [p1;p2]) ->
     p_let lp (reduce_pat p1) (reduce_pat p2)
  | Pat_Fun_Symbol (Sym_Form_Pvar ty, [p1;p2]) ->
     p_pvar (reduce_pat p1) ty (reduce_pat p2)
  | Pat_Fun_Symbol (Sym_Form_Prog_var k, [p]) ->
     p_prog_var (reduce_pat p) k
  | Pat_Fun_Symbol (Sym_Form_Glob, [p1;p2]) ->
     p_glob (reduce_pat p1) (reduce_pat p2)
  | Pat_Fun_Symbol (Sym_Form_Hoare_F, [p1;p2;p3]) ->
     p_hoareF (reduce_pat p1) (reduce_pat p2) (reduce_pat p3)
  | Pat_Fun_Symbol (Sym_Form_Hoare_S, [p1;p2;p3;p4]) ->
     p_hoareS (reduce_pat p1) (reduce_pat p2) (reduce_pat p3) (reduce_pat p4)
  | Pat_Fun_Symbol (Sym_Form_bd_Hoare_F, [p1;p2;p3;p4;p5]) ->
     p_bdHoareF (reduce_pat p1) (reduce_pat p2) (reduce_pat p3)
       (reduce_pat p4) (reduce_pat p5)
  | Pat_Fun_Symbol (Sym_Form_bd_Hoare_S, [p1;p2;p3;p4;p5;p6]) ->
     p_bdHoareS (reduce_pat p1) (reduce_pat p2) (reduce_pat p3)
       (reduce_pat p4) (reduce_pat p5) (reduce_pat p6)
  | Pat_Fun_Symbol (Sym_Form_Equiv_F, [p1;p2;p3;p4]) ->
     p_equivF (reduce_pat p1) (reduce_pat p2) (reduce_pat p3) (reduce_pat p4)
  | Pat_Fun_Symbol (Sym_Form_Equiv_S, [p1;p2;p3;p4;p5;p6]) ->
     p_equivS (reduce_pat p1) (reduce_pat p2) (reduce_pat p3)
       (reduce_pat p4) (reduce_pat p5) (reduce_pat p6)
  | Pat_Fun_Symbol (Sym_Form_Eager_F, [p1;p2;p3;p4;p5;p6]) ->
     p_eagerF (reduce_pat p1) (reduce_pat p2) (reduce_pat p3)
       (reduce_pat p4) (reduce_pat p5) (reduce_pat p6)
  | Pat_Fun_Symbol (Sym_Form_Pr, [p1;p2;p3;p4]) ->
     p_pr (reduce_pat p1) (reduce_pat p2) (reduce_pat p3) (reduce_pat p4)
  | Pat_Fun_Symbol (Sym_Stmt_Seq, l) ->
     p_stmt (List.map reduce_pat l)
  | Pat_Fun_Symbol (Sym_Instr_Assign, [p1;p2]) ->
     p_assign (reduce_pat p1) (reduce_pat p2)
  | Pat_Fun_Symbol (Sym_Instr_Sample, [p1;p2]) ->
     p_sample (reduce_pat p1) (reduce_pat p2)
  | Pat_Fun_Symbol (Sym_Instr_Call, p1::pargs) ->
     p_call None (reduce_pat p1) (List.map reduce_pat pargs)
  | Pat_Fun_Symbol (Sym_Instr_Call_Lv, p0::p1::pargs) ->
     p_call (Some (reduce_pat p0)) (reduce_pat p1) (List.map reduce_pat pargs)
  | Pat_Fun_Symbol (Sym_Instr_If, [p1;p2;p3]) ->
     p_instr_if (reduce_pat p1) (reduce_pat p2) (reduce_pat p3)
  | Pat_Fun_Symbol (Sym_Instr_While, [p1;p2]) ->
     p_while (reduce_pat p1) (reduce_pat p2)
  | Pat_Fun_Symbol (Sym_Instr_Assert, [p1]) ->
     p_assert (reduce_pat p1)
  | Pat_Fun_Symbol (Sym_Xpath, [p1;p2]) ->
     p_xpath (reduce_pat p1) (reduce_pat p2)
  | Pat_Fun_Symbol (Sym_Mpath, p1::pall) ->
     p_mpath (reduce_pat p1) (List.map reduce_pat pall)
  | Pat_Fun_Symbol (Sym_Quant (q,b), [p]) ->
     p_quant q b (reduce_pat p)
  | _ -> assert false

(* -------------------------------------------------------------------------- *)
let p_if_simpl (p1 : pattern) (p2 : pattern) (p3 : pattern) =
  if p_equal p2 p3 then p2
  else match p_bool_val p1, p_bool_val p2, p_bool_val p3 with
  | Some true, _, _  -> p2
  | Some false, _, _ -> p3
  | _, Some true, _  -> p_imp_simpl (p_not_simpl p1) p3
  | _, Some false, _ -> p_anda_simpl (p_not_simpl p1) p3
  | _, _, Some true  -> p_imp_simpl p1 p2
  | _, _, Some false -> p_anda_simpl p1 p2
  | _, _, _          -> p_if p1 p2 p3

let p_proj_simpl (p1 : pattern) (i : int) (ty : ty) =
  match p1.p_node with
  | Pat_Fun_Symbol(Sym_Form_Tuple,pargs) when 0 <= i && i < List.length pargs ->
     List.nth pargs i
  | Pat_Axiom(Axiom_Form f) -> pat_form (f_proj_simpl f i ty)
  | _ -> p_proj p1 i ty

let try_form ot p =
  match ot with
  | None -> p
  | Some t ->
     let p1, args = p_destr_app p in
     if List.for_all is_form (p1::args)
     then pat_form (f_app (form_of_pattern p1) (List.map form_of_pattern args) t)
     else p

let p_app_simpl_opt ?ho op pargs oty = match op with
  | None -> None
  | Some p ->
     omap reduce_pat (
         p_betared_opt (reduce_pat (p_app ?ho p pargs oty))
       )

let p_app_simpl ?ho op pargs oty =
  odfl (p_app ?ho op pargs oty) (p_app_simpl_opt ?ho (Some op) pargs oty)

let ps_app_simpl ?ho op pargs oty =
  odfl (p_app ?ho op pargs oty) (p_betared_opt (Simplify.ps_app ?ho op pargs oty))

let p_forall_simpl b p =
  let b = List.filter (fun (id,_) -> Mid.mem id (pat_fv p)) b in
  p_forall b p

let p_exists_simpl b p =
  let b = List.filter (fun (id,_) -> Mid.mem id (pat_fv p)) b in
  p_exists b p

let p_destr_app p =
  match p.p_node with
  | Pat_Fun_Symbol (Sym_Form_App _, p::lp) -> p, lp
  | Pat_Axiom (Axiom_Form { f_node = Fapp (f,args) }) ->
     pat_form f, List.map pat_form args
  | _ -> p, []

(* -------------------------------------------------------------------------- *)
let get_ty2 (p1 : pattern) (p2 : pattern) =
  match p1.p_ogty, p2.p_ogty with
  | OGTty (Some ty), _ | _, OGTty (Some ty)-> ty
  | _ -> tbool


(* -------------------------------------------------------------------------- *)
module FV = struct
  type fv = int Mid.t

  let add_fv (m: fv) (x : ident) =
    Mid.change (fun i -> Some (odfl 0 i + 1)) x m

  let union (m1 : fv) (m2 : fv) =
    Mid.union (fun _ i1 i2 -> Some (i1 + i2)) m1 m2

  let rec lvalue h (map : fv) =
    function
    | LvVar (pv,_) ->
        pattern h map (pat_pv pv)
    | LvTuple t ->
        List.fold_left (pattern h) map (List.map (fun (x,_) -> pat_pv x) t)
    | LvMap ((_,_),pv,e,_) ->
        pattern h (union map e.e_fv) (pat_pv pv)

  and axiom h =
    let rec aux (map : fv) (a : axiom) =
      match a with
      | Axiom_Form f -> union f.f_fv map
      | Axiom_Memory m -> add_fv map m
      | Axiom_Instr i -> union map i.i_fv
      | Axiom_Stmt s -> union map s.s_fv
      | Axiom_MemEnv (m, _) -> add_fv map m
      | Axiom_Prog_Var pv -> pattern h map (pat_xpath pv.pv_name)
      | Axiom_Xpath xp -> pattern h map (pat_mpath xp.x_top)
      | Axiom_Mpath mp ->
          let env0 = EcEnv.LDecl.toenv h in
          if is_none (EcEnv.Mod.by_mpath_opt mp env0) then map else
          List.fold_left (pattern h)
            (pattern h map (pat_mpath_top mp.m_top))
            (List.map pat_mpath mp.m_args)

      | Axiom_Mpath_top (`Local id) -> add_fv map id
      | Axiom_Mpath_top _ -> map
      | Axiom_Local (id,_) -> add_fv map id
      | Axiom_Op _ -> map
      | Axiom_Hoarecmp _ -> map
      | Axiom_Lvalue lv -> lvalue h map lv

    in fun m a -> aux m a

  and pattern h =
    let rec aux (map : int Mid.t) p = match p.p_node with
      | Pat_Anything -> map
      | Pat_Meta_Name (p,n,_) -> aux (add_fv map n) p
      | Pat_Sub p -> aux map p
      | Pat_Or lp -> List.fold_left aux map lp
      | Pat_Red_Strat (p,_) -> aux map p
      | Pat_Fun_Symbol (Sym_Quant (_,b),lp) ->
         let map' = List.fold_left aux Mid.empty lp in
         let map' =
           Mid.filter
             (fun x _ -> not (List.exists (fun (y,_) -> id_equal x y) b))
             map' in
         union map map'
      | Pat_Fun_Symbol (Sym_Form_Pr, lp) ->
         let map = List.fold_left aux map lp in
         Mid.remove mhr map
      | Pat_Fun_Symbol (_,lp) -> List.fold_left aux map lp
      | Pat_Axiom a -> axiom h map a

    in fun m p -> aux m p

  (* ------------------------------------------------------------------ *)
  let lvalue0  h = lvalue  h Mid.empty
  let axiom0   h = axiom   h Mid.empty
  let pattern0 h = pattern h Mid.empty
end

(* -------------------------------------------------------------------------- *)
module PReduction = struct
  open EcReduction
  open Psubst

  let rec h_red_args
        (p_f : 'a -> pattern)
        (f :  EcEnv.LDecl.hyps -> reduction_info -> Psubst.p_subst ->'a -> pattern option)
        (hyps : EcEnv.LDecl.hyps) (ri : reduction_info) (s : Psubst.p_subst) = function
    | [] -> None
    | a :: r ->
       match f hyps ri s a with
       | Some a -> Some (a :: (List.map p_f r))
       | None -> omap (fun l -> (p_f a)::l) (h_red_args p_f f hyps ri s r)

  let is_record (hyps : EcEnv.LDecl.hyps) (f : form) =
    match EcFol.destr_app f with
    | { f_node = Fop (p,_) }, _ ->
       EcEnv.Op.is_record_ctor (EcEnv.LDecl.toenv hyps) p
    | _ -> false

  let rec p_is_record (hyps : EcEnv.LDecl.hyps) (p : pattern) =
    match p.p_node with
    | Pat_Fun_Symbol (Sym_Form_App _, p::_) ->
       p_is_record hyps p
    | Pat_Axiom (Axiom_Form f) -> begin
        match EcFol.destr_app f with
        | { f_node = Fop (p,_) }, _ ->
           EcEnv.Op.is_record_ctor (EcEnv.LDecl.toenv hyps) p
        | _ -> false
      end
    | Pat_Axiom (Axiom_Op (op,_)) ->
       EcEnv.Op.is_record_ctor (EcEnv.LDecl.toenv hyps) op
    | _ -> false

  let reduce_local_opt (hyps : EcEnv.LDecl.hyps) (ri : reduction_info)
        (s : Psubst.p_subst) (id : Name.t) (ob : pbindings option) (ogty : ogty): pattern option =
    if ri.delta_h id
    then
      if is_none ob && EcEnv.LDecl.can_unfold id hyps then
         Some (pat_form (EcEnv.LDecl.unfold id hyps))
      else
        let p = meta_var id ob ogty in
        let p' = Psubst.p_subst s p in
        if p_equal p p' then None else Some p'
    else None

  let is_delta_p ri pop = match pop.p_node with
    | Pat_Axiom (Axiom_Form { f_node = Fop (op, _) } )
      | Pat_Axiom (Axiom_Op (op, _)) ->
       ri.delta_p op
    | _ -> false

  let get_op p = match p.p_node with
    | Pat_Axiom (Axiom_Form { f_node = Fop (op, lty) } )
      | Pat_Axiom (Axiom_Op (op, lty)) -> Some (op, lty)
    | _ -> None

  let reduce_op ri env op =
    if   is_delta_p ri op
    then omap (fun (op,tys) -> pat_form (EcEnv.Op.reduce env op tys))
           (get_op op)
    else None

  let can_eta x (f, args) =
    match List.rev args with
    | { f_node = Flocal y } :: args ->
       let check v = not (Mid.mem x v.f_fv) in
       id_equal x y && List.for_all check (f :: args)
    | _ -> false

  let p_can_eta h x (f, args) =
    match List.rev args with
    | { p_node = (Pat_Axiom (Axiom_Form { f_node = Flocal y }
                             | Axiom_Local (y,_))
                  | Pat_Meta_Name ({ p_node = Pat_Anything }, y, _))} :: args ->
       let check v = not (Mid.mem x (FV.pattern0 h v)) in
       id_equal x y && List.for_all check (f :: args)
    | _ -> false

  let rec h_red_pattern_opt (hyps : EcEnv.LDecl.hyps) (ri : reduction_info)
        (s : Psubst.p_subst) (p : pattern) =
    try
      match p.p_node with
      | Pat_Anything -> None
      | Pat_Meta_Name (_,n,ob) -> reduce_local_opt hyps ri s n ob p.p_ogty
      | Pat_Sub p -> omap (fun x -> mk_pattern (Pat_Sub x) OGTany)
                       (h_red_pattern_opt hyps ri s p)
      | Pat_Or _ -> None
      | Pat_Red_Strat _ -> None
      | Pat_Axiom a -> h_red_axiom_opt hyps ri s a
      | Pat_Fun_Symbol (symbol,lp) ->
      match symbol, lp with
      (* β-reduction *)
      | Sym_Form_App _,
        { p_node = (Pat_Fun_Symbol (Sym_Quant (Llambda,_),[_])
                    | Pat_Axiom (Axiom_Form { f_node = Fquant (Llambda,_,_)}))}::_
           when ri.beta -> p_betared_opt p

      (* ζ-reduction *)
      | Sym_Form_App (ty,ho),
        { p_node =
            (Pat_Meta_Name ({ p_node = Pat_Anything }, id, ob)) ;
          p_ogty = ogty} :: pargs ->
         if ri.beta then p_app_simpl_opt ~ho (reduce_local_opt hyps ri s id ob ogty) pargs ty
         else omap (fun x -> p_app ~ho x pargs ty) (reduce_local_opt hyps ri s id ob ogty)

      (* ζ-reduction *)
      | Sym_Form_App (oty,ho),
        { p_node = (Pat_Axiom (Axiom_Form { f_node = Flocal id ; f_ty = ty})
                    | Pat_Axiom (Axiom_Local (id,ty)))}::pargs ->
         if ri.beta then p_app_simpl_opt ~ho (reduce_local_opt hyps ri s id None (OGTty (Some ty))) pargs oty
         else omap (fun x -> p_app ~ho x pargs oty) (reduce_local_opt hyps ri s id None (OGTty (Some ty)))

      (* ζ-reduction *)
      | Sym_Form_Let (LSymbol(x,_)), [p1;p2] when ri.zeta ->
         let s = Psubst.p_bind_local Psubst.p_subst_id x p1 in
         Some (Psubst.p_subst s p2)

      (* ι-reduction (let-tuple) *)
      | Sym_Form_Let (LTuple ids),
        [{ p_node = Pat_Fun_Symbol (Sym_Form_Tuple, lp)};p2]
           when ri.zeta ->
         let s = List.fold_left2 (fun s (x,_) p -> Psubst.p_bind_local s x p)
                   Psubst.p_subst_id ids lp in
         Some (Psubst.p_subst s p2)

      (* ι-reduction (let-records) *)
      | Sym_Form_Let (LRecord (_, ids)), [p1;p2]
           when ri.iota && p_is_record hyps p1 ->
         let args  = snd (p_destr_app p1) in
         let subst =
           List.fold_left2 (fun subst (x, _) e ->
               match x with
               | None   -> subst
               | Some x -> Psubst.p_bind_local subst x e)
             Psubst.p_subst_id ids args
         in
         Some (Psubst.p_subst subst p2)

      (* ι-reduction (records projection) *)
      | Sym_Form_App (_,ho),
        { p_node = Pat_Axiom (Axiom_Form ({ f_node = Fop (op, _) ; f_ty = fty } as f1))}
        ::pargs
           when ri.iota && EcEnv.Op.is_projection (EcEnv.LDecl.toenv hyps) op -> begin
          let op =
            match pargs with
            | [mk] -> begin
                match odfl mk (h_red_pattern_opt hyps ri s mk) with
                | { p_node = Pat_Axiom (Axiom_Form { f_node = Fapp ({ f_node = Fop (mkp, _)}, mkargs) } ) } ->
                   if not (EcEnv.Op.is_record_ctor (EcEnv.LDecl.toenv hyps) mkp) then None
                   else
                     let v = oget (EcEnv.Op.by_path_opt op (EcEnv.LDecl.toenv hyps)) in
                     let v = proj3_2 (EcDecl.operator_as_proj v) in
                     let v = try Some(List.nth mkargs v)
                             with _ -> None in
                     begin
                       match v with
                       | None -> None
                       | Some v -> h_red_form_opt hyps ri s v
                     end
                | { p_node = Pat_Fun_Symbol
                               (Sym_Form_App _,
                                { p_node = (Pat_Axiom (Axiom_Form { f_node = Fop (mkp,_)}
                                                       | Axiom_Op (mkp,_)))}::pargs)} ->
                   if not (EcEnv.Op.is_record_ctor (EcEnv.LDecl.toenv hyps) mkp) then None
                   else
                     let v = oget (EcEnv.Op.by_path_opt op (EcEnv.LDecl.toenv hyps)) in
                     let v = proj3_2 (EcDecl.operator_as_proj v) in
                     let v = try Some(List.nth pargs v)
                             with _ -> None in
                     begin
                       match v with
                       | None -> None
                       | Some v -> h_red_pattern_opt hyps ri s v
                     end
                | _ -> None
              end
            | _ -> None
          in match op with
             | None ->
                omap (fun x -> p_app ~ho x pargs (Some fty)) (h_red_form_opt hyps ri s f1)
             | _ -> op
        end

      (* ι-reduction (tuples projection) *)
      | Sym_Form_Proj (i,ty), [p1] when ri.iota ->
         let p' = p_proj_simpl p1 i ty in
         if p = p'
         then omap (fun x -> p_proj x i ty) (h_red_pattern_opt hyps ri s p1)
         else Some p'

      (* ι-reduction (if-then-else) *)
      | Sym_Form_If, [p1;p2;p3] when ri.iota ->
         let p' = p_if_simpl p1 p2 p3 in
         if   p_equal p p'
         then omap (fun x -> p_if x p2 p3) (h_red_pattern_opt hyps ri s p1)
         else Some p'

      (* ι-reduction (match-fix) *)
      | Sym_Form_App (ty,ho),
        { p_node = Pat_Axiom (Axiom_Form ({ f_node = Fop (op, lty) } as f1))}::args
           when ri.iota
                && EcEnv.Op.is_fix_def (EcEnv.LDecl.toenv hyps) op -> begin
          try
            let op  = oget (EcEnv.Op.by_path_opt op (EcEnv.LDecl.toenv hyps)) in
            let fix = EcDecl.operator_as_fix op in
            if List.length args <> snd (fix.EcDecl.opf_struct) then
              raise EcEnv.NotReducible
            else
            let pargs = Array.of_list args in
            let myfun (opb, acc) v =
              let v = pargs.(v) in
              let v = odfl v (h_red_pattern_opt hyps ri s v) in
              match p_destr_app v with
              | { p_node = Pat_Axiom (Axiom_Form { f_node = Fop (op, _) }
                                      | Axiom_Op (op, _ )) }, cargs
                   when EcEnv.Op.is_dtype_ctor (EcEnv.LDecl.toenv hyps) op -> begin
                  let idx = EcEnv.Op.by_path op (EcEnv.LDecl.toenv hyps) in
                  let idx = snd (EcDecl.operator_as_ctor idx) in
                  match opb with
                  | EcDecl.OPB_Leaf _    -> assert false
                  | EcDecl.OPB_Branch bs ->
                     ((Parray.get bs idx).EcDecl.opb_sub, cargs :: acc)
                end
              | _ -> raise EcEnv.NotReducible in
            let pargs = List.fold_left myfun
                      (fix.EcDecl.opf_branches, [])
                      (fst fix.EcDecl.opf_struct) in
            let pargs, (bds, body) =
              match pargs with
              | EcDecl.OPB_Leaf (bds, body), cargs -> (List.rev cargs, (bds, body))
              | _ -> assert false in

            let s =
              List.fold_left2
                (fun s (x,_) fa -> Psubst.p_bind_local s x fa)
                Psubst.p_subst_id fix.EcDecl.opf_args args in

            let s =
              List.fold_left2
                (fun s bds cargs ->
                  List.fold_left2
                    (fun s (x,_) fa -> Psubst.p_bind_local s x fa)
                    s bds cargs)
                s bds pargs in

            let body = EcFol.form_of_expr EcFol.mhr body in
            let body =
              EcFol.Fsubst.subst_tvar
                (EcTypes.Tvar.init (List.map fst op.EcDecl.op_tparams) lty) body in
            Some (Psubst.p_subst s (pat_form body))

          with
          | EcEnv.NotReducible ->
             omap (fun x -> p_app ~ho x args ty)
               (h_red_form_opt hyps ri s f1)
        end

      (* μ-reduction *)
      | Sym_Form_Glob, [mp;mem] when ri.modpath ->
         let p' = match mp.p_node, mem.p_node with
           | Pat_Axiom (Axiom_Mpath mp), Pat_Axiom (Axiom_Memory m) ->
              let f  = f_glob mp m in
              let f' = EcEnv.NormMp.norm_glob (EcEnv.LDecl.toenv hyps) m mp in
              if f_equal f f' then None
              else Some (pat_form f')
           | _ ->
           match h_red_pattern_opt hyps ri s mp with
           | Some mp' when not (p_equal mp mp') -> Some (p_glob mp' mem)
           | _ -> omap (fun x -> p_glob mp x) (h_red_pattern_opt hyps ri s mem) in
         p'

      (* μ-reduction *)
      | Sym_Form_Pvar ty, [ppv;m] ->
         let pv = match ppv.p_node with
           | Pat_Axiom (Axiom_Prog_Var pv) ->
              let pv' = EcEnv.NormMp.norm_pvar (EcEnv.LDecl.toenv hyps) pv in
              if pv_equal pv pv' then
                omap (p_pvar ppv ty) (h_red_pattern_opt hyps ri s m)
              else Some (p_pvar (pat_pv pv') ty m)
           | _ ->
           match h_red_pattern_opt hyps ri s ppv with
           | Some pv -> Some (p_pvar pv ty m)
           | None -> omap (p_pvar ppv ty) (h_red_pattern_opt hyps ri s m) in
         pv

    (* logical reduction *)
    | Sym_Form_App (ty,ho),
      { p_node = Pat_Axiom (Axiom_Form ({f_node = Fop (op, tys); } as fo))}::args
         when is_some ri.logic && is_logical_op op
      ->
       let pcompat =
         match oget ri.logic with `Full -> true | `ProductCompat -> false
       in

       let p' =
         match op_kind op, args with
         | Some (`Not), [f1]    when pcompat -> Some (p_not_simpl f1)
         | Some (`Imp), [f1;f2] when pcompat -> Some (p_imp_simpl f1 f2)
         | Some (`Iff), [f1;f2] when pcompat -> Some (p_iff_simpl f1 f2)


         | Some (`And `Asym), [f1;f2] -> Some (p_anda_simpl f1 f2)
         | Some (`Or  `Asym), [f1;f2] -> Some (p_ora_simpl f1 f2)
         | Some (`And `Sym ), [f1;f2] -> Some (p_and_simpl f1 f2)
         | Some (`Or  `Sym ), [f1;f2] -> Some (p_or_simpl f1 f2)
         | Some (`Int_le   ), [f1;f2] -> Some (p_int_le_simpl f1 f2)
         | Some (`Int_lt   ), [f1;f2] -> Some (p_int_lt_simpl f1 f2)
         | Some (`Real_le  ), [f1;f2] -> Some (p_real_le_simpl f1 f2)
         | Some (`Real_lt  ), [f1;f2] -> Some (p_real_lt_simpl f1 f2)
         | Some (`Int_add  ), [f1;f2] -> Some (p_int_add_simpl f1 f2)
         | Some (`Int_opp  ), [f]     -> Some (p_int_opp_simpl f)
         | Some (`Int_mul  ), [f1;f2] -> Some (p_int_mul_simpl f1 f2)
         | Some (`Real_add ), [f1;f2] -> Some (p_real_add_simpl f1 f2)
         | Some (`Real_opp ), [f]     -> Some (p_real_opp_simpl f)
         | Some (`Real_mul ), [f1;f2] -> Some (p_real_mul_simpl f1 f2)
         | Some (`Real_inv ), [f]     -> Some (p_real_inv_simpl f)
         | Some (`Eq       ), [f1;f2] -> begin
             match (p_destr_app f1), (p_destr_app f2) with
             | ({ p_node = Pat_Axiom (Axiom_Form { f_node = Fop (op1, _)})}, args1),
               ({ p_node = Pat_Axiom (Axiom_Form { f_node = Fop (op2, _)})}, args2)
                  when EcEnv.Op.is_dtype_ctor (EcEnv.LDecl.toenv hyps) op1
                       && EcEnv.Op.is_dtype_ctor (EcEnv.LDecl.toenv hyps) op2 ->

                let idx p =
                  let idx = EcEnv.Op.by_path p (EcEnv.LDecl.toenv hyps) in
                  snd (EcDecl.operator_as_ctor idx)
                in
                if   idx op1 <> idx op2
                then Some p_false
                else Some (p_ands (List.map2 (p_eq tbool) args1 args2))

             | _ -> if p_equal f1 f2 then Some p_true
                    else Some (p_eq_simpl (get_ty2 f1 f2) f1 f2)
           end

         | _ when ri.delta_p op ->
            let op = h_red_op_opt hyps ri s op tys in
            p_app_simpl_opt ~ho op args ty

         | _ -> Some p
       in
       begin
         match p' with
         | Some p' ->
            if p_equal p p'
            then omap (fun l -> p_app ~ho (pat_form fo) l ty)
                   (h_red_args (fun x -> x) h_red_pattern_opt hyps ri s args)
            else Some p'
         | None -> None
       end

    (* δ-reduction *)
    | Sym_Form_App (ty,ho), pop::args when is_delta_p ri pop ->
       let op = reduce_op ri (EcEnv.LDecl.toenv hyps) pop in
       omap (fun op -> p_app_simpl ~ho op args ty) op

    (* η-reduction *)
    | Sym_Quant (Llambda, (x, OGTty _)::binds),
      [{ p_node = Pat_Axiom (Axiom_Form { f_node = Fapp (fn, args) })}]
         when can_eta x (fn, args)
      -> Some (p_quant Llambda binds
                 (pat_form
                    (EcFol.f_ty_app
                       (EcEnv.LDecl.toenv hyps) fn
                       (List.take (List.length args - 1) args))))

    (* η-reduction *)
    | Sym_Quant (Llambda, (x, OGTty _)::binds),
      [{ p_node = Pat_Fun_Symbol (Sym_Form_App (ty,ho), pn::pargs)}]
         when p_can_eta hyps x (pn, pargs) ->
       Some (p_quant Llambda binds
               (p_app ~ho pn (List.take (List.length pargs - 1) pargs) ty))

    (* contextual rule - let *)
    | Sym_Form_Let lp, [p1;p2] ->
       omap (fun p1 -> p_let lp p1 p2) (h_red_pattern_opt hyps ri s p1)

    (* Contextual rule - application args. *)
    | Sym_Form_App (ty,ho), p1::args ->
       omap (fun p1 -> p_app ~ho p1 args ty) (h_red_pattern_opt hyps ri s p1)

    (* (\* Contextual rule - bindings *\)
     * | Sym_Form_Quant (Lforall as t, b), [p1]
     *   | Sym_Form_Quant (Lexists as t, b), [p1]
     *      when ri.logic = Some `Full -> begin
     *     let ctor = match t with
     *       | Lforall -> f_forall_simpl
     *       | Lexists -> f_exists_simpl
     *       | _       -> assert false in
     *
     *     try
     *       let env = Mod.add_mod_binding b env in
     *       ctor b (h_red ri env hyps f1)
     *     with NotReducible ->
     *       let f' = ctor b f1 in
     *       if f_equal f f' then raise NotReducible else f'
     *   end *)

      (* | Sym_Form_If, [p1;p2;p3] ->
       *
       * | Sym_Form_App ty, p1::pargs ->
       *
       * | Sym_Form_Tuple, pt ->
       *
       * | Sym_Form_Proj (i,ty), [p1] ->
       *
       * | Sym_Form_Match ty, p1::pargs ->
       *
       * | Sym_Form_Quant (q,bs), [p1] ->
       *
       * | Sym_Form_Let lp, [p1;p2] ->
       *
       * | Sym_Form_Pvar ty, [p1] ->
       *
       * | Sym_Form_Prog_var k1, [xp;m] ->
       *
       * | Sym_Form_Glob, [mp;m] ->
       *
       * | Sym_Form_Hoare_F, [pr1;xp1;po1] ->
       *
       * | Sym_Form_Hoare_S, [m1;pr1;s1;po1] ->
       *
       * | Sym_Form_bd_Hoare_F, [pr1;xp1;po1;cmp1;bd1] ->
       *
       * | Sym_Form_bd_Hoare_S, [m1;pr1;s1;po1;cmp1;bd1] ->
       *
       * | Sym_Form_Equiv_F, [pr1;xpl1;xpr1;po1] ->
       *
       * | Sym_Form_Equiv_S, [ml1;mr1;pr1;sl1;sr1;po1] ->
       *
       * | Sym_Form_Eager_F, [pr1;sl1;xpl1;xpr1;sr1;po1] ->
       *
       * | Sym_Form_Pr, [m1;xp1;args1;event1] ->
       *
       * | Sym_Stmt_Seq, s1 ->
       *
       * | Sym_Instr_Assign, [lv1;e1] ->
       *
       * | Sym_Instr_Call, xp1::args1 ->
       *
       * | Sym_Instr_Call_Lv, lv1::xp1::args1 ->
       *
       * | Sym_Instr_If, [cond1;st1;sf1] ->
       *
       * | Sym_Instr_While, [cond1;s1] ->
       *
       * | Sym_Instr_Assert, [cond1] ->
       *
       * | Sym_Xpath, [mp1;p1] ->
       *
       * | Sym_Mpath, mtop1::margs1 ->
       *
       * | Sym_App, op1::args1 ->
       *
       * | Sym_Quant (q1,pb1), [p1] -> *)

      (* | _ -> assert false *)
    | _ -> None
    with
    | EcEnv.NotReducible -> None

  and h_red_axiom_opt hyps ri s (a : axiom) =
    try match a with
      | Axiom_Hoarecmp _    -> None
      | Axiom_Memory m      -> h_red_mem_opt hyps ri s m
      | Axiom_MemEnv m      -> h_red_memenv_opt hyps ri s m
      | Axiom_Prog_Var pv   -> h_red_prog_var_opt hyps ri s pv
      | Axiom_Op (op,lty)   -> h_red_op_opt hyps ri s op lty
      | Axiom_Mpath_top m   -> h_red_mpath_top_opt hyps ri s m
      | Axiom_Mpath m       -> h_red_mpath_opt hyps ri s m
      | Axiom_Instr i       -> h_red_instr_opt hyps ri s i
      | Axiom_Stmt stmt     -> h_red_stmt_opt hyps ri s stmt
      | Axiom_Lvalue lv     -> h_red_lvalue_opt hyps ri s lv
      | Axiom_Xpath x       -> h_red_xpath_opt hyps ri s x
      | Axiom_Local (id,ty) -> h_red_local_opt hyps ri s id ty
      | Axiom_Form f        -> h_red_form_opt hyps ri s f
    with
    | EcEnv.NotReducible -> None

  and h_red_mem_opt _hyps ri s m : pattern option =
    if ri.delta_h m
    then
      match MName.find_opt m s.ps_patloc with
      | Some _ as p -> p
      | None -> MName.find_opt m s.ps_patloc
    else None

  and h_red_memenv_opt _hyps ri s m =
    if ri.delta_h (fst m)
    then MName.find_opt (fst m) s.ps_patloc
    else None

  and h_red_prog_var_opt hyps ri s pv =
    omap (fun x -> p_prog_var x pv.pv_kind) (h_red_xpath_opt hyps ri s pv.pv_name)

  and h_red_op_opt hyps ri _s op lty =
    if ri.delta_p op
    then Some (pat_form (EcEnv.Op.reduce (EcEnv.LDecl.toenv hyps) op lty))
    else None

  and h_red_mpath_top_opt _hyps ri s m =
    if ri.modpath
    then
      match m with
      | `Concrete _ -> None
      | `Local id -> MName.find_opt id s.ps_patloc
    else None

  and h_red_mpath_opt hyps ri s m =
    if ri.modpath
    then match h_red_mpath_top_opt hyps ri s m.m_top with
         | Some p ->
            Some (p_mpath p (List.map pat_mpath m.m_args))
         | None ->
            omap (fun l -> p_mpath (pat_mpath_top m.m_top) l)
              (h_red_args pat_mpath h_red_mpath_opt hyps ri s m.m_args)
    else None

  and h_red_instr_opt hyps ri s i =
    match i.i_node with
    | Sasgn (lv,e) -> begin
        match h_red_lvalue_opt hyps ri s lv with
        | Some lv -> Some (p_assign lv (pat_form (form_of_expr e)))
        | None ->
           omap (fun p -> Simplify.ps_assign (pat_lvalue lv) p)
             (h_red_form_opt hyps ri s (form_of_expr e))
      end
    | Srnd (lv,e) -> begin
        match h_red_lvalue_opt hyps ri s lv with
        | Some lv -> Some (p_sample lv (pat_form (form_of_expr e)))
        | None ->
           omap (fun p -> Simplify.ps_sample (pat_lvalue lv) p)
             (h_red_form_opt hyps ri s (form_of_expr e))
      end
    | Scall (olv,f,args) -> begin
        match omap (h_red_lvalue_opt hyps ri s) olv with
        | Some (Some lv) ->
           Some (Simplify.ps_call (Some lv) (pat_xpath f)
                   (List.map (fun x -> pat_form (form_of_expr x)) args))
        | Some None | None ->
        match h_red_xpath_opt hyps ri s f with
        | Some f ->
           Some (Simplify.ps_call (omap pat_lvalue olv) f
                   (List.map (fun x -> pat_form (form_of_expr x)) args))
        | None ->
           let olv = omap pat_lvalue olv in
           omap
             (fun args -> Simplify.ps_call olv (pat_xpath f) args)
             (h_red_args (fun e -> pat_form (form_of_expr e))
                (fun hyps ri s e -> h_red_form_opt hyps ri s (form_of_expr e))
                hyps ri s args)
      end
    | Sif (cond,s1,s2) -> begin
        match h_red_form_opt hyps ri s (form_of_expr cond) with
        | Some cond ->
           Some (Simplify.ps_instr_if cond (pat_stmt s1) (pat_stmt s2))
        | None ->
        match h_red_stmt_opt hyps ri s s1 with
        | Some s1 ->
           Some (Simplify.ps_instr_if (pat_form(form_of_expr cond)) s1 (pat_stmt s2))
        | None ->
           omap
             (fun s2 -> Simplify.ps_instr_if (pat_form(form_of_expr cond)) (pat_stmt s1) s2)
             (h_red_stmt_opt hyps ri s s2)
      end
    | Swhile (cond,body) -> begin
        match h_red_form_opt hyps ri s (form_of_expr cond) with
        | Some cond -> Some (Simplify.ps_while cond (pat_stmt body))
        | None ->
           omap (fun s -> Simplify.ps_while (pat_form(form_of_expr cond)) s)
             (h_red_stmt_opt hyps ri s body)
      end
    | Sassert e -> omap p_assert (h_red_form_opt hyps ri s (form_of_expr e))
    | Sabstract name ->
       if ri.delta_h name
       then MName.find_opt name s.ps_patloc
       else None

  and h_red_stmt_opt hyps ri s stmt =
    omap (fun l -> pat_fun_symbol Sym_Stmt_Seq l)
      (h_red_args pat_instr h_red_instr_opt hyps ri s stmt.s_node)

  and h_red_lvalue_opt hyps ri s = function
    | LvVar (pv,ty) ->
       omap (fun x -> Simplify.ps_lvalue_var x ty) (h_red_prog_var_opt hyps ri s pv)
    | LvTuple l ->
       omap p_lvalue_tuple
         (h_red_args (fun (pv,ty) -> pat_lvalue (LvVar(pv,ty)))
            (fun hyps ri s x -> h_red_lvalue_opt hyps ri s (LvVar x)) hyps ri s l)
    | LvMap _ -> None


  and h_red_xpath_opt hyps ri s x =
    if ri.modpath
    then match h_red_mpath_opt hyps ri s x.x_top with
         | Some p -> Some (Simplify.ps_xpath p (pat_op x.x_sub [] None))
         | None -> None
    else None

  and h_red_local_opt hyps ri s id ty =
    match reduce_local_opt hyps ri s id None (OGTty (Some ty)) with
    | Some { p_node = Pat_Axiom (Axiom_Form f)} as op ->
       if ty_equal ty f.f_ty then op else None
    | _ -> None

  and h_red_form_opt hyps ri s (f : form) =
    match EcReduction.h_red_opt ri hyps f with
    | Some f' when not (f_equal f f') -> Some (pat_form f')
    | _ ->
    match f.f_node with
    (* β-reduction *)
    | Fapp ({ f_node = Fquant (Llambda, _, _)}, _) when ri.beta ->
       begin
         try Some (pat_form (f_betared f)) with
         | _ -> None
       end

    (* ζ-reduction *)
    | Flocal x -> h_red_local_opt hyps ri s x f.f_ty

    (* ζ-reduction *)
    | Fapp ({ f_node = Flocal x ; f_ty = ty }, args) ->
       let pargs = List.map pat_form args in
       omap (fun o -> ps_app_simpl o pargs (Some f.f_ty))
         (h_red_local_opt hyps ri s x ty)

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
    | Flet (LRecord (_, ids), f1, f2) when ri.iota && is_record hyps f1 ->
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
    | Fapp ({ f_node = Fop (op, _); f_ty = ty} as f1, args)
         when ri.iota && EcEnv.Op.is_projection (EcEnv.LDecl.toenv hyps) op -> begin
        let op =
          match args with
          | [mk] -> begin
              match (odfl (pat_form mk) (h_red_form_opt hyps ri s mk)).p_node with
              | Pat_Axiom
                (Axiom_Form
                   { f_node =
                       Fapp ({ f_node = Fop (mkp, _) }, mkargs) } ) ->
                 if not (EcEnv.Op.is_record_ctor (EcEnv.LDecl.toenv hyps) mkp) then
                   None
                 else
                   let v = oget (EcEnv.Op.by_path_opt op (EcEnv.LDecl.toenv hyps)) in
                   let v = proj3_2 (EcDecl.operator_as_proj v) in
                   let v = try Some(List.nth mkargs v)
                           with _ -> None in
                   begin
                     match v with
                     | None -> None
                     | Some v -> h_red_form_opt hyps ri s v
                   end
              | Pat_Fun_Symbol
                  (Sym_Form_App _,
                   { p_node = Pat_Axiom (Axiom_Form { f_node = Fop (mkp,_)}
                                         | Axiom_Op (mkp,_))}::pargs) ->
                 if not (EcEnv.Op.is_record_ctor (EcEnv.LDecl.toenv hyps) mkp) then None
                 else
                   let v = oget (EcEnv.Op.by_path_opt op (EcEnv.LDecl.toenv hyps)) in
                   let v = proj3_2 (EcDecl.operator_as_proj v) in
                   let v = try Some(List.nth pargs v)
                           with _ -> None in
                   begin
                     match v with
                     | None -> None
                     | Some v -> h_red_pattern_opt hyps ri s v
                   end
              | _ -> None
            end
          | _ -> None
        in match op with
           | None ->
              omap (fun x -> Simplify.ps_app x (List.map pat_form args) (Some ty))
                (h_red_form_opt hyps ri s f1)
           | _ -> op
      end

    (* ι-reduction (tuples projection) *)
    | Fproj(f1, i) when ri.iota ->
       let f' = f_proj_simpl f1 i f.f_ty in
       if f_equal f f'
       then omap (fun x -> Simplify.ps_proj x i f.f_ty) (h_red_form_opt hyps ri s f1)
       else Some (pat_form f')

    (* ι-reduction (if-then-else) *)
    | Fif (f1, f2, f3) when ri.iota ->
       let f' = f_if_simpl f1 f2 f3 in
       if f_equal f f'
       then omap (fun x -> Simplify.ps_if x (pat_form f2) (pat_form f3)) (h_red_form_opt hyps ri s f1)
       else Some (pat_form f')

    (* ι-reduction (match-fix) *)
    | Fapp ({ f_node = Fop (p, tys); } as f1, fargs)
         when ri.iota && EcEnv.Op.is_fix_def (EcEnv.LDecl.toenv hyps) p -> begin

        try
          let op  = oget (EcEnv.Op.by_path_opt p (EcEnv.LDecl.toenv hyps)) in
          let fix = EcDecl.operator_as_fix op in

          if List.length fargs <> snd (fix.EcDecl.opf_struct) then
            raise EcEnv.NotReducible;

          let args  = Array.of_list (List.map pat_form fargs) in
          let myfun (opb, acc) v =
            let v = args.(v) in
            let v = odfl v (h_red_pattern_opt hyps ri s v) in

            match p_destr_app v
              (* fst_map (fun x -> x.f_node) (EcFol.destr_app v) *)
            with
            | { p_node = Pat_Axiom(Axiom_Form { f_node = Fop (p, _)})}, cargs
                 when EcEnv.Op.is_dtype_ctor (EcEnv.LDecl.toenv hyps) p -> begin
                let idx = EcEnv.Op.by_path p (EcEnv.LDecl.toenv hyps) in
                let idx = snd (EcDecl.operator_as_ctor idx) in
                match opb with
                | EcDecl.OPB_Leaf   _  -> assert false
                | EcDecl.OPB_Branch bs ->
                   ((Parray.get bs idx).EcDecl.opb_sub, cargs :: acc)
              end
            | _ -> raise EcEnv.NotReducible in
          let pargs = List.fold_left myfun
                        (fix.EcDecl.opf_branches, []) (fst fix.EcDecl.opf_struct)
          in

          let pargs, (bds, body) =
            match pargs with
            | EcDecl.OPB_Leaf (bds, body), cargs ->
               (List.rev cargs, (bds, body))
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

        with EcEnv.NotReducible ->
          omap (fun x -> Simplify.ps_app x (List.map pat_form fargs) (Some f.f_ty))
            (h_red_form_opt hyps ri s f1)
      end

    (* μ-reduction *)
    | Fglob (mp, m) when ri.modpath ->
       let f' = EcEnv.NormMp.norm_glob (EcEnv.LDecl.toenv hyps) m mp in
       if f_equal f f' then None
       else Some (pat_form f')

    (* μ-reduction *)
    | Fpvar (pv, m) when ri.modpath ->
       let pv' = EcEnv.NormMp.norm_pvar (EcEnv.LDecl.toenv hyps) pv in
       if pv_equal pv pv' then None
       else Some (Simplify.ps_pvar (pat_pv pv') f.f_ty (pat_memory m))

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
                  when EcEnv.Op.is_dtype_ctor (EcEnv.LDecl.toenv hyps) p1
                       && EcEnv.Op.is_dtype_ctor (EcEnv.LDecl.toenv hyps) p2 ->

                let idx p =
                  let idx = EcEnv.Op.by_path p (EcEnv.LDecl.toenv hyps) in
                  snd (EcDecl.operator_as_ctor idx)
                in
                if   idx p1 <> idx p2
                then Some p_false
                else Some (pat_form (f_ands (List.map2 f_eq args1 args2)))

             (* | (_, []), (_, []) ->
              *    let eq_ty1, env = eq_type f1.f_ty EcTypes.tunit env in
              *    let o =
              *      if eq_ty1
              *      then
              *        let eq_ty2, env = eq_type f2.f_ty EcTypes.tunit env in
              *        if eq_ty2
              *        then Some f_true
              *        else let _ = restore_environnement env in None
              *      else let _ = restore_environnement env in None in
              *    begin
              *      match o with
              *      | Some f -> Some (pat_form f)
              *      | None ->
              *         if   f_equal f1 f2 || is_alpha_eq hyps f1 f2
              *         then Some p_true
              *         else Some (pat_form (f_eq_simpl f1 f2))
              *    end *)

             | _ ->
                if   f_equal f1 f2 || is_alpha_eq hyps f1 f2
                then Some p_true
                else Some (pat_form (f_eq_simpl f1 f2))
           end

         | _ when ri.delta_p p ->
            omap (fun o -> ps_app_simpl o (List.map pat_form args) (Some f.f_ty))
              (h_red_op_opt hyps ri s p tys)

         | _ -> Some (pat_form f)
       in
       begin
         match f' with
         | Some { p_node = Pat_Axiom(Axiom_Form f')} ->
            if f_equal f f'
            then omap (fun l -> p_app (pat_form fo) l (Some f.f_ty))
                   (h_red_args pat_form h_red_form_opt hyps ri s args)
            else Some (pat_form f')
         | Some _ -> f'
         | None -> None
       end

    (* δ-reduction *)
    | Fop (p, tys) ->
       h_red_op_opt hyps ri s p tys

    (* δ-reduction *)
    | Fapp ({ f_node = Fop (p, tys) }, args) when ri.delta_p p ->
       omap (fun op -> ps_app_simpl op (List.map pat_form args) (Some f.f_ty))
         (h_red_op_opt hyps ri s p tys)

    (* η-reduction *)
    | Fquant (Llambda, [x, GTty _], { f_node = Fapp (fn, args) })
         when can_eta x (fn, args) ->
       Some (Simplify.ps_app (pat_form fn)
               (List.map pat_form (List.take (List.length args - 1) args))
               (Some f.f_ty))

    (* contextual rule - let *)
    | Flet (lp, f1, f2) ->
       omap (fun x -> Simplify.ps_let lp x (pat_form f2)) (h_red_form_opt hyps ri s f1)

    (* Contextual rule - application args. *)
    | Fapp (f1, args) ->
       omap (fun x -> Simplify.ps_app x (List.map pat_form args) (Some f.f_ty))
         (h_red_form_opt hyps ri s f1)

    (* Contextual rule - bindings *)
    | Fquant (Lforall as t, b, f1)
    | Fquant (Lexists as t, b, f1) when ri.logic = Some `Full -> begin
        let ctor b =
          let b = List.map (fun (id,t) -> id, ogty_of_gty t) b in
          match t with
          | Lforall -> p_forall_simpl b
          | Lexists -> p_exists_simpl b
          | _       -> assert false in

        try
          let localkind_of_binding (id,gty) =
            match gty with
            | GTty ty -> id,EcBaseLogic.LD_var (ty,None)
            | GTmodty (mt,mr) -> id,EcBaseLogic.LD_modty (mt,mr)
            | GTmem mt -> id,EcBaseLogic.LD_mem mt in
          let b' = List.map localkind_of_binding b in
          let hyps =
            List.fold_left
              (fun h (id,k) -> EcEnv.LDecl.add_local ~check_id_only:true id k h)
              hyps b' in
          omap (ctor b) (h_red_form_opt hyps ri s f1)
        with EcEnv.NotReducible ->
          let f' = ctor b (pat_form f1) in
          if (match f' with | { p_node = Pat_Axiom(Axiom_Form f')} -> f_equal f f'
                            | _ -> false)
          then None
          else Some f'
      end

    | _ -> None

  let h_red_pattern_opt h r s p = match h_red_pattern_opt h r s p with
    | None -> None
    | Some p' ->
       if p = p' then None else Some p'

  let h_red_axiom_opt h r s a = match h_red_axiom_opt h r s a with
    | None -> None
    | Some p' ->
       if pat_axiom a = p' then None else Some p'

end
