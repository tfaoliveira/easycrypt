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
  | Axiom_Int       of EcBigInt.zint
  | Axiom_Local     of ident * ty
  | Axiom_Op        of path * ty list * ty option

  | Axiom_Memory    of memory
  | Axiom_MemEnv    of memenv
  | Axiom_Prog_Var  of prog_var
  | Axiom_Mpath_top of mpath_top
  | Axiom_Mpath     of mpath
  | Axiom_Stmt      of stmt
  | Axiom_Lvalue    of lvalue
  | Axiom_Xpath     of xpath
  | Axiom_Hoarecmp  of hoarecmp

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
  | Pat_Meta_Name  of pattern option * meta_name * pbindings option
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

let rec p_equal : pattern -> pattern -> bool = (=)

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
  | { p_node = Pat_Axiom (Axiom_Op (op1, lty1, Some ty1)) },
    { f_node = Fop (op2, lty2); f_ty = ty2 } ->
     ty_equal ty1 ty2 && EcPath.p_equal op1 op2
                      && List.for_all2 ty_equal lty1 lty2
  | { p_node = Pat_Axiom (Axiom_Op (op1, lty1, None)); p_ogty = OGTty (Some ty1) },
    { f_node = Fop (op2, lty2); f_ty = ty2 } ->
     ty_equal ty1 ty2 && EcPath.p_equal op1 op2
                      && List.for_all2 ty_equal lty1 lty2
  | { p_node = Pat_Axiom (Axiom_Op (op1, lty1, _)); p_ogty = OGTty None },
    { f_node = Fop (op2, lty2) } ->
     EcPath.p_equal op1 op2 && List.for_all2 ty_equal lty1 lty2
  | _ -> false

let axiom_equal (a1 : axiom) (a2 : axiom) =
  match a1, a2 with
  | Axiom_Int z1, Axiom_Int z2 -> EcBigInt.equal z1 z2
  | Axiom_Local (id1,ty1), Axiom_Local (id2,ty2) ->
     id_equal id1 id2 && ty_equal ty1 ty2
  | Axiom_Op (op1,lty1,Some t1), Axiom_Op (op2,lty2,Some t2) ->
     EcPath.p_equal op1 op2 && List.for_all2 ty_equal (t1::lty1) (t2::lty2)
  | Axiom_Op (op1,lty1,_), Axiom_Op (op2,lty2,_) ->
     EcPath.p_equal op1 op2 && List.for_all2 ty_equal lty1 lty2
  | Axiom_Memory m1, Axiom_Memory m2 -> EcMemory.mem_equal m1 m2
  | Axiom_MemEnv m1, Axiom_MemEnv m2 -> EcMemory.me_equal m1 m2
  | Axiom_Prog_Var pv1, Axiom_Prog_Var pv2 -> pv_equal pv1 pv2
  | Axiom_Mpath_top mt1, Axiom_Mpath_top mt2 ->
     EcPath.mt_equal mt1 mt2
  | Axiom_Mpath m1, Axiom_Mpath m2 -> EcPath.m_equal m1 m2
  | Axiom_Stmt s1, Axiom_Stmt s2 -> s_equal s1 s2
  | Axiom_Lvalue lv1, Axiom_Lvalue lv2 -> lv_equal lv1 lv2
  | Axiom_Xpath xp1, Axiom_Xpath xp2 -> x_equal xp1 xp2
  | Axiom_Hoarecmp cmp1, Axiom_Hoarecmp cmp2 -> cmp1 = cmp2
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

let pat_int z       = mk_pattern (Pat_Axiom (Axiom_Int z))         (OGTty (Some tint))
let pat_memory m    = mk_pattern (Pat_Axiom (Axiom_Memory m))      (OGTmem None)
let pat_memenv m    = mk_pattern (Pat_Axiom (Axiom_MemEnv m))      (OGTmem (Some (snd m)))
let pat_mpath m     = mk_pattern (Pat_Axiom (Axiom_Mpath m))       (OGTmodty None)
let pat_mpath_top m = mk_pattern (Pat_Axiom (Axiom_Mpath_top m))   (OGTmodty None)
let pat_xpath x     = mk_pattern (Pat_Axiom (Axiom_Xpath x))       OGTxpath
let pat_op op lty o = mk_pattern (Pat_Axiom (Axiom_Op (op,lty,o))) (OGTty o)
let pat_lvalue lv   = mk_pattern (Pat_Axiom (Axiom_Lvalue lv))     OGTlv
let pat_stmt s      = mk_pattern (Pat_Axiom (Axiom_Stmt s))        OGTstmt
let pat_local id ty = mk_pattern (Pat_Axiom (Axiom_Local (id,ty))) (OGTty (Some ty))
let pat_cmp cmp     = mk_pattern (Pat_Axiom (Axiom_Hoarecmp cmp))  OGThcmp
let pat_pv pv       = mk_pattern (Pat_Axiom (Axiom_Prog_Var pv))   OGTpv

let axiom_mpath m   = Axiom_Mpath m

let pat_meta p name ob =
  mk_pattern (Pat_Meta_Name (Some p,name,ob)) p.p_ogty

let meta_var name ob ogty =
  mk_pattern (Pat_Meta_Name (None, name, ob)) ogty


let pat_axiom x = match x with
  | Axiom_Int       z      -> pat_int z
  | Axiom_Memory    m      -> pat_memory m
  | Axiom_MemEnv    m      -> pat_memenv m
  | Axiom_Prog_Var  pv     -> pat_pv pv
  | Axiom_Op      (op,l,o) -> pat_op op l o
  | Axiom_Mpath_top mt     -> pat_mpath_top mt
  | Axiom_Mpath     m      -> pat_mpath m
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

let rec parrow (b : pbindings) (o : ogty) = match o with
  | OGTty (Some ty) -> begin
      match b with
      | [] -> OGTty (Some ty)
      | (_, ogty) :: b ->
         match ogty with
         | OGTty (Some t1) -> parrow b (OGTty (Some (tfun t1 ty)))
         | OGTty None      -> OGTty None
         | _ -> OGTany
    end
  | OGTty None -> OGTty None
  | _ -> OGTany



let parrow args t = parrow (List.rev args) t

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
  | Sym_Quant (Llambda, b),[p]-> mk_pattern (Pat_Fun_Symbol(s,lp)) (parrow b p.p_ogty)
  | _ -> assert false


(* -------------------------------------------------------------------------- *)

let p_destr_app p = match p.p_node with
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
    | Pat_Meta_Name (p,n,_) ->
       let map = pat_add_fv map n in
       odfl map (omap (aux map) p)
    | Pat_Sub p -> aux map p
    | Pat_Or lp -> List.fold_left aux map lp
    | Pat_Red_Strat (p,_) -> aux map p
    | Pat_Fun_Symbol (Sym_Quant (_,b),lp) ->
       let map = List.fold_left aux Mid.empty lp in
       Mid.filter (fun x _ -> List.exists (fun (y,_) -> id_equal x y) b) map
    | Pat_Fun_Symbol (_,lp) -> List.fold_left aux map lp
    | Pat_Axiom a ->
       match a with
       | Axiom_Int _ -> map
       | Axiom_Memory m -> pat_add_fv map m
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
  else mk_pattern (Pat_Fun_Symbol(Sym_Mpath,p::args)) (OGTmodty None)

let p_xpath (p : pattern) (f : pattern) =
  pat_fun_symbol Sym_Xpath [p;f]

let p_prog_var (p : pattern) (k : pvar_kind) =
  pat_fun_symbol (Sym_Form_Prog_var k) [p]

let p_lvalue_var (p : pattern) (ty : ty) =
  match p.p_node with
  | Pat_Axiom(Axiom_Prog_Var pv) -> pat_lvalue (LvVar(pv,ty))
  | p -> (* FIXME *) mk_pattern p (OGTty (Some ty))

let p_lvalue_tuple (p : pattern list) =
  mk_pattern (Pat_Fun_Symbol(Sym_Form_Tuple,p)) OGTlv

let p_pvar (pv : pattern) (ty : ty) (m : pattern) =
  pat_fun_symbol (Sym_Form_Pvar ty) [pv;m]

let p_glob (mp : pattern) (m : pattern) =
  pat_fun_symbol Sym_Form_Glob [mp;m]

let p_if (p1 : pattern) (p2 : pattern) (p3 : pattern) =
  pat_fun_symbol Sym_Form_If [p1;p2;p3]

let p_match (p : pattern) (ty : ty) (lp : pattern list) =
  pat_fun_symbol (Sym_Form_Match ty) (p::lp)

let p_tuple (lp : pattern list) =
  pat_fun_symbol Sym_Form_Tuple lp

let p_proj (p1 : pattern) (i : int) (ty : ty) =
  pat_fun_symbol (Sym_Form_Proj (i,ty)) [p1]

let p_let (l : lpattern) (p1 : pattern) (p2 : pattern) =
  pat_fun_symbol (Sym_Form_Let l) [p1;p2]

let is_higher_order (p : pattern) = match p.p_node with
  | Pat_Meta_Name (None, _, _) -> true
  | _ -> false

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
  mk_pattern (Pat_Fun_Symbol(Sym_Stmt_Seq,lp)) OGTstmt

let p_var_form x ty = let t = OGTty (Some ty) in meta_var x None t

let p_assign (plv : pattern) (pe : pattern) =
  pat_fun_symbol Sym_Instr_Assign [plv;pe]

let p_sample (plv : pattern) (pe : pattern) =
  pat_fun_symbol Sym_Instr_Sample [plv;pe]

let p_call (olv : pattern option) (f : pattern) (args : pattern list) =
  match olv, f.p_node with
  | None   ,_ -> pat_fun_symbol Sym_Instr_Call        (f::args)
  | Some lv,_ -> pat_fun_symbol Sym_Instr_Call_Lv (lv::f::args)

let p_instr_if (pcond : pattern) (ps1 : pattern) (ps2 : pattern) =
  pat_fun_symbol Sym_Instr_If [pcond;ps1;ps2]

let p_while (pcond : pattern) (ps : pattern) =
  pat_fun_symbol Sym_Instr_While [pcond;ps]

let p_assert (p : pattern) =
  pat_fun_symbol Sym_Instr_Assert [p]


let p_hoareF (pr : pattern) (f : pattern) (po : pattern) =
  pat_fun_symbol Sym_Form_Hoare_F [pr;f;po]

let p_hoareS (m : pattern) (pr : pattern) (s : pattern) (po : pattern) =
  pat_fun_symbol Sym_Form_Hoare_S [m;pr;s;po]

let p_bdHoareF (pr : pattern) (f : pattern) (po : pattern) (cmp : pattern)
      (bd : pattern) =
  pat_fun_symbol Sym_Form_bd_Hoare_F [pr;f;po;cmp;bd]

let p_bdHoareS (m : pattern) (pr : pattern) (s : pattern) (po : pattern)
      (cmp : pattern) (bd : pattern) =
  pat_fun_symbol Sym_Form_bd_Hoare_S [m;pr;s;po;cmp;bd]

let p_equivF (pr : pattern) (fl : pattern) (fr : pattern) (po : pattern) =
  pat_fun_symbol Sym_Form_Equiv_F [pr;fl;fr;po]

let p_equivS (ml : pattern) (mr : pattern) (pr : pattern) (sl : pattern)
      (sr : pattern) (po : pattern) =
  pat_fun_symbol Sym_Form_Equiv_S [ml;mr;pr;sl;sr;po]

let p_eagerF (pr : pattern) (sl : pattern) (fl : pattern)
      (fr : pattern) (sr : pattern) (po : pattern) =
  pat_fun_symbol Sym_Form_Eager_F [pr;sl;fl;fr;sr;po]

let p_pr (pm : pattern) (pf : pattern) (pargs : pattern) (pevent : pattern) =
  pat_fun_symbol Sym_Form_Pr [pm;pf;pargs;pevent]

let rec pat_form f = match f.f_node with
  | Fint z -> pat_int z
  | Flocal id -> pat_local id f.f_ty
  | Fop (op,lty) -> pat_op op lty (Some f.f_ty)
  | Fquant (q,b,f1) -> p_quant q (List.map (snd_map ogty_of_gty) b) (pat_form f1)
  | Fif (f1,f2,f3) -> p_if (pat_form f1) (pat_form f2) (pat_form f3)
  | Fmatch (f1,fs,ty) -> p_match (pat_form f1) ty (List.map pat_form fs)
  | Flet (lp,f1,f2) -> p_let lp (pat_form f1) (pat_form f2)
  | Fpvar (pv,mem) -> p_pvar (pat_pv pv) f.f_ty (pat_memory mem)
  | Fglob (m,mem) -> p_glob (pat_mpath m) (pat_memory mem)
  | Fapp (op,args) -> p_app (pat_form op) (List.map pat_form args) (Some f.f_ty)
  | Ftuple t -> p_tuple (List.map pat_form t)
  | Fproj (f1,i) -> p_proj (pat_form f1) i f.f_ty
  | FhoareF h ->
     p_hoareF (pat_form h.hf_pr) (pat_xpath h.hf_f) (pat_form h.hf_po)
  | FhoareS h ->
     p_hoareS (pat_memenv h.hs_m) (pat_form h.hs_pr) (pat_stmt h.hs_s)
       (pat_form h.hs_po)
  | FbdHoareF h ->
     p_bdHoareF (pat_form h.bhf_pr) (pat_xpath h.bhf_f) (pat_form h.bhf_po)
       (pat_cmp h.bhf_cmp) (pat_form h.bhf_bd)
  | FbdHoareS h ->
     p_bdHoareS (pat_memenv h.bhs_m) (pat_form h.bhs_pr) (pat_stmt h.bhs_s)
       (pat_form h.bhs_po) (pat_cmp h.bhs_cmp) (pat_form h.bhs_bd)
  | FequivF h ->
     p_equivF (pat_form h.ef_pr) (pat_xpath h.ef_fl) (pat_xpath h.ef_fr)
       (pat_form h.ef_po)
  | FequivS h ->
     p_equivS (pat_memenv h.es_ml) (pat_memenv h.es_mr) (pat_form h.es_pr)
       (pat_stmt h.es_sl) (pat_stmt h.es_sr) (pat_form h.es_po)
  | FeagerF h ->
     p_eagerF (pat_form h.eg_pr) (pat_stmt h.eg_sl) (pat_xpath h.eg_fl)
       (pat_xpath h.eg_fr) (pat_stmt h.eg_sr) (pat_form h.eg_po)
  | Fpr h ->
     p_pr (pat_memory h.pr_mem) (pat_xpath h.pr_fun) (pat_form h.pr_args)
       (pat_form h.pr_event)

let pat_instr i = match i.i_node with
  | Sasgn (lv, e) -> p_assign (pat_lvalue lv) (pat_form (form_of_expr e))
  | Srnd  (lv, e) -> p_sample (pat_lvalue lv) (pat_form (form_of_expr e))
  | Scall (olv, f, args) -> p_call (omap pat_lvalue olv) (pat_xpath f)
                              (List.map (fun e -> pat_form (form_of_expr e)) args)
  | Sif (e, s1, s2) -> p_instr_if (pat_form (form_of_expr e))
                         (pat_stmt s1) (pat_stmt s2)
  | Swhile (e, s) -> p_while (pat_form (form_of_expr e)) (pat_stmt s)
  | Sassert e -> p_assert (pat_form (form_of_expr e))
  | Sabstract id -> meta_var id None OGTinstr

(* -------------------------------------------------------------------------- *)
let lv_ty (f_ty : ty -> ty) = function
  | LvVar (pv,ty) -> LvVar (pv,f_ty ty)
  | LvTuple l -> LvTuple (List.map (fun (x,ty)->(x,f_ty ty)) l)
  | LvMap ((op,lty),pv,e,ty) ->
     LvMap ((op,List.map f_ty lty),pv,e_map f_ty (fun x->x) e,f_ty ty)


let p_fold_map (f : 'a -> pattern -> 'a * pattern) (a : 'a) (p : pattern) : 'a * pattern =
  match p.p_node with
  | Pat_Meta_Name (None,_,_) -> a, p
  | Pat_Meta_Name (Some p,n,ob) ->
     let a, p = f a p in a, pat_meta p n ob
  | Pat_Sub p ->
     let a, p = f a p in a, mk_pattern (Pat_Sub p) OGTany
  | Pat_Or lp ->
     let a, lp = List.fold_left_map f a lp in a, mk_pattern (Pat_Or lp) OGTany
  | Pat_Red_Strat (p, red) ->
     let a, p = f a p in a, mk_pattern (Pat_Red_Strat (p, red)) p.p_ogty
  | Pat_Fun_Symbol (s, lp) ->
     let a, lp = List.fold_left_map f a lp in a, pat_fun_symbol s lp
  | Pat_Axiom axiom ->
     match axiom with
     | Axiom_Int _ -> a, p
     | Axiom_Stmt s ->
        let a, s = List.fold_left_map f a (List.map pat_instr s.s_node) in
        a, p_stmt s
     | Axiom_Lvalue lv -> begin
         match lv with
         | LvVar (pv,ty) ->
            let a, p = f a (pat_pv pv) in a, p_lvalue_var p ty
         | LvTuple t ->
            let a, t =
              List.fold_left_map f a
                (List.map (fun (pv,ty) -> pat_lvalue (LvVar (pv,ty))) t) in
            a, p_lvalue_tuple t
         | LvMap _ -> a, p
       end
     | Axiom_Prog_Var pv ->
        let a, p = f a (pat_xpath pv.pv_name) in
        a, p_prog_var p pv.pv_kind
     | Axiom_Xpath xp ->
        let a, p = f a (pat_mpath xp.x_top) in
        a, p_xpath p (pat_op xp.x_sub [] None)
     | Axiom_Mpath mp ->
        let a, m = f a (pat_mpath_top mp.m_top) in
        let a, margs = List.fold_left_map f a (List.map pat_mpath mp.m_args) in
        a, p_mpath m margs
     | Axiom_Op _ | Axiom_Local _ | Axiom_Memory _ | Axiom_MemEnv _
       | Axiom_Mpath_top _ | Axiom_Hoarecmp _ -> a, p

let p_map (f : pattern -> pattern) (p : pattern) : pattern =
  snd (p_fold_map (fun () p -> (), f p) () p)

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

  let p_bind_ogty (s : p_subst) (nfrom : ident) (nto : ident) (ogty : ogty) =
    match gty_of_ogty ogty with
    | Some (GTty ty)       -> p_bind_rename s nfrom nto ty
    | Some (GTmem _)       -> p_bind_mem s nfrom nto
    | Some (GTmodty (_,_)) -> p_bind_mod s nfrom (mpath (`Local nto) [])
    | _ ->
       let merge o = assert (o = None); Some (meta_var nto None ogty) in
       { s with ps_patloc = Mid.change merge nfrom s.ps_patloc }

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
      | Pat_Sub p -> mk_pattern (Pat_Sub (p_subst s p)) p.p_ogty
      | Pat_Or lp -> mk_pattern (Pat_Or (List.map (p_subst s) lp)) p.p_ogty
      | Pat_Red_Strat (p,f) ->
         let p = p_subst s p in mk_pattern (Pat_Red_Strat (p,f)) p.p_ogty
      | Pat_Meta_Name (op,name,ob) -> begin
          match Mid.find_opt name s.ps_patloc with
          | Some p -> p
          | None ->
          match op with
          | None -> meta_var name ob p.p_ogty
          | Some p -> let p = p_subst s p in pat_meta p name ob
        end
      | Pat_Axiom a -> begin
          match a with
          | Axiom_Int _ -> p
          | Axiom_Mpath_top mtop -> mtop_subst s mtop
          | Axiom_Mpath m -> mp_subst s m
          | Axiom_Xpath xp -> xp_subst s xp
          | Axiom_Memory m -> mem_subst s m
          | Axiom_MemEnv m -> memenv_subst s m
          | Axiom_Prog_Var pv -> pv_subst s pv
          | Axiom_Op (op,lty,ot) ->
             let ot = omap (ty_subst s.ps_sty) ot in
             let lty = List.Smart.map (ty_subst s.ps_sty) lty in
             let oty = match ot, p.p_ogty with
               | Some _, _ -> ot
               | None, OGTty (Some ty) -> Some (ty_subst s.ps_sty ty)
               | _ -> None in
             pat_op op lty oty
          | Axiom_Stmt st -> stmt_subst s st
          | Axiom_Lvalue lv -> lv_subst s lv
          | Axiom_Hoarecmp _ -> p
          | Axiom_Local (id,_) -> odfl p (Mid.find_opt id s.ps_patloc)
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
          | Sym_Form_If, _         -> assert false
          | Sym_Form_App _, _      -> assert false
          | Sym_Form_Proj _, _     -> assert false
          | Sym_Form_Match _, _    -> assert false
          | Sym_Form_Let _, _      -> assert false
          | Sym_Form_Pvar _, _     -> assert false
          | Sym_Form_Prog_var _, _ -> assert false
          | Sym_Form_Glob, _       -> assert false
          | Sym_Form_Hoare_F, _    -> assert false
          | Sym_Form_Hoare_S, _    -> assert false
          | Sym_Form_bd_Hoare_F, _ -> assert false
          | Sym_Form_bd_Hoare_S, _ -> assert false
          | Sym_Form_Equiv_F, _    -> assert false
          | Sym_Form_Equiv_S, _    -> assert false
          | Sym_Form_Eager_F, _    -> assert false
          | Sym_Form_Pr, _         -> assert false
          | Sym_Instr_Assign, _    -> assert false
          | Sym_Instr_Sample, _    -> assert false
          | Sym_Instr_Call, _      -> assert false
          | Sym_Instr_Call_Lv, _   -> assert false
          | Sym_Instr_If, _        -> assert false
          | Sym_Instr_While, _     -> assert false
          | Sym_Instr_Assert, _    -> assert false
          | Sym_Xpath, _           -> assert false
          | Sym_Mpath, _           -> assert false
          | Sym_Quant _, _         -> assert false
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
      | Pat_Meta_Name (None,_,_) -> None
      | Pat_Meta_Name (Some p,n,ob) ->
         omap (fun p -> pat_meta p n ob) (p_betared_opt p)
      | Pat_Sub p ->
         omap (fun p -> mk_pattern (Pat_Sub p) p.p_ogty) (p_betared_opt p)
      | Pat_Or [p] -> p_betared_opt p
      | Pat_Or _ -> None
      | Pat_Red_Strat (p,f) ->
         omap (fun p -> mk_pattern (Pat_Red_Strat (p,f)) p.p_ogty) (p_betared_opt p)
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
  | { p_node = Pat_Axiom(Axiom_Op (op,[],ty)) } ->
     EcPath.p_equal op EcCoreLib.CI_Bool.p_true
     && odfl true (omap (ty_equal tbool) ty)
  | _ -> false

let p_is_false = function
  | { p_node = Pat_Axiom(Axiom_Op (op,[],ty)) } ->
     EcPath.p_equal op EcCoreLib.CI_Bool.p_false
     && odfl true (omap (ty_equal tbool) ty)
  | _ -> false

let p_bool_val p =
  if p_is_true p then Some true
  else if p_is_false p then Some false
  else None

let p_eq (p1 : pattern) (p2 : pattern) =
  match p1.p_ogty, p2.p_ogty with
  | OGTty (Some t1), _
    | _, OGTty (Some t1) -> p_app (pop_eq t1) [p1;p2] (Some t1)
  | _ -> p_app (pop_eq tbool) [p1;p2] None

let p_not p = p_app (pat_form EcFol.fop_not) [p] (Some EcTypes.tbool)

let p_imp (p1 : pattern) (p2 : pattern) =
  p_app (pat_form EcFol.fop_imp) [p1;p2] (Some EcTypes.tbool)

let p_anda (p1 : pattern) (p2 : pattern) =
  p_app (pat_form EcFol.fop_anda) [p1;p2] (Some EcTypes.tbool)

let p_ora (p1 : pattern) (p2 : pattern) =
  p_app (pat_form EcFol.fop_ora) [p1;p2] (Some EcTypes.tbool)

let p_iff (p1 : pattern) (p2 : pattern) =
  p_app (pat_form EcFol.fop_iff) [p1;p2] (Some EcTypes.tbool)

let p_and (p1 : pattern) (p2 : pattern) =
  p_app (pat_form EcFol.fop_and) [p1;p2] (Some EcTypes.tbool)

let p_or (p1 : pattern) (p2 : pattern) =
  p_app (pat_form EcFol.fop_or) [p1;p2] (Some EcTypes.tbool)

let p_ands (ps : pattern list) = match List.rev ps with
  | [] -> p_true
  | p::ps -> List.fold_left ((^~) p_and) p ps

(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
 (* CORELIB *)
let pop_real_mul    = pat_form fop_real_mul
let pop_real_inv    = pat_form fop_real_inv
let pop_real_of_int = pat_form fop_real_of_int

let p_int (i : EcBigInt.zint) = pat_int i


let p_real_of_int p  = p_app pop_real_of_int [p] (Some treal)
let p_rint n         = p_real_of_int (p_int n)

let p_i0 = pat_form f_i0
let p_i1 = pat_form f_i1

let p_r0 = pat_form f_r0
let p_r1 = pat_form f_r1

let p_destr_int (p : pattern) = match p.p_node with
  | Pat_Axiom (Axiom_Int x) -> x
  | _ ->
  match p_destr_app p with
  | op, [{ p_node = Pat_Axiom (Axiom_Int x) }]
       when op_equal op fop_int_opp -> EcBigInt.neg x
  | _ -> destr_error "p_destr_int"

let p_destr_rint p =
  match p_destr_app p with
  | op, [p1] when op_equal op fop_real_of_int ->
     begin
       try p_destr_int p1
       with DestrError _ -> destr_error "destr_rint"
     end
  | _ -> destr_error "destr_rint"

let p_int_le (p1 : pattern) (p2 : pattern) =
  p_app (pat_form fop_int_le) [p1;p2] (Some EcTypes.tbool)

let p_int_lt (p1 : pattern) (p2 : pattern) =
  p_app (pat_form fop_int_lt) [p1;p2] (Some EcTypes.tbool)

let p_int_add (p1 : pattern) (p2 : pattern) =
  p_app (pat_form fop_int_add) [p1;p2] (Some EcTypes.tint)

let p_int_opp (p : pattern) =
  p_app (pat_form fop_int_opp) [p] (Some EcTypes.tint)

let p_int_mul (p1 : pattern) (p2 : pattern) =
  p_app (pat_form fop_int_mul) [p1;p2] (Some EcTypes.tint)



let get_real_of_int (p : pattern) =
  try Some (p_destr_rint p) with DestrError _ -> None

let p_real_le (p1 : pattern) (p2 : pattern) =
  p_app (pat_form fop_real_le) [p1;p2] (Some EcTypes.tbool)

let p_real_lt (p1 : pattern) (p2 : pattern) =
  p_app (pat_form fop_real_lt) [p1;p2] (Some EcTypes.tbool)

let p_real_add (p1 : pattern) (p2 : pattern) =
  p_app (pat_form fop_real_add) [p1;p2] (Some EcTypes.treal)

let p_real_opp (p : pattern) =
  p_app (pat_form fop_real_opp) [p] (Some EcTypes.treal)

let p_real_mul (p1 : pattern) (p2 : pattern) =
  p_app (pat_form fop_real_mul) [p1;p2] (Some EcTypes.treal)

let p_real_inv (p : pattern) =
  p_app (pat_form fop_real_inv) [p] (Some EcTypes.treal)

let p_real_div (p1 : pattern) (p2 : pattern) =
  p_real_mul p1 (p_real_inv p2)

(* -------------------------------------------------------------------------- *)
let p_is_not = function
  | { p_node = Pat_Axiom(Axiom_Op (op,[],ot)) } ->
     EcPath.p_equal op EcCoreLib.CI_Bool.p_not
     && odfl true (omap (ty_equal (toarrow [tbool] tbool)) ot)
  | _ -> false

let p_destr_not p = match p_destr_app p with
  | op, [p1] when p_is_not op -> p1
  | _ -> assert false

(* -------------------------------------------------------------------------- *)
let p_not_simpl_opt (p : pattern) =
  if p_is_not p then Some (p_destr_not p)
  else if p_is_true p then Some p_false
  else if p_is_false p then Some p_true
  else None

let p_not_simpl p = odfl (p_not p) (p_not_simpl_opt p)

let p_imp_simpl_opt (p1 : pattern) (p2 : pattern) =
  match p_bool_val p1, p_bool_val p2 with
  | Some true, _ -> Some p2
  | Some false, _ | _, Some true -> Some p_true
  | _, Some false -> Some (p_not_simpl p1)
  | _ -> if p_equal p1 p2 then Some p_true
         else None

let p_imp_simpl p1 p2 = odfl (p_imp p1 p2) (p_imp_simpl_opt p1 p2)

let p_anda_simpl_opt (p1 : pattern) (p2 : pattern) =
  match p_bool_val p1, p_bool_val p2 with
  | Some true , _          -> Some p2
  | Some false, _          -> Some p_false
  | _         , Some true  -> Some p1
  | _         , Some false -> Some p_false
  | _                      -> None

let p_anda_simpl p1 p2 = odfl (p_anda p1 p2) (p_anda_simpl_opt p1 p2)

let p_ora_simpl_opt (p1 : pattern) (p2 : pattern) =
  match p_bool_val p1, p_bool_val p2 with
  | Some true , _          -> Some p_true
  | Some false, _          -> Some p2
  | _         , Some true  -> Some p_true
  | _         , Some false -> Some p1
  | _                      -> None

let p_ora_simpl p1 p2 = odfl (p_ora p1 p2) (p_ora_simpl_opt p1 p2)

let rec p_iff_simpl_opt (p1 : pattern) (p2 : pattern) =
  if p_equal  p1 p2 then Some p_true
  else
  match p_bool_val p1, p_bool_val p2 with
  | Some true , _          -> Some p2
  | Some false, _          -> Some (p_not_simpl p2)
  | _         , Some true  -> Some p1
  | _         , Some false -> Some (p_not_simpl p1)
  | _ ->
  match p_destr_app p1, p_destr_app p2 with
  | (op1, [p1]), (op2, [p2])
       when (op_equal op1 fop_not && op_equal op2 fop_not) ->
     Some (p_iff_simpl p1 p2)
  | _ -> None

and p_iff_simpl (p1 : pattern) (p2 : pattern) =
  match p_iff_simpl_opt p1 p2 with
  | Some p -> p
  | None -> p_iff p1 p2

let p_and_simpl_opt (p1 : pattern) (p2 : pattern) =
  match p_bool_val p1, p_bool_val p2 with
  | Some false, _ | _, Some false -> Some p_false
  | Some true, _ -> Some p2
  | _, Some true -> Some p1
  | _ -> None

let p_and_simpl p1 p2 = odfl (p_and p1 p2) (p_and_simpl_opt p1 p2)

let p_or_simpl_opt (p1 : pattern) (p2 : pattern) =
  match p_bool_val p1, p_bool_val p2 with
  | Some true, _ | _, Some true -> Some p_true
  | Some false, _ -> Some p2
  | _, Some false -> Some p1
  | _ -> None

let p_or_simpl p1 p2 = odfl (p_or p1 p2) (p_or_simpl_opt p1 p2)

let p_andas_simpl = List.fold_right p_anda_simpl

let rec p_eq_simpl_opt (p1 : pattern) (p2 : pattern) =
  if p_equal p1 p2 then Some p_true
  else match p1.p_node, p2.p_node with
  | Pat_Axiom (Axiom_Int _), Pat_Axiom (Axiom_Int _) -> Some p_false

  | Pat_Axiom (Axiom_Op (op1, [], _) ),
    Pat_Axiom (Axiom_Op (op2, [], _) )
       when
         (EcPath.p_equal op1 EcCoreLib.CI_Bool.p_true  &&
          EcPath.p_equal op2 EcCoreLib.CI_Bool.p_false  )
      || (EcPath.p_equal op2 EcCoreLib.CI_Bool.p_true  &&
          EcPath.p_equal op1 EcCoreLib.CI_Bool.p_false  )
    -> Some p_false

  | Pat_Fun_Symbol (Sym_Form_App _, [op1; { p_node = Pat_Axiom (Axiom_Int _)}]),
    Pat_Fun_Symbol (Sym_Form_App _, [op2; { p_node = Pat_Axiom (Axiom_Int _)}])
      when op_equal op1 fop_real_of_int && op_equal op2 fop_real_of_int
    -> Some p_false

  | Pat_Fun_Symbol (Sym_Form_Tuple, l1), Pat_Fun_Symbol (Sym_Form_Tuple, l2)
       when List.length l1 = List.length l2 ->
      Some
        (p_andas_simpl
           (List.map2 (fun x y -> p_eq_simpl x y) l1 l2) p_true)

  | _ -> None

and p_eq_simpl p1 p2 = odfl (p_eq p1 p2) (p_eq_simpl_opt p1 p2)


(* -------------------------------------------------------------------------- *)
let p_int_le_simpl_opt (p1 : pattern) (p2 : pattern) =
  if p_equal p1 p2 then Some p_true
  else
    try Some (pat_form (f_bool (EcBigInt.compare (p_destr_int p1) (p_destr_int p2) <= 0)))
    with DestrError _ -> None

let p_int_le_simpl p1 p2 = odfl (p_int_le p1 p2) (p_int_le_simpl_opt p1 p2)

let p_int_lt_simpl_opt (p1 : pattern) (p2 : pattern) =
  if p_equal p1 p2 then Some p_true
  else
    try Some (pat_form (f_bool (EcBigInt.compare (p_destr_int p1) (p_destr_int p2) < 0)))
    with DestrError _ -> None

let p_int_lt_simpl p1 p2 = odfl (p_int_lt p1 p2) (p_int_lt_simpl_opt p1 p2)

let p_int_opp_simpl_opt (p : pattern) =
  match p_destr_app p with
  | op, [p] when op_equal op fop_int_opp -> Some p
  | _ -> if p_equal p_i0 p then Some p_i0 else None

let p_int_opp_simpl p = odfl (p_int_opp p) (p_int_opp_simpl_opt p)

let p_int_add_simpl_opt =
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
    | Some i1, Some i2 -> Some (p_int (EcBigInt.add i1 i2))

    | Some i1, _ when EcBigInt.equal i1 EcBigInt.zero -> Some p2
    | _, Some i2 when EcBigInt.equal i2 EcBigInt.zero -> Some p1

    | _, _ ->
        let simpls = [
           (fun () -> try_add_opp p1 p2);
           (fun () -> try_add_opp p2 p1);
           (fun () -> i1 |> obind (try_addc^~ p2));
           (fun () -> i2 |> obind (try_addc^~ p1));
        ] in

        ofdfl
          (fun () -> None)
          (List.Exceptionless.find_map (fun f -> Some (f ())) simpls)

let p_int_add_simpl p1 p2 = odfl (p_int_add p1 p2) (p_int_add_simpl_opt p1 p2)

let p_int_mul_simpl_opt (p1 : pattern) (p2 : pattern) =
  try  Some (p_int (EcBigInt.mul (p_destr_int p1) (p_destr_int p2)))
  with DestrError _ ->
    if p_equal p_i0 p1 || p_equal p_i0 p2 then Some p_i0
    else if p_equal p_i1 p1 then Some p2
    else if p_equal p_i1 p2 then Some p1
    else None

let p_int_mul_simpl p1 p2 = odfl (p_int_mul p1 p2) (p_int_mul_simpl_opt p1 p2)

(* -------------------------------------------------------------------- *)
let p_real_le_simpl_opt (p1 : pattern) (p2 : pattern) =
  if p_equal p1 p2 then Some p_true else
    match get_real_of_int p1, get_real_of_int p2 with
    | Some x1, Some x2 -> Some (pat_form (f_bool (EcBigInt.compare x1 x2 <= 0)))
    | _ -> None

let p_real_le_simpl p1 p2 = odfl (p_real_le p1 p2) (p_real_le_simpl_opt p1 p2)

let p_real_lt_simpl_opt (p1 : pattern) (p2 : pattern) =
  if p_equal p1 p2 then Some p_true else
    match get_real_of_int p1, get_real_of_int p2 with
    | Some x1, Some x2 -> Some (pat_form (f_bool (EcBigInt.compare x1 x2 < 0)))
    | _ -> None

let p_real_lt_simpl p1 p2 = odfl (p_real_lt p1 p2) (p_real_lt_simpl_opt p1 p2)

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

let rec p_real_split p = match p_destr_app p with
  | op, [p1;p2] when op_equal op fop_real_mul -> begin
      match p_destr_app p1, p_destr_app p2 with
      | _         , (op, [p2]) when op_equal op fop_real_inv -> (p1, p2)
      | (op, [p1]), _          when op_equal op fop_real_inv -> (p2, p1)
      | _                                                    -> (p, p_r1)
    end
  | op, [p1] when op_equal op fop_real_inv -> (p_r1, p1)
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

let p_real_add_simpl_opt (p1 : pattern) (p2 : pattern) =
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
  | Some i1, Some i2 -> Some (p_rint (BI.add i1 i2))

  | Some i1, _ when BI.equal i1 BI.zero -> Some p2
  | _, Some i2 when BI.equal i2 BI.zero -> Some p1

  | _ ->
     let simpls = [
         (fun () -> try_norm_rintdiv p1 p2);
         (fun () -> try_add_opp p1 p2);
         (fun () -> try_add_opp p2 p1);
         (fun () -> r1 |> obind (try_addc^~ p2));
         (fun () -> r2 |> obind (try_addc^~ p1));
       ] in

     ofdfl
       (fun () -> None)
       (List.Exceptionless.find_map (fun f -> Some (f ())) simpls)

let p_real_opp_simpl_opt (p : pattern) =
  match p_destr_app p with
  | op, [p] when op_equal op fop_real_opp -> Some p
  | _ -> None

let p_real_is_zero p =
  try  EcBigInt.equal EcBigInt.zero (p_destr_rint p)
  with DestrError _ -> false

let p_real_is_one p =
  try  EcBigInt.equal EcBigInt.one (p_destr_rint p)
  with DestrError _ -> false


let rec p_real_mul_simpl_opt p1 p2 =
  let (n1, d1) = p_real_split p1 in
  let (n2, d2) = p_real_split p2 in

  p_real_div_simpl_r_opt
    (p_real_mul_simpl_r n1 n2)
    (p_real_mul_simpl_r d1 d2)
    n1 n2 d1 d2

and p_real_div_simpl_opt p1 p2 =
  let (n1, d1) = p_real_split p1 in
  let (n2, d2) = p_real_split p2 in

  p_real_div_simpl_r_opt
    (p_real_mul_simpl_r n1 d2)
    (p_real_mul_simpl_r d1 n2)
    n1 d2 d1 n2

and p_real_mul_simpl_r p1 p2 =
  if p_real_is_zero p1 || p_real_is_zero p2 then Some p_r0 else

  if p_real_is_one p1 then Some p2 else
  if p_real_is_one p2 then Some p1 else

  try
    Some (p_rint (EcBigInt.Notations.( *^ ) (p_destr_rint p1) (p_destr_rint p2)))
  with DestrError _ -> None

and p_real_div_simpl_r_opt op1 op2 n1 n2 d1 d2 =
  match op1, op2 with
  | None   , None    -> None
  | Some p1, None    -> p_real_div_simpl_r p1 (p_real_mul d1 d2)
  | None   , Some p2 -> p_real_div_simpl_r (p_real_mul n1 n2) p2
  | Some p1, Some p2 -> p_real_div_simpl_r p1 p2


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

  in match p_real_inv_simpl_opt p2 with
     | None -> p_real_mul_simpl_r p1 (p_real_inv p2)
     | Some p2 -> p_real_mul_simpl_r p1 p2

and p_real_inv_simpl_opt p =
  match p_destr_app p with
  | op, [p1] when op_equal op fop_real_inv -> Some p1
  | _ ->
     try
       match p_destr_rint p with
       | n when EcBigInt.equal n EcBigInt.zero -> Some p_r0
       | n when EcBigInt.equal n EcBigInt.one  -> Some p_r1
       | _ -> destr_error "destr_rint/inv"
     with DestrError _ -> None

(* -------------------------------------------------------------------------- *)
let rec reduce_pat p = match p.p_node with
  | Pat_Red_Strat _ | Pat_Sub _ | Pat_Or _ -> p
  | Pat_Meta_Name (None, id, None) -> begin
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
let p_if_simpl_opt (p1 : pattern) (p2 : pattern) (p3 : pattern) =
  if p_equal p2 p3 then Some p2
  else match p_bool_val p1, p_bool_val p2, p_bool_val p3 with
  | Some true, _, _  -> Some p2
  | Some false, _, _ -> Some p3
  | _, Some true, _  -> Some (p_imp_simpl (p_not_simpl p1) p3)
  | _, Some false, _ -> Some (p_anda_simpl (p_not_simpl p1) p3)
  | _, _, Some true  -> Some (p_imp_simpl p1 p2)
  | _, _, Some false -> Some (p_anda_simpl p1 p2)
  | _, _, _          -> None

let p_proj_simpl (p1 : pattern) (i : int) (ty : ty) =
  match p1.p_node with
  | Pat_Fun_Symbol(Sym_Form_Tuple,pargs) when 0 <= i && i < List.length pargs ->
     List.nth pargs i
  | _ -> p_proj p1 i ty

let p_app_simpl_opt ?ho op pargs oty =
  omap reduce_pat (p_betared_opt (reduce_pat (p_app ?ho op pargs oty)))

let p_app_simpl ?ho op pargs oty =
  odfl (p_app ?ho op pargs oty) (p_app_simpl_opt ?ho op pargs oty)


let ps_app_simpl ?ho op pargs oty =
  odfl (p_app ?ho op pargs oty) (p_betared_opt (p_app ?ho op pargs oty))

let p_forall_simpl b p =
  let b = List.filter (fun (id,_) -> Mid.mem id (pat_fv p)) b in
  p_forall b p

let p_exists_simpl b p =
  let b = List.filter (fun (id,_) -> Mid.mem id (pat_fv p)) b in
  p_exists b p

let p_destr_app p =
  match p.p_node with
  | Pat_Fun_Symbol (Sym_Form_App _, p::lp) -> p, lp
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
      | Axiom_Int _ -> map
      | Axiom_Memory m -> add_fv map m
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
      | Pat_Meta_Name (None, n, _) -> add_fv map n
      | Pat_Meta_Name (Some p, n, _) -> aux (add_fv map n) p
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

  let rec p_is_record (hyps : EcEnv.LDecl.hyps) (p : pattern) =
    match p_destr_app p with
    | { p_node = Pat_Axiom (Axiom_Op (p,_,_)) }, _ ->
       EcEnv.Op.is_record_ctor (EcEnv.LDecl.toenv hyps) p
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
    | Pat_Axiom (Axiom_Op (op, _, _)) -> ri.delta_p op
    | _ -> false

  let can_eta x (f, args) =
    match List.rev args with
    | { f_node = Flocal y } :: args ->
       let check v = not (Mid.mem x v.f_fv) in
       id_equal x y && List.for_all check (f :: args)
    | _ -> false

  let p_can_eta h x (f, args) =
    match List.rev args with
    | { p_node = (Pat_Axiom (Axiom_Local (y,_))
                  | Pat_Meta_Name (None, y, _))} :: args ->
       let check v = not (Mid.mem x (FV.pattern0 h v)) in
       id_equal x y && List.for_all check (f :: args)
    | _ -> false

  let rec h_red_pattern_opt (hyps : EcEnv.LDecl.hyps) (ri : reduction_info)
        (s : Psubst.p_subst) (p : pattern) =
    try
      match p.p_node with
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
        { p_node = Pat_Fun_Symbol (Sym_Quant (Llambda,_),[_])}::_
           when ri.beta -> p_betared_opt p

      (* ζ-reduction *)
      | Sym_Form_App (ty,ho),
        { p_node = (Pat_Meta_Name (None, id, ob)) ; p_ogty = ogty} :: pargs ->
         if ri.beta
         then match reduce_local_opt hyps ri s id ob ogty with
              | None -> None
              | Some op -> Some (p_app_simpl ~ho op pargs ty)
         else omap (fun x -> p_app ~ho x pargs ty)
                (reduce_local_opt hyps ri s id ob ogty)

      (* ζ-reduction *)
      | Sym_Form_App (oty,ho),
        { p_node = Pat_Axiom (Axiom_Local (id,ty))} :: pargs ->
         if ri.beta
         then match reduce_local_opt hyps ri s id None (OGTty (Some ty)) with
              | None -> None
              | Some op -> Some (p_app_simpl ~ho op pargs oty)
         else omap (fun x -> p_app ~ho x pargs oty)
                (reduce_local_opt hyps ri s id None (OGTty (Some ty)))

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
        ({ p_node = Pat_Axiom (Axiom_Op (op, _, Some fty)) } as p1) :: pargs
           when ri.iota && EcEnv.Op.is_projection (EcEnv.LDecl.toenv hyps) op -> begin
          let op =
            match pargs with
            | [mk] -> begin
                match odfl mk (h_red_pattern_opt hyps ri s mk) with
                | { p_node =
                      Pat_Fun_Symbol
                        (Sym_Form_App _,
                         { p_node = Pat_Axiom (Axiom_Op (mkp,_,_))} :: pargs)} ->
                   if not (EcEnv.Op.is_record_ctor (EcEnv.LDecl.toenv hyps) mkp)
                   then None
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
                omap (fun x -> p_app ~ho x pargs (Some fty))
                  (h_red_pattern_opt hyps ri s p1)
             | _ -> op
        end

      (* ι-reduction (tuples projection) *)
      | Sym_Form_Proj (i,ty), [p1] when ri.iota ->
         let p' = p_proj_simpl p1 i ty in
         if p = p'
         then omap (fun x -> p_proj x i ty) (h_red_pattern_opt hyps ri s p1)
         else Some p'

      (* ι-reduction (if-then-else) *)
      | Sym_Form_If, [p1;p2;p3] when ri.iota -> begin
          match p_if_simpl_opt p1 p2 p3 with
          | None -> omap (fun x -> p_if x p2 p3) (h_red_pattern_opt hyps ri s p1)
          | Some _ as p -> p
        end

      (* ι-reduction (match-fix) *)
      | Sym_Form_App (ty,ho),
        ({ p_node = Pat_Axiom (Axiom_Op (op, lty, _)) } as p1) :: args
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
              | { p_node = Pat_Axiom (Axiom_Op (op, _, _)) }, cargs
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
               (h_red_pattern_opt hyps ri s p1)
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
      { p_node = Pat_Axiom (Axiom_Op (op, tys, _))} :: args
         when is_some ri.logic && is_logical_op op
      ->
       let pcompat =
         match oget ri.logic with `Full -> true | `ProductCompat -> false
       in

       let p' =
         match op_kind op, args with
         | Some (`Not), [f1]    when pcompat -> p_not_simpl_opt f1
         | Some (`Imp), [f1;f2] when pcompat -> p_imp_simpl_opt f1 f2
         | Some (`Iff), [f1;f2] when pcompat -> p_iff_simpl_opt f1 f2


         | Some (`And `Asym), [f1;f2] ->     p_anda_simpl_opt f1 f2
         | Some (`Or  `Asym), [f1;f2] ->      p_ora_simpl_opt f1 f2
         | Some (`And `Sym ), [f1;f2] ->      p_and_simpl_opt f1 f2
         | Some (`Or  `Sym ), [f1;f2] ->       p_or_simpl_opt f1 f2
         | Some (`Int_le   ), [f1;f2] ->   p_int_le_simpl_opt f1 f2
         | Some (`Int_lt   ), [f1;f2] ->   p_int_lt_simpl_opt f1 f2
         | Some (`Real_le  ), [f1;f2] ->  p_real_le_simpl_opt f1 f2
         | Some (`Real_lt  ), [f1;f2] ->  p_real_lt_simpl_opt f1 f2
         | Some (`Int_add  ), [f1;f2] ->  p_int_add_simpl_opt f1 f2
         | Some (`Int_opp  ), [f]     ->  p_int_opp_simpl_opt f
         | Some (`Int_mul  ), [f1;f2] ->  p_int_mul_simpl_opt f1 f2
         | Some (`Real_add ), [f1;f2] -> p_real_add_simpl_opt f1 f2
         | Some (`Real_opp ), [f]     -> p_real_opp_simpl_opt f
         | Some (`Real_mul ), [f1;f2] -> p_real_mul_simpl_opt f1 f2
         | Some (`Real_inv ), [f]     -> p_real_inv_simpl_opt f
         | Some (`Eq       ), [f1;f2] -> begin
             match (p_destr_app f1), (p_destr_app f2) with
             | ({ p_node = Pat_Axiom (Axiom_Op (op1, _, _))}, args1),
               ({ p_node = Pat_Axiom (Axiom_Op (op2, _, _))}, args2)
                  when EcEnv.Op.is_dtype_ctor (EcEnv.LDecl.toenv hyps) op1
                       && EcEnv.Op.is_dtype_ctor (EcEnv.LDecl.toenv hyps) op2 ->

                let idx p =
                  let idx = EcEnv.Op.by_path p (EcEnv.LDecl.toenv hyps) in
                  snd (EcDecl.operator_as_ctor idx)
                in
                if   idx op1 <> idx op2
                then Some p_false
                else Some (p_ands (List.map2 p_eq args1 args2))

             | _ -> if p_equal f1 f2 then Some p_true
                    else Some (p_eq_simpl f1 f2)
           end

         | _ when ri.delta_p op -> begin
             match h_red_op_opt hyps ri s op tys with
             | None -> None
             | Some op -> Some (p_app_simpl ~ho op args ty)
           end

         | _ -> Some p
       in p'

    (* δ-reduction *)
    | Sym_Form_App (ty,ho),
      ({ p_node = Pat_Axiom (Axiom_Op (op,lty,_)) } as pop) :: args
         when is_delta_p ri pop ->
       let op = h_red_op_opt hyps ri s op lty in
       omap (fun op -> p_app_simpl ~ho op args ty) op

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

    | _ -> None
    with
    | EcEnv.NotReducible -> None

  and h_red_axiom_opt hyps ri s (a : axiom) =
    try match a with
      | Axiom_Hoarecmp _    -> None
      | Axiom_Memory m      -> h_red_mem_opt hyps ri s m
      | Axiom_MemEnv m      -> h_red_memenv_opt hyps ri s m
      | Axiom_Prog_Var pv   -> h_red_prog_var_opt hyps ri s pv
      | Axiom_Op (op,lty,_) -> h_red_op_opt hyps ri s op lty
      | Axiom_Mpath_top m   -> h_red_mpath_top_opt hyps ri s m
      | Axiom_Mpath m       -> h_red_mpath_opt hyps ri s m
      | Axiom_Stmt stmt     -> h_red_stmt_opt hyps ri s stmt
      | Axiom_Lvalue lv     -> h_red_lvalue_opt hyps ri s lv
      | Axiom_Xpath x       -> h_red_xpath_opt hyps ri s x
      | Axiom_Local (id,ty) -> h_red_local_opt hyps ri s id ty
      | Axiom_Int _         -> None
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
    then
      try Some (pat_form (EcEnv.Op.reduce (EcEnv.LDecl.toenv hyps) op lty))
      with EcEnv.NotReducible -> None
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

  and h_red_stmt_opt hyps ri s stmt =
    omap (fun l -> pat_fun_symbol Sym_Stmt_Seq l)
      (h_red_args (fun x -> x) h_red_pattern_opt hyps ri s
         (List.map pat_instr stmt.s_node))

  and h_red_lvalue_opt hyps ri s = function
    | LvVar (pv,ty) ->
       omap (fun x -> p_lvalue_var x ty) (h_red_prog_var_opt hyps ri s pv)
    | LvTuple l ->
       omap p_lvalue_tuple
         (h_red_args (fun (pv,ty) -> pat_lvalue (LvVar(pv,ty)))
            (fun hyps ri s x -> h_red_lvalue_opt hyps ri s (LvVar x)) hyps ri s l)
    | LvMap _ -> None

  and h_red_xpath_opt hyps ri s x =
    if ri.modpath
    then match h_red_mpath_opt hyps ri s x.x_top with
         | Some p -> Some (p_xpath p (pat_op x.x_sub [] None))
         | None -> None
    else None

  and h_red_local_opt hyps ri s id ty =
    match reduce_local_opt hyps ri s id None (OGTty (Some ty)) with
    | Some { p_ogty = ogty } as op ->
       if ogty_equal (OGTty (Some ty)) ogty then op else None
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
