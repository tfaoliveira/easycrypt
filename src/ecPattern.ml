(* ------------------------------------------------------------------------------ *)
open EcUtils
open EcFol
open EcTypes
open EcPath
open EcMemory
open EcIdent
open EcModules

module Name = EcIdent

module MName = Mid

(* -------------------------------------------------------------------------- *)

type meta_name = Name.t

type ogty =
  | OGTty    of ty option
  | OGTmodty of (module_type * mod_restr) option
  | OGTmem   of EcMemory.memtype option

type pbinding  = ident * ogty
type pbindings = pbinding list


type axiom =
  | Axiom_Form     of form
  | Axiom_Memory   of memory
  | Axiom_MemEnv   of memenv
  | Axiom_Prog_Var of prog_var
  | Axiom_Op       of path * ty list
  | Axiom_Module   of mpath_top
  | Axiom_Mpath    of mpath
  | Axiom_Instr    of instr
  | Axiom_Stmt     of stmt
  | Axiom_Lvalue   of lvalue
  | Axiom_Xpath    of xpath
  | Axiom_Hoarecmp of hoarecmp
  | Axiom_Local    of ident * ty

type fun_symbol =
  (* from type form *)
  | Sym_Form_If
  | Sym_Form_App          of ty
  | Sym_Form_Tuple
  | Sym_Form_Proj         of int * ty
  | Sym_Form_Match        of ty
  | Sym_Form_Quant        of quantif * bindings
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
  | Sym_App
  | Sym_Quant             of quantif * pbindings


(* invariant of pattern : if the form is not Pat_Axiom, then there is
     at least one of the first set of patterns *)
type pattern =
  | Pat_Anything
  | Pat_Meta_Name  of pattern * meta_name * pbindings option
  | Pat_Sub        of pattern
  | Pat_Or         of pattern list
  | Pat_Instance   of pattern option * meta_name * path * pattern list
  | Pat_Red_Strat  of pattern * reduction_strategy

  | Pat_Fun_Symbol of fun_symbol * pattern list
  | Pat_Axiom      of axiom
  | Pat_Type       of pattern * ogty

and reduction_strategy =
  EcReduction.reduction_info -> EcReduction.reduction_info ->
  EcReduction.reduction_info * EcReduction.reduction_info


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

let pat_axiom x = Pat_Axiom x

let axiom_form f    = Axiom_Form f
let axiom_mpath m   = Axiom_Mpath m

let pat_form f      = pat_axiom (Axiom_Form f)
let pat_memory m    = pat_axiom (Axiom_Memory m)
let pat_memenv m    = pat_axiom (Axiom_MemEnv m)
let pat_mpath m     = pat_axiom (Axiom_Mpath m)
let pat_mpath_top m = pat_axiom (Axiom_Module m)
let pat_xpath x     = pat_axiom (Axiom_Xpath x)
let pat_op op lty   = pat_axiom (Axiom_Op (op,lty))
let pat_lvalue lv   = pat_axiom (Axiom_Lvalue lv)
let pat_instr i     = pat_axiom (Axiom_Instr i)
let pat_stmt s      = pat_axiom (Axiom_Stmt s)
let pat_local id ty = pat_axiom (Axiom_Local (id,ty))
let pat_cmp cmp     = pat_axiom (Axiom_Hoarecmp cmp)
let pat_pv pv       = pat_axiom (Axiom_Prog_Var pv)

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

let pat_add_fv map (n : ident) =
  match Mid.find_opt n map with
  | None -> Mid.add n 1 map
  | Some i -> Mid.add n (i+1) map

let pat_fv_union m1 m2 =
  Mid.fold_left (fun m n _ -> pat_add_fv m n) m1 m2

let pat_fv p =
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
       let map = List.fold_left aux Mid.empty lp in
       Mid.filter (fun x _ -> List.exists (fun (y,_) -> id_equal x y) b) map
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

(* -------------------------------------------------------------------------- *)
let p_equal = (==)

let ogty_equal o1 o2 = match o1, o2 with
  | OGTty (Some t1), OGTty (Some t2) -> ty_equal t1 t2
  | OGTty _, OGTty _ -> true
  | (OGTty _, _) | (_, OGTty _) -> false
  | OGTmem (Some mt1), OGTmem (Some mt2) -> EcMemory.mt_equal mt1 mt2
  | (OGTmem _, _) | (_, OGTmem _) -> false
  | OGTmodty (Some (mt1,mr1)), OGTmodty (Some (mt2,mr2)) ->
     if EcModules.mty_equal mt1 mt2
     then EcModules.mr_equal mr1 mr2
     else false
  | OGTmodty _, OGTmodty _ -> true

(* -------------------------------------------------------------------------- *)
let p_type (p : pattern) (ogty : ogty) =
  match p with
  | Pat_Type(_,gty2) when ogty_equal ogty gty2 -> p
  | Pat_Type _ -> assert false
  | _ -> Pat_Type(p,ogty)

let p_mpath (p : pattern) (args : pattern list) =
  if args = [] then p
  else
  let rec oget_mpaths acc = function
    | [] -> Some (List.rev acc)
    | (Pat_Axiom(Axiom_Mpath m))::r ->
       oget_mpaths (m::acc) r
    | (Pat_Axiom(Axiom_Module mt))::r ->
       oget_mpaths ((mpath mt [])::acc) r
    | _ -> None in
  let oget_mpaths l = oget_mpaths [] l in
  let oget_mpath =
    match p with
    | Pat_Axiom(Axiom_Module mt) -> Some (mpath mt [])
    | Pat_Axiom(Axiom_Mpath m)   -> Some m
    | _ -> None in
  match oget_mpath, oget_mpaths args with
  | Some m, Some args ->
     Pat_Axiom(Axiom_Mpath (mpath m.m_top (m.m_args @ args)))
  | _,_ -> Pat_Fun_Symbol(Sym_Mpath,p::args)

let p_xpath (p : pattern) (f : pattern) =
  match p,f with
  | Pat_Axiom(Axiom_Mpath m),Pat_Axiom(Axiom_Op (op,[])) ->
     Pat_Axiom(Axiom_Xpath (EcPath.xpath m op))
  | _ -> Pat_Fun_Symbol(Sym_Xpath,[p;f])

let p_prog_var (p : pattern) (k : pvar_kind) =
  match p with
  | Pat_Axiom(Axiom_Xpath x) -> Pat_Axiom(Axiom_Prog_Var (pv x k))
  | _ -> Pat_Fun_Symbol(Sym_Form_Prog_var k,[p])

let p_lvalue_var (p : pattern) (ty : ty) =
  match p with
  | Pat_Axiom(Axiom_Prog_Var pv) ->
     Pat_Axiom(Axiom_Lvalue(LvVar(pv,ty)))
  | p -> p_type p (OGTty (Some ty))

let p_lvalue_tuple (p : pattern list) =
  let rec oget_pv acc = function
    | [] -> Some (List.rev acc)
    | a :: r ->
       match a with
       | Pat_Type(Pat_Axiom(Axiom_Prog_Var pv),OGTty (Some ty))
         | Pat_Axiom(Axiom_Lvalue(LvVar (pv,ty))) ->
          oget_pv ((pv,ty)::acc) r
       | _ -> None
  in match oget_pv [] p with
     | None -> Pat_Fun_Symbol(Sym_Form_Tuple,p)
     | Some l -> Pat_Axiom(Axiom_Lvalue(LvTuple l))

let p_pvar (pv : pattern) (ty : ty) (m : pattern) =
  match pv,m with
  | Pat_Axiom(Axiom_Prog_Var pv),Pat_Axiom(Axiom_Memory m) ->
     pat_form (f_pvar pv ty m)
  | _ -> Pat_Fun_Symbol(Sym_Form_Pvar ty, [pv;m])

let p_glob (mp : pattern) (m : pattern) =
  match mp, m with
  | Pat_Axiom(Axiom_Mpath mp),Pat_Axiom(Axiom_Memory m) ->
     pat_form (f_glob mp m)
  | _ -> Pat_Fun_Symbol(Sym_Form_Glob, [mp;m])

let p_if (p1 : pattern) (p2 : pattern) (p3 : pattern) =
  Pat_Fun_Symbol(Sym_Form_If,[p1;p2;p3])

let p_match (p : pattern) (ty : ty) (lp : pattern list) =
  match p, olist_all (function Pat_Axiom(Axiom_Form f) -> Some f | _ -> None) lp with
  | Pat_Axiom(Axiom_Form op),Some lf ->
     pat_form (mk_form (Fmatch (op,lf,ty)) ty)
  | _ -> Pat_Fun_Symbol(Sym_Form_Match ty,p::lp)

let p_tuple (lp : pattern list) =
  match olist_all (function Pat_Axiom(Axiom_Form f) -> Some f | _ -> None) lp with
  | Some l -> pat_form (f_tuple l)
  | None -> Pat_Fun_Symbol(Sym_Form_Tuple,lp)

let p_proj (p1 : pattern) (i : int) (ty : ty) =
  match p1 with
  | Pat_Fun_Symbol(Sym_Form_Tuple,lp) ->
     List.nth lp i
  | _ -> Pat_Fun_Symbol(Sym_Form_Proj (i,ty),[p1])

let p_let (l : lpattern) (p1 : pattern) (p2 : pattern) =
  match p1,p2 with
  | Pat_Axiom(Axiom_Form f1),Pat_Axiom(Axiom_Form f2) ->
     pat_form (EcFol.f_let l f1 f2)
  | _ -> Pat_Fun_Symbol(Sym_Form_Let l,[p1;p2])

let p_app (p : pattern) (args : pattern list) (ty : ty option) =
  match args,ty with
  | [],_ -> p
  | _, None ->
     Pat_Fun_Symbol(Sym_App,p::args)
  | _,Some ty -> Pat_Fun_Symbol(Sym_Form_App ty,p::args)

let p_f_quant q bs p =
  match bs with
  | [] -> p
  | _  -> Pat_Fun_Symbol(Sym_Form_Quant (q,bs),[p])

let p_quant q bs p =
  match bs with
  | [] -> p
  | _  -> Pat_Fun_Symbol(Sym_Quant (q,bs),[p])

let p_f_forall b p = p_f_quant Llambda b p

let p_f_exists b p = p_f_quant Lexists b p

let p_stmt (lp : pattern list) =
  match olist_all (function Pat_Axiom(Axiom_Instr i) -> Some i | _ -> None) lp with
  | Some l -> pat_stmt (stmt l)
  | None -> Pat_Fun_Symbol(Sym_Stmt_Seq,lp)

let p_var_form x ty =
  p_type (Pat_Meta_Name (Pat_Anything, x, None)) (OGTty (Some ty))

let p_assign (plv : pattern) (pe : pattern) = match plv, pe with
  | Pat_Axiom(Axiom_Lvalue lv),Pat_Axiom(Axiom_Form f) -> begin
      match expr_of_form f with
      | None ->
         Pat_Fun_Symbol(Sym_Instr_Assign,[plv;pe])
      | Some e -> Pat_Axiom(Axiom_Instr(i_asgn (lv,e)))
    end
  | _ -> Pat_Fun_Symbol(Sym_Instr_Assign,[plv;pe])

let p_sample (plv : pattern) (pe : pattern) = match plv, pe with
  | Pat_Axiom(Axiom_Lvalue lv),Pat_Axiom(Axiom_Form f) -> begin
      match expr_of_form f with
      | None ->
         Pat_Fun_Symbol(Sym_Instr_Sample,[plv;pe])
      | Some e -> Pat_Axiom(Axiom_Instr(i_rnd (lv,e)))
    end
  | _ -> Pat_Fun_Symbol(Sym_Instr_Sample,[plv;pe])

let p_call (olv : pattern option) (f : pattern) (args : pattern list) =
  let get_expr = function
    | Pat_Axiom(Axiom_Form f) -> expr_of_form f
    | _ -> None in
  match olv,f with
  | None,Pat_Axiom(Axiom_Xpath proc) -> begin
      match olist_all get_expr args with
      | Some args -> Pat_Axiom(Axiom_Instr(i_call(None,proc,args)))
      | None -> Pat_Fun_Symbol(Sym_Instr_Call,f::args)
    end
  | Some(Pat_Axiom(Axiom_Lvalue lv) as olv),Pat_Axiom(Axiom_Xpath proc) ->
     begin
       match olist_all get_expr args with
       | Some args -> Pat_Axiom(Axiom_Instr(i_call(Some lv,proc,args)))
       | None -> Pat_Fun_Symbol(Sym_Instr_Call_Lv,olv::f::args)
     end
  | None,_ -> Pat_Fun_Symbol(Sym_Instr_Call,f::args)
  | Some lv,_ -> Pat_Fun_Symbol(Sym_Instr_Call_Lv,lv::f::args)

let p_instr_if (pcond : pattern) (ps1 : pattern) (ps2 : pattern) =
  match pcond, ps1, ps2 with
  | Pat_Axiom(Axiom_Form f),Pat_Axiom(Axiom_Stmt s1),Pat_Axiom(Axiom_Stmt s2) ->
     odfl (Pat_Fun_Symbol(Sym_Instr_If,[pcond;ps1;ps2]))
       (omap (fun cond -> Pat_Axiom(Axiom_Instr(i_if(cond,s1,s2))))
          (expr_of_form f))
  | _ -> Pat_Fun_Symbol(Sym_Instr_If,[pcond;ps1;ps2])

let p_while (pcond : pattern) (ps : pattern) =
  match pcond, ps with
  | Pat_Axiom(Axiom_Form f),Pat_Axiom(Axiom_Stmt s) ->
     odfl (Pat_Fun_Symbol(Sym_Instr_While,[pcond;ps]))
       (omap (fun cond -> Pat_Axiom(Axiom_Instr(i_while(cond,s))))
          (expr_of_form f))
  | _ -> Pat_Fun_Symbol(Sym_Instr_While,[pcond;ps])

let p_assert (p : pattern) = match p with
  | Pat_Axiom(Axiom_Form f) ->
     odfl (Pat_Fun_Symbol(Sym_Instr_Assert,[p]))
       (omap (fun e -> Pat_Axiom(Axiom_Instr(i_assert e))) (expr_of_form f))
  | _ -> Pat_Fun_Symbol(Sym_Instr_Assert,[p])


let p_hoareF (pr : pattern) (f : pattern) (po : pattern) =
  match pr,f,po with
  | Pat_Axiom(Axiom_Form pr),
    Pat_Axiom(Axiom_Xpath f),
    Pat_Axiom(Axiom_Form po) ->
     pat_form (f_hoareF pr f po)
  | _ -> Pat_Fun_Symbol(Sym_Form_Hoare_F,[pr;f;po])

let p_hoareS (m : pattern) (pr : pattern) (s : pattern) (po : pattern) =
  match m,pr,s,po with
  | Pat_Axiom(Axiom_MemEnv m),
    Pat_Axiom(Axiom_Form pr),
    Pat_Axiom(Axiom_Stmt s),
    Pat_Axiom(Axiom_Form po) ->
     pat_form (f_hoareS m pr s po)
  | _ -> Pat_Fun_Symbol(Sym_Form_Hoare_F,[m;pr;s;po])

let p_bdHoareF (pr : pattern) (f : pattern) (po : pattern) (cmp : pattern)
      (bd : pattern) =
  match pr, f, po, cmp, bd with
  | Pat_Axiom(Axiom_Form pr),
    Pat_Axiom(Axiom_Xpath f),
    Pat_Axiom(Axiom_Form po),
    Pat_Axiom(Axiom_Hoarecmp cmp),
    Pat_Axiom(Axiom_Form bd) ->
     pat_form(f_bdHoareF pr f po cmp bd)
  | _ ->
     Pat_Fun_Symbol(Sym_Form_bd_Hoare_F,[pr;f;po;cmp;bd])

let p_bdHoareS (m : pattern) (pr : pattern) (s : pattern) (po : pattern)
      (cmp : pattern) (bd : pattern) =
  match m, pr, s, po, cmp, bd with
  | Pat_Axiom(Axiom_MemEnv m),
    Pat_Axiom(Axiom_Form pr),
    Pat_Axiom(Axiom_Stmt s),
    Pat_Axiom(Axiom_Form po),
    Pat_Axiom(Axiom_Hoarecmp cmp),
    Pat_Axiom(Axiom_Form bd) ->
     pat_form(f_bdHoareS m pr s po cmp bd)
  | _ ->
     Pat_Fun_Symbol(Sym_Form_bd_Hoare_F,[m;pr;s;po;cmp;bd])

let p_equivF (pr : pattern) (fl : pattern) (fr : pattern) (po : pattern) =
  match pr, fl, fr, po with
  | Pat_Axiom(Axiom_Form pr),
    Pat_Axiom(Axiom_Xpath fl),
    Pat_Axiom(Axiom_Xpath fr),
    Pat_Axiom(Axiom_Form po) ->
     pat_form (f_equivF pr fl fr po)
  | _ ->
     Pat_Fun_Symbol(Sym_Form_Equiv_F,[pr;fl;fr;po])

let p_equivS (ml : pattern) (mr : pattern) (pr : pattern) (sl : pattern)
      (sr : pattern) (po : pattern) =
  match ml, mr, pr, sl, sr, po with
  | Pat_Axiom(Axiom_MemEnv ml),
    Pat_Axiom(Axiom_MemEnv mr),
    Pat_Axiom(Axiom_Form pr),
    Pat_Axiom(Axiom_Stmt sl),
    Pat_Axiom(Axiom_Stmt sr),
    Pat_Axiom(Axiom_Form po) ->
     pat_form (f_equivS ml mr pr sl sr po)
  | _ ->
     Pat_Fun_Symbol(Sym_Form_Equiv_F,[ml;mr;pr;sl;sr;po])

let p_eagerF (pr : pattern) (sl : pattern) (fl : pattern)
      (fr : pattern) (sr : pattern) (po : pattern) =
  match pr, sl, fl, fr, sr, po with
  | Pat_Axiom(Axiom_Form pr),
    Pat_Axiom(Axiom_Stmt sl),
    Pat_Axiom(Axiom_Xpath fl),
    Pat_Axiom(Axiom_Xpath fr),
    Pat_Axiom(Axiom_Stmt sr),
    Pat_Axiom(Axiom_Form po) ->
     pat_form (f_eagerF pr sl fl fr sr po)
  | _ ->
     Pat_Fun_Symbol(Sym_Form_Eager_F,[pr;sl;fl;fr;sr;po])

let p_pr (pm : pattern) (pf : pattern) (pargs : pattern) (pevent : pattern) =
  match pm, pf, pargs, pevent with
  | Pat_Axiom(Axiom_Memory m),
    Pat_Axiom(Axiom_Xpath f),
    Pat_Axiom(Axiom_Form args),
    Pat_Axiom(Axiom_Form event) ->
     pat_form (f_pr m f args event)
  | _ -> Pat_Fun_Symbol(Sym_Form_Pr,[pm;pf;pargs;pevent])

(* -------------------------------------------------------------------------- *)
let lv_ty (f_ty : ty -> ty) = function
  | LvVar (pv,ty) -> LvVar (pv,f_ty ty)
  | LvTuple l -> LvTuple (List.map (fun (x,ty)->(x,f_ty ty)) l)
  | LvMap ((op,lty),pv,e,ty) ->
     LvMap ((op,List.map f_ty lty),pv,e_map f_ty (fun x->x) e,f_ty ty)


let rec p_map_fold (f : 'a -> pattern -> 'a * pattern) (a : 'a) (p : pattern)
        : 'a * pattern =
  let a, p' = f a p in
  if not (p = p') then a, p' else
  match p with
  | Pat_Anything -> a, p
  | Pat_Meta_Name (p,n,ob) ->
     let a, p = p_map_fold f a p in a, Pat_Meta_Name (p,n,ob)
  | Pat_Sub p ->
     let a, p = p_map_fold f a p in a, Pat_Sub p
  | Pat_Or lp ->
     let a, lp = List.map_fold (p_map_fold f) a lp in a, Pat_Or lp
  | Pat_Instance _ -> assert false
  | Pat_Red_Strat (p, red) ->
     let a, p = p_map_fold f a p in a, Pat_Red_Strat (p, red)
  | Pat_Type(p,gty) ->
     let a, p = p_map_fold f a p in a, p_type p gty
  | Pat_Fun_Symbol (s, lp) ->
     let a, lp = List.map_fold (p_map_fold f) a lp in
     a, Pat_Fun_Symbol (s, lp)
  | Pat_Axiom axiom ->
     match axiom with
     | Axiom_Form fo -> begin
         match fo.f_node with
         | Fquant (q,b,f') ->
            let a, p' = p_map_fold f a (pat_form f') in
            let p' = match p with
              | Pat_Axiom(Axiom_Form f'') ->
                 pat_form (EcFol.FSmart.f_quant (fo, (q,b,f')) (q, b, f''))
              | _ -> p_f_quant q b p' in
            a, p'
         | Fif (f1,f2,f3) ->
            let a, p1 = p_map_fold f a (pat_form f1) in
            let a, p2 = p_map_fold f a (pat_form f2) in
            let a, p3 = p_map_fold f a (pat_form f3) in
            let p = match p1,p2,p3 with
              | Pat_Axiom (Axiom_Form f1'),
                Pat_Axiom (Axiom_Form f2'),
                Pat_Axiom (Axiom_Form f3') ->
                 pat_form (EcFol.FSmart.f_if (fo, (f1,f2,f3)) (f1',f2',f3'))
              | _ -> p_if p1 p2 p3
            in a, p
         | Fmatch (f1,fargs,ty) ->
            let a, p1   = p_map_fold f a (pat_form f1) in
            let a, args = List.map_fold (p_map_fold f) a
                            (List.map pat_form fargs) in
            let oargs   =
              olist_all (function Pat_Axiom(Axiom_Form f) -> Some f | _ -> None)
                args in
            let p = match p1, oargs with
              | Pat_Axiom(Axiom_Form f1'),Some fargs' ->
                 pat_form (EcFol.FSmart.f_match (fo,(f1,fargs,ty)) (f1',fargs',ty))
              | _ -> p_match p1 ty args in
            a, p
         | Flet (lp,f1,f2) ->
            let a, p1 = p_map_fold f a (pat_form f1) in
            let a, p2 = p_map_fold f a (pat_form f2) in
            let p = match p1, p2 with
              | Pat_Axiom(Axiom_Form f1'),Pat_Axiom(Axiom_Form f2') ->
                 pat_form (EcFol.FSmart.f_let (fo,(lp,f1,f2)) (lp,f1',f2'))
              | _ -> p_let lp p1 p2 in
            a, p
         | Fpvar (pv,m) ->
            let a, p1 = p_map_fold f a (pat_pv pv) in
            let a, p2 = p_map_fold f a (pat_memory m) in
            let p = match p1, p2 with
              | Pat_Axiom (Axiom_Prog_Var pv'), Pat_Axiom (Axiom_Memory m') ->
                 pat_form (EcFol.FSmart.f_pvar (fo,(pv,fo.f_ty,m)) (pv',fo.f_ty,m'))
              | _ -> p_pvar p1 fo.f_ty p2
            in a, p
         | Fglob (mp,m) ->
            let a, p1 = p_map_fold f a (pat_mpath mp) in
            let a, p2 = p_map_fold f a (pat_memory m) in
            let p = match p1, p2 with
              | Pat_Axiom (Axiom_Mpath mp'), Pat_Axiom (Axiom_Memory m') ->
                 pat_form (EcFol.FSmart.f_glob (fo,(mp,m)) (mp',m'))
              | _ -> p_glob p1 p2 in
            a, p
         | Fapp (fop,fargs) ->
            let a, pop   = p_map_fold f a (pat_form fop) in
            let a, pargs = List.map_fold (p_map_fold f) a
                             (List.map pat_form fargs) in
            let oargs    =
              olist_all (function Pat_Axiom(Axiom_Form f) -> Some f | _ -> None)
                pargs in
            let p = match pop, oargs with
              | Pat_Axiom (Axiom_Form fop'), Some fargs' ->
                 pat_form (EcFol.FSmart.f_app (fo,(fop,fargs,fo.f_ty)) (fop',fargs',fo.f_ty))
              | _ -> p_app pop pargs (Some fo.f_ty) in
            a, p
         | Ftuple t ->
            let a, pt = List.map_fold (p_map_fold f) a (List.map pat_form t) in
            let ot    =
              olist_all (function Pat_Axiom(Axiom_Form f) -> Some f | _ -> None) pt in
            let p = match ot with
              | Some t' -> pat_form (EcFol.FSmart.f_tuple (fo,t) t')
              | None    -> p_tuple pt in
            a, p
         | Fproj (f1,i) ->
            let a, p1 = p_map_fold f a (pat_form f1) in
            let p = match p1 with
              | Pat_Axiom(Axiom_Form f1') ->
                 pat_form (EcFol.FSmart.f_proj (fo,(f1,fo.f_ty)) (f1',fo.f_ty) i)
              | _ -> p_proj p1 i fo.f_ty in
            a, p
         | FhoareF h ->
            let a, pr = p_map_fold f a (pat_form h.hf_pr) in
            let a, xp = p_map_fold f a (pat_xpath h.hf_f) in
            let a, po = p_map_fold f a (pat_form h.hf_po) in
            let p = match pr,xp,po with
              | Pat_Axiom(Axiom_Form hf_pr),
                Pat_Axiom(Axiom_Xpath hf_f),
                Pat_Axiom(Axiom_Form hf_po) ->
                 pat_form (EcFol.FSmart.f_hoareF (fo,h) { hf_pr ; hf_f ; hf_po })
              | _ -> p_hoareF pr xp po in
            a, p
         | FhoareS h ->
            let a, mem = p_map_fold f a (pat_memenv h.hs_m) in
            let a, pr  = p_map_fold f a (pat_form h.hs_pr) in
            let a, s   = p_map_fold f a (pat_stmt h.hs_s) in
            let a, po  = p_map_fold f a (pat_form h.hs_po) in
            let p = match mem,pr,s,po with
              | Pat_Axiom(Axiom_MemEnv hs_m),
                Pat_Axiom(Axiom_Form hs_pr),
                Pat_Axiom(Axiom_Stmt hs_s),
                Pat_Axiom(Axiom_Form hs_po) ->
                 pat_form (EcFol.FSmart.f_hoareS (fo,h) { hs_m ; hs_pr ; hs_s ; hs_po })
              | _ -> p_hoareS mem pr s po in
            a, p
         | FbdHoareF h ->
            let a, pr  = p_map_fold f a (pat_form h.bhf_pr) in
            let a, xp  = p_map_fold f a (pat_xpath h.bhf_f) in
            let a, po  = p_map_fold f a (pat_form h.bhf_po) in
            let a, cmp = p_map_fold f a (pat_cmp h.bhf_cmp) in
            let a, bd  = p_map_fold f a (pat_form h.bhf_bd) in
            let p = match pr,xp,po,cmp,bd with
              | Pat_Axiom(Axiom_Form bhf_pr),
                Pat_Axiom(Axiom_Xpath bhf_f),
                Pat_Axiom(Axiom_Form bhf_po),
                Pat_Axiom(Axiom_Hoarecmp bhf_cmp),
                Pat_Axiom(Axiom_Form bhf_bd) ->
                 pat_form (EcFol.FSmart.f_bdHoareF (fo,h) { bhf_pr ; bhf_f ; bhf_po ; bhf_cmp ; bhf_bd })
              | _ -> p_bdHoareF pr xp po cmp bd in
            a, p
         | FbdHoareS h ->
            let a, mem = p_map_fold f a (pat_memenv h.bhs_m) in
            let a, pr  = p_map_fold f a (pat_form h.bhs_pr) in
            let a, s   = p_map_fold f a (pat_stmt h.bhs_s) in
            let a, po  = p_map_fold f a (pat_form h.bhs_po) in
            let a, cmp = p_map_fold f a (pat_cmp h.bhs_cmp) in
            let a, bd  = p_map_fold f a (pat_form h.bhs_bd) in
            let p = match mem,pr,s,po,cmp,bd with
              | Pat_Axiom(Axiom_MemEnv bhs_m),
                Pat_Axiom(Axiom_Form bhs_pr),
                Pat_Axiom(Axiom_Stmt bhs_s),
                Pat_Axiom(Axiom_Form bhs_po),
                Pat_Axiom(Axiom_Hoarecmp bhs_cmp),
                Pat_Axiom(Axiom_Form bhs_bd) ->
                 pat_form (EcFol.FSmart.f_bdHoareS (fo,h) { bhs_m ; bhs_pr ; bhs_s ; bhs_po ; bhs_cmp; bhs_bd })
              | _ -> p_bdHoareS mem pr s po cmp bd in
            a, p
         | FequivF h ->
            let a, pr = p_map_fold f a (pat_form h.ef_pr) in
            let a, xl = p_map_fold f a (pat_xpath h.ef_fl) in
            let a, xr = p_map_fold f a (pat_xpath h.ef_fr) in
            let a, po = p_map_fold f a (pat_form h.ef_po) in
            let p = match pr,xl,xr,po with
              | Pat_Axiom(Axiom_Form ef_pr),
                Pat_Axiom(Axiom_Xpath ef_fl),
                Pat_Axiom(Axiom_Xpath ef_fr),
                Pat_Axiom(Axiom_Form ef_po) ->
                 pat_form (EcFol.FSmart.f_equivF (fo,h) { ef_pr ; ef_fl ; ef_fr ; ef_po })
              | _ -> p_equivF pr xl xr po in
            a, p
         | FequivS h ->
            let a, ml = p_map_fold f a (pat_memenv h.es_ml) in
            let a, mr = p_map_fold f a (pat_memenv h.es_mr) in
            let a, pr = p_map_fold f a (pat_form h.es_pr) in
            let a, sl = p_map_fold f a (pat_stmt h.es_sl) in
            let a, sr = p_map_fold f a (pat_stmt h.es_sr) in
            let a, po = p_map_fold f a (pat_form h.es_po) in
            let p = match ml,mr,pr,sl,sr,po with
              | Pat_Axiom(Axiom_MemEnv es_ml),
                Pat_Axiom(Axiom_MemEnv es_mr),
                Pat_Axiom(Axiom_Form es_pr),
                Pat_Axiom(Axiom_Stmt es_sl),
                Pat_Axiom(Axiom_Stmt es_sr),
                Pat_Axiom(Axiom_Form es_po) ->
                 pat_form (EcFol.FSmart.f_equivS (fo,h) { es_ml; es_mr ; es_pr ; es_sl ; es_sr ; es_po })
              | _ -> p_equivS ml mr pr sl sr po in
            a, p
         | FeagerF h ->
            let a, pr = p_map_fold f a (pat_form h.eg_pr) in
            let a, sl = p_map_fold f a (pat_stmt h.eg_sl) in
            let a, fl = p_map_fold f a (pat_xpath h.eg_fl) in
            let a, fr = p_map_fold f a (pat_xpath h.eg_fr) in
            let a, sr = p_map_fold f a (pat_stmt h.eg_sr) in
            let a, po = p_map_fold f a (pat_form h.eg_po) in
            let p = match pr,sl,fl,fr,sr,po with
              | Pat_Axiom(Axiom_Form eg_pr),
                Pat_Axiom(Axiom_Stmt eg_sl),
                Pat_Axiom(Axiom_Xpath eg_fl),
                Pat_Axiom(Axiom_Xpath eg_fr),
                Pat_Axiom(Axiom_Stmt eg_sr),
                Pat_Axiom(Axiom_Form eg_po) ->
                 pat_form (EcFol.FSmart.f_eagerF (fo,h) { eg_pr ; eg_sl; eg_fl ; eg_fr ; eg_sr ; eg_po })
              | _ -> p_eagerF pr sl fl fr sr po in
            a, p
         | Fpr h ->
            let a, m    = p_map_fold f a (pat_memory h.pr_mem) in
            let a, xp   = p_map_fold f a (pat_xpath h.pr_fun) in
            let a, args = p_map_fold f a (pat_form h.pr_args) in
            let a, ev   = p_map_fold f a (pat_form h.pr_event) in
            let p = match m, xp, args, ev with
              | Pat_Axiom(Axiom_Memory pr_mem),
                Pat_Axiom(Axiom_Xpath pr_fun),
                Pat_Axiom(Axiom_Form pr_args),
                Pat_Axiom(Axiom_Form pr_event) ->
                 pat_form (EcFol.FSmart.f_pr (fo,h) { pr_mem ; pr_fun ; pr_args; pr_event })
              | _ -> p_pr m xp args ev in
            a, p
         | Fint _ | Flocal _ | Fop _ -> f a p
       end
     | Axiom_Instr i -> begin
         match i.i_node with
         | Sasgn (lv,e) ->
            let a, plv = p_map_fold f a (pat_lvalue lv) in
            let a, pe  = p_map_fold f a (pat_form (form_of_expr e)) in
            a, p_assign plv pe
         | Srnd (lv,e) ->
            let a, plv = p_map_fold f a (pat_lvalue lv) in
            let a, pe  = p_map_fold f a (pat_form (form_of_expr e)) in
            a, p_sample plv pe
         | Scall (olv,xp,args) ->
            let a, olv = match olv with
              | Some lv -> let a,p = p_map_fold f a (pat_lvalue lv) in a, Some p
              | None -> a, None in
            let a, xp = p_map_fold f a (pat_xpath xp) in
            let a, args =
              List.map_fold (p_map_fold f) a
                (List.map (fun arg -> pat_form (form_of_expr arg)) args) in
            a, p_call olv xp args
         | Sif (e,s1,s2) ->
            let a, pe = p_map_fold f a (pat_form (form_of_expr e)) in
            let a, s1 = p_map_fold f a (pat_stmt s1) in
            let a, s2 = p_map_fold f a (pat_stmt s2) in
            a, p_instr_if pe s1 s2
         | Swhile (e,s) ->
            let a, pe = p_map_fold f a (pat_form (form_of_expr e)) in
            let a, s  = p_map_fold f a (pat_stmt s) in
            a, p_while pe s
         | Sassert e ->
            let a, p = p_map_fold f a (pat_form (form_of_expr e)) in
            a, p_assert p
         | Sabstract _ -> f a p
       end
     | Axiom_Stmt s ->
        let a, s = List.map_fold (p_map_fold f) a (List.map pat_instr s.s_node) in
        a, p_stmt s
     | Axiom_Lvalue lv -> begin
         match lv with
         | LvVar (pv,ty) ->
            let a, p = p_map_fold f a (pat_pv pv) in a, p_lvalue_var p ty
         | LvTuple t ->
            let a, t = List.map_fold (p_map_fold f) a
                         (List.map (fun (pv,ty) -> pat_lvalue (LvVar (pv,ty))) t) in
            a, p_lvalue_tuple t
         | LvMap _ -> f a p
       end
     | Axiom_Prog_Var pv ->
        let a, p = p_map_fold f a (pat_xpath pv.pv_name) in
        a, p_prog_var p pv.pv_kind
     | Axiom_Xpath xp ->
        let a, p = p_map_fold f a (pat_mpath xp.x_top) in
        a, p_xpath p (pat_op xp.x_sub [])
     | Axiom_Mpath mp ->
        let a, m = p_map_fold f a (pat_mpath_top mp.m_top) in
        let a, margs = List.map_fold (p_map_fold f) a
                         (List.map pat_mpath mp.m_args) in
        a, p_mpath m margs
     | Axiom_Op _ | Axiom_Local _ | Axiom_Memory _ | Axiom_MemEnv _
       | Axiom_Module _ | Axiom_Hoarecmp _ -> a, p



(* -------------------------------------------------------------------------- *)
let rec p_replace_if (f : pattern -> bool) (replacement : pattern) (p : pattern) =
  if f p then replacement
  else
  let replace p = if f p then replacement else p in
  match p with
  | Pat_Anything -> p
  | Pat_Meta_Name (p',n,ob) -> Pat_Meta_Name (replace p',n,ob)
  | Pat_Sub p' -> Pat_Sub (replace p')
  | Pat_Or lp -> Pat_Or (List.map replace lp)
  | Pat_Instance _ -> assert false
  | Pat_Red_Strat (p, red) -> Pat_Red_Strat (replace p, red)
  | Pat_Type(p,gty) -> p_type (replace p) gty
  | Pat_Fun_Symbol (s, lp) -> Pat_Fun_Symbol (s, List.map replace lp)
  | Pat_Axiom axiom ->
     match axiom with
     | Axiom_Form fo -> begin
         match fo.f_node with
         | Fquant (q,b,f') ->
            let p' = replace (pat_form f') in
            let p' = match p with
              | Pat_Axiom(Axiom_Form f'') ->
                 pat_form (EcFol.FSmart.f_quant (fo, (q,b,f')) (q, b, f''))
              | _ -> p_f_quant q b p' in
            p'
         | Fif (f1,f2,f3) ->
            let p1 = replace (pat_form f1) in
            let p2 = replace (pat_form f2) in
            let p3 = replace (pat_form f3) in
            let p = match p1,p2,p3 with
              | Pat_Axiom (Axiom_Form f1'),
                Pat_Axiom (Axiom_Form f2'),
                Pat_Axiom (Axiom_Form f3') ->
                 pat_form (EcFol.FSmart.f_if (fo, (f1,f2,f3)) (f1',f2',f3'))
              | _ -> p_if p1 p2 p3
            in p
         | Fmatch (f1,fargs,ty) ->
            let p1   = replace (pat_form f1) in
            let args = List.map replace (List.map pat_form fargs) in
            let oargs   =
              olist_all (function Pat_Axiom(Axiom_Form f) -> Some f | _ -> None)
                args in
            let p = match p1, oargs with
              | Pat_Axiom(Axiom_Form f1'),Some fargs' ->
                 pat_form (EcFol.FSmart.f_match (fo,(f1,fargs,ty)) (f1',fargs',ty))
              | _ -> p_match p1 ty args in
            p
         | Flet (lp,f1,f2) ->
            let p1 = replace (pat_form f1) in
            let p2 = replace (pat_form f2) in
            let p = match p1, p2 with
              | Pat_Axiom(Axiom_Form f1'),Pat_Axiom(Axiom_Form f2') ->
                 pat_form (EcFol.FSmart.f_let (fo,(lp,f1,f2)) (lp,f1',f2'))
              | _ -> p_let lp p1 p2 in
            p
         | Fpvar (pv,m) ->
            let p1 = replace (pat_pv pv) in
            let p2 = replace (pat_memory m) in
            let p = match p1, p2 with
              | Pat_Axiom (Axiom_Prog_Var pv'), Pat_Axiom (Axiom_Memory m') ->
                 pat_form (EcFol.FSmart.f_pvar (fo,(pv,fo.f_ty,m)) (pv',fo.f_ty,m'))
              | _ -> p_pvar p1 fo.f_ty p2
            in p
         | Fglob (mp,m) ->
            let p1 = replace (pat_mpath mp) in
            let p2 = replace (pat_memory m) in
            let p = match p1, p2 with
              | Pat_Axiom (Axiom_Mpath mp'), Pat_Axiom (Axiom_Memory m') ->
                 pat_form (EcFol.FSmart.f_glob (fo,(mp,m)) (mp',m'))
              | _ -> p_glob p1 p2 in
            p
         | Fapp (fop,fargs) ->
            let pop   = replace (pat_form fop) in
            let pargs = List.map replace (List.map pat_form fargs) in
            let oargs    =
              olist_all (function Pat_Axiom(Axiom_Form f) -> Some f | _ -> None)
                pargs in
            let p = match pop, oargs with
              | Pat_Axiom (Axiom_Form fop'), Some fargs' ->
                 pat_form (EcFol.FSmart.f_app (fo,(fop,fargs,fo.f_ty)) (fop',fargs',fo.f_ty))
              | _ -> p_app pop pargs (Some fo.f_ty) in
            p
         | Ftuple t ->
            let pt = List.map replace (List.map pat_form t) in
            let ot    =
              olist_all (function Pat_Axiom(Axiom_Form f) -> Some f | _ -> None) pt in
            let p = match ot with
              | Some t' -> pat_form (EcFol.FSmart.f_tuple (fo,t) t')
              | None    -> p_tuple pt in
            p
         | Fproj (f1,i) ->
            let p1 = replace (pat_form f1) in
            let p = match p1 with
              | Pat_Axiom(Axiom_Form f1') ->
                 pat_form (EcFol.FSmart.f_proj (fo,(f1,fo.f_ty)) (f1',fo.f_ty) i)
              | _ -> p_proj p1 i fo.f_ty in
            p
         | FhoareF h ->
            let pr = replace (pat_form h.hf_pr) in
            let xp = replace (pat_xpath h.hf_f) in
            let po = replace (pat_form h.hf_po) in
            let p = match pr,xp,po with
              | Pat_Axiom(Axiom_Form hf_pr),
                Pat_Axiom(Axiom_Xpath hf_f),
                Pat_Axiom(Axiom_Form hf_po) ->
                 pat_form (EcFol.FSmart.f_hoareF (fo,h) { hf_pr ; hf_f ; hf_po })
              | _ -> p_hoareF pr xp po in
            p
         | FhoareS h ->
            let mem = replace (pat_memenv h.hs_m) in
            let pr  = replace (pat_form h.hs_pr) in
            let s   = replace (pat_stmt h.hs_s) in
            let po  = replace (pat_form h.hs_po) in
            let p = match mem,pr,s,po with
              | Pat_Axiom(Axiom_MemEnv hs_m),
                Pat_Axiom(Axiom_Form hs_pr),
                Pat_Axiom(Axiom_Stmt hs_s),
                Pat_Axiom(Axiom_Form hs_po) ->
                 pat_form (EcFol.FSmart.f_hoareS (fo,h) { hs_m ; hs_pr ; hs_s ; hs_po })
              | _ -> p_hoareS mem pr s po in
            p
         | FbdHoareF h ->
            let pr  = replace (pat_form h.bhf_pr) in
            let xp  = replace (pat_xpath h.bhf_f) in
            let po  = replace (pat_form h.bhf_po) in
            let cmp = replace (pat_cmp h.bhf_cmp) in
            let bd  = replace (pat_form h.bhf_bd) in
            let p = match pr,xp,po,cmp,bd with
              | Pat_Axiom(Axiom_Form bhf_pr),
                Pat_Axiom(Axiom_Xpath bhf_f),
                Pat_Axiom(Axiom_Form bhf_po),
                Pat_Axiom(Axiom_Hoarecmp bhf_cmp),
                Pat_Axiom(Axiom_Form bhf_bd) ->
                 pat_form (EcFol.FSmart.f_bdHoareF (fo,h) { bhf_pr ; bhf_f ; bhf_po ; bhf_cmp ; bhf_bd })
              | _ -> p_bdHoareF pr xp po cmp bd in
            p
         | FbdHoareS h ->
            let mem = replace (pat_memenv h.bhs_m) in
            let pr  = replace (pat_form h.bhs_pr) in
            let s   = replace (pat_stmt h.bhs_s) in
            let po  = replace (pat_form h.bhs_po) in
            let cmp = replace (pat_cmp h.bhs_cmp) in
            let bd  = replace (pat_form h.bhs_bd) in
            let p = match mem,pr,s,po,cmp,bd with
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
            let pr = replace (pat_form h.ef_pr) in
            let xl = replace (pat_xpath h.ef_fl) in
            let xr = replace (pat_xpath h.ef_fr) in
            let po = replace (pat_form h.ef_po) in
            let p = match pr,xl,xr,po with
              | Pat_Axiom(Axiom_Form ef_pr),
                Pat_Axiom(Axiom_Xpath ef_fl),
                Pat_Axiom(Axiom_Xpath ef_fr),
                Pat_Axiom(Axiom_Form ef_po) ->
                 pat_form (EcFol.FSmart.f_equivF (fo,h) { ef_pr ; ef_fl ; ef_fr ; ef_po })
              | _ -> p_equivF pr xl xr po in
            p
         | FequivS h ->
            let ml = replace (pat_memenv h.es_ml) in
            let mr = replace (pat_memenv h.es_mr) in
            let pr = replace (pat_form h.es_pr) in
            let sl = replace (pat_stmt h.es_sl) in
            let sr = replace (pat_stmt h.es_sr) in
            let po = replace (pat_form h.es_po) in
            let p = match ml,mr,pr,sl,sr,po with
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
            let pr = replace (pat_form h.eg_pr) in
            let sl = replace (pat_stmt h.eg_sl) in
            let fl = replace (pat_xpath h.eg_fl) in
            let fr = replace (pat_xpath h.eg_fr) in
            let sr = replace (pat_stmt h.eg_sr) in
            let po = replace (pat_form h.eg_po) in
            let p = match pr,sl,fl,fr,sr,po with
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
            let m    = replace (pat_memory h.pr_mem) in
            let xp   = replace (pat_xpath h.pr_fun) in
            let args = replace (pat_form h.pr_args) in
            let ev   = replace (pat_form h.pr_event) in
            let p = match m, xp, args, ev with
              | Pat_Axiom(Axiom_Memory pr_mem),
                Pat_Axiom(Axiom_Xpath pr_fun),
                Pat_Axiom(Axiom_Form pr_args),
                Pat_Axiom(Axiom_Form pr_event) ->
                 pat_form (EcFol.FSmart.f_pr (fo,h) { pr_mem ; pr_fun ; pr_args; pr_event })
              | _ -> p_pr m xp args ev in
            p
         | Fint _ | Flocal _ | Fop _ -> replace p
       end
     | Axiom_Instr i -> begin
         match i.i_node with
         | Sasgn (lv,e) ->
            let plv = replace (pat_lvalue lv) in
            let pe = replace (pat_form (form_of_expr e)) in
            p_assign plv pe
         | Srnd (lv,e) ->
            let plv = replace (pat_lvalue lv) in
            let pe = replace (pat_form (form_of_expr e)) in
            p_sample plv pe
         | Scall (olv,xp,args) ->
            let olv = match olv with
              | Some lv -> let p = replace (pat_lvalue lv) in Some p
              | None -> None in
            let xp = replace (pat_xpath xp) in
            let args = List.map replace
                         (List.map (fun arg -> pat_form (form_of_expr arg)) args) in
            p_call olv xp args
         | Sif (e,s1,s2) ->
            let pe = replace (pat_form (form_of_expr e)) in
            let s1 = replace (pat_stmt s1) in
            let s2 = replace (pat_stmt s2) in
            p_instr_if pe s1 s2
         | Swhile (e,s) ->
            let pe = replace (pat_form (form_of_expr e)) in
            let s  = replace (pat_stmt s) in
            p_while pe s
         | Sassert e ->
            let p = replace (pat_form (form_of_expr e)) in
            p_assert p
         | Sabstract _ -> replace p
       end
     | Axiom_Stmt s ->
        let s = List.map replace (List.map pat_instr s.s_node) in
        p_stmt s
     | Axiom_Lvalue lv -> begin
         match lv with
         | LvVar (pv,ty) ->
            let p = replace (pat_pv pv) in p_lvalue_var p ty
         | LvTuple t ->
            let t = List.map replace
                         (List.map (fun (pv,ty) -> pat_lvalue (LvVar (pv,ty))) t) in
            p_lvalue_tuple t
         | LvMap _ -> replace p
       end
     | Axiom_Prog_Var pv ->
        let p = replace (pat_xpath pv.pv_name) in
        p_prog_var p pv.pv_kind
     | Axiom_Xpath xp ->
        let p = replace (pat_mpath xp.x_top) in
        p_xpath p (pat_op xp.x_sub [])
     | Axiom_Mpath mp ->
        let m = replace (pat_mpath_top mp.m_top) in
        let margs = List.map replace (List.map pat_mpath mp.m_args) in
        p_mpath m margs
     | Axiom_Op _ | Axiom_Local _ | Axiom_Memory _ | Axiom_MemEnv _
       | Axiom_Module _ | Axiom_Hoarecmp _ -> p


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
    let smp = Mid.map_filter (function Pat_Axiom(Axiom_Mpath m) -> Some m | _ -> None)
                ps_patloc in
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
        let mp   = Mid.map_filter (function Pat_Axiom(Axiom_Mpath m) -> Some m | _ -> None)
                     s.ps_patloc in
        let xsub = EcPath.x_substm s.ps_sty.ts_p mp in
        let p'   = mty_subst s.ps_sty.ts_p sub p in
        let rx'  = Sx.fold (fun m rx' -> Sx.add (xsub m) rx') rx Sx.empty in
        let r'   = Sm.fold (fun m r' -> Sm.add (sub m) r') r Sm.empty in

        if   p == p' && Sx.equal rx rx' && Sm.equal r r'
        then gty
        else GTmodty (p', (rx', r'))

    | GTmem mt ->
        let mp  = Mid.map_filter (function Pat_Axiom(Axiom_Mpath m) -> Some m | _ -> None)
                    s.ps_patloc in
        let mt' = EcMemory.mt_substm s.ps_sty.ts_p mp
                    (ty_subst s.ps_sty) mt in
        if mt == mt' then gty else GTmem mt'

  let ogty_subst (s : p_subst) (ogty : ogty) =
    match ogty with
    | OGTty ty -> OGTty (omap (fun ty -> gty_as_ty (gty_subst s (GTty ty))) ty)
    | OGTmem mt -> OGTmem (omap (fun mt -> gty_as_mem (gty_subst s (GTmem mt))) mt)
    | OGTmodty (Some (mt, mr)) ->
       let mt, mr = gty_as_mod (gty_subst s (GTmodty (mt,mr))) in
       OGTmodty (Some (mt, mr))
    | OGTmodty None -> ogty

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
      in (s,xt)
    else
      (s, (x, gty'))

  let add_pbindings = List.map_fold add_pbinding

  (* ------------------------------------------------------------------------ *)
  let rec p_subst (s : p_subst) (p : pattern) =
    let p = match p with
    | Pat_Anything -> Pat_Anything
    | Pat_Sub p -> Pat_Sub (p_subst s p)
    | Pat_Or lp -> Pat_Or (List.map (p_subst s) lp)
    | Pat_Instance _ -> assert false
    | Pat_Red_Strat (p,f) -> Pat_Red_Strat (p_subst s p,f)
    | Pat_Type (p,gty) ->
       let gty = ogty_subst s gty in
       p_type (p_subst s p) gty
    | Pat_Meta_Name (p,name,ob) -> begin
        match Mid.find_opt name s.ps_patloc with
        | Some p -> p
        | None -> Pat_Meta_Name (p_subst s p,name,ob)
      end
    | Pat_Axiom a -> begin
        match a with
        | Axiom_Form fp -> begin
            match fp.f_node with
            | Fquant (q, b, f) ->
               let s, b' = add_bindings s b in
               let p     = p_subst s (pat_form f) in
               p_f_quant q b' p

            | Flet (lp, f1, f2) ->
               let f1'    = p_subst s (pat_form f1) in
               let s, lp' = subst_lpattern s lp in
               let f2'    = p_subst s (pat_form f2) in
               p_let lp' f1' f2'

            | Flocal id -> begin
                match Mid.find_opt id s.ps_patloc with
                | Some (Pat_Axiom (Axiom_Local (id,ty))) -> pat_form (f_local id ty)
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
               p_type (p_pvar pv' ty' m') (OGTty (Some ty'))
               (* pat_form (FSmart.f_pvar (fp, (pv, fp.f_ty, m)) (pv', ty', m')) *)

            | Fglob (mp, m) ->
               let m'  = mem_subst s m in
               let mp' = mp_subst s mp in
               p_glob mp' m'
               (* pat_form (FSmart.f_glob (fp, (mp, m)) (mp', m')) *)

            | FhoareF hf ->
               assert (not (Mid.mem mhr s.ps_patloc)
                       && not (Mid.mem mhr s.ps_patloc));
               let pr' = p_subst s (pat_form hf.hf_pr) in
               let po' = p_subst s (pat_form hf.hf_po) in
               let mp' = xp_subst s hf.hf_f in
               p_hoareF pr' mp' po'
               (* FSmart.f_hoareF (fp, hf) { hf_pr = pr'; hf_po = po'; hf_f = mp'; } *)

            | FhoareS hs ->
               assert (not (Mid.mem (fst hs.hs_m) s.ps_patloc));
               let pr' = p_subst s (pat_form hs.hs_pr) in
               let po' = p_subst s (pat_form hs.hs_po) in
               let st' = stmt_subst s hs.hs_s in
               let me' = memenv_subst s hs.hs_m in
               p_hoareS  me' pr' st' po'
               (* FSmart.f_hoareS (fp, hs)
                *   { hs_pr = pr'; hs_po = po'; hs_s = st'; hs_m = me'; } *)

            | FbdHoareF bhf ->
               assert (not (Mid.mem mhr s.ps_patloc)
                       && not (Mid.mem mhr s.ps_patloc));
               let pr' = p_subst s (pat_form bhf.bhf_pr) in
               let po' = p_subst s (pat_form bhf.bhf_po) in
               let mp' = xp_subst s bhf.bhf_f in
               let bd' = p_subst s (pat_form bhf.bhf_bd) in
               p_bdHoareF pr' mp' po' (pat_cmp bhf.bhf_cmp) bd'
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
               p_bdHoareS me' pr' st' po'
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
               p_equivF pr' fl' fr' po'
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

               p_equivS ml' mr' pr' sl' sr' po'
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

               p_eagerF pr' sl' fl' fr' sr' po'
               (* FSmart.f_eagerF (fp, eg)
                *   { eg_pr = pr'; eg_sl = sl';eg_fl = fl';
                *     eg_fr = fr'; eg_sr = sr'; eg_po = po'; } *)

            | Fpr pr ->
               assert (not (Mid.mem mhr s.ps_patloc));
               let pr_mem   = mem_subst s pr.pr_mem in
               let pr_fun   = xp_subst s pr.pr_fun in
               let pr_args  = p_subst s (pat_form pr.pr_args) in
               let pr_event = p_subst s (pat_form pr.pr_event) in

               p_pr pr_mem pr_fun pr_args pr_event
               (* FSmart.f_pr (fp, pr) { pr_mem; pr_fun; pr_args; pr_event; } *)

            | Fif (f1, f2, f3) ->
               p_if (p_subst s (pat_form f1)) (p_subst s (pat_form f2))
                 (p_subst s (pat_form f3))

            | Fmatch (f1, fargs, ty) ->
               p_match (p_subst s (pat_form f1)) (ty_subst s.ps_sty ty)
                 (List.map (fun x -> p_subst s (pat_form x)) fargs)

            | Fint _ -> pat_form fp

            | Fapp (op,args) ->
               let p = p_app (p_subst s (pat_form op))
                         (List.map (fun x -> p_subst s (pat_form x)) args)
                         (Some (ty_subst s.ps_sty fp.f_ty)) in
               odfl p (p_betared_opt p)

            | Ftuple t ->
               p_tuple (List.map (fun x -> p_subst s (pat_form x)) t)

            | Fproj (f1,i) ->
               p_proj (p_subst s (pat_form f1)) i (ty_subst s.ps_sty fp.f_ty)

          end (* axiom_form *)

        | Axiom_Module mtop -> mtop_subst s mtop

        | Axiom_Mpath m -> mp_subst s m

        | Axiom_Xpath xp -> xp_subst s xp

        | Axiom_Memory m -> mem_subst s m

        | Axiom_MemEnv m -> memenv_subst s m

        | Axiom_Prog_Var pv -> pv_subst s pv

        | Axiom_Op (op,lty) ->
           let lty = List.Smart.map (ty_subst s.ps_sty) lty in
           pat_op op lty

        | Axiom_Instr i -> i_subst s i

        | Axiom_Stmt st -> stmt_subst s st

        | Axiom_Lvalue lv -> lv_subst s lv

        | Axiom_Hoarecmp _ -> p

        | Axiom_Local (id,ty) ->
           odfl p (omap (fun p -> p_type p (OGTty (Some ty)))
                     (Mid.find_opt id s.ps_patloc))

      end (* pat_axiom *)

    | Pat_Fun_Symbol (sym,lp) -> begin
        match sym,lp with
        | Sym_Form_If, [cond;p1;p2] ->
           let cond, p1, p2 = p_subst s cond, p_subst s p1, p_subst s p2 in
           p_if cond p1 p2
        | Sym_Form_App ty, op::args ->
           p_app (p_subst s op) (List.map (p_subst s) args) (Some (ty_subst s.ps_sty ty))
        | Sym_Form_Tuple, t ->
           p_tuple (List.map (p_subst s) t)
        | Sym_Form_Proj (i,ty), [p] ->
           p_proj (p_subst s p) i (ty_subst s.ps_sty ty)
        | Sym_Form_Match ty, op::args ->
           p_match (p_subst s op) (ty_subst s.ps_sty ty) (List.map (p_subst s) args)
        | Sym_Form_Quant (q,bs), [p] ->
           let s, b' = add_bindings s bs in
           let p'    = p_subst s p in
           p_f_quant q b' p'
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
        | Sym_App, op::args ->
           p_app (p_subst s op) (List.map (p_subst s) args) None
        | Sym_Quant (q,bs), [p] ->
           let s, b' = add_pbindings s bs in
           let p'    = p_subst s p in
           p_quant q b' p'

        | _ -> assert false

      end (* pat_fun_symbol *)
    in p

    and pv_subst s pv =
      (* FIXME *)
      let mp = Mid.map_filter (function Pat_Axiom(Axiom_Mpath m) -> Some m | _ -> None)
                 s.ps_patloc in
      let pv = EcTypes.pv_subst (EcPath.x_substm s.ps_sty.ts_p mp) pv in
      match xp_subst s pv.pv_name with
      | Pat_Axiom (Axiom_Xpath xp) when x_equal xp pv.pv_name -> pat_pv pv
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
         | Pat_Axiom(Axiom_Mpath m2) -> m_equal m1 m2
         | _ -> false in
       if List.for_all2 m_is_eq mp.m_args margs
       then pat_mpath mp
       else p_mpath (pat_mpath_top mp.m_top) margs

    and mem_subst s m =
      match Mid.find_opt m s.ps_patloc with
      | Some p -> p
      | _ -> pat_memory m

    and xp_subst s xp =
      let mp = Mid.map_filter (function Pat_Axiom(Axiom_Mpath m) -> Some m | _ -> None)
                 s.ps_patloc in
      let xp = EcPath.x_substm s.ps_sty.ts_p mp xp in
      match mp_subst s xp.x_top with
      | Pat_Axiom (Axiom_Mpath mp) when m_equal mp xp.x_top -> pat_xpath xp
      | p -> p_xpath p (pat_op xp.x_sub [])

    and memenv_subst s m =
      let mp  = Mid.map_filter
                  (function Pat_Axiom(Axiom_Mpath m) -> Some m | _ -> None)
                  s.ps_patloc in
      let mem = Mid.map_filter
                  (function Pat_Axiom(Axiom_Memory m) -> Some m | _ -> None)
                  s.ps_patloc in
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
      | Pat_Axiom(Axiom_Prog_Var pv) ->
         pat_lvalue
           (LvMap
              ((op,List.map (ty_subst s.ps_sty) lty),
               pv, e_map (ty_subst s.ps_sty) (fun x->x) e, ty_subst s.ps_sty ty))
      | _ -> assert false

    and p_betared_opt = function
      | Pat_Anything -> None
      | Pat_Meta_Name (p,n,ob) ->
         omap (fun p -> Pat_Meta_Name (p,n,ob)) (p_betared_opt p)
      | Pat_Sub p ->
         omap (fun p -> Pat_Sub p) (p_betared_opt p)
      | Pat_Or [p] -> p_betared_opt p
      | Pat_Or _ -> None
      | Pat_Instance _ -> assert false
      | Pat_Type (p,gty) ->
         omap (fun p -> p_type p gty) (p_betared_opt p)
      | Pat_Red_Strat (p,f) ->
         omap (fun p -> Pat_Red_Strat (p,f)) (p_betared_opt p)
      | Pat_Axiom (Axiom_Form f) ->
         let f2 = try EcFol.f_betared f with
                  | _ -> f in
         if f_equal f f2 then None
         else Some (pat_form f2)
      | Pat_Axiom _ -> None
      | Pat_Fun_Symbol (s,lp) ->
      match s,lp with
      | Sym_Form_App ty,
        (Pat_Fun_Symbol(Sym_Form_Quant(Llambda, bds),[p]))::pargs ->
         let (bs1,bs2),(pargs1,pargs2) = List.prefix2 bds pargs in
         let subst = p_subst_id in
         let subst =
           List.fold_left2 (fun s (id,_) p -> p_bind_local s id p)
             subst bs1 pargs1 in
         Some (p_app (p_f_quant Llambda bs2 (p_subst subst p)) pargs2 (Some ty))
      | Sym_App,
        (Pat_Fun_Symbol(Sym_Form_Quant(Llambda, bds),[p]))::pargs ->
         let (bs1,bs2),(pargs1,pargs2) = List.prefix2 bds pargs in
         let subst = p_subst_id in
         let subst =
           List.fold_left2 (fun s (id,_) p -> p_bind_local s id p)
             subst bs1 pargs1 in
         Some (p_app (p_f_quant Llambda bs2 (p_subst subst p)) pargs2 None)
      | Sym_Form_App ty,
        (Pat_Fun_Symbol(Sym_Quant(Llambda, bds),[p]))::pargs ->
         let (bs1,bs2),(pargs1,pargs2) = List.prefix2 bds pargs in
         let subst = p_subst_id in
         let subst =
           List.fold_left2 (fun s (id,_) p -> p_bind_local s id p)
             subst bs1 pargs1 in
         Some (p_app (p_quant Llambda bs2 (p_subst subst p)) pargs2 (Some ty))
      | Sym_App,
        (Pat_Fun_Symbol(Sym_Quant(Llambda, bds),[p]))::pargs ->
         let (bs1,bs2),(pargs1,pargs2) = List.prefix2 bds pargs in
         let subst = p_subst_id in
         let subst =
           List.fold_left2 (fun s (id,_) p -> p_bind_local s id p)
             subst bs1 pargs1 in
         Some (p_app (p_quant Llambda bs2 (p_subst subst p)) pargs2 None)
      | _ -> None

end

(* -------------------------------------------------------------------------- *)

let p_betared_opt = Psubst.p_betared_opt

(* -------------------------------------------------------------------------- *)

let p_destr_app = function
  | Pat_Axiom(Axiom_Form f) ->
     let p,lp = EcFol.destr_app f in
     pat_form p, List.map pat_form lp
  | Pat_Fun_Symbol(Sym_Form_App _,p::lp)
    | Pat_Fun_Symbol(Sym_App, p::lp) -> p,lp
  | p -> p, []

(* -------------------------------------------------------------------------- *)
let f_op_real_of_int = f_op EcCoreLib.CI_Real.p_real_of_int [] (tfun tint treal)

(* -------------------------------------------------------------------------- *)
let p_true  = pat_form EcFol.f_true
let p_false = pat_form EcFol.f_false

let p_is_true = function
  | Pat_Axiom(Axiom_Form f) -> EcCoreFol.is_true f
  | _ -> false

let p_is_false = function
  | Pat_Axiom(Axiom_Form f) -> EcCoreFol.is_false f
  | _ -> false

let p_bool_val p =
  if p_is_true p then Some true
  else if p_is_false p then Some false
  else None

let p_eq (p1 : pattern) (p2 : pattern) = match p1, p2 with
  | Pat_Axiom(Axiom_Form f1), Pat_Axiom (Axiom_Form f2) ->
     pat_form (f_eq f1 f2)
  | _ -> assert false

let p_not = function
  | Pat_Axiom(Axiom_Form f) -> pat_form (EcFol.f_not f)
  | p -> p_app (pat_form EcFol.fop_not) [p] (Some EcTypes.tbool)

let p_imp (p1 : pattern) (p2 : pattern) = match p1,p2 with
  | Pat_Axiom(Axiom_Form f1),
    Pat_Axiom(Axiom_Form f2) ->
     pat_form (EcFol.f_imp f1 f2)
  | _ -> p_app (pat_form EcFol.fop_imp) [p1;p2]
           (Some EcTypes.tbool)

let p_anda (p1 : pattern) (p2 : pattern) = match p1,p2 with
  | Pat_Axiom(Axiom_Form f1),
    Pat_Axiom(Axiom_Form f2) ->
     pat_form  (EcFol.f_anda f1 f2)
  | _ -> p_app (pat_form EcFol.fop_anda) [p1;p2]
           (Some EcTypes.tbool)

let p_ora (p1 : pattern) (p2 : pattern) = match p1, p2 with
  | Pat_Axiom (Axiom_Form f1), Pat_Axiom (Axiom_Form f2) ->
     pat_form (EcFol.f_ora f1 f2)
  | _ -> p_app (pat_form EcFol.fop_ora) [p1;p2] (Some EcTypes.tbool)

let p_iff (p1 : pattern) (p2 : pattern) = match p1, p2 with
  | Pat_Axiom (Axiom_Form f1), Pat_Axiom (Axiom_Form f2) ->
     pat_form (EcFol.f_iff f1 f2)
  | _ -> p_app (pat_form EcFol.fop_iff) [p1;p2] (Some EcTypes.tbool)

let p_and (p1 : pattern) (p2 : pattern) = match p1, p2 with
  | Pat_Axiom (Axiom_Form f1), Pat_Axiom (Axiom_Form f2) ->
     pat_form (EcFol.f_and f1 f2)
  | _ -> p_app (pat_form EcFol.fop_and) [p1;p2] (Some EcTypes.tbool)

let p_or (p1 : pattern) (p2 : pattern) = match p1, p2 with
  | Pat_Axiom (Axiom_Form f1), Pat_Axiom (Axiom_Form f2) ->
     pat_form (EcFol.f_or f1 f2)
  | _ -> p_app (pat_form EcFol.fop_or) [p1;p2] (Some EcTypes.tbool)

let p_ands (ps : pattern list) = match List.rev ps with
  | [] -> p_true
  | p::ps -> List.fold_left ((^~) p_and) p ps

(* -------------------------------------------------------------------------- *)
let p_int_0 = pat_form (f_i0)
let p_real_0 = pat_form (f_r0)

let p_destr_int (p : pattern) = match p with
  | Pat_Axiom (Axiom_Form { f_node = Fint x } ) -> x
  | Pat_Axiom (Axiom_Form { f_node = Fapp (op, [{f_node = Fint n}])})
       when f_equal op fop_int_opp ->
     EcBigInt.neg n
  | _ -> destr_error "p_destr_int"

let p_int_le (p1 : pattern) (p2 : pattern) = match p1, p2 with
  | Pat_Axiom (Axiom_Form f1), Pat_Axiom (Axiom_Form f2) ->
     pat_form (EcFol.f_int_le f1 f2)
  | _ -> p_app (pat_form (f_op EcCoreLib.CI_Int.p_int_le [] (toarrow [tint ; tint ] tbool))) [p1;p2] (Some EcTypes.tbool)

let p_int_lt (p1 : pattern) (p2 : pattern) = match p1, p2 with
  | Pat_Axiom (Axiom_Form f1), Pat_Axiom (Axiom_Form f2) ->
     pat_form (EcFol.f_int_lt f1 f2)
  | _ -> p_app (pat_form (f_op EcCoreLib.CI_Int.p_int_lt [] (toarrow [tint ; tint ] tbool))) [p1;p2] (Some EcTypes.tbool)

let p_int_add (p1 : pattern) (p2 : pattern) = match p1, p2 with
  | Pat_Axiom (Axiom_Form f1), Pat_Axiom (Axiom_Form f2) ->
     pat_form (EcFol.f_int_add f1 f2)
  | _ -> p_app (pat_form fop_int_add) [p1;p2] (Some EcTypes.tint)

let p_int_opp (p : pattern) = match p with
  | Pat_Axiom (Axiom_Form f) -> pat_form (EcFol.f_int_opp f)
  | _ -> p_app (pat_form fop_int_opp) [p] (Some EcTypes.tint)

let p_int_mul (p1 : pattern) (p2 : pattern) = match p1, p2 with
  | Pat_Axiom (Axiom_Form f1), Pat_Axiom (Axiom_Form f2) ->
     pat_form (EcFol.f_int_mul f1 f2)
  | _ -> p_app (pat_form (f_op EcCoreLib.CI_Int.p_int_mul [] (toarrow [tint ; tint ] tint))) [p1;p2] (Some EcTypes.tint)

let p_real_le (p1 : pattern) (p2 : pattern) = match p1, p2 with
  | Pat_Axiom (Axiom_Form f1), Pat_Axiom (Axiom_Form f2) ->
     pat_form (EcFol.f_real_le f1 f2)
  | _ -> p_app (pat_form (f_op EcCoreLib.CI_Real.p_real_le [] (toarrow [treal ; treal ] tbool))) [p1;p2] (Some EcTypes.tbool)

let p_real_lt (p1 : pattern) (p2 : pattern) = match p1, p2 with
  | Pat_Axiom (Axiom_Form f1), Pat_Axiom (Axiom_Form f2) ->
     pat_form (EcFol.f_real_lt f1 f2)
  | _ -> p_app (pat_form (f_op EcCoreLib.CI_Real.p_real_lt [] (toarrow [treal ; treal ] tbool))) [p1;p2] (Some EcTypes.tbool)

let p_real_add (p1 : pattern) (p2 : pattern) = match p1, p2 with
  | Pat_Axiom (Axiom_Form f1), Pat_Axiom (Axiom_Form f2) ->
     pat_form (EcFol.f_real_add f1 f2)
  | _ -> p_app (pat_form (f_op EcCoreLib.CI_Real.p_real_add [] (toarrow [tint ; tint ] treal))) [p1;p2] (Some EcTypes.treal)

let p_real_opp (p : pattern) = match p with
  | Pat_Axiom (Axiom_Form f) -> pat_form (EcFol.f_int_opp f)
  | _ -> p_app (pat_form (f_op EcCoreLib.CI_Real.p_real_opp [] (toarrow [treal] treal))) [p] (Some EcTypes.treal)

let p_real_mul (p1 : pattern) (p2 : pattern) = match p1, p2 with
  | Pat_Axiom (Axiom_Form f1), Pat_Axiom (Axiom_Form f2) ->
     pat_form (EcFol.f_real_mul f1 f2)
  | _ -> p_app (pat_form (f_op EcCoreLib.CI_Real.p_real_mul [] (toarrow [treal ; treal ] treal))) [p1;p2] (Some EcTypes.treal)

let p_real_inv (p : pattern) = match p with
  | Pat_Axiom (Axiom_Form f) -> pat_form (EcFol.f_real_inv f)
  | _ -> p_app (pat_form (f_op EcCoreLib.CI_Real.p_real_inv [] (toarrow [treal] treal))) [p] (Some EcTypes.treal)

(* -------------------------------------------------------------------------- *)
let p_is_not = function
  | Pat_Axiom(Axiom_Form f) -> EcFol.is_not f
  | _ -> false

let p_destr_not = function
  | Pat_Axiom(Axiom_Form f) -> pat_form (EcFol.destr_not f)
  | _ -> assert false

(* -------------------------------------------------------------------------- *)
let p_not_simpl (p : pattern) =
  if p_is_not p then p_destr_not p
  else if p_is_true p then p_false
  else if p_is_false p then p_true
  else p_not p

let p_imp_simpl (p1 : pattern) (p2 : pattern) =
  if p_is_true p1 then p2
  else if p_is_false p1 || p_is_true p2 then p_true
  else if p_is_false p2 then p_not_simpl p1
  else if p_equal p1 p2 then p_true
  else p_imp p1 p2

let p_anda_simpl (p1 : pattern) (p2 : pattern) =
  if p_is_true p1 then p2
  else if p_is_false p1 then p_false
  else if p_is_true p2 then p1
  else if p_is_false p2 then p_false
  else p_anda p1 p2

let p_ora_simpl (p1 : pattern) (p2 : pattern) =
  if p_is_true p1 then p_true
  else if p_is_false p1 then p2
  else if p_is_true p2 then p_true
  else if p_is_false p2 then p1
  else p_ora p1 p2

let rec p_iff_simpl (p1 : pattern) (p2 : pattern) =
       if p_equal  p1 p2 then p_true
  else if p_is_true  p1  then p2
  else if p_is_false p1  then p_not_simpl p2
  else if p_is_true  p2  then p1
  else if p_is_false p2  then p_not_simpl p1
  else
    let aux p1 = match p1 with
      | Pat_Fun_Symbol
        ((Sym_Form_App _ | Sym_App),
         [Pat_Axiom (Axiom_Form { f_node = Fop (op1, []) }
                     | Axiom_Op (op1,[]));p1]) ->
         Some op1, p1
      | Pat_Axiom
          (Axiom_Form
             { f_node = Fapp ({f_node = Fop (op,[])}, [f1]) } ) ->
         Some op, pat_form f1
      | _ -> None, p1 in
    match aux p1, aux p2 with
    | (Some op1, p1), (Some op2, p2)
         when
           (EcPath.p_equal op1 EcCoreLib.CI_Bool.p_not &&
              EcPath.p_equal op2 EcCoreLib.CI_Bool.p_not) ->
       p_iff_simpl p1 p2
    | _ -> p_iff p1 p2

let p_and_simpl (p1 : pattern) (p2 : pattern) =
  if      p_is_true p1  then p2
  else if p_is_false p1 then p_false
  else if p_is_true p2  then p1
  else if p_is_false p2 then p_false
  else p_and p1 p2

let p_or_simpl (p1 : pattern) (p2 : pattern) =
  if      p_is_true p1  then p_true
  else if p_is_false p1 then p2
  else if p_is_true p2  then p_true
  else if p_is_false p2 then p1
  else p_or p1 p2

let p_andas_simpl = List.fold_right p_anda_simpl

let rec p_eq_simpl (p1 : pattern) (p2 : pattern) =
  if p_equal p1 p2 then p_true
  else match p1, p2 with
  | Pat_Axiom (Axiom_Form { f_node = Fint _ } ),
    Pat_Axiom (Axiom_Form { f_node = Fint _ } ) -> p_false

  | Pat_Axiom (Axiom_Form { f_node = Fapp (op1, [{f_node = Fint _}]) }),
    Pat_Axiom (Axiom_Form { f_node = Fapp (op2, [{f_node = Fint _}]) })
      when f_equal op1 f_op_real_of_int &&
           f_equal op2 f_op_real_of_int
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

  | _ -> p_eq p1 p2


(* -------------------------------------------------------------------------- *)
let p_int_le_simpl (p1 : pattern) (p2 : pattern) =
  if p_equal p1 p2 then p_true
  else match p1, p2 with
  | Pat_Axiom (Axiom_Form { f_node = Fint x1 } ),
    Pat_Axiom (Axiom_Form { f_node = Fint x2 } ) ->
     pat_form (f_bool (EcBigInt.compare x1 x2 <= 0))
  | _, _ -> p_int_le p1 p2

let p_int_lt_simpl (p1 : pattern) (p2 : pattern) =
  if p_equal p1 p2 then p_true
  else match p1, p2 with
  | Pat_Axiom (Axiom_Form { f_node = Fint x1 } ),
    Pat_Axiom (Axiom_Form { f_node = Fint x2 } ) ->
     pat_form (f_bool (EcBigInt.compare x1 x2 < 0))
  | _, _ -> p_int_le p1 p2

let p_int_add_simpl (p1 : pattern) (p2 : pattern) =
  try pat_form (f_int (EcBigInt.add (p_destr_int p1) (p_destr_int p2)))
  with
  | DestrError _ ->
     if p_equal p_int_0 p1 then p2
     else if p_equal p_int_0 p2 then p1
     else match p2 with
          | Pat_Axiom (Axiom_Form { f_node = Fapp (op, [f2]) })
               when f_equal op fop_int_opp && p_equal p1 (pat_form f2) ->
             p_int_0
          | Pat_Fun_Symbol ((Sym_Form_App _ | Sym_App),
                            [Pat_Axiom (Axiom_Form op);p2])
               when f_equal op fop_int_opp && p_equal p1 p2 ->
             p_int_0
          | _ -> p_int_add p1 p2

let p_int_opp_simpl (p : pattern) = match p with
  | Pat_Axiom (Axiom_Form f) -> pat_form (f_int_opp_simpl f)
  | _ -> p_int_opp p

let p_int_mul_simpl (p1 : pattern) (p2 : pattern) = match p1, p2 with
  | Pat_Axiom (Axiom_Form f1), Pat_Axiom (Axiom_Form f2) ->
     pat_form (f_int_mul_simpl f1 f2)
  | _ -> p_int_mul p1 p2

let p_real_le_simpl (p1 : pattern) (p2 : pattern) =
  if p_equal p1 p2 then p_true else
    let aux p = match p with
      | Pat_Axiom (Axiom_Form { f_node = Fapp (op1,
                                               [{f_node = Fint x1}]) })
           when f_equal op1 f_op_real_of_int ->
         Some x1
      | _ -> None in
    match aux p1, aux p2 with
    | Some x1, Some x2 -> pat_form (f_bool (EcBigInt.compare x1 x2 <= 0))
    | _ -> p_real_le p1 p2

let p_real_lt_simpl (p1 : pattern) (p2 : pattern) =
  let f_op_real_of_int =
    f_op EcCoreLib.CI_Real.p_real_of_int [] (tfun tint treal) in
  if p_equal p1 p2 then p_true else
    let aux p = match p with
      | Pat_Axiom (Axiom_Form { f_node = Fapp (op1,
                                               [{f_node = Fint x1}]) })
           when f_equal op1 f_op_real_of_int ->
         Some x1
      | _ -> None in
    match aux p1, aux p2 with
    | Some x1, Some x2 -> pat_form (f_bool (EcBigInt.compare x1 x2 < 0))
    | _ -> p_real_lt p1 p2

let p_real_add_simpl (p1 : pattern) (p2 : pattern) = match p1, p2 with
  | Pat_Axiom (Axiom_Form f1), Pat_Axiom (Axiom_Form f2) ->
     pat_form (f_real_add_simpl f1 f2)
  | _ -> p_real_add p1 p2

let p_real_opp_simpl (p : pattern) = match p with
  | Pat_Axiom (Axiom_Form f) -> pat_form (f_real_opp_simpl f)
  | _ -> p_real_opp p

let p_real_mul_simpl (p1 : pattern) (p2 : pattern) = match p1, p2 with
  | Pat_Axiom (Axiom_Form f1), Pat_Axiom (Axiom_Form f2) ->
     pat_form (f_real_mul_simpl f1 f2)
  | _ -> p_real_mul p1 p2

let p_real_inv_simpl (p : pattern) = match p with
  | Pat_Axiom (Axiom_Form f) -> pat_form (f_real_inv_simpl f)
  | Pat_Fun_Symbol ((Sym_Form_App _ | Sym_App),
                    [Pat_Axiom (Axiom_Form { f_node = Fop (op,_) }
                                | Axiom_Op (op,_));f])
       when (op_kind op) = Some `Real_inv ->
     f
  | _ -> p_real_inv p


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
  match p1 with
  | Pat_Fun_Symbol(Sym_Form_Tuple,pargs) -> List.nth pargs i
  | Pat_Axiom(Axiom_Form f) -> pat_form (f_proj_simpl f i ty)
  | _ -> p_proj p1 i ty

let p_app_simpl_opt op pargs oty = match op,oty with
  | None, _ -> None
  | Some p, Some ty -> p_betared_opt (Pat_Fun_Symbol(Sym_Form_App ty,p::pargs))
  | Some p, None -> p_betared_opt (Pat_Fun_Symbol(Sym_App,p::pargs))

let p_app_simpl op pargs oty =
  odfl (p_app op pargs oty) (p_app_simpl_opt (Some op) pargs oty)

let p_forall_simpl b p =
  let b = List.filter (fun (id,_) -> Mid.mem id (pat_fv p)) b in
  p_f_forall b p

let p_exists_simpl b p =
  let b = List.filter (fun (id,_) -> Mid.mem id (pat_fv p)) b in
  p_f_exists b p

let p_destr_app p =
  match p with
  | Pat_Fun_Symbol ((Sym_Form_App _ | Sym_App), p::lp) -> p,lp
  | Pat_Axiom (Axiom_Form { f_node = Fapp (f,args) }) ->
     pat_form f, List.map pat_form args
  | _ -> p, []


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
    match p with
    | Pat_Fun_Symbol ((Sym_Form_App _ | Sym_App), p::_) ->
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
        (s : Psubst.p_subst) (id : Name.t) : pattern option =
    if ri.delta_h id
    then
      let p = Pat_Meta_Name (Pat_Anything,id,None) in
      let p' = Psubst.p_subst s p in
      if p = p'
      then
        try Some (pat_form (EcEnv.LDecl.unfold id hyps)) with
        | EcEnv.NotReducible -> None
      else Some p'
    else None

  let rec is_delta_p ri pop = match pop with
    | Pat_Axiom (Axiom_Form { f_node = Fop (op, _) } )
      | Pat_Axiom (Axiom_Op (op, _)) ->
       ri.delta_p op
    | Pat_Type (op, OGTty _) -> is_delta_p ri op
    | _ -> false

  let rec get_op = function
    | Pat_Axiom (Axiom_Form { f_node = Fop (op, lty) } )
      | Pat_Axiom (Axiom_Op (op, lty)) -> Some (op, lty)
    | Pat_Type (op, OGTty _) -> get_op op
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

  (* let p_can_eta x (f, args) =
   *   match List.rev args with
   *   | (Pat_Axiom (Axiom_Form { f_node = Flocal y }
   *                | Axiom_Local (y,_))
   *      | Pat_Meta_Name (Pat_Anything, y, _)) :: args ->
   *      let check v = not (Mid.mem x v.f_fv) in
   *      id_equal x y && List.for_all check (f :: args)
   *   | _ -> false *)


  let rec h_red_pattern_opt (hyps : EcEnv.LDecl.hyps) (ri : reduction_info)
        (s : Psubst.p_subst) (p : pattern) =
    try
      match p with
      | Pat_Anything -> None
      | Pat_Meta_Name (_,n,_) -> reduce_local_opt hyps ri s n
      | Pat_Sub p -> omap (fun x -> Pat_Sub x) (h_red_pattern_opt hyps ri s p)
      | Pat_Or _ -> assert false
      | Pat_Instance _ -> assert false
      | Pat_Red_Strat _ -> None
      | Pat_Type (p,gty) -> omap (fun x -> p_type x gty) (h_red_pattern_opt hyps ri s p)
      | Pat_Axiom a -> h_red_axiom_opt hyps ri s a
      | Pat_Fun_Symbol (symbol,lp) ->
      match symbol, lp with
      (* β-reduction *)
      | (Sym_Form_App _ | Sym_App),
        (Pat_Fun_Symbol ((Sym_Form_Quant (Llambda, _)
                          | Sym_Quant (Llambda,_)),[_]))::_
           when ri.beta -> p_betared_opt p

      (* ζ-reduction *)
      | Sym_Form_App ty, (Pat_Meta_Name (Pat_Anything,id,_)
                         | Pat_Axiom (Axiom_Form { f_node = Flocal id })
                         | Pat_Axiom (Axiom_Local (id,_)))::pargs ->
         if ri.beta then p_app_simpl_opt (reduce_local_opt hyps ri s id) pargs (Some ty)
         else omap (fun x -> p_app x pargs (Some ty)) (reduce_local_opt hyps ri s id)

      (* ζ-reduction *)
      | Sym_Form_Let (LSymbol(x,_)), [p1;p2] when ri.zeta ->
         let s = Psubst.p_bind_local Psubst.p_subst_id x p1 in
         Some (Psubst.p_subst s p2)

      (* ι-reduction (let-tuple) *)
      | Sym_Form_Let (LTuple ids), [Pat_Fun_Symbol (Sym_Form_Tuple, lp);p2]
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
      | (Sym_Form_App _ | Sym_App),
        (Pat_Axiom (Axiom_Form ({ f_node = Fop (op, _) ; f_ty = fty } as f1)))
        ::pargs
           when ri.iota && EcEnv.Op.is_projection (EcEnv.LDecl.toenv hyps) op -> begin
          let op =
            match pargs with
            | [mk] -> begin
                match odfl mk (h_red_pattern_opt hyps ri s mk) with
                | Pat_Axiom (Axiom_Form { f_node = Fapp ({ f_node = Fop (mkp, _)}, mkargs) } ) ->
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
                | Pat_Fun_Symbol
                   ((Sym_Form_App _ | Sym_App),
                    (Pat_Axiom (Axiom_Form { f_node = Fop (mkp,_)}
                                | Axiom_Op (mkp,_)))::pargs) ->
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
                omap (fun x -> p_app x pargs (Some fty)) (h_red_form_opt hyps ri s f1)
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
      | Sym_Form_App ty,
        (Pat_Axiom (Axiom_Form ({ f_node = Fop (op, lty) } as f1)))::args
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
              | Pat_Axiom (Axiom_Form { f_node = Fop (op, _) }
                           | Axiom_Op (op, _ )), cargs
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
             omap (fun x -> p_app x args (Some ty))
               (h_red_form_opt hyps ri s f1)
        end

      (* ι-reduction (match-fix) *)
      | Sym_App,
        (Pat_Axiom (Axiom_Form ({ f_node = Fop (op, lty) } as f1)))::args
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
              | Pat_Axiom (Axiom_Form { f_node = Fop (op, _) }
                           | Axiom_Op (op, _ )), cargs
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
             omap (fun x -> p_app x args (None))
               (h_red_form_opt hyps ri s f1)
        end

      (* μ-reduction *)
      | Sym_Form_Glob, [mp;mem] when ri.modpath ->
         let p' = match mp, mem with
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
         let pv = match ppv with
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
    | Sym_Form_App ty,
      (Pat_Axiom (Axiom_Form ({f_node = Fop (op, tys); } as fo)))::args
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
             | (Pat_Axiom (Axiom_Form { f_node = Fop (op1, _)}), args1),
               (Pat_Axiom (Axiom_Form { f_node = Fop (op2, _)}), args2)
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

         | _ when ri.delta_p op ->
            let op = h_red_op_opt hyps ri s op tys in
            p_app_simpl_opt op args (Some ty)

         | _ -> Some p
       in
       begin
         match p' with
         | Some p' ->
            if p_equal p p'
            then omap (fun l -> p_app (pat_form fo) l (Some ty))
                   (h_red_args (fun x -> x) h_red_pattern_opt hyps ri s args)
            else Some p'
         | None -> None
       end

    (* δ-reduction *)
    | Sym_Form_App ty, pop::args when is_delta_p ri pop ->
       let op = reduce_op ri (EcEnv.LDecl.toenv hyps) pop in
       omap (fun op -> p_app_simpl op args (Some ty)) op

    (* δ-reduction *)
    | Sym_App, pop::args when is_delta_p ri pop ->
       let op = reduce_op ri (EcEnv.LDecl.toenv hyps) pop in
       omap (fun op -> p_app_simpl op args None) op

    (* (\* η-reduction *\)
     * | Sym_Form_Quant (Llambda, [x, GTty _]),
     *   [Pat_Axiom (Axiom_Form { f_node = Fapp (fn, args) })]
     *      when can_eta x (fn, args)
     *   -> Some (pat_form
     *              (EcFol.f_ty_app
     *                 (EcEnv.LDecl.toenv hyps) fn
     *                 (List.take (List.length args - 1) args)))
     *
     * (\* η-reduction *\)
     * | Sym_Form_Quant (Llambda, [x, GTty _]),
     *   [Pat_Fun_Symbol (Sym_Form_App ty, pn::pargs)]
     *      when p_can_eta x (pn, pargs) ->
     *
     *
     * (\* contextual rule - let *\)
     * | Flet (lp, f1, f2) -> f_let lp (h_red ri env hyps f1) f2
     *
     * (\* Contextual rule - application args. *\)
     * | Fapp (f1, args) ->
     *    f_app (h_red ri env hyps f1) args f.f_ty
     *
     * (\* Contextual rule - bindings *\)
     * | Fquant (Lforall as t, b, f1)
     *   | Fquant (Lexists as t, b, f1) when ri.logic = Some `Full -> begin
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
      | Axiom_Module m      -> h_red_mpath_top_opt hyps ri s m
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
           omap (fun p -> p_assign (pat_lvalue lv) p)
             (h_red_form_opt hyps ri s (form_of_expr e))
      end
    | Srnd (lv,e) -> begin
        match h_red_lvalue_opt hyps ri s lv with
        | Some lv -> Some (p_sample lv (pat_form (form_of_expr e)))
        | None ->
           omap (fun p -> p_sample (pat_lvalue lv) p)
             (h_red_form_opt hyps ri s (form_of_expr e))
      end
    | Scall (olv,f,args) -> begin
        match omap (h_red_lvalue_opt hyps ri s) olv with
        | Some (Some lv) ->
           Some (p_call (Some lv) (pat_xpath f)
                   (List.map (fun x -> pat_form (form_of_expr x)) args))
        | Some None | None ->
        match h_red_xpath_opt hyps ri s f with
        | Some f ->
           Some (p_call (omap pat_lvalue olv) f
                   (List.map (fun x -> pat_form (form_of_expr x)) args))
        | None ->
           let olv = omap pat_lvalue olv in
           omap
             (fun args -> p_call olv (pat_xpath f) args)
             (h_red_args (fun e -> pat_form (form_of_expr e))
                (fun hyps ri s e -> h_red_form_opt hyps ri s (form_of_expr e))
                hyps ri s args)
      end
    | Sif (cond,s1,s2) -> begin
        match h_red_form_opt hyps ri s (form_of_expr cond) with
        | Some cond ->
           Some (p_instr_if cond (pat_stmt s1) (pat_stmt s2))
        | None ->
        match h_red_stmt_opt hyps ri s s1 with
        | Some s1 ->
           Some (p_instr_if (pat_form(form_of_expr cond)) s1 (pat_stmt s2))
        | None ->
           omap
             (fun s2 -> p_instr_if (pat_form(form_of_expr cond)) (pat_stmt s1) s2)
             (h_red_stmt_opt hyps ri s s2)
      end
    | Swhile (cond,body) -> begin
        match h_red_form_opt hyps ri s (form_of_expr cond) with
        | Some cond -> Some (p_while cond (pat_stmt body))
        | None ->
           omap (fun s -> p_while (pat_form(form_of_expr cond)) s)
             (h_red_stmt_opt hyps ri s body)
      end
    | Sassert e -> omap p_assert (h_red_form_opt hyps ri s (form_of_expr e))
    | Sabstract name ->
       if ri.delta_h name
       then MName.find_opt name s.ps_patloc
       else None

  and h_red_stmt_opt hyps ri s stmt =
    omap (fun l -> Pat_Fun_Symbol(Sym_Stmt_Seq,l))
      (h_red_args pat_instr h_red_instr_opt hyps ri s stmt.s_node)

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
         | Some p -> Some (p_xpath p (pat_op x.x_sub []))
         | None -> None
    else None

  and h_red_local_opt _hyps ri s id _ty =
    if ri.delta_h id
    then MName.find_opt id s.ps_patloc
    else None

  and h_red_form_opt hyps ri s (f : form) =
    match f.f_node with
    (* β-reduction *)
    | Fapp ({ f_node = Fquant (Llambda, _, _)}, _) when ri.beta ->
       begin
         try Some (Pat_Axiom(Axiom_Form(f_betared f))) with
         | _ -> None
       end

    (* ζ-reduction *)
    | Flocal x -> reduce_local_opt hyps ri s x

    (* ζ-reduction *)
    | Fapp ({ f_node = Flocal x }, args) ->
       let pargs = List.map pat_form args in
       p_app_simpl_opt (reduce_local_opt hyps ri s x) pargs (Some f.f_ty)

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
    | Fapp ({ f_node = Fop (p, _); f_ty = ty} as f1, args)
         when ri.iota && EcEnv.Op.is_projection (EcEnv.LDecl.toenv hyps) p -> begin
        let op =
          match args with
          | [mk] -> begin
              match odfl (pat_form mk) (h_red_form_opt hyps ri s mk) with
              | Pat_Axiom
                (Axiom_Form
                   { f_node =
                       Fapp ({ f_node = Fop (mkp, _) }, mkargs) } ) ->
                 if not (EcEnv.Op.is_record_ctor (EcEnv.LDecl.toenv hyps) mkp) then
                   None
                 else
                   let v = oget (EcEnv.Op.by_path_opt (* op *) mkp (EcEnv.LDecl.toenv hyps)) in
                   let v = proj3_2 (EcDecl.operator_as_proj v) in
                   let v = try Some(List.nth mkargs v)
                           with _ -> None in
                   begin
                     match v with
                     | None -> None
                     | Some v -> h_red_form_opt hyps ri s v
                   end
              | Pat_Fun_Symbol
                  ((Sym_Form_App _ | Sym_App),
                   (Pat_Axiom (Axiom_Form { f_node = Fop (mkp,_)}
                               | Axiom_Op (mkp,_)))::pargs) ->
                 if not (EcEnv.Op.is_record_ctor (EcEnv.LDecl.toenv hyps) mkp) then None
                 else
                   let v = oget (EcEnv.Op.by_path_opt (* op *) mkp (EcEnv.LDecl.toenv hyps)) in
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
              omap (fun x -> p_app x (List.map pat_form args) (Some ty))
                (h_red_form_opt hyps ri s f1)
           | _ -> op
      end

    (* ι-reduction (tuples projection) *)
    | Fproj(f1, i) when ri.iota ->
       let f' = f_proj_simpl f1 i f.f_ty in
       if f_equal f f'
       then omap (fun x -> p_proj x i f.f_ty) (h_red_form_opt hyps ri s f1)
       else Some (pat_form f')

    (* ι-reduction (if-then-else) *)
    | Fif (f1, f2, f3) when ri.iota ->
       let f' = f_if_simpl f1 f2 f3 in
       if f_equal f f'
       then omap (fun x -> p_if x (pat_form f2) (pat_form f3)) (h_red_form_opt hyps ri s f1)
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
            | Pat_Axiom(Axiom_Form { f_node = Fop (p, _)}), cargs
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
          omap (fun x -> p_app x (List.map pat_form fargs) (Some f.f_ty))
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
            let op = h_red_op_opt hyps ri s p tys in
            p_app_simpl_opt op (List.map pat_form args) (Some f.f_ty)

         | _ -> Some (pat_form f)
       in
       begin
         match f' with
         | Some (Pat_Axiom(Axiom_Form f')) ->
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
       let op = h_red_op_opt hyps ri s p tys in
       p_app_simpl_opt op (List.map pat_form args) (Some f.f_ty)

    (* η-reduction *)
    | Fquant (Llambda, [x, GTty _], { f_node = Fapp (f, [{ f_node = Flocal y }]) })
         when id_equal x y && not (Mid.mem x f.f_fv)
      -> Some (pat_form f)

    (* contextual rule - let *)
    | Flet (lp, f1, f2) ->
       omap (fun x -> p_let lp x (pat_form f2)) (h_red_form_opt hyps ri s f1)

    (* Contextual rule - application args. *)
    | Fapp (f1, args) ->
       omap (fun x -> p_app x (List.map pat_form args) (Some f.f_ty))
         (h_red_form_opt hyps ri s f1)

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
          let hyps = List.fold_left (fun h (id,k) -> EcEnv.LDecl.add_local id k h)
              hyps b' in
          omap (ctor b) (h_red_form_opt hyps ri s f1)
        with EcEnv.NotReducible ->
          let f' = ctor b (pat_form f1) in
          if (match f' with | Pat_Axiom(Axiom_Form f') -> f_equal f f'
                            | _ -> false)
          then None
          else Some f'
      end

    | _ -> None

end
