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

type pbindings = (ident * gty option) list

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
  | Pat_Type       of pattern * gty

and reduction_strategy = pattern -> axiom -> (pattern * axiom) option


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
let rec expr_of_form (f : form) : expr option = match f.f_node with
  | Fquant (q,b,f1)    ->
     let eq = match q with
       | Llambda -> `ELambda
       | Lforall -> `EForall
       | Lexists -> `EExists in
     let b = try Some(List.map (snd_map EcFol.gty_as_ty) b) with
             | _ -> None in
     odfl None (omap (fun b -> omap (EcTypes.e_quantif eq b)
                                 (expr_of_form f1)) b)
  | Fif (f1,f2,f3)     -> begin
      match expr_of_form f1 with
      | None -> None
      | Some e1 ->
      match expr_of_form f2 with
      | None -> None
      | Some e2 ->
      match expr_of_form f3 with
      | None -> None
      | Some e3 -> Some (EcTypes.e_if e1 e2 e3)
    end
  | Fmatch (f1,lf,ty) -> begin
      match expr_of_form f1 with
      | None -> None
      | Some e1 -> omap (fun l -> EcTypes.e_match e1 l ty)
                     (olist_all expr_of_form lf)
    end
  | Flet (lp,f1,f2)    ->
     odfl None
       (omap (fun e1 ->
            omap (fun e2 -> EcTypes.e_let lp e1 e2)
              (expr_of_form f2))
          (expr_of_form f1))
  | Fint i             -> Some (EcTypes.e_int i)
  | Flocal id          -> Some (EcTypes.e_local id f.f_ty)
  | Fpvar (pv,_)       -> Some (EcTypes.e_var pv f.f_ty)
  | Fop (op,lty)       -> Some (EcTypes.e_op op lty f.f_ty)
  | Fapp (f1,args)     ->
     odfl None
       (omap (fun e1 ->
            omap (fun l -> EcTypes.e_app e1 l f.f_ty)
              (olist_all expr_of_form args))
          (expr_of_form f1))
  | Ftuple t           ->
     omap (fun l -> EcTypes.e_tuple l) (olist_all expr_of_form t)
  | Fproj (f1,i)       ->
     omap (fun e -> EcTypes.e_proj e i f.f_ty) (expr_of_form f1)
  | _                  -> None

(* -------------------------------------------------------------------------- *)

type map = pattern MName.t


(* -------------------------------------------------------------------------- *)
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
let p_equal : pattern -> pattern -> bool = (==)

(* -------------------------------------------------------------------------- *)
let p_type (p : pattern) (gty : gty) =
  match p with
  | Pat_Type(_,gty2) when gty_equal gty gty2 -> p
  | Pat_Type _ -> assert false
  | _ -> Pat_Type(p,gty)

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
  | p -> Pat_Type(p,GTty ty)

let p_lvalue_tuple (p : pattern list) =
  let rec oget_pv acc = function
    | [] -> Some (List.rev acc)
    | a :: r ->
       match a with
       | Pat_Type(Pat_Axiom(Axiom_Prog_Var pv),GTty ty)
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
     Pat_Axiom(Axiom_Form (f_hoareF pr f po))
  | _ -> Pat_Fun_Symbol(Sym_Form_Hoare_F,[pr;f;po])

let p_hoareS (m : pattern) (pr : pattern) (s : pattern) (po : pattern) =
  match m,pr,s,po with
  | Pat_Axiom(Axiom_MemEnv m),
    Pat_Axiom(Axiom_Form pr),
    Pat_Axiom(Axiom_Stmt s),
    Pat_Axiom(Axiom_Form po) ->
     Pat_Axiom(Axiom_Form (f_hoareS m pr s po))
  | _ -> Pat_Fun_Symbol(Sym_Form_Hoare_F,[m;pr;s;po])

let p_bdHoareF (pr : pattern) (f : pattern) (po : pattern) (cmp : pattern)
      (bd : pattern) =
  match pr, f, po, cmp, bd with
  | Pat_Axiom(Axiom_Form pr),
    Pat_Axiom(Axiom_Xpath f),
    Pat_Axiom(Axiom_Form po),
    Pat_Axiom(Axiom_Hoarecmp cmp),
    Pat_Axiom(Axiom_Form bd) ->
     Pat_Axiom(Axiom_Form(f_bdHoareF pr f po cmp bd))
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
     Pat_Axiom(Axiom_Form(f_bdHoareS m pr s po cmp bd))
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

let rec p_map (f_ty : ty -> ty) (aux : pattern -> pattern) (p : pattern) =
  match p with
  | Pat_Anything -> aux p
  | Pat_Meta_Name (p,n,ob) ->
     let ob' =
       omap (fun l -> List.map (function
                          | (a,Some (GTty ty)) -> a, Some (GTty (f_ty ty))
                          | x -> x) l) ob in
     Pat_Meta_Name(aux p,n,ob')
  | Pat_Sub p -> Pat_Sub (aux p)
  | Pat_Or lp -> Pat_Or (List.map aux lp)
  | Pat_Instance _ -> assert false
  | Pat_Red_Strat(p,f) -> Pat_Red_Strat(aux p,f)
  | Pat_Type(p,GTty ty) -> Pat_Type(aux p,GTty (f_ty ty))
  | Pat_Type(p,gty) -> Pat_Type(aux p,gty)
  | Pat_Fun_Symbol(s,lp) ->
     let s = match s with
       | Sym_Form_App ty -> Sym_Form_App (f_ty ty)
       | Sym_Form_Match ty -> Sym_Form_Match (f_ty ty)
       | Sym_Form_Quant (q,bs) ->
          let f (x,gty as b) = match gty with
            | GTty ty -> (x,GTty (f_ty ty))
            | _ -> b in
          Sym_Form_Quant (q,List.map f bs)
       | Sym_Form_Pvar ty -> Sym_Form_Pvar (f_ty ty)
       | Sym_Quant (q,ob) ->
          let f (x,ogty as b) = match ogty with
            | Some (GTty ty) -> (x,Some (GTty (f_ty ty)))
            | _ -> b in
          Sym_Quant (q, List.map f ob)
       | Sym_Form_Let lp ->
          let lp = match lp with
            | LSymbol (x,ty) -> LSymbol (x,f_ty ty)
            | LTuple t -> LTuple (List.map (fun (x,ty) -> (x,f_ty ty)) t)
            | LRecord (p,l) -> LRecord (p,List.map (fun (x,ty) -> (x,f_ty ty)) l) in
          Sym_Form_Let lp
       | _ -> s in
     Pat_Fun_Symbol(s, List.map aux lp)
  | Pat_Axiom a ->
     match a with
     | Axiom_Form f -> pat_form (f_map f_ty (fun x -> x) f)
     | Axiom_Op (op,lty) -> pat_op op (List.map f_ty lty)
     | Axiom_Local (id,ty) -> pat_local id (f_ty ty)
     | Axiom_Instr i -> begin
         match i.i_node with
         | Sasgn (lv,e) -> pat_instr (i_asgn (lv_ty f_ty lv,e_map f_ty (fun x->x) e))
         | Srnd (lv,e) -> pat_instr (i_rnd (lv_ty f_ty lv,e_map f_ty (fun x->x) e))
         | Scall (olv,f,args) ->
            pat_instr (i_call (omap (lv_ty f_ty) olv,f,
                               List.map (e_map f_ty (fun x->x)) args))
         | Sif (e,s1,s2) ->
            let p = match aux (pat_stmt s1),aux (pat_stmt s2) with
              | Pat_Axiom(Axiom_Stmt s1),Pat_Axiom(Axiom_Stmt s2) ->
                 pat_instr (i_if (e_map f_ty (fun x->x) e,s1,s2))
              | s1,s2 ->
                 Pat_Fun_Symbol(Sym_Instr_If,[pat_form(form_of_expr mhr e);s1;s2])
            in p
         | Swhile (e,s) -> begin
             match aux (pat_stmt s) with
             | Pat_Axiom(Axiom_Stmt s) ->
                pat_instr (i_while (e_map f_ty (fun x->x) e,s))
             | s ->
                Pat_Fun_Symbol(Sym_Instr_While,[pat_form(form_of_expr mhr e);s])
           end
         | Sassert e -> pat_instr (i_assert (e_map f_ty (fun x->x) e))
         | Sabstract _ -> p
       end
     | Axiom_Lvalue lv -> pat_lvalue (lv_ty f_ty lv)
     | _ -> p



let rec p_map_fold (f : 'a -> pattern -> 'a * pattern) (a : 'a) (p : pattern) : 'a * pattern =
  let a, p' = f a p in
  if not (p = p') then a, p' else
  match p with
  | Pat_Anything -> f a p
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
     let a, p = p_map_fold f a p in a, Pat_Type (p, gty)
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
            let a, pe  = p_map_fold f a (pat_form (form_of_expr mhr e)) in
            a, p_assign plv pe
         | Srnd (lv,e) ->
            let a, plv = p_map_fold f a (pat_lvalue lv) in
            let a, pe  = p_map_fold f a (pat_form (form_of_expr mhr e)) in
            a, p_sample plv pe
         | Scall (olv,xp,args) ->
            let a, olv = match olv with
              | Some lv -> let a,p = p_map_fold f a (pat_lvalue lv) in a, Some p
              | None -> a, None in
            let a, xp = p_map_fold f a (pat_xpath xp) in
            let a, args =
              List.map_fold (p_map_fold f) a
                (List.map (fun arg -> pat_form (form_of_expr mhr arg)) args) in
            a, p_call olv xp args
         | Sif (e,s1,s2) ->
            let a, pe = p_map_fold f a (pat_form (form_of_expr mhr e)) in
            let a, s1 = p_map_fold f a (pat_stmt s1) in
            let a, s2 = p_map_fold f a (pat_stmt s2) in
            a, p_instr_if pe s1 s2
         | Swhile (e,s) ->
            let a, pe = p_map_fold f a (pat_form (form_of_expr mhr e)) in
            let a, s  = p_map_fold f a (pat_stmt s) in
            a, p_while pe s
         | Sassert e ->
            let a, p = p_map_fold f a (pat_form (form_of_expr mhr e)) in
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
  | Pat_Type(p,gty) -> Pat_Type(replace p, gty)
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
            let pe = replace (pat_form (form_of_expr mhr e)) in
            p_assign plv pe
         | Srnd (lv,e) ->
            let plv = replace (pat_lvalue lv) in
            let pe = replace (pat_form (form_of_expr mhr e)) in
            p_sample plv pe
         | Scall (olv,xp,args) ->
            let olv = match olv with
              | Some lv -> let p = replace (pat_lvalue lv) in Some p
              | None -> None in
            let xp = replace (pat_xpath xp) in
            let args = List.map replace
                         (List.map (fun arg -> pat_form (form_of_expr mhr arg)) args) in
            p_call olv xp args
         | Sif (e,s1,s2) ->
            let pe = replace (pat_form (form_of_expr mhr e)) in
            let s1 = replace (pat_stmt s1) in
            let s2 = replace (pat_stmt s2) in
            p_instr_if pe s1 s2
         | Swhile (e,s) ->
            let pe = replace (pat_form (form_of_expr mhr e)) in
            let s  = replace (pat_stmt s) in
            p_while pe s
         | Sassert e ->
            let p = replace (pat_form (form_of_expr mhr e)) in
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
      ps_freshen : bool;
      ps_patloc  : pattern             Mid.t;
      ps_mp      : mpath               Mid.t;
      ps_mem     : ident               Mid.t;
      ps_opdef   : (ident list * expr) Mp.t;
      ps_pddef   : (ident list * form) Mp.t;
      ps_exloc   : expr                Mid.t;
      ps_sty     : ty_subst;
    }

  let p_subst_id = {
      ps_freshen = false;
      ps_patloc  = Mid.empty;
      ps_mp      = Mid.empty;
      ps_mem     = Mid.empty;
      ps_opdef   = Mp.empty;
      ps_pddef   = Mp.empty;
      ps_exloc   = Mid.empty;
      ps_sty     = ty_subst_id;
    }

  let is_subst_id s =
       s.ps_freshen = false
    && is_ty_subst_id s.ps_sty
    && Mid.is_empty   s.ps_patloc
    && Mid.is_empty   s.ps_mem
    && Mp.is_empty    s.ps_opdef
    && Mp.is_empty    s.ps_pddef
    && Mid.is_empty   s.ps_exloc

  let p_subst_init ?mods ?sty ?opdef ?prdef () =
    { p_subst_id with
      ps_mp    = odfl Mid.empty mods;
      ps_sty   = odfl ty_subst_id sty;
      ps_opdef = odfl Mp.empty opdef;
      ps_pddef = odfl Mp.empty prdef;
    }

  let p_bind_local (s : p_subst) (id : ident) (p : pattern) =
    let merge o = assert (o = None); Some p in
    { s with ps_patloc = Mid.change merge id s.ps_patloc }

  let p_bind_mem (s : p_subst) (m1 : memory) (m2 : memory) =
    let merge o = assert (o = None); Some m2 in
    { s with ps_mem = Mid.change merge m1 s.ps_mem }

  let p_bind_mod (s : p_subst) (x : ident) (m : mpath) =
    let merge o = assert (o = None); Some m in
    { s with ps_mp = Mid.change merge x s.ps_mp }

  let p_bind_rename (s : p_subst) (nfrom : ident) (nto : ident) (ty : ty) =
    let np = pat_local nto ty in
    let ne = e_local nto ty in
    let s = p_bind_local s nfrom np in
    let merge o = assert (o = None); Some ne in
    { s with ps_exloc = Mid.change merge nfrom s.ps_exloc }

  (* ------------------------------------------------------------------------ *)
  let p_rem_local (s : p_subst) (n : ident) =
    { s with ps_patloc = Mid.remove n s.ps_patloc;
             ps_exloc  = Mid.remove n s.ps_exloc; }

  let p_rem_mem (s : p_subst) (m : memory) =
    { s with ps_mem = Mid.remove m s.ps_mem }

  let p_rem_mod (s : p_subst) (m : ident) =
    let smp = Mid.remove m s.ps_mp in
    let sty = s.ps_sty in
    let sty = { sty with ts_mp = EcPath.m_subst sty.ts_p smp } in
    { s with ps_mp = smp; ps_sty = sty; }

  (* ------------------------------------------------------------------------ *)
  let add_local (s : p_subst) (n,t as nt : ident * ty) =
    let n' = if s.ps_freshen then EcIdent.fresh n else n in
    let t' = (ty_subst s.ps_sty) t in
    if   n == n' && t == t'
    then (s, nt)
    else (p_bind_rename s n n' t'), (n',t')

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
        let xsub = EcPath.x_substm s.ps_sty.ts_p s.ps_mp in
        let p'   = mty_subst s.ps_sty.ts_p sub p in
        let rx'  = Sx.fold (fun m rx' -> Sx.add (xsub m) rx') rx Sx.empty in
        let r'   = Sm.fold (fun m r' -> Sm.add (sub m) r') r Sm.empty in

        if   p == p' && Sx.equal rx rx' && Sm.equal r r'
        then gty
        else GTmodty (p', (rx', r'))

    | GTmem mt ->
        let mt' = EcMemory.mt_substm s.ps_sty.ts_p s.ps_mp
                    (ty_subst s.ps_sty) mt in
        if mt == mt' then gty else GTmem mt'

  (* ------------------------------------------------------------------------ *)
  let add_binding (s : p_subst) (x,gty as xt : binding) =
    let gty' = gty_subst s gty in
    let x'   = if s.ps_freshen then EcIdent.fresh x else x in
    if   x == x' && gty == gty'
    then
      let s = match gty with
        | GTty _    -> p_rem_local s x
        | GTmodty _ -> p_rem_mod   s x
        | GTmem _   -> p_rem_mem   s x in
      (s,xt)
    else
      let s = match gty' with
        | GTty   ty -> p_bind_rename s x x' ty
        | GTmodty _ -> p_bind_mod s x (EcPath.mident x')
        | GTmem   _ -> p_bind_mem s x x'
      in
      (s, (x', gty'))

  let add_bindings = List.map_fold add_binding

  (* ------------------------------------------------------------------------ *)
  let add_pbinding (s : p_subst) (x,ogty as xt : ident * gty option) =
    let gty' = omap (gty_subst s) ogty in
    let x'   = if s.ps_freshen then EcIdent.fresh x else x in
    if   x == x' && ogty == gty'
    then
      let s = match ogty with
        | Some (GTty _)    -> p_rem_local s x
        | Some (GTmodty _) -> p_rem_mod   s x
        | Some (GTmem _)   -> p_rem_mem   s x
        | None             -> s
      in (s,xt)
    else
      let s = match gty' with
        | Some (GTty   ty) -> p_bind_rename s x x' ty
        | Some (GTmodty _) -> p_bind_mod s x (EcPath.mident x')
        | Some (GTmem   _) -> p_bind_mem s x x'
        | None             -> s
      in
      (s, (x', gty'))

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
       let gty = gty_subst s gty in
       Pat_Type (p_subst s p,gty)
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
                | Some p -> p
                | None ->
                   let ty = ty_subst s.ps_sty fp.f_ty in
                   pat_form (FSmart.f_local (fp, (id, fp.f_ty)) (id, ty))
              end

            | Fop (p, lty) when Mp.mem p s.ps_opdef ->
               let ty   = ty_subst s.ps_sty fp.f_ty in
               let lty  = List.Smart.map (ty_subst s.ps_sty) lty in
               let body = oget (Mp.find_opt p s.ps_opdef) in
               p_subst_op s.ps_freshen (Some ty) lty [] body

            | Fop (p, lty) when Mp.mem p s.ps_pddef ->
               let ty   = ty_subst s.ps_sty fp.f_ty in
               let lty  = List.Smart.map (ty_subst s.ps_sty) lty in
               let body = oget (Mp.find_opt p s.ps_pddef) in
               p_subst_pd (Some ty) lty [] body

            | Fapp ({ f_node = Fop (op, lty) }, args) when Mp.mem op s.ps_opdef ->
               let ty   = ty_subst s.ps_sty fp.f_ty in
               let lty  = List.Smart.map (ty_subst s.ps_sty) lty in
               let body = oget (Mp.find_opt op s.ps_opdef) in
               let args = List.map (fun f -> p_subst s (pat_form f)) args in
               p_subst_op s.ps_freshen (Some ty) lty args body

            | Fapp ({ f_node = Fop (op, lty) }, args) when Mp.mem op s.ps_pddef ->
               let ty   = ty_subst s.ps_sty fp.f_ty in
               let lty  = List.Smart.map (ty_subst s.ps_sty) lty in
               let body = oget (Mp.find_opt op s.ps_pddef) in
               let args = List.map (fun f -> p_subst s (pat_form f)) args in
               p_subst_pd (Some ty) lty args body

            | Fop (op, lty) ->
               let ty'  = ty_subst s.ps_sty fp.f_ty in
               let lty' = List.Smart.map (ty_subst s.ps_sty) lty in
               let op'  = s.ps_sty.ts_p op in
               pat_form (FSmart.f_op (fp, (op, lty, fp.f_ty)) (op', lty', ty'))

            | Fpvar (pv, m) ->
               let pv' = pv_subst s pv in
               let m'  = mem_subst s m in
               let ty' = ty_subst s.ps_sty fp.f_ty in
               p_type (p_pvar pv' ty' m') (GTty ty')
               (* pat_form (FSmart.f_pvar (fp, (pv, fp.f_ty, m)) (pv', ty', m')) *)

            | Fglob (mp, m) ->
               let m'  = mem_subst s m in
               let mp' = mp_subst s mp in
               p_glob mp' m'
               (* pat_form (FSmart.f_glob (fp, (mp, m)) (mp', m')) *)

            | FhoareF hf ->
               assert (not (Mid.mem mhr s.ps_mem) && not (Mid.mem mhr s.ps_mem));
               let pr' = p_subst s (pat_form hf.hf_pr) in
               let po' = p_subst s (pat_form hf.hf_po) in
               let mp' = xp_subst s hf.hf_f in
               p_hoareF pr' mp' po'
               (* FSmart.f_hoareF (fp, hf) { hf_pr = pr'; hf_po = po'; hf_f = mp'; } *)

            | FhoareS hs ->
               assert (not (Mid.mem (fst hs.hs_m) s.ps_mem));
               let pr' = p_subst s (pat_form hs.hs_pr) in
               let po' = p_subst s (pat_form hs.hs_po) in
               let st' = stmt_subst s hs.hs_s in
               let me' = memenv_subst s hs.hs_m in
               p_hoareS  me' pr' st' po'
               (* FSmart.f_hoareS (fp, hs)
                *   { hs_pr = pr'; hs_po = po'; hs_s = st'; hs_m = me'; } *)

            | FbdHoareF bhf ->
               assert (not (Mid.mem mhr s.ps_mem) && not (Mid.mem mhr s.ps_mem));
               let pr' = p_subst s (pat_form bhf.bhf_pr) in
               let po' = p_subst s (pat_form bhf.bhf_po) in
               let mp' = xp_subst s bhf.bhf_f in
               let bd' = p_subst s (pat_form bhf.bhf_bd) in
               p_bdHoareF pr' mp' po' (pat_cmp bhf.bhf_cmp) bd'
               (* FSmart.f_bdHoareF (fp, bhf)
                *   { bhf with bhf_pr = pr'; bhf_po = po';
                *              bhf_f  = mp'; bhf_bd = bd'; } *)

            | FbdHoareS bhs ->
               assert (not (Mid.mem (fst bhs.bhs_m) s.ps_mem));
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
               assert (not (Mid.mem mleft s.ps_mem) && not (Mid.mem mright s.ps_mem));
               let pr' = p_subst s (pat_form ef.ef_pr) in
               let po' = p_subst s (pat_form ef.ef_po) in
               let fl' = xp_subst s ef.ef_fl in
               let fr' = xp_subst s ef.ef_fr in
               p_equivF pr' fl' fr' po'
               (* FSmart.f_equivF (fp, ef)
                *   { ef_pr = pr'; ef_po = po'; ef_fl = fl'; ef_fr = fr'; } *)

            | FequivS eqs ->
               assert (not (Mid.mem (fst eqs.es_ml) s.ps_mem) &&
                         not (Mid.mem (fst eqs.es_mr) s.ps_mem));
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
               assert (not (Mid.mem mleft s.ps_mem) && not (Mid.mem mright s.ps_mem));
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
               assert (not (Mid.mem mhr s.ps_mem));
               let pr_mem   = mem_subst s pr.pr_mem in
               let pr_fun   = xp_subst s pr.pr_fun in
               let pr_args  = p_subst s (pat_form pr.pr_args) in
               let pr_event = p_subst s (pat_form pr.pr_event) in

               p_pr pr_mem pr_fun pr_args pr_event
               (* FSmart.f_pr (fp, pr) { pr_mem; pr_fun; pr_args; pr_event; } *)

            | _ -> p_map (ty_subst s.ps_sty) (p_subst s) (pat_form fp)
          end (* axiom_form *)

        | Axiom_Module mtop -> mtop_subst s mtop

        | Axiom_Mpath m -> mp_subst s m

        | Axiom_Xpath xp -> xp_subst s xp

        | Axiom_Memory m -> mem_subst s m

        | Axiom_MemEnv m -> memenv_subst s m

        | Axiom_Prog_Var pv -> pv_subst s pv

        | Axiom_Op (op,lty) when Mp.mem op s.ps_opdef ->
           let lty  = List.Smart.map (ty_subst s.ps_sty) lty in
           let body = oget (Mp.find_opt op s.ps_opdef) in
           p_subst_op s.ps_freshen None lty [] body

        | Axiom_Op (op, lty) when Mp.mem op s.ps_pddef ->
           let lty  = List.Smart.map (ty_subst s.ps_sty) lty in
           let body = oget (Mp.find_opt op s.ps_pddef) in
           p_subst_pd None lty [] body

        | Axiom_Op (op,lty) ->
           let lty = List.Smart.map (ty_subst s.ps_sty) lty in
           pat_op op lty

        | Axiom_Instr i -> i_subst s i

        | Axiom_Stmt st -> stmt_subst s st

        | Axiom_Lvalue lv -> lv_subst s lv

        | Axiom_Hoarecmp _ -> p

        | Axiom_Local (id,ty) ->
           odfl p (omap (fun p -> p_type p (GTty ty)) (Mid.find_opt id s.ps_patloc))

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
           p_bdHoareS (p_subst s pm) (p_subst s pr) (p_subst s ps) (p_subst s po)
             (p_subst s cmp) (p_subst s bd)
        | Sym_Form_Equiv_F, [pr;fl;fr;po] ->
           p_equivF (p_subst s pr) (p_subst s fl) (p_subst s fr) (p_subst s po)
        | Sym_Form_Equiv_S, [ml;mr;pr;sl;sr;po] ->
           p_equivS (p_subst s ml) (p_subst s mr) (p_subst s pr) (p_subst s sl)
             (p_subst s sr) (p_subst s po)
        | Sym_Form_Eager_F, [pr;sl;fl;fr;sr;po] ->
           p_eagerF (p_subst s pr) (p_subst s sl) (p_subst s fl) (p_subst s fr)
             (p_subst s sr) (p_subst s po)
        | Sym_Form_Pr, [pm;pf;pargs;pevent] ->
           p_pr (p_subst s pm) (p_subst s pf) (p_subst s pargs) (p_subst s pevent)
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
      let pv = EcTypes.pv_subst (EcPath.x_substm s.ps_sty.ts_p s.ps_mp) pv in
      match xp_subst s pv.pv_name with
      | Pat_Axiom (Axiom_Xpath xp) when x_equal xp pv.pv_name -> pat_pv pv
      | p -> p_prog_var p pv.pv_kind


    and mtop_subst s mtop = match mtop with
      | `Local id ->
         odfl (pat_mpath_top (s.ps_sty.ts_mp (mpath mtop [])).m_top)
           (Mid.find_opt id s.ps_patloc)
      | _ -> pat_mpath_top (s.ps_sty.ts_mp (mpath mtop [])).m_top

    and mp_subst s mp =
      pat_mpath (s.ps_sty.ts_mp mp)

    and mem_subst s m =
      (* FIXME *)
      pat_memory (Mid.find_def m m s.ps_mem)

    and xp_subst s xp =
      (* FIXME *)
      pat_xpath (EcPath.x_substm s.ps_sty.ts_p s.ps_mp xp)

    and memenv_subst s m =
      (* FIXME *)
      pat_memenv (EcMemory.me_substm s.ps_sty.ts_p s.ps_mp s.ps_mem
                    (ty_subst s.ps_sty) m)

    and e_subst s e = p_subst s (pat_form (form_of_expr mhr e))

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

    and p_subst_op freshen oty lty args (tyids, e) =

      let e =
        (* FIXME *)
        let sty = Tvar.init tyids lty in
        let sty = { ty_subst_id with ts_v = Mid.find_opt^~ sty; } in
        let sty = { p_subst_id with ps_freshen = freshen; ps_sty = sty ; } in
        e_subst sty e
      in

      let (sag, args, e) =
        match e with
        | Pat_Axiom(Axiom_Form { f_node = Fquant (Llambda, largs, lbody) })
             when args <> [] ->
           let largs1, largs2 = List.takedrop (List.length args  ) largs in
           let  args1,  args2 = List.takedrop (List.length largs1)  args in
           (Mid.of_list (List.combine (List.map fst largs1) args1),
            args2, p_f_quant Llambda largs2 (pat_form lbody))
        | Pat_Fun_Symbol(Sym_Form_Quant (Llambda,largs),[pbody])
             when args <> [] ->
           let largs1, largs2 = List.takedrop (List.length args  ) largs in
           let  args1,  args2 = List.takedrop (List.length largs1)  args in
           (Mid.of_list (List.combine (List.map fst largs1) args1),
            args2, p_f_quant Llambda largs2 pbody)
        | _ -> (Mid.of_list [], args, e)
      in

      let sag = { p_subst_id with ps_patloc = sag } in
      p_app (p_subst sag e) args oty


    and p_subst_pd oty lty args (tyids, f) =
      (* FIXME: factor this out *)
      (* FIXME: is fd_freshen value correct? *)

      let p =
        let sty = Tvar.init tyids lty in
        let sty = { ty_subst_id with ts_v = Mid.find_opt^~ sty; } in
        let sty = { p_subst_id with ps_freshen = true; ps_sty = sty; } in
        p_subst sty (pat_form f)
      in

      let (sag, args, p) =
        match p with
        | Pat_Axiom(Axiom_Form f) -> begin
            match f.f_node with
            | Fquant (Llambda, largs, lbody) when args <> [] ->
               let largs1, largs2 = List.takedrop (List.length args  ) largs in
               let  args1,  args2 = List.takedrop (List.length largs1)  args in
               (Mid.of_list (List.combine (List.map fst largs1) args1),
                args2, pat_form (f_lambda largs2 lbody))

            | _ -> (Mid.of_list [], args, p)
          end
        | Pat_Fun_Symbol (Sym_Form_Quant (Llambda, largs), [lbody])
             when args <> [] ->
           let largs1, largs2 = List.takedrop (List.length args  ) largs in
           let  args1,  args2 = List.takedrop (List.length largs1)  args in
           (Mid.of_list (List.combine (List.map fst largs1) args1),
            args2, p_f_quant Llambda largs2 lbody)

        (* FIXME : Sym_Form_Quant *)
        | _ -> (Mid.of_list [], args, p)
      in

      let sag = { p_subst_id with ps_patloc = sag } in
      p_app (p_subst sag p) args oty

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


end

(* -------------------------------------------------------------------------- *)
let rec p_betared_opt = function
  | Pat_Anything -> None
  | Pat_Meta_Name (p,n,ob) ->
     omap (fun p -> Pat_Meta_Name (p,n,ob)) (p_betared_opt p)
  | Pat_Sub p ->
     omap (fun p -> Pat_Sub p) (p_betared_opt p)
  | Pat_Or [p] -> p_betared_opt p
  | Pat_Or _ -> None
  | Pat_Instance _ -> assert false
  | Pat_Type (p,gty) ->
     omap (fun p -> Pat_Type(p,gty)) (p_betared_opt p)
  | Pat_Red_Strat (p,f) ->
     omap (fun p -> Pat_Red_Strat (p,f)) (p_betared_opt p)
  | Pat_Axiom (Axiom_Form f) ->
     let f2 = try EcFol.f_betared f with
              | _ -> f in
     if f_equal f f2 then None
     else Some (Pat_Axiom(Axiom_Form f2))
  | Pat_Axiom _ -> None
  | Pat_Fun_Symbol (s,lp) ->
     match s,lp with
     | Sym_Form_App ty,
       (Pat_Fun_Symbol(Sym_Form_Quant(Llambda, bds),[p]))::pargs ->
        let (bs1,bs2),(pargs1,pargs2) = List.prefix2 bds pargs in
        let subst = Psubst.p_subst_id in
        let subst =
          List.fold_left2 (fun s (id,_) p -> Psubst.p_bind_local s id p)
            subst bs1 pargs1 in
        Some (p_app (p_f_quant Llambda bs2 (Psubst.p_subst subst p)) pargs2 (Some ty))
     | Sym_App,
       (Pat_Fun_Symbol(Sym_Form_Quant(Llambda, bds),[p]))::pargs ->
        let (bs1,bs2),(pargs1,pargs2) = List.prefix2 bds pargs in
        let subst = Psubst.p_subst_id in
        let subst =
          List.fold_left2 (fun s (id,_) p -> Psubst.p_bind_local s id p)
            subst bs1 pargs1 in
        Some (p_app (p_f_quant Llambda bs2 (Psubst.p_subst subst p)) pargs2 None)
     | Sym_Form_App ty,
       (Pat_Fun_Symbol(Sym_Quant(Llambda, bds),[p]))::pargs ->
        let (bs1,bs2),(pargs1,pargs2) = List.prefix2 bds pargs in
        let subst = Psubst.p_subst_id in
        let subst =
          List.fold_left2 (fun s (id,_) p -> Psubst.p_bind_local s id p)
            subst bs1 pargs1 in
        Some (p_app (p_quant Llambda bs2 (Psubst.p_subst subst p)) pargs2 (Some ty))
     | Sym_App,
       (Pat_Fun_Symbol(Sym_Quant(Llambda, bds),[p]))::pargs ->
        let (bs1,bs2),(pargs1,pargs2) = List.prefix2 bds pargs in
        let subst = Psubst.p_subst_id in
        let subst =
          List.fold_left2 (fun s (id,_) p -> Psubst.p_bind_local s id p)
            subst bs1 pargs1 in
        Some (p_app (p_quant Llambda bs2 (Psubst.p_subst subst p)) pargs2 None)
     | _ -> None


(* -------------------------------------------------------------------------- *)

let p_destr_app = function
  | Pat_Axiom(Axiom_Form f) ->
     let p,lp = EcFol.destr_app f in
     pat_form p, List.map pat_form lp
  | Pat_Fun_Symbol(Sym_Form_App _,p::lp)
    | Pat_Fun_Symbol(Sym_App, p::lp) -> p,lp
  | p -> p, []

(* -------------------------------------------------------------------------- *)
let p_true  = Pat_Axiom(Axiom_Form EcFol.f_true)
let p_false = Pat_Axiom(Axiom_Form EcFol.f_false)

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

let p_not = function
  | Pat_Axiom(Axiom_Form f) -> Pat_Axiom(Axiom_Form (EcFol.f_not f))
  | p -> p_app (Pat_Axiom(Axiom_Form EcFol.fop_not)) [p] (Some EcTypes.tbool)

let p_imp (p1 : pattern) (p2 : pattern) = match p1,p2 with
  | Pat_Axiom(Axiom_Form f1),
    Pat_Axiom(Axiom_Form f2) ->
     Pat_Axiom(Axiom_Form (EcFol.f_imp f1 f2))
  | _ -> p_app (Pat_Axiom(Axiom_Form EcFol.fop_imp)) [p1;p2]
           (Some EcTypes.tbool)

let p_anda (p1 : pattern) (p2 : pattern) = match p1,p2 with
  | Pat_Axiom(Axiom_Form f1),
    Pat_Axiom(Axiom_Form f2) ->
     Pat_Axiom(Axiom_Form (EcFol.f_anda f1 f2))
  | _ -> p_app (Pat_Axiom(Axiom_Form EcFol.fop_anda)) [p1;p2]
           (Some EcTypes.tbool)

(* -------------------------------------------------------------------------- *)
let p_is_not = function
  | Pat_Axiom(Axiom_Form f) -> EcFol.is_not f
  | _ -> false

let p_destr_not = function
  | Pat_Axiom(Axiom_Form f) -> Pat_Axiom(Axiom_Form (EcFol.destr_not f))
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
  | Pat_Axiom(Axiom_Form f) -> Pat_Axiom(Axiom_Form (f_proj_simpl f i ty))
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
