open EcUtils
open EcFol
open EcTypes
open EcPath
open EcMemory
open EcIdent
open EcModules

(* This is for EcTransMatching ---------------------------------------- *)
let default_start_name = "$start"
let default_end_name = "$end"
let default_name = "$default"

(* -------------------------------------------------------------------------- *)

module Name = EcIdent

module MName = Mid

(* -------------------------------------------------------------------------- *)

type meta_name = Name.t

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
  | Sym_Form_Proj         of int
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
  | Sym_Quant             of quantif * ((ident * (gty option)) list)

(* invariant of pattern : if the form is not Pat_Axiom, then there is
     at least one of the first set of patterns *)
type pattern =
  | Pat_Anything
  | Pat_Meta_Name  of pattern * meta_name
  | Pat_Sub        of pattern
  | Pat_Or         of pattern list
  | Pat_Instance   of pattern option * meta_name * path * pattern list
  | Pat_Red_Strat  of pattern * reduction_strategy

  | Pat_Fun_Symbol of fun_symbol * pattern list
  | Pat_Axiom      of axiom
  | Pat_Type       of pattern * gty

and reduction_strategy = pattern -> axiom -> (pattern * axiom) option


type map = pattern MName.t


(* -------------------------------------------------------------------------- *)
let pat_axiom x = Pat_Axiom x

let pat_form f = pat_axiom (Axiom_Form f)

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
    | Pat_Meta_Name (p,n) ->
       aux (pat_add_fv map n) p
    | Pat_Sub p -> aux map p
    | Pat_Or lp -> List.fold_left aux map lp
    | Pat_Instance _ -> assert false
    | Pat_Red_Strat (p,_) -> aux map p
    | Pat_Type (p,_) -> aux map p
    | Pat_Fun_Symbol (_,lp) -> List.fold_left aux map lp
    | Pat_Axiom a ->
       match a with
       | Axiom_Form f -> pat_fv_union f.f_fv map
       | Axiom_Memory m -> pat_add_fv map m
       | Axiom_Instr i -> pat_fv_union map i.i_fv
       | Axiom_Stmt s -> pat_fv_union map s.s_fv
       | _ -> map
  in aux Mid.empty p

(* -------------------------------------------------------------------------- *)
let p_equal : pattern -> pattern -> bool = (==)

(* -------------------------------------------------------------------------- *)
let p_if (p1 : pattern) (p2 : pattern) (p3 : pattern) =
  Pat_Fun_Symbol(Sym_Form_If,[p1;p2;p3])

let p_proj (p1 : pattern) (i : int) (ty : ty) =
  Pat_Type(Pat_Fun_Symbol(Sym_Form_Proj i,[p1]),GTty ty)

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

let p_pvar (x : prog_var) (ty : ty) (m : EcMemory.memory) =
  pat_form(EcFol.f_pvar x ty m)

(* -------------------------------------------------------------------------- *)

module Psubst = struct

  type p_subst = {
      ps_loc : pattern Mid.t;
    }

  let p_subst_id = { ps_loc = Mid.empty }

  let p_bind_local (s : p_subst) (id : EcIdent.t) (p : pattern) =
    { s with ps_loc = Mid.add id p s.ps_loc }

  let p_subst (_s : p_subst) (p : pattern) = p

end


(* -------------------------------------------------------------------------- *)
let rec p_betared_opt = function
  | Pat_Anything -> None
  | Pat_Meta_Name (p,n) ->
     omap (fun p -> Pat_Meta_Name (p,n)) (p_betared_opt p)
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

let p_app_simpl_opt op pargs ty = match op with
  | None -> None
  | Some p -> p_betared_opt (Pat_Fun_Symbol(Sym_Form_App ty,p::pargs))

let p_forall_simpl b p =
  let b = List.filter (fun (id,_) -> Mid.mem id (pat_fv p)) b in
  p_f_forall b p

let p_exists_simpl b p =
  let b = List.filter (fun (id,_) -> Mid.mem id (pat_fv p)) b in
  p_f_exists b p
