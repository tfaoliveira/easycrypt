open EcUtils
open EcPattern
open EcPath
open EcModules
open EcTypes
open EcIdent
open EcFol

(** Convention :
    - 1 : the game with the to-be-instanciated adversary
    - 2 : the specified game
 **)

let rec e_get_used_vars m (e : expr) = match e.e_node with
  | Evar { pv_name = name ; pv_kind = PVloc } -> Mx.add name e m
  | Eint _ | Elocal _ | Eop _ | Evar _ -> m
  | Eapp (op,args) -> List.fold_left e_get_used_vars m (op::args)
  | Equant (_,_,e) -> e_get_used_vars m e
  | Elet (_,e1,e2) -> List.fold_left e_get_used_vars m [e1;e2]
  | Etuple t       -> List.fold_left e_get_used_vars m t
  | Eif (e1,e2,e3) -> List.fold_left e_get_used_vars m [e1;e2;e3]
  | Ematch (e,l,_) -> List.fold_left e_get_used_vars m (e::l)
  | Eproj (e1,_)   -> e_get_used_vars m e1

let lv_get_set_vars m = function
  | LvVar ({ pv_name = name } as pv, ty) -> Mx.add name (e_var pv ty) m
  | LvTuple t ->
     List.fold_left (fun m (pv,ty) -> Mx.add pv.pv_name (e_var pv ty) m) m t
  | LvMap (_, ({ pv_name = name } as pv), _, t)  -> Mx.add name (e_var pv t) m

let rec i_get_set_vars m (i : instr) = match i.i_node with
  | Sasgn (lv, _) | Srnd (lv, _) -> lv_get_set_vars m lv
  | Scall (Some lv, _f, _) -> lv_get_set_vars m lv
  | Scall (None, _f, _) -> m
  | Sif (_, s1, s2) ->
     let m = s_get_set_vars m s2 in s_get_set_vars m s1
  | Swhile (_, s) -> s_get_set_vars m s
  | Sassert _ | Sabstract _ -> m

and s_get_set_vars m (s : stmt) = List.fold_left i_get_set_vars m s.s_node


let rec i_get_used_vars m (i : instr) = match i.i_node with
  | Sasgn (LvMap (_, pv, e1, t), e2)
    | Srnd  (LvMap (_, pv, e1, t), e2) ->
     let m = e_get_used_vars m e1 in
     let m = e_get_used_vars m e2 in
     Mx.add pv.pv_name (e_var pv t) m
  | Sasgn (_, e) | Srnd (_, e) -> e_get_used_vars m e
  | Scall (_,_f,le) -> List.fold_left e_get_used_vars m le
  | Sif (e1, s1, s2) ->
     let m = s_get_used_vars m s2 in
     let m = s_get_used_vars m s1 in
     e_get_used_vars m e1
  | Swhile (e1, s) ->
     let m = s_get_used_vars m s in
     e_get_used_vars m e1
  | Sassert e1 -> e_get_used_vars m e1
  | Sabstract _ -> m

and s_get_used_vars m (s : stmt) =
  let rec aux m = function
    | [] -> m
    | i :: rest ->
       let m' = i_get_set_vars Mx.empty i in
       let m = Mx.set_diff m m' in
       let m = i_get_used_vars m i in
       aux m rest
  in aux m (List.rev s.s_node)

type expansion = (expr Mx.t) list

let map_of_lvalue_expr (lv : lvalue) (e : expr) = match lv with
  | LvVar (pv, _) -> Mx.singleton pv.pv_name e
  | LvTuple l -> Mx.of_list (List.mapi (fun i (pv, t) -> pv.pv_name, e_proj e i t) l)
  | LvMap ((op, optys), pv, e', ty) ->
     let e'' = e_app (e_op op optys ty) [e_var pv (List.hd optys); e'; e] ty in
     Mx.singleton pv.pv_name e''


let rec xp_in_e (pv1 : xpath) (e : expr) = match e.e_node with
  | Eint _ -> false
  | Elocal _ -> false
  | Evar { pv_name = pv2 } -> x_equal pv1 pv2
  | Eop _ -> false
  | Eapp (e1,eargs) -> xp_in_e pv1 e1 || List.exists (xp_in_e pv1) eargs
  | Equant (_,_,e1) -> xp_in_e pv1 e1
  | Elet (_,e1,e2) -> xp_in_e pv1 e1 || xp_in_e pv1 e2
  | Etuple el -> List.exists (xp_in_e pv1) el
  | Eif (e1,e2,e3) -> xp_in_e pv1 e1 || xp_in_e pv1 e2 || xp_in_e pv1 e3
  | Ematch (e1,el,_) -> xp_in_e pv1 e1 || List.exists (xp_in_e pv1) el
  | Eproj (e1,_) -> xp_in_e pv1 e1

let full_expand (expand : expansion) (e : expr) =
  let rec aux e m = match e.e_node with
    | Eint _ | Elocal _ | Eop _ -> e
    | Evar { pv_name = xp } -> if Mx.mem xp m then Mx.find xp m else e
    | Eapp (e1,eargs) ->
       let e1'    = aux e1 m in
       let eargs' = List.map (fun x -> aux x m) eargs in
       if List.for_all2 e_equal (e1::eargs) (e1'::eargs') then e
       else e_app e1 eargs' e.e_ty
    | Equant (q,b,e1) ->
       let e1' = aux e1 m in
       if e_equal e1 e1' then e
       else e_quantif q b e1'
    | Elet (lp,e1,e2) ->
       let e1' = aux e1 m in
       let e2' = aux e2 m in
       if e_equal e1 e1' && e_equal e2 e2' then e
       else e_let lp e1 e2
    | Etuple l ->
       let l' = List.map (fun x -> aux x m) l in
       if List.for_all2 e_equal l l' then e
       else e_tuple l'
    | Eif (e1,e2,e3) ->
       let e1' = aux e1 m in
       let e2' = aux e2 m in
       let e3' = aux e3 m in
       if e_equal e1 e1' && e_equal e2 e2' && e_equal e3 e3' then e
       else e_if e1 e2 e3
    | Ematch (e1,eargs,ty) ->
       let e1'    = aux e1 m in
       let eargs' = List.map (fun x -> aux x m) eargs in
       if List.for_all2 e_equal (e1::eargs) (e1'::eargs') then e
       else e_app e1 eargs' ty
    | Eproj (e1,i) ->
       let e1' = aux e1 m in
       if e_equal e1 e1' then e
       else e_proj e1' i e.e_ty
  in List.fold_left aux e expand

let add_expansion (lv : lvalue) (e : expr) (expand : expansion) =
  (map_of_lvalue_expr lv e) :: expand

let create_name (xp : xpath) =
  let rec aux (p : path) = match p.p_node with
    | Psymbol s -> EcIdent.create s
    | Pqname (p,_) -> aux p
  in aux xp.x_sub

type instance_advserary = {
    ia_args           : expr list;
    ia_known_vars     : expr Mx.t;
    ia_known_values   : expansion;
    ia_accepted_stmt  : instr list;
    ia_working_stmt   : instr list;
    ia_return_value   : expr;
  }

let initiate_instance_adv (s : stmt) (args : expr list) (res : expr) = {
    ia_args           = args;
    ia_known_vars     = Mx.empty;
    ia_known_values   = [];
    ia_accepted_stmt  = [];
    ia_working_stmt   = s.s_node;
    ia_return_value   = res;
  }

exception CannotExpress

let try_express_expr_using_exprs (_e : expr) (_args : expr list) =
  raise CannotExpress

let expr_expand (m : expr Mx.t) (e : expr) = full_expand [m] e

let rec lv_remove (lv1 : lvalue) (m : expr Mx.t) = match lv1 with
  | LvVar (pv1, _) -> Mx.remove pv1.pv_name m
  | LvTuple t -> List.fold_left (fun m (pv,_) -> Mx.remove pv.pv_name m) m t
  | LvMap (_, pv, _, _) -> Mx.remove pv.pv_name m

let rec instr_expand (m : expr Mx.t) (i : instr) =
  if Mx.is_empty m then i, m
  else
  match i.i_node with
  | (Sasgn (LvMap ((op, optys), pv, e1, t) as lv, e2)
     | Srnd (LvMap ((op, optys), pv, e1, t) as lv, e2)) ->
     let used_vars = e_get_used_vars (Mx.singleton pv.pv_name (e_var pv t)) e1 in
     if Mx.set_disjoint m used_vars then
       let e2' = expr_expand m e2 in
       let m = Mx.remove pv.pv_name m in
       let i = if e_equal e2 e2' then i else i_asgn (lv, e2') in
       i, m
     else
       let lv, e = LvVar (pv, t),
                   e_app (e_op op optys t) [e_var pv t; e1; e2] t in
       let e' = expr_expand m e in
       let i = if e_equal e e' then i else i_asgn (lv, e') in
       let m = Mx.remove pv.pv_name m in
       i, m
  | Sasgn (lv, e) | Srnd (lv, e) ->
     let e' = expr_expand m e in
     let m = Mx.set_diff m (lv_get_set_vars Mx.empty lv) in
     let i = if e_equal e e' then i else i_asgn (lv, e') in
     i, m
  | Scall (None, f, args) ->
     let args' = List.map (expr_expand m) args in
     (* FIXME : remove global variables that can be modified by f *)
     let m = m in
     let i = if List.for_all2 e_equal args args' then i
             else i_call (None, f, args') in
     i, m
  | Scall (Some (LvMap ((op, optys), pv, e, t)), f, args) ->
     if Mx.mem pv.pv_name m then assert false
     else
       let args' = List.map (expr_expand m) args in
       let e'  = expr_expand m e in
       let m = m in
       (* FIXME : remove global variables that can be modified by f *)
       let i = if List.for_all2 e_equal args args' then i
               else
                 let lv = LvMap ((op, optys), pv, e', t) in
                 i_call (Some lv, f, args') in
       i, m
  | Scall (Some lv, f, args) ->
     let args' = List.map (expr_expand m) args in
     let m = Mx.set_diff m (lv_get_set_vars Mx.empty lv) in
     (* FIXME : remove global variables that can be modified by f *)
     let i = if List.for_all2 e_equal args args' then i
             else i_call (Some lv, f, args') in
     i, m
  | Sif (cond, s1, s2) ->
     let cond'   = expr_expand m cond in
     let s1', m1 = stmt_expand m s1.s_node in
     let s2', m2 = stmt_expand m s2.s_node in
     let m       = Mx.set_inter m1 m2 in
     let i = if e_equal cond cond' && List.for_all2 i_equal s1.s_node s1'
                && List.for_all2 i_equal s2.s_node s2' then i
             else i_if (cond', stmt s1', stmt s2') in
     i, m
  | Swhile (cond, s) ->
     let cond' = expr_expand m cond in
     let s', m = stmt_expand m s.s_node in
     let i = if e_equal cond cond' && List.for_all2 i_equal s.s_node s' then i
             else i_while (cond', stmt s') in
     i, m
  | Sassert e ->
     let e' = expr_expand m e in
     let i = if e_equal e e' then i else i_assert e' in
     i, m
  | _ -> i, m


and stmt_expand (m : expr Mx.t) (s : instr list) : instr list * expr Mx.t =
  let rec aux m acc l = if Mx.is_empty m then (List.rev acc) @ l, m else
    match l with
    | [] -> List.rev acc, m
    | i :: rest ->
       let i, m = instr_expand m i in
       aux m (i :: acc) rest
  in
  aux m [] s


let remove_from_known_values (l : xpath list) (expand : expansion) =
  let rec aux xp acc l =
    match l with
    | [] -> List.rev acc
    | m :: rest when Mx.is_empty m -> aux xp acc rest
    | m :: rest ->
       if Mx.exists (fun _ e -> Mx.mem xp (e_get_used_vars Mx.empty e)) m
       then
         let m = Mx.remove xp m in
         if Mx.is_empty m then (List.rev acc) @ rest
         else (List.rev acc) @ (m :: rest)
       else
         let m = Mx.remove xp m in
         if Mx.is_empty m then aux xp acc rest
         else aux xp (m :: acc) rest
  in
  let f l xp = aux xp [] l in
  List.fold_left f expand l


let ia_remove_from_known_values (lv : lvalue) (ia : instance_advserary) =
  match lv with
  | LvVar ({ pv_name = name }, _) ->
     { ia with ia_known_values = remove_from_known_values [name] ia.ia_known_values; }
  | LvTuple t ->
     { ia with
       ia_known_values = remove_from_known_values
                           (List.map (fun (pv,_) -> pv.pv_name) t)
                           ia.ia_known_values; }
  | LvMap (_, { pv_name = name }, _, _) ->
     { ia with ia_known_values = remove_from_known_values [name] ia.ia_known_values; }

let accepted_instr i rest ia =
  { ia with
    ia_known_vars    = i_get_set_vars ia.ia_known_vars i;
    ia_accepted_stmt = i :: ia.ia_accepted_stmt;
    ia_working_stmt  = rest;
    ia_known_values  =
      List.fold_left (fun m x -> remove_from_known_values [x] m)
        ia.ia_known_values (Mx.keys (i_get_set_vars Mx.empty i));
  }

exception CannotProcess


let rec process (ia : instance_advserary) =
  match ia.ia_working_stmt with
  | [] -> ia

  | ({ i_node = Sasgn (lv, e) } as i) :: rest ->
     let used_vars = i_get_used_vars Mx.empty i in
     if Mx.set_submap used_vars ia.ia_known_vars
     then
       process (accepted_instr i rest { ia with
                    ia_known_values = add_expansion lv e ia.ia_known_values; })
     else
       begin
         try let e = try_express_expr_using_exprs e
                       (ia.ia_args @ (Mx.values ia.ia_known_vars)) in
             let i = i_asgn (lv, e) in
             process (accepted_instr i rest { ia with
                          ia_known_values = add_expansion lv e ia.ia_known_values; })
         with
         | CannotExpress ->
         let e' = full_expand ia.ia_known_values e in
         let m = map_of_lvalue_expr lv e in
         if e_equal e' e then
           let ia_working_stmt, m = stmt_expand m rest in
           let ia_return_value    = expr_expand m ia.ia_return_value in
           process { ia with ia_working_stmt; ia_return_value; }
         else
           try let e = try_express_expr_using_exprs e'
                         (ia.ia_args @ (Mx.values ia.ia_known_vars)) in
               let i = i_asgn (lv, e) in
               process (accepted_instr i rest { ia with
                            ia_known_values = add_expansion lv e ia.ia_known_values; })
           with
           | CannotExpress ->
           let ia_working_stmt, m = stmt_expand m rest in
           let ia_return_value    = expr_expand m ia.ia_return_value in
           process { ia with ia_working_stmt; ia_return_value; }
       end

  | ({ i_node = Srnd (lv, e) } as i) :: rest ->
     let used_vars = i_get_used_vars Mx.empty i in
     if Mx.set_submap used_vars ia.ia_known_vars
     then process (accepted_instr i rest ia)
     else begin
         try let e = try_express_expr_using_exprs e
                       (ia.ia_args @ (Mx.values ia.ia_known_vars)) in
             let i = match lv with
               | LvMap ((op, optys), pv, e1, t)
                    when Mx.mem pv.pv_name ia.ia_known_vars ->
                  let e1 = try_express_expr_using_exprs e1
                             (ia.ia_args @ (Mx.values ia.ia_known_vars)) in
                  i_rnd (LvMap ((op, optys), pv, e1, t), e)
               | _ -> i_rnd (lv, e) in
             process (accepted_instr i rest ia)
         with
         | CannotExpress -> raise CannotProcess
       end

  | ({ i_node = Scall (olv, f, args) } as i) :: rest ->
     let used_vars = i_get_used_vars Mx.empty i in
     if Mx.set_submap used_vars ia.ia_known_vars
     then process (accepted_instr i rest ia)
     else begin
         try let args = List.map (fun x ->
                            try_express_expr_using_exprs x
                              (ia.ia_args @ (Mx.values ia.ia_known_vars))) args in
             let i = match olv with
               | Some (LvMap ((op, optys), pv, e1, t))
                    when Mx.mem pv.pv_name ia.ia_known_vars ->
                  let e1 = try_express_expr_using_exprs e1
                             (ia.ia_args @ (Mx.values ia.ia_known_vars)) in
                  i_call (Some (LvMap ((op, optys), pv, e1, t)), f, args)
               | _ -> i_call (olv, f, args) in
             process (accepted_instr i rest ia)
         with
         | CannotExpress -> raise CannotProcess
       end

  | ({ i_node = Sif (cond, s1, s2) } as i) :: rest ->
     let used_vars = i_get_used_vars Mx.empty i in
     if Mx.set_submap used_vars ia.ia_known_vars
     then process (accepted_instr i rest ia)
     else
       let ia, i =
         try
           let cond =
             try try_express_expr_using_exprs cond
                   (ia.ia_args @ (Mx.values ia.ia_known_vars))
             with CannotExpress ->
               try_express_expr_using_exprs (expr_expand ia.ia_known_vars cond)
                 (ia.ia_args @ (Mx.values ia.ia_known_vars)) in
           let ia1 = {
               ia with
               ia_accepted_stmt = [];
               ia_working_stmt = s1.s_node;
             } in
           let ia2 = {
               ia with
               ia_accepted_stmt = [];
               ia_working_stmt = s2.s_node;
             } in
           let ia1 = process ia1 in
           let ia2 = process ia2 in
           let s1 = stmt (List.rev ia1.ia_accepted_stmt) in
           let s2 = stmt (List.rev ia2.ia_accepted_stmt) in
           let i = i_if (cond, s1, s2) in
           (* FIXME : erase known values that are updated in either s1 or s2 *)
           { ia with
             ia_known_vars = Mx.set_inter ia1.ia_known_vars ia2.ia_known_vars;
           }, i
         with CannotExpress -> raise CannotProcess
       in process (accepted_instr i rest ia)

  | ({ i_node = Swhile (cond, s) } as i) :: rest ->
     let used_vars = i_get_used_vars Mx.empty i in
     if Mx.set_submap used_vars ia.ia_known_vars
     then process (accepted_instr i rest ia)
     else
       let ia, i =
         try
           let cond =
             try try_express_expr_using_exprs cond
                   (ia.ia_args @ (Mx.values ia.ia_known_vars))
             with CannotExpress ->
               try_express_expr_using_exprs (expr_expand ia.ia_known_vars cond)
                 (ia.ia_args @ (Mx.values ia.ia_known_vars)) in
           let ia1 = {
               ia with
               ia_accepted_stmt = [];
               ia_working_stmt = s.s_node;
             } in
           let ia1 = process ia1 in
           let s = stmt (List.rev ia1.ia_accepted_stmt) in
           let i = i_while (cond, s) in
           (* FIXME : erase known values that are updated in either s1 or s2 *)
           ia, i
         with CannotExpress -> raise CannotProcess
       in process (accepted_instr i rest ia)

  | ({ i_node = Sassert e } as i) :: rest ->
     let used_vars = e_get_used_vars Mx.empty e in
     if Mx.set_submap used_vars ia.ia_known_vars
     then process (accepted_instr i rest ia)
     else raise CannotProcess

  | ({ i_node = Sabstract _ } as i) :: rest ->
     process (accepted_instr i rest ia)

let process ia =
  let ia = process ia in
  { ia with ia_return_value = full_expand ia.ia_known_values ia.ia_return_value; }

let pattern_of_pv names (pv,t) = match pv.pv_kind with
  | PVloc when Mx.mem pv.pv_name names -> names, Mx.find pv.pv_name names
  | PVloc ->
     let var = meta_var (create_name pv.pv_name) None (OGTty (Some t)) in
     Mx.add pv.pv_name var names, var
  | PVglob -> names, pat_lvalue (LvVar (pv,t))


let my_mem = EcIdent.create "my mem"

let quant_of_equant = function
  | `EExists -> Lexists
  | `EForall -> Lforall
  | `ELambda -> Llambda

let rec abstract_expr names e =
  let f = abstract_expr names in
  match e.e_node with
  | Evar { pv_name = name } when Mx.mem name names -> Mx.find name names
  | Eint _ | Elocal _ | Eop _ | Evar _ -> pat_form (form_of_expr my_mem e)
  | Eapp (e1, args) -> p_app (f e1) (List.map f args) (Some e.e_ty)
  | Equant (q, b, e1) -> p_f_quant (quant_of_equant q) (List.map (fun (i,t) -> i,(GTty t)) b) (f e1)
  | Elet (lp, e1, e2) -> p_let lp (f e1) (f e2)
  | Etuple t -> p_tuple (List.map f t)
  | Eif (e1, e2, e3) -> p_if (f e1) (f e2) (f e3)
  | Ematch (e1, args, t) -> p_match (f e1) t (List.map f args)
  | Eproj (e1, i) -> p_proj (f e1) i e.e_ty

let pattern_of_stmt (f : xpath) (s : stmt) (r : expr) =
  let rec aux names acc res = function
    | [] -> List.rev acc, names, res
    | i :: rest ->
    match i.i_node with
    | Sasgn (lv, e) ->
       let rest, m = stmt_expand (map_of_lvalue_expr lv e) rest in
       let res     = expr_expand m res in
       aux names acc res rest

    | Srnd (lv, e) ->
       let names, p, rest, res =
         match lv with
         | LvVar (pv, t) ->
            let names, p = pattern_of_pv names (pv,t) in
            names, p_sample p (abstract_expr names e), rest, res
         | LvTuple t ->
            let names, ptuple = List.fold_left_map pattern_of_pv names t in
            names, p_sample (p_tuple ptuple) (abstract_expr names e), rest, res
         | LvMap ((op, optys), pv, e', t) ->
            let x = pv_loc f "x" in
            let p = meta_var (EcIdent.create "x") None (OGTty (Some (e.e_ty))) in
            let names = Mx.add x.pv_name p names in
            let p1 = p_sample p (abstract_expr names e) in
            let lv, e = LvVar (pv, t),
                        e_app (e_op op optys t)
                          [(e_var pv t); e'; (e_var x e.e_ty)] t in
            let rest, m = stmt_expand (map_of_lvalue_expr lv e) rest in
            let res     = expr_expand m res in
            names, p1, rest, res
       in
       aux names (p :: acc) res rest

    | Scall (None, f1, args) ->
       let p = p_call None (pat_xpath f1) (List.map (abstract_expr names) args) in
       aux names (p :: acc) res rest
    | Scall (Some lv, f1, args) ->
       let names, p, rest, res =
         match lv with
         | LvVar (pv, t) ->
            let names, p = pattern_of_pv names (pv,t) in
            names, p_call (Some p) (pat_xpath f1)
                     (List.map (abstract_expr names) args), rest, res
         | LvTuple t ->
            let names, ptuple = List.fold_left_map pattern_of_pv names t in
            names, p_call (Some (p_tuple ptuple)) (pat_xpath f1)
                     (List.map (abstract_expr names) args), rest, res
         | LvMap ((op, optys), pv, e', t) ->
            let ty = List.last optys in
            let x = pv_loc f "x" in
            let p = meta_var (EcIdent.create "x") None (OGTty (Some ty)) in
            let names = Mx.add x.pv_name p names in
            let p1 = p_call (Some p) (pat_xpath f1)
                       (List.map (abstract_expr names) args) in
            let lv, e = LvVar (pv, t),
                        e_app (e_op op optys t)
                          [(e_var pv t); e'; (e_var x ty)] t in
            let rest, m = stmt_expand (map_of_lvalue_expr lv e) rest in
            let res     = expr_expand m res in
            names, p1, rest, res
       in aux names (p :: acc) res rest

    | Sif (cond, s1, s2) ->
       let pcond = abstract_expr names cond in
       let s1, names, _ =
         aux names [] (e_local (EcIdent.create "toto ") tbool) s1.s_node in
       let s2, names, _ =
         aux names [] (e_local (EcIdent.create "toto ") tbool) s2.s_node in
       let p = p_instr_if pcond (p_stmt s1) (p_stmt s2) in
       aux names (p :: acc) res rest

    | Swhile (cond, s) ->
       let pcond = abstract_expr names cond in
       let s, names, _ =
         aux names [] (e_local (EcIdent.create "toto ") tbool) s.s_node in
       let p = p_while pcond (p_stmt s) in
       aux names (p :: acc) res rest

    | Sassert e ->
       let p = p_assert (abstract_expr names e) in
       aux names (p :: acc) res rest

    | Sabstract _ ->
       aux names ((pat_instr i) :: acc) res rest
  in
  let s, _, r = aux Mx.empty [] r s.s_node in s, r


module Vertex = struct
  type t = instr * int

  let compare (i1,n1) (i2,n2) =
    if n1 = n2 then i_compare i1 i2
    else n1 - n2

  let equal (i1,n1) (i2,n2) = n1 = n2 && i_equal i1 i2

  let hash (i1,_) = i_hash i1

  let get_instr ((v,_) : t) = v

end


module Mv = struct
  include EcMaps.Map.Make(Vertex)
end


module DependGraph = struct
  include Graph.Persistent.Digraph.ConcreteBidirectional(Vertex)

  let add_instr ((graph,ivars) : t * (vertex Mx.t)) (n : int) (i : instr) =
    let graph = add_vertex graph (i,n) in
    let used_vars = i_get_used_vars Mx.empty i in
    let graph = Mx.fold_left
                  (fun g x _ ->
                    if Mx.mem x ivars then add_edge g (Mx.find x ivars) (i,n)
                    else g) graph used_vars in
    let set_vars = i_get_set_vars Mx.empty i in
    let ivars = Mx.fold_left (fun m x _ -> Mx.add x (i,n) m) ivars set_vars in
    (* FIXME : add instruction inside ifs and whiles in the graph *)
    (graph, ivars)

  let add_stmt (s : stmt) =
    List.fold_lefti add_instr (empty,Mx.empty) s.s_node

  type accessibles = bool Mv.t

  let compute_accessibles (graph : t) : accessibles =
    fold_vertex
      (fun vertex m -> if [] = pred graph vertex
                       then Mv.add vertex false m
                       else m)
      graph Mv.empty

  let get_accessibles (a : accessibles) : vertex list =
    Mv.keys (Mv.filter (fun _ b -> not b) a)

  let next_accessibles (graph : t) (a : accessibles) (v : vertex) : accessibles =
    if Mv.mem v a then
      let a = Mv.add v true a in
      let v_succ = succ graph v in
      let f a v' =
        let v'_pred = pred graph v' in
        if List.for_all (fun x -> Mv.mem x a) v'_pred then Mv.add v' false a else a
      in
      List.fold_left f a v_succ
    else a

end


type find_proc_engine = {
    find_hyps       : EcEnv.LDecl.hyps;
    find_adv        : mpath;
    find_adv_procs  : (EcFMatching.environment * DependGraph.accessibles * instr list) Mx.t;
    find_pattern    : pattern list;
    find_pat_return : pattern;
    find_stmt       : instr list;
    find_return     : expr;
  }


let find_stmt_for_one_procedure_at_the_end (e : find_proc_engine) =
  let env = EcFMatching.mkenv h EcReduction.nodelta EcReduction.nodelta in
  let engine = EcFMatching.mkengine (Axiom_Form (form_of_expr my_mem r2)) r1 env in
  match EcFMatching.search_eng engine with
  | None -> raise (Invalid_argument "return values do not match.")
  | Some nengine ->
  let env     = nengine.EcFMatching.ne_env in
  let g2, _   = DependGraph.add_stmt s2 in
  let access2 = DependGraph.compute_accessibles g2 in
  let rec aux env access ps1 s2 =
    match ps1 with
    | [] -> env, access
    | p1 :: prest ->
    match s2 with
    | [] -> raise Not_found
    | [ i ] ->

    | i :: rest ->
    let engine   = EcFMatching.mkengine (Axiom_Instr (Vertex.get_instr i)) p1 env in
    let copy_env = EcFMatching.copy_environment env in
    try match EcFMatching.search_eng engine with
        | None -> raise Not_found
        | Some nengine ->
           let access = DependGraph.next_accessibles g2 access i in
           let s2     = DependGraph.get_accessibles access in
           aux nengine.EcFMatching.ne_env access prest s2
    with
    | Not_found ->
       let _ = EcFMatching.restore_environment copy_env in
       aux copy_env access ps1 rest
  in
  let s2 = DependGraph.get_accessibles access2 in
  aux env access2 p s2





let try_instance (f1 : xpath) (s1 : stmt) (r1 : expr) (s2 : stmt) (r2 : expr) =
  let p1, r1 = pattern_of_stmt f1 s1 r1 in
