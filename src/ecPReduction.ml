open EcUtils
open EcReduction
open EcIdent
open EcFol
open EcTypes
open EcPath
open EcModules
open EcPattern
open Psubst



let rec p_is_true p = match p_destr_app p with
  | { p_node = Pat_Axiom(Axiom_Op (op,[],ty)) }, [] ->
     EcPath.p_equal op EcCoreLib.CI_Bool.p_true
     && odfl true (omap (ty_equal tbool) ty)
  | pop, [t] -> op_equal pop fop_not && p_is_false t
  | _ -> false

and p_is_false p = match p_destr_app p with
  | { p_node = Pat_Axiom(Axiom_Op (op,[],ty)) }, [] ->
     EcPath.p_equal op EcCoreLib.CI_Bool.p_false
     && odfl true (omap (ty_equal tbool) ty)
  | pop, [t] -> op_equal pop fop_not && p_is_true t
  | _ -> false

let p_bool_val p =
  if p_is_true p then Some true
  else if p_is_false p then Some false
  else None

(* -------------------------------------------------------------------------- *)
let p_is_not p = match p with
  | { p_node = Pat_Axiom(Axiom_Op (op,[],ot)) } ->
     EcPath.p_equal op EcCoreLib.CI_Bool.p_not
     && odfl true (omap (ty_equal (toarrow [tbool] tbool)) ot)
  | _ -> false

let p_destr_not p = match p_destr_app p with
  | op, [p1] when p_is_not op -> p1
  | _ -> assert false

(* -------------------------------------------------------------------------- *)
let p_not_simpl_opt (p : pattern) =
  let op, _ = p_destr_app p in
  if p_is_not op then Some (p_destr_not p)
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
let p_is_i0 p = try EcBigInt.equal (p_destr_int p) EcBigInt.zero
                with DestrError _ -> false

let p_is_i1 p = try EcBigInt.equal (p_destr_int p) EcBigInt.one
                with DestrError _ -> false


let p_int_le_simpl_opt (p1 : pattern) (p2 : pattern) =
  if p1 = p2 then Some p_true
  else
    try Some (pat_form (f_bool (EcBigInt.compare (p_destr_int p1) (p_destr_int p2) <= 0)))
    with DestrError _ -> None

let p_int_le_simpl p1 p2 = odfl (p_int_le p1 p2) (p_int_le_simpl_opt p1 p2)

let p_int_lt_simpl_opt (p1 : pattern) (p2 : pattern) =
  if p1 = p2 then Some p_false
  else
    try Some (pat_form (f_bool (EcBigInt.compare (p_destr_int p1) (p_destr_int p2) < 0)))
    with DestrError _ -> None

let p_int_lt_simpl p1 p2 = odfl (p_int_lt p1 p2) (p_int_lt_simpl_opt p1 p2)

let p_int_opp_simpl_opt (p : pattern) =
  match p_destr_app p with
  | op, [p] when op_equal op fop_int_opp -> Some p
  | _ -> if p_is_i0 p then Some p_i0 else None

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

        List.Exceptionless.find_map (fun f -> f ()) simpls

let p_int_add_simpl p1 p2 = odfl (p_int_add p1 p2) (p_int_add_simpl_opt p1 p2)

let p_int_mul_simpl_opt (p1 : pattern) (p2 : pattern) =
  try  Some (p_int (EcBigInt.mul (p_destr_int p1) (p_destr_int p2)))
  with DestrError _ ->
    if p_is_i0 p1 || p_is_i0 p2 then Some p_i0
    else if p_is_i1 p1 then Some p2
    else if p_is_i1 p2 then Some p1
    else None

let p_int_mul_simpl p1 p2 = odfl (p_int_mul p1 p2) (p_int_mul_simpl_opt p1 p2)

let get_real_of_int (p : pattern) =
  try Some (p_destr_rint p) with DestrError _ -> None

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

     List.Exceptionless.find_map (fun f -> f ()) simpls

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


let rec p_real_mul_simpl e p1 p2 : pattern =
  let ppe = EcPrinting.PPEnv.ofenv e in
  EcEnv.notify e `Warning "simplify mul : p_real_mul_simpl (%a) (%a)"
    (EcPrinting.pp_pattern ppe) p1
    (EcPrinting.pp_pattern ppe) p2;
  let (n1, d1) = p_real_split p1 in
  let (n2, d2) = p_real_split p2 in

  p_real_div_simpl_r e
    (p_real_mul_simpl_r e n1 n2)
    (p_real_mul_simpl_r e d1 d2)

and p_real_div_simpl e p1 p2 =
  let ppe = EcPrinting.PPEnv.ofenv e in
  EcEnv.notify e `Warning "simplify mul : p_real_div_simpl (%a) (%a)"
    (EcPrinting.pp_pattern ppe) p1
    (EcPrinting.pp_pattern ppe) p2;
  let (n1, d1) = p_real_split p1 in
  let (n2, d2) = p_real_split p2 in

  p_real_div_simpl_r e
    (p_real_mul_simpl_r e n1 d2)
    (p_real_mul_simpl_r e d1 n2)

and p_real_mul_simpl_r e p1 p2 =
  let ppe = EcPrinting.PPEnv.ofenv e in
  EcEnv.notify e `Warning "simplify mul : p_real_mul_simpl_r (%a) (%a)"
    (EcPrinting.pp_pattern ppe) p1
    (EcPrinting.pp_pattern ppe) p2;
  if p_real_is_zero p1 || p_real_is_zero p2 then p_r0 else

  if p_real_is_one p1 then p2 else
  if p_real_is_one p2 then p1 else

  try
    p_rint (EcBigInt.Notations.( *^ ) (p_destr_rint p1) (p_destr_rint p2))
  with DestrError _ -> p_real_mul p1 p2

and p_real_div_simpl_r e p1 p2 =
  let ppe = EcPrinting.PPEnv.ofenv e in
  EcEnv.notify e `Warning "simplify mul : p_real_div_simpl_r (%a) (%a)"
    (EcPrinting.pp_pattern ppe) p1
    (EcPrinting.pp_pattern ppe) p2;
  let (p1, p2) =
    try
      let n1 = p_destr_rint p1 in
      let n2 = p_destr_rint p2 in
      let gd = EcBigInt.gcd n1 n2 in

      p_rint (EcBigInt.div n1 gd), p_rint (EcBigInt.div n2 gd)

    with
    | DestrError _ -> (p1, p2)
    | Division_by_zero -> (p_r0, p_r1)

  in p_real_mul_simpl_r e p1 (odfl (p_real_inv p2) (p_real_inv_simpl_opt p2))

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

let p_real_mul_simpl_opt e p1 p2 =
  let f1 = p_real_mul_simpl e p1 p2 in
  let f2 = p_real_mul p1 p2 in
  if f1 = f2 then None else Some f1

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

let ps_app_simpl ?ho op pargs oty =
  odfl (p_app ?ho op pargs oty) (p_betared_opt (p_app ?ho op pargs oty))

let p_forall_simpl b p =
  let b = List.filter (fun (id,_) -> Mid.mem id (pat_fv p)) b in
  p_forall b p

let p_exists_simpl b p =
  let b = List.filter (fun (id,_) -> Mid.mem id (pat_fv p)) b in
  p_exists b p



let update_higher_order p =
  let f p = match p.p_node with
    | Pat_Fun_Symbol
      (Sym_Form_App (ty,_), ({ p_node = Pat_Meta_Name _ } as p)::args) ->
       p_app ~ho:MaybeHO p args ty
    | _ -> p in
  p_map f p

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
      (s : Psubst.p_subst) (p : pattern) (id : Name.t)
      (ob : pbindings option) : pattern option =
  if ri.delta_h id
  then
    if is_none ob && EcEnv.LDecl.can_unfold id hyps then
      Some (pat_form (EcEnv.LDecl.unfold id hyps))
    else
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
    | Pat_Meta_Name (_,n,ob) -> reduce_local_opt hyps ri s p n ob
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
         ({ p_node = (Pat_Meta_Name (None, id, ob)) ; p_ogty = _ogty} as p) :: pargs ->
          if ri.beta
          then match reduce_local_opt hyps ri s p id ob with
               | None -> None
               | Some op -> Some (p_app_simpl ~ho op pargs ty)
          else omap (fun x -> p_app ~ho x pargs ty)
                 (reduce_local_opt hyps ri s p id ob)

       (* ζ-reduction *)
       | Sym_Form_App (oty,ho),
         ({ p_node = Pat_Axiom (Axiom_Local (id,_ty))} as p) :: pargs ->
          if ri.beta
          then match reduce_local_opt hyps ri s p id None with
               | None -> None
               | Some op -> Some (p_app_simpl ~ho op pargs oty)
          else omap (fun x -> p_app ~ho x pargs oty)
                 (reduce_local_opt hyps ri s p id None)

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
            | Some (`Real_mul ), [f1;f2] -> p_real_mul_simpl_opt (EcEnv.LDecl.toenv hyps) f1 f2
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
       | Sym_Form_App (ty,_ho),
         ({ p_node = Pat_Axiom (Axiom_Op (op,lty,_)) } as pop) :: args
            when is_delta_p ri pop ->
          let op = h_red_op_opt hyps ri s op lty in
          omap (fun op -> update_higher_order (p_app_simpl op args ty)) op

       (* η-reduction *)
       | Sym_Quant (Llambda, (x, OGTty (Some t1))::binds),
         [{ p_node = Pat_Fun_Symbol (Sym_Form_App (ty,ho), pn::pargs)}]
            when p_can_eta hyps x (pn, pargs) ->
          Some (p_quant Llambda binds
                  (p_app ~ho pn (List.take (List.length pargs - 1) pargs)
                     (omap (tfun t1) ty)))

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
      | Axiom_Local (id,_t) -> reduce_local_opt hyps ri s (pat_axiom a) id None
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

let h_red_pattern_opt h r s p = match h_red_pattern_opt h r s p with
  | None -> None
  | Some p' ->
     if p = p' then None else Some p'

let h_red_axiom_opt h r s a = match h_red_axiom_opt h r s a with
  | None -> None
  | Some p' ->
     if pat_axiom a = p' then None else Some p'
