open EcUtils
open EcIdent
open EcParsetree
open EcCoreGoal
(* open EcHiGoal *)
open EcEnv
open FApi
open EcLocation
open EcPattern
open EcFMatching
open EcCoreFol
open EcUid
open EcModules
open EcTypes

let default_name = "object matched to rewrite"
let rewrite_name = "rewrited object"
let default_name = Name.create default_name
let rewrite_name = EcIdent.create rewrite_name

let process_match (x : pqsymbol) (tc : tcenv1)  =
  let (env,hyps,_f) = tc1_eflat tc in
  let pf_env = tc1_penv tc in
  let axiom_name = Ax.lookup_path (unloc x) env in
  let pt_env = EcProofTerm.pt_of_uglobal pf_env hyps axiom_name in
  let f = pt_env.EcProofTerm.ptev_ax in

  let unienv = pt_env.EcProofTerm.ptev_env.EcProofTerm.pte_ue in

  let fmt    = Format.std_formatter in
  let ppe    = EcPrinting.PPEnv.ofenv env in

  (* let _ = Format.fprintf fmt "%a\n" (EcPrinting.pp_axiom ~long:true ppe) axiom in *)

  (* let f = (snd axiom).ax_spec in *)
  let binds,f' = match f.f_node with
    | Fquant (Lforall, binds, f1) -> binds, f1
    | _ -> [],f in

  let f1,f2 = match f'.f_node with
    | Fapp (op, [f1 ; f2]) when EcPath.p_equal EcCoreLib.CI_Bool.p_eq (fst (destr_op op)) -> f1,f2
    | _ -> f',f' in

  let red_info = EcReduction.full_red in

  let fun_none _ _  = None in
  let fun_red p f = EcFMatching.red_make_strat_from_info red_info hyps p f in

  let p = pattern_of_form binds f1 in
  let p = match p with
    | Pat_Fun_Symbol(Sym_Form_App ty,op::lp) ->
       let op = Pat_Red_Strat(op,fun_red) in
       Pat_Fun_Symbol(Sym_Form_App ty,op::lp)
    | _ -> p in
  let p = Pat_Meta_Name (p, default_name) in
  let p = Pat_Sub p in

  let f = tc1_goal tc in

  let print p =
       Format.fprintf fmt "%a\n" (EcPrinting.pp_pattern ppe) p
  in

  let print_names n o =
       let _ = Format.fprintf fmt "with name \"%a\" :\n" (EcPrinting.pp_local ppe) n in
       print o
  in

  let engine = EcFMatching.mkengine f p hyps fun_none EcReduction.full_red unienv in

  let types_to_unify =
    let add_unigty acc = function
      | _, GTty ty -> Suid.union acc (EcTypes.Tuni.univars ty)
      | _,_ -> acc in
    let add_unity acc ty = Suid.union acc (EcTypes.Tuni.univars ty) in
    let rec aux_a acc a = aux acc (Pat_Axiom a)
    and aux_f acc f = aux_a acc (Axiom_Form f)
    and aux_i acc i = aux_a acc (Axiom_Instr i)
    and aux_lv acc (lv : lvalue) = match lv with
      | LvVar (_,ty) -> add_unity acc ty
      | LvTuple l ->
         List.fold_left (fun m (_,ty) -> add_unity m ty) acc l
      | LvMap ((_,lty),_,e,ty) ->
         let acc = List.fold_left add_unity acc (ty::lty) in
         aux_f acc (form_of_expr mhr e)
    and aux (acc : Suid.t) (p : EcPattern.pattern) =
      match p with
      | Pat_Anything -> acc
      | Pat_Meta_Name (p,_) -> aux acc p
      | Pat_Sub p -> aux acc p
      | Pat_Or lp ->
         List.fold_left aux acc lp
      | Pat_Instance _ -> assert false
      | Pat_Red_Strat (p,_) -> aux acc p
      | Pat_Type (p,gty) -> aux (add_unigty acc (gty,gty)) p
      | Pat_Axiom a -> begin
          match a with
          | Axiom_Form f -> begin
              let aux = aux_f in
              let acc = add_unity acc f.f_ty in
              match f.f_node with
              | Fquant (_,bds,f1) ->
                 aux (List.fold_left add_unigty acc bds) f1
              | Fif (f1,f2,f3) ->
                 List.fold_left aux acc [f1;f2;f3]
              | Fmatch (f1,lf,ty) ->
                 List.fold_left aux (add_unity acc ty) (f1::lf)
              | Flet (_,f1,f2) ->
                 List.fold_left aux acc [f1;f2]
              | Fint _ -> acc
              | Flocal _ -> acc
              | Fpvar _ -> acc
              | Fglob _ -> acc
              | Fop (_,lty) -> List.fold_left add_unity acc lty
              | Fapp (op,args) ->
                 List.fold_left aux acc (op::args)
              | Ftuple t ->
                 List.fold_left aux acc t
              | Fproj (f1,_) -> aux acc f1
              | FhoareF h ->
                 List.fold_left aux acc [h.hf_pr;h.hf_po]
              | FhoareS h ->
                 List.fold_left aux acc [h.hs_pr;h.hs_po]
              | FbdHoareF h ->
                 List.fold_left aux acc [h.bhf_pr;h.bhf_po;h.bhf_bd]
              | FbdHoareS h ->
                 List.fold_left aux acc [h.bhs_pr;h.bhs_po;h.bhs_bd]
              | FequivF h ->
                 List.fold_left aux acc [h.ef_pr;h.ef_po]
              | FequivS h ->
                 List.fold_left aux acc [h.es_pr;h.es_po]
              | FeagerF h ->
                 List.fold_left aux acc [h.eg_pr;h.eg_po]
              | Fpr h ->
                 List.fold_left aux acc [h.pr_args;h.pr_event]
            end
          | Axiom_Memory _ -> acc
          | Axiom_MemEnv _ -> acc
          | Axiom_Prog_Var _ -> acc
          | Axiom_Op (_,lty) ->
             List.fold_left add_unity acc lty
          | Axiom_Module _ | Axiom_Mpath _ -> acc
          | Axiom_Instr i -> begin
              match i.i_node with
              | Sasgn (lv,e) | Srnd (lv,e) ->
                 aux_f (aux_lv acc lv) (form_of_expr mhr e)
              | Scall (olv,_,le) ->
                 List.fold_left aux_f (odfl acc (omap (aux_lv acc) olv))
                   (List.map (form_of_expr mhr) le)
              | Sif (e,s1,s2) ->
                 let acc = aux_f acc (form_of_expr mhr e) in
                 let acc = aux_a acc (Axiom_Stmt s1) in
                 aux_a acc (Axiom_Stmt s2)
              | Swhile (e,s) ->
                 aux_a (aux_f acc (form_of_expr mhr e)) (Axiom_Stmt s)
              | Sassert e ->
                 aux_f acc (form_of_expr mhr e)
              | Sabstract _ -> acc
            end
          | Axiom_Stmt s -> List.fold_left aux_i acc s.s_node
          | Axiom_Lvalue lv -> aux_lv acc lv
          | Axiom_Local (_,ty) -> add_unity acc ty
          | Axiom_Hoarecmp _ | Axiom_Xpath _ -> acc
        end
      | Pat_Fun_Symbol (s,lp) ->
         let acc =
           match s with
           | Sym_Form_If | Sym_Form_Tuple | Sym_Form_Proj _ | Sym_Form_Prog_var _
             | Sym_Form_Glob | Sym_Form_Hoare_F | Sym_Form_Hoare_S
             | Sym_Form_bd_Hoare_F | Sym_Form_bd_Hoare_S | Sym_Form_Equiv_F
             | Sym_Form_Equiv_S | Sym_Form_Eager_F | Sym_Form_Pr | Sym_Stmt_Seq
             | Sym_Instr_Assign | Sym_Instr_Sample | Sym_Instr_Call
             | Sym_Instr_Call_Lv | Sym_Instr_If | Sym_Instr_While
             | Sym_Instr_Assert | Sym_Xpath | Sym_Mpath | Sym_App -> acc
           | Sym_Form_App ty
             | Sym_Form_Match ty
             | Sym_Form_Pvar ty -> add_unity acc ty
           | Sym_Form_Quant (_,binds) ->
              List.fold_left add_unigty acc binds
           | Sym_Quant (_,binds) ->
              let f acc (_,ogty) = match ogty with
                | Some (GTty ty) -> add_unity acc ty
                | _ -> acc in
              List.fold_left f acc binds
           | Sym_Form_Let lp ->
              match lp with
              | LSymbol (_,ty) -> add_unity acc ty
              | LTuple l ->
                 List.fold_left (fun m (_,ty) -> add_unity m ty) acc l
              | LRecord (_,lty) ->
                 List.fold_left (fun m (_,ty) -> add_unity m ty) acc lty
         in List.fold_left aux acc lp

    in aux Suid.empty p
  in

  let print_types (id : EcUid.uid) (ty : EcTypes.ty option) =
    match ty with
    | Some ty ->
       Format.fprintf fmt "Type@ @[%a@]@ is unified with@ @[%a@].@ "
         (EcPrinting.pp_type ppe) (EcTypes.tuni id)
         (EcPrinting.pp_type ppe) ty
    | None ->
       Format.fprintf fmt "Type@ @[%a@]@ is not unified.@ "
         (EcPrinting.pp_type ppe) (EcTypes.tuni id)
  in

  let _ = match EcFMatching.search_eng engine with
    | None ->
       Format.fprintf
         fmt "Failed match of@ @[%a@]@ with@ @[%a@]@ "
         (EcPrinting.pp_pattern ppe) p
         (EcPrinting.pp_form ppe) f

    | Some nengine ->
       let engine =
         { engine with
           e_binds = nengine.ne_binds;
           e_continuation = nengine.ne_continuation;
           e_env = nengine.ne_env;
         } in
       let map = engine.e_env.env_map in
       let ty_unification =
         let close = EcUnify.UniEnv.close engine.e_env.env_unienv in
         Muid.mapi (fun ty _ -> close ty) types_to_unify
       in
       let map =
         Mid.add rewrite_name (Pat_Axiom(Axiom_Form(rewrite_term engine f2))) map in
       let _ = Mid.iter print_names map in
       Muid.iter print_types ty_unification
  in

  tcenv_of_tcenv1 tc
