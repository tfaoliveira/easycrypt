open EcIdent
open EcParsetree
open EcCoreGoal
(* open EcHiGoal *)
open EcEnv
open FApi
open EcLocation
open EcDecl
open EcFMatching
open EcCoreFol
open FPattern
open EcPath

let default_name = "object matched to rewrite"
let rewrite_name = "rewrited object"
let default_name = Name.create default_name
let rewrite_name = EcIdent.create rewrite_name

let process_match (x : pqsymbol) (tc : tcenv1)  =
  let (env,hyps,_f) = tc1_eflat tc in
  let axiom = Ax.lookup (unloc x) env in

  let fmt    = Format.std_formatter in
  let ppe    = EcPrinting.PPEnv.ofenv env in

  (* let _ = Format.fprintf fmt "%a\n" (EcPrinting.pp_axiom ~long:true ppe) axiom in *)

  let f = (snd axiom).ax_spec in
  let binds,f' = match f.f_node with
    | Fquant (Lforall, binds, f1) -> binds, f1
    | _ -> [],f in

  let f1,f2 = match f'.f_node with
    | Fapp (op, [f1 ; f2]) when EcPath.p_equal EcCoreLib.CI_Bool.p_eq (fst (destr_op op)) -> f1,f2
    | _ -> f',f' in

  let p = pattern_of_form binds f1 in
  let p = Pat_Meta_Name (p, default_name) in
  let p = Pat_Sub p in

  let f = tc1_goal tc in

  let print = function
    | (Pat_Axiom (Axiom_Memory m),_) ->
       Format.fprintf fmt "%a\n" (EcPrinting.pp_local ppe) m
    | (Pat_Axiom (Axiom_Form f)),_ ->
       Format.fprintf fmt "%a\n" (EcPrinting.pp_form ppe) f
    | (Pat_Axiom (Axiom_Module (`Local id)),_) ->
       Format.fprintf fmt "%a\n" (EcPrinting.pp_local ppe) id
    | (Pat_Axiom (Axiom_Module (`Concrete (p1,_)) ),_) ->
       Format.fprintf fmt "%a\n" (EcPrinting.pp_opname ppe) p1
    | (Pat_Axiom (Axiom_Mpath { m_top = `Local id }),_) ->
       Format.fprintf fmt "%a\n" (EcPrinting.pp_local ppe) id
    | _,_ -> ()
  in

  let print_names n o =
       let _ = Format.fprintf fmt "with name \"%a\" :\n" (EcPrinting.pp_local ppe) n in
       print o
  in

  let fun_none _ _ = None in

  let _ = match FPattern.search f p hyps fun_none with
    | None ->
       Format.fprintf
         fmt "%a\n" (EcPrinting.pp_form ppe)
         (EcFol.f_local (EcIdent.create "there_is_no_map") EcTypes.tint)
    | Some map ->
       let map = Mid.add rewrite_name (Pat_Axiom (Axiom_Form (rewrite_term map f2)), Mid.empty) map in
       Mid.iter print_names map
  in

  tcenv_of_tcenv1 tc
