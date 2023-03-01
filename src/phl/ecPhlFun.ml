(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcPath
open EcTypes
open EcFol
open EcMemory
open EcModules
open EcEnv
open EcPV

open EcCoreGoal
open EcLowPhlGoal

module TTC = EcProofTyping

(* FIXME: oracles should ensure they preserve the state of the adversaries
 *
 * Two solutions:
 *   - add the equalities in the pre and post.
 *   - ensure that oracle doesn't write the adversaries states
 *
 * See [ospec] in [equivF_abs_spec / equivF_abs_upto] *)

(* -------------------------------------------------------------------- *)
let check_oracle_use (_pf : proofenv) env adv o =
  let restr = { mr_empty with
                mr_mpaths = { mr_empty.mr_mpaths with
                              ur_neg = Sm.singleton adv; }} in

  (* This only checks the memory restrictions. *)
  EcTyping.check_mem_restr_fun env o restr

let check_concrete pf env f =
  if NormMp.is_abstract_fun f env then
    tc_error_lazy pf (fun fmt ->
      let ppe = EcPrinting.PPEnv.ofenv env in
      Format.fprintf fmt
        "The function %a is abstract. Provide an invariant to the [proc] tactic"
        (EcPrinting.pp_funname ppe) f)

(* -------------------------------------------------------------------- *)
let lossless_hyps env top sub =
  let clear_to_top restr =
    let mr_mpaths = { (ur_empty Sm.empty) with ur_neg = Sm.singleton top } in
    { restr with mr_xpaths = ur_empty Sx.empty;
                 mr_mpaths = mr_mpaths } in

  let sig_ = EcEnv.NormMp.sig_of_mp env top in
  let bd =
    List.map
      (fun (id, mt) ->
         let mt = update_mt ~mt_restr:(clear_to_top mt.mt_restr) mt in
         (id, GTmodty (Any,mt))
      ) sig_.mis_params
  in
  (* WARN: this implies that the oracle do not have access to top *)
  let args  = List.map (fun (id,_) -> EcPath.mident id) sig_.mis_params in
  let concl = f_losslessF (EcPath.xpath (EcPath.m_apply top args) sub) in
  let calls =
    allowed (EcSymbols.Msym.find sub sig_.mis_restr.mr_params)
  in
  let hyps = List.map f_losslessF calls in
    f_forall bd (f_imps hyps concl)

(* -------------------------------------------------------------------- *)
let subst_pre env fs (m : memory) s =
  let fresh ov =
    match ov.ov_name with
    | None   -> assert false;
    | Some v -> { v_name = v; v_type = ov.ov_type }
  in
  let v = List.map (fun v -> f_pvloc (fresh v) m) fs.fs_anames in
  PVM.add env pv_arg m (f_tuple v) s

(* ------------------------------------------------------------------ *)
let t_hoareF_fun_def_r tc =
  let env = FApi.tc1_env tc in
  let hf = tc1_as_hoareF tc in
  let f = NormMp.norm_xfun env hf.hf_f in
  check_concrete !!tc env f;
  let (memenv, (fsig, fdef), env) = Fun.hoareS f env in
  let m = EcMemory.memory memenv in
  let fres = odfl f_tt (omap (form_of_expr m) fdef.f_ret) in
  let post = PVM.subst1 env pv_res m fres hf.hf_po in
  let pre  = PVM.subst env (subst_pre env fsig m PVM.empty) hf.hf_pr in
  let concl' = f_hoareS memenv pre fdef.f_body post in
  FApi.xmutate1 tc `FunDef [concl']

(* ------------------------------------------------------------------ *)
let t_choareF_fun_def_r tc =
  let env = FApi.tc1_env tc in
  let chf = tc1_as_choareF tc in
  let f = NormMp.norm_xfun env chf.chf_f in
  check_concrete !!tc env f;
  let (memenv, (fsig, fdef), env) = Fun.hoareS f env in
  let m = EcMemory.memory memenv in
  let fres = odfl f_tt (omap (form_of_expr m) fdef.f_ret) in
  let post = PVM.subst1 env pv_res m fres chf.chf_po in
  let spre = subst_pre env fsig m PVM.empty in
  let pre = PVM.subst env spre chf.chf_pr in
  let c   = PVM.subst env spre chf.chf_co in
  let cond, c = match fdef.f_ret with
    | None -> None, c
    | Some ret ->
      let EcCHoare.{ cond; res = c } =
        EcCHoare.cost_sub_self ~c ~sub:(EcCHoare.cost_of_expr_any memenv ret)
      in
      Some cond, c
  in
  let concl' = f_cHoareS memenv pre fdef.f_body post c in
  let goals = ofold (fun f fs -> f :: fs) [concl'] cond in
  FApi.xmutate1 tc `FunDef goals

(* ------------------------------------------------------------------ *)
let t_bdhoareF_fun_def_r tc =
  let env = FApi.tc1_env tc in
  let bhf = tc1_as_bdhoareF tc in
  let f = NormMp.norm_xfun env bhf.bhf_f in
  check_concrete !!tc env f;
  let (memenv, (fsig, fdef), env) = Fun.hoareS f env in
  let m = EcMemory.memory memenv in
  let fres = odfl f_tt (omap (form_of_expr m) fdef.f_ret) in
  let post = PVM.subst1 env pv_res m fres bhf.bhf_po in
  let spre = subst_pre env fsig m PVM.empty in
  let pre = PVM.subst env spre bhf.bhf_pr in
  let bd  = PVM.subst env spre bhf.bhf_bd in
  let concl' = f_bdHoareS memenv pre fdef.f_body post bhf.bhf_cmp bd in
  FApi.xmutate1 tc `FunDef [concl']

(* ------------------------------------------------------------------ *)
let t_equivF_fun_def_r tc =
  let env = FApi.tc1_env tc in
  let ef = tc1_as_equivF tc in
  let fl = NormMp.norm_xfun env ef.ef_fl in
  let fr = NormMp.norm_xfun env ef.ef_fr in
  check_concrete !!tc env fl; check_concrete !!tc env fr;
  let (menvl, eqsl, menvr, eqsr, env) = Fun.equivS fl fr env in
  let (fsigl, fdefl) = eqsl in
  let (fsigr, fdefr) = eqsr in
  let ml = EcMemory.memory menvl in
  let mr = EcMemory.memory menvr in
  let fresl = odfl f_tt (omap (form_of_expr ml) fdefl.f_ret) in
  let fresr = odfl f_tt (omap (form_of_expr mr) fdefr.f_ret) in
  let s = PVM.add env pv_res ml fresl PVM.empty in
  let s = PVM.add env pv_res mr fresr s in
  let post = PVM.subst env s ef.ef_po in
  let s = subst_pre env fsigl ml PVM.empty in
  let s = subst_pre env fsigr mr s in
  let pre = PVM.subst env s ef.ef_pr in
  let concl' = f_equivS menvl menvr pre fdefl.f_body fdefr.f_body post in
  FApi.xmutate1 tc `FunDef [concl']

(* -------------------------------------------------------------------- *)
let t_hoareF_fun_def   = FApi.t_low0 "hoare-fun-def"   t_hoareF_fun_def_r
let t_choareF_fun_def  = FApi.t_low0 "choare-fun-def"  t_choareF_fun_def_r
let t_bdhoareF_fun_def = FApi.t_low0 "bdhoare-fun-def" t_bdhoareF_fun_def_r
let t_equivF_fun_def   = FApi.t_low0 "equiv-fun-def"   t_equivF_fun_def_r

(* -------------------------------------------------------------------- *)
let t_fun_def_r tc =
  let th  = t_hoareF_fun_def
  and tch = t_choareF_fun_def
  and tbh = t_bdhoareF_fun_def
  and te  = t_equivF_fun_def in

  t_hF_or_chF_or_bhF_or_eF ~th ~tch ~tbh ~te tc

let t_fun_def = FApi.t_low0 "fun-def" t_fun_def_r

(* -------------------------------------------------------------------- *)
(* invariant information provided by the user, used to apply the rule *)
type abs_inv_el = {
  oracle : xpath; (* Oracle *)
  finite : bool;  (* number of calls to the oracle is finite *)
  cost   : form;
  (* Cost of an oracle call.
     If [finite], of type [tint -> tcost].
     Otherwise, of type [tcost]. *)
}

(* abstract call rull invariant information *)
type abs_inv_inf = abs_inv_el list

let process_p_abs_inv_inf
    (tc            : tcenv1)
    (hyps          : LDecl.hyps)
    (p_abs_inv_inf : p_abs_inv_inf) : ptybindings * abs_inv_inf
  =
  let open EcLocation in
  let open EcParsetree in
  let l = ref [] in
  let check_uniq (x : poracle_cost) =
    match x.p_param with
    | None -> ()
    | Some y ->
      let s = EcLocation.unloc y in
      if List.mem s !l then
        tc_error !!tc ~catchable:false ~loc:(loc y)
          "duplicate name %s" s
      else l := s :: !l in
  List.iter check_uniq p_abs_inv_inf;

  let env = LDecl.toenv hyps in

  let doit el =
    let f = EcTyping.trans_gamepath env el.p_oracle in

    (* if the cost information are for an oracle that can be called an infinite
       number of times, there is no binded cost parameter. *)
    if not el.p_finite then
      let c = TTC.pf_process_form !!tc hyps tcost el.p_cost in
      None, { oracle = f; finite = el.p_finite; cost = c; }
    else
      (* otherwise, this is more complicated:
         there is a binded cost parameter, and the cost is a lambda from
         [tint] to [tcost]. *)
      let x = el.p_param in
      let lo = match x with
        | Some y -> loc y
        | None   -> loc el.p_oracle in
      let x = match x with
        | Some _ -> mk_loc lo x
        | None   -> mk_loc lo (Some (mk_loc lo "k")) in

      let bd = [x], mk_loc lo PTunivar in
      let p_cost = mk_loc (loc el.p_cost) (PFlambda([bd], el.p_cost)) in
      let c = TTC.pf_process_form !!tc hyps (tfun tint tcost) p_cost in
      Some bd, { oracle = f; finite = el.p_finite; cost = c; }
  in

  let bds_abs_inv_info = List.map doit p_abs_inv_inf in

  (* split bindings from user info, and clear empty bindings. *)
  let bds, abs_inv_info = List.split bds_abs_inv_info in
  List.filter_map (fun x -> x) bds, abs_inv_info

type inv_inf =
  | Std     of form
  | CostAbs of abs_inv_inf

(* -------------------------------------------------------------------- *)
module FunAbsLow = struct
  (* ------------------------------------------------------------------ *)
  let hoareF_abs_spec _pf env f inv =
    let {top; oi_param; } = EcLowPhlGoal.abstract_info env f in
    let fv = PV.fv env mhr inv in
    PV.check_depend env fv top;
    let ospec o = f_hoareF inv o inv in
    let sg = List.map ospec (allowed oi_param) in
    (inv, inv, sg)

  (* ------------------------------------------------------------------ *)
  (* Extends a list of arguments provided by the user with a default case
     for any oracle without user information.

     Arguments:
     - [ois] is the list of available oracles
     - [xc] are cost information provided by the user on some of the oracles
       in [ois].
     - [inv] are invariant of the form [λ x1...xn, φ] where [xi] of type
       [tint]. There is one variable [xi] for every element [el] in [xc]
       such that [el.finite] is [true] (in the same order).

     We extend [xc] by adding a default value for all oracles that are
     an *abstract* module without parameters, and modify [inv]
     accordingly.
     By default, we assume that these elements are called a finite number of
     times (hence we add a new variable [xj] too). *)
  let extend_abs_inv_inf
      (ois : xpath list)
      (xc  : abs_inv_inf)
      (inv : form) : EcFol.form * abs_inv_inf
    =
    let xc, new_bds =
      List.fold_left (fun (xc, new_bds) oracle ->
          if EcPath.m_is_local oracle.x_top &&
             oracle.x_top.m_args = [] &&
             not (List.exists (fun x -> x_equal x.oracle oracle) xc) then
            let k = EcIdent.create "k", GTty tint in

            let calls =  Mx.singleton oracle f_x1 in
            let cost = f_lambda [k] (f_cost_r (cost_r f_x0 calls true)) in
            let xc = { oracle; cost; finite = true; } :: xc in

            xc, k :: new_bds

          else (xc, new_bds)
        ) (xc, []) ois
    in
    (* the new bindings are added to [inv], to have a uniform treatment *)
    let inv = f_lambda new_bds inv in

    inv, xc


  (* Given an oracle procedure [o] of an xpath [f], compute the corresponding
     abstract oracle procedure of the functor associated to [f]. *)
  let func_orcl (o : xpath) (i : abstract_info) : xpath =
    let arg_o = List.assoc o.x_top i.args_map in
    EcPath.xpath (mident arg_o) o.x_sub

  (* Given an oracle procedure [o] of [f], gives the maximum number
     of calls that can be made to [o], using the cost restrictions of
     the functor associated to [f]. *)
  let func_cost_orcl
      (proc : EcSymbols.symbol) (o : xpath) (i : abstract_info) : form
    =
    EcCHoare.cost_orcl proc (func_orcl o i) i.cost_info

  (* Arguments:
     - [top]  : functor name (with erased module arguments)
     - [fn]   : procedure of [top] called
     - [ois]  : list of available oracles
     - [info] : cost informations of [top]
     - [xc]   : cost information provided by the user on some of the oracles
                in [ois]

     Computes the total cost of the call to [top.fn] according to [xc]. *)
  let abs_spec_cost
      (top  : mpath)
      (fn   : EcSymbols.symbol)
      (ois  : xpath list)
      (info : abstract_info)
      (xc   : abs_inv_inf) : form
    =
    let fn_orcl = EcPath.xpath top fn in

    let f_cost =
      match info.opacity with
      | Opaque -> f_cost_r (cost_r f_x0 (Mx.singleton fn_orcl f_x1) true)
      | Open -> f_cost_proj_r info.cost_info (Intr fn)
    in

    let orcls_cost = List.map (fun o ->
        (* [finite]: is the number of calls to [o] finite.
           [o_cost]: cost of a call to [o]. *)
        let { finite; cost = o_cost } =
          List.find (fun x -> x_equal x.oracle o) xc
        in

        (* Upper-bound on the costs of [o]'s calls. *)
        if finite then
          let cbd = func_cost_orcl fn o info in
          EcCHoare.choare_xsum o_cost (f_i0, cbd)
        else f_cost_xscale f_Inf o_cost
      ) ois
    in
    List.fold_left f_cost_add f_cost orcls_cost


  (* Return: pre, post, total cost, sub-goals *)
  let choareF_abs_spec
      (pf  : proofenv)
      (env : env)
      (f   : xpath)
      (inv : form)
      (xc  : abs_inv_inf)
    : form * form * form * form list
    =
    (* [top] is the functor associated to [f.x_top] (i.e. arguments are stripped). *)
    let {top; oi_param; } as info =
      EcLowPhlGoal.abstract_info env f
    in
    let ppe = EcPrinting.PPEnv.ofenv env in

    (* We check that the invariant cannot be modified by the adversary. *)
    let fv_inv = PV.fv env mhr inv in
    PV.check_depend env fv_inv top;

    let hyps = LDecl.init env [] in

    (* If [f] can call [o] at most zero times, we remove it. *)
    let ois : xpath list =
      let ois = allowed oi_param in
      List.filter (fun o ->
          let c = func_cost_orcl f.x_sub o info in
          let c = EcReduction.simplify EcReduction.full_red hyps c in
          match destr_xint c with
          | `Inf | `Unknown -> true
          | `Int c -> not (EcReduction.xconv `Conv hyps c f_x0)
        ) ois
    in

    let inv, xc = extend_abs_inv_inf ois xc inv in

    (* We create the oracles invariants *)

    let bds, _ = decompose_lambda inv in
    let xc_fin = List.filter (fun x -> x.finite) xc in

    (* We have one binder per *finite* oracle.
       Oracle that can be called infinitely often do not have a counter
       associated to them. *)
    assert (List.length bds = List.length xc_fin);
    let mks : EcIdent.t Mx.t =
      List.fold_left2 (fun mks (k,_) x ->
          Mx.add x.oracle k mks
        ) Mx.empty bds xc_fin
    in

    (* instantisation of [bds] for the pre-condition. Type [tint]. *)
    let kargs_pr = List.map (fun (x,_) -> f_local x tint) bds in
    let pr = f_app_simpl inv kargs_pr tbool in

    (* build the subgoal for the i-th oracle *)
    let ospec (o_called : xpath) : form =
      let { cost = o_cost; finite = o_finite } =
        try List.find (fun x -> x_equal x.oracle o_called) xc
        with Not_found ->
          tc_error pf "no cost information has been supplied for %a"
            (EcPrinting.pp_funname ppe) o_called
      in

      let k_called =
        try Mx.find o_called mks
        with Not_found -> assert (not o_finite); EcIdent.create "dummy"
        (* fresh dummy ident, so that all tests below fail  *)
      in

      (* We now compute the cost of the [k]-th call to [o_called].
         - if [o] can be called a finite number of times, the cost is
           parametrized by the number of the i-th call.
         - otherwise, the cost information to prove is a constant
           upper-bound. *)
      let k_o_cost =
        if o_finite then
          f_app_simpl o_cost [f_local k_called tint] tcost
        else o_cost
      in

      (* instantisation of [bds] for the post-condition. Type [tint].
         Identical to [kargs_pr], except for the called oracle [k_called],
         which is incremented by one. *)
      let kargs_po : form list =
        List.map (fun (x,_) ->
            let f = f_local x tint in
            if EcIdent.id_equal x k_called then f_int_add f f_i1
            else f
          ) bds
      in

      let po = f_app_simpl inv kargs_po tbool in
      let call_bounds =
        List.map2 (fun xc_el (x,_) ->
            let xf  = f_local x tint in
            let ge0 = f_int_le f_i0 xf in
            let cbd = func_cost_orcl f.x_sub xc_el.oracle info in
            let max =
              if EcIdent.id_equal x k_called then f_xlt (f_N xf) cbd
              else f_xle (f_N xf) cbd
            in
            f_anda ge0 max
          ) xc_fin bds
      in
      let call_bounds = f_ands0_simpl call_bounds in

      let form = f_cHoareF pr o_called po k_o_cost in
      f_forall_simpl bds (f_imp_simpl call_bounds form)
    in

    (* We have the conditions for the oracles. *)
    let sg_orcls = List.map ospec ois in

    (* check user finiteness annotation on oracles  *)
    let sg_finite =
      List.map (fun xc_el ->
          assert (xc_el.finite);
          let cbd = func_cost_orcl f.x_sub xc_el.oracle info in
          f_is_int cbd
        ) xc_fin
    in


    (* Finally, we compute the conclusion. *)
    (* choare [{ inv 0 } f {exists ks, 0 <= ks <= cbd /\ inv ks }]
              time sum_cost] *)
    let pre_inv =
      let ks0 = List.map (fun _ -> f_i0) bds in
      f_app_simpl inv ks0 tbool
    in

    let post_inv =
      let call_bounds =
        List.map2 (fun xc_el (x,_) ->
            let xf  = f_local x tint in
            let ge0 = f_int_le f_i0 xf in
            let cbd = func_cost_orcl f.x_sub xc_el.oracle info in
            let max = f_xle (f_N xf) cbd in
            f_anda ge0 max
          ) xc_fin bds
      in
      let call_bounds = f_ands0_simpl call_bounds in
      f_exists bds (f_and call_bounds pr)
    in

    let total_cost = abs_spec_cost top f.x_sub ois info xc in

    (pre_inv, post_inv, total_cost, sg_finite @ sg_orcls)


  (* ------------------------------------------------------------------ *)
  let bdhoareF_abs_spec pf env f inv =
    let { top; oi_param } = EcLowPhlGoal.abstract_info env f in
    let fv = PV.fv env mhr inv in

    PV.check_depend env fv top;
    let ospec o =
      check_oracle_use pf env top o;
      f_bdHoareF inv o inv FHeq f_r1 in

    let sg = List.map ospec (allowed oi_param) in
    (inv, inv, lossless_hyps env top f.x_sub :: sg)

  (* ------------------------------------------------------------------ *)
  let equivF_abs_spec pf env
      (fl  : xpath)
      (fr  : xpath)
      (inv : form) : form * form * form list
    =
    let { top = topl; f = _fl; oi_param = oil; fsig = sigl },
        { top = topr; f = _fr; oi_param = oir; fsig = sigr } =
      EcLowPhlGoal.abstract_info2 env fl fr
    in

    let ml, mr = mleft, mright in
    let fvl = PV.fv env ml inv in
    let fvr = PV.fv env mr inv in
    PV.check_depend env fvl topl;
    PV.check_depend env fvr topr;
    let eqglob = f_eqglob topl ml topr mr in

    let ospec o_l o_r =
      let use =
        try
          check_oracle_use pf env topl o_l;
          if   EcPath.x_equal o_l o_r
          then check_oracle_use pf env topl o_r;
          false
        with _ -> true
      in

      let fo_l = EcEnv.Fun.by_xpath o_l env in
      let fo_r = EcEnv.Fun.by_xpath o_r env in

      let eq_params =
        f_eqparams
          fo_l.f_sig.fs_arg fo_l.f_sig.fs_anames ml
          fo_r.f_sig.fs_arg fo_r.f_sig.fs_anames mr in

      let eq_res =
        f_eqres fo_l.f_sig.fs_ret ml fo_r.f_sig.fs_ret mr in

      let invs = if use then [eqglob; inv] else [inv] in
      let pre  = EcFol.f_ands (eq_params :: invs) in
      let post = EcFol.f_ands (eq_res :: invs) in
      f_equivF pre o_l o_r post
    in

    let sg = List.map2 ospec (allowed oil) (allowed oir) in

    let eq_params =
      f_eqparams
        sigl.fs_arg sigl.fs_anames ml
        sigr.fs_arg sigr.fs_anames mr in

    let eq_res = f_eqres sigl.fs_ret ml sigr.fs_ret mr in
    let lpre   = [eqglob;inv] in
    let pre    = f_ands (eq_params::lpre) in
    let post   = f_ands [eq_res; eqglob; inv] in

    (pre, post, sg)
end

(* ------------------------------------------------------------------ *)
let t_hoareF_abs_r inv tc =
  let env = FApi.tc1_env tc in
  let hf = tc1_as_hoareF tc in
  let pre, post, sg = FunAbsLow.hoareF_abs_spec !!tc env hf.hf_f inv in

  let tactic tc = FApi.xmutate1 tc `FunAbs sg in
  FApi.t_last tactic (EcPhlConseq.t_hoareF_conseq pre post tc)

(* ------------------------------------------------------------------ *)
let t_choareF_abs_r inv inv_inf tc =
  let env = FApi.tc1_env tc in
  let hf = tc1_as_choareF tc in
  let pre, post, cost, sg =
    FunAbsLow.choareF_abs_spec !!tc env hf.chf_f inv inv_inf in

  let tactic tc = FApi.xmutate1 tc `FunAbs sg in
  FApi.t_last tactic
    (EcPhlConseq.t_cHoareF_conseq_full pre post cost tc)


(* ------------------------------------------------------------------ *)
let t_bdhoareF_abs_r inv tc =
  let env = FApi.tc1_env tc in
  let bhf = tc1_as_bdhoareF tc in

  match bhf.bhf_cmp with
  | FHeq when f_equal bhf.bhf_bd f_r1 ->
      let pre, post, sg =
        FunAbsLow.bdhoareF_abs_spec !!tc env bhf.bhf_f inv
      in
      let tactic tc = FApi.xmutate1 tc `FunAbs sg in
      FApi.t_last tactic (EcPhlConseq.t_bdHoareF_conseq pre post tc)

  | _ -> tc_error !!tc "bound must of \"= 1\""

(* ------------------------------------------------------------------ *)
let t_equivF_abs_r inv tc =
  let env = FApi.tc1_env tc in
  let ef = tc1_as_equivF tc in
  let pre, post, sg =
    FunAbsLow.equivF_abs_spec !!tc env ef.ef_fl ef.ef_fr inv
  in

  let tactic tc = FApi.xmutate1 tc `FunAbs sg in
  FApi.t_last tactic (EcPhlConseq.t_equivF_conseq pre post tc)

(* -------------------------------------------------------------------- *)
let t_hoareF_abs   = FApi.t_low1 "hoare-fun-abs"   t_hoareF_abs_r
let t_choareF_abs  = FApi.t_low2 "choare-fun-abs"  t_choareF_abs_r
let t_bdhoareF_abs = FApi.t_low1 "bdhoare-fun-abs" t_bdhoareF_abs_r
let t_equivF_abs   = FApi.t_low1 "equiv-fun-abs"   t_equivF_abs_r

(* -------------------------------------------------------------------- *)
module UpToLow = struct
  (* ------------------------------------------------------------------ *)
  let equivF_abs_upto pf env fl fr bad invP invQ =
    let { top = topl; f = _fl; oi_param = oil; fsig = sigl },
        { top = topr; f = _fr; oi_param = oir; fsig = sigr } =
      EcLowPhlGoal.abstract_info2 env fl fr
    in

    let ml, mr = mleft, mright in
    let bad2 = Fsubst.f_subst_mem mhr mr bad in
    let allinv = f_ands [bad2; invP; invQ] in
    let fvl = PV.fv env ml allinv in
    let fvr = PV.fv env mr allinv in

    PV.check_depend env fvl topl;
    PV.check_depend env fvr topr;

    (* FIXME: check there is only global variable *)
    let eqglob = f_eqglob topl ml topr mr in

    let ospec o_l o_r =
      check_oracle_use pf env topl o_l;
      if   EcPath.x_equal o_l o_r
      then check_oracle_use pf env topl o_r;

      let fo_l = EcEnv.Fun.by_xpath o_l env in
      let fo_r = EcEnv.Fun.by_xpath o_r env in
      let eq_params =
        f_eqparams
          fo_l.f_sig.fs_arg fo_l.f_sig.fs_anames ml
          fo_r.f_sig.fs_arg fo_r.f_sig.fs_anames mr in

      let eq_res =
        f_eqres fo_l.f_sig.fs_ret ml fo_r.f_sig.fs_ret mr in

      let pre   = EcFol.f_ands [EcFol.f_not bad2; eq_params; invP] in
      let post  = EcFol.f_if_simpl bad2 invQ (f_and eq_res invP) in
      let cond1 = f_equivF pre o_l o_r post in
      let cond2 =
        let q = Fsubst.f_subst_mem ml EcFol.mhr invQ in
          f_forall[(mr, GTmem abstract_mt)]
            (f_imp bad2 (f_bdHoareF q o_l q FHeq f_r1)) in
      let cond3 =
        let q  = Fsubst.f_subst_mem mr EcFol.mhr invQ in
        let bq = f_and bad q in
          f_forall [(ml, GTmem abstract_mt)]
            (f_bdHoareF bq o_r bq FHeq f_r1) in

      [cond1; cond2; cond3]
    in

    let sg = List.map2 ospec (allowed oil) (allowed oir) in
    let sg = List.flatten sg in
    let lossless_a = lossless_hyps env topl fl.x_sub in
    let sg = lossless_a :: sg in

    let eq_params =
      f_eqparams
        sigl.fs_arg sigl.fs_anames ml
        sigr.fs_arg sigr.fs_anames mr in

    let eq_res = f_eqres sigl.fs_ret ml sigr.fs_ret mr in

    let pre  = [eqglob;invP] in
    let pre  = f_if_simpl bad2 invQ (f_ands (eq_params::pre)) in
    let post = f_if_simpl bad2 invQ (f_ands [eq_res;eqglob;invP]) in

    (pre, post, sg)
end

(* -------------------------------------------------------------------- *)
let t_equivF_abs_upto_r bad invP invQ tc =
  let env = FApi.tc1_env tc in
  let ef = tc1_as_equivF tc in
  let pre, post, sg =
    UpToLow.equivF_abs_upto !!tc env ef.ef_fl ef.ef_fr bad invP invQ
  in

  let tactic tc = FApi.xmutate1 tc `FunUpto sg in
  FApi.t_last tactic (EcPhlConseq.t_equivF_conseq pre post tc)

let t_equivF_abs_upto = FApi.t_low3 "equiv-fun-abs-upto" t_equivF_abs_upto_r

(* -------------------------------------------------------------------- *)
module ToCodeLow = struct
  (* ------------------------------------------------------------------ *)
  let to_code env f m =
    let fd = Fun.by_xpath f env in
    let me = EcMemory.empty_local ~witharg:false m in

    let args =
      let freshen_arg i ov =
        match ov.ov_name with
        | None   -> { ov with ov_name = Some (Printf.sprintf "arg%d" (i + 1)) }
        | Some _ -> ov
      in List.mapi freshen_arg fd.f_sig.fs_anames
    in

    let (me, args) = EcMemory.bindall_fresh args me in

    let res = { ov_name = Some "r"; ov_type = fd.f_sig.fs_ret; } in

    let me, res = EcMemory.bind_fresh res me in

    let eargs = List.map (fun v -> e_var (pv_loc (oget v.ov_name)) v.ov_type) args in
    let args =
      let var ov = { v_name = oget ov.ov_name; v_type = ov.ov_type } in
      List.map var args
    in

    let icall =
      i_call (Some (LvVar (pv_loc (oget res.ov_name), res.ov_type)), f, eargs)
    in (me, stmt [icall], res, args)

  let add_var env vfrom mfrom v me s =
    PVM.add env vfrom mfrom (f_pvar (pv_loc (oget v.ov_name)) v.ov_type (fst me)) s

  let add_var_tuple env vfrom mfrom vs me s =
    let vs =
      List.map (fun v -> f_pvar (pv_loc v.v_name) v.v_type (fst me)) vs
    in PVM.add env vfrom mfrom (f_tuple vs) s
end

(* -------------------------------------------------------------------- *)
let t_fun_to_code_hoare_r tc =
  let env = FApi.tc1_env tc in
  let hf = tc1_as_hoareF tc in
  let f = hf.hf_f in
  let m, st, r, a = ToCodeLow.to_code env f mhr in
  let spr = ToCodeLow.add_var_tuple env pv_arg mhr a m PVM.empty in
  let spo = ToCodeLow.add_var env pv_res mhr r m PVM.empty in
  let pre  = PVM.subst env spr hf.hf_pr in
  let post = PVM.subst env spo hf.hf_po in
  let concl = f_hoareS m pre st post in

  FApi.xmutate1 tc `FunToCode [concl]

(* -------------------------------------------------------------------- *)
(* This is for the proc* tactic, which replaces a statement about `G.f` by
   a statement about `x <$ G.f(args)`. *)
let t_fun_to_code_choare_r tc =
  let env = FApi.tc1_env tc in
  let chf = tc1_as_choareF tc in
  let f = chf.chf_f in
  let m, st, r, a = ToCodeLow.to_code env f mhr in
  let spr = ToCodeLow.add_var_tuple env pv_arg mhr a m PVM.empty in
  let spo = ToCodeLow.add_var env pv_res mhr r m PVM.empty in
  let pre  = PVM.subst env spr chf.chf_pr in
  let post = PVM.subst env spo chf.chf_po in
  let concl = f_cHoareS m pre st post chf.chf_co in

  FApi.xmutate1 tc `FunToCode [concl]

(* -------------------------------------------------------------------- *)
let t_fun_to_code_bdhoare_r tc =
  let env = FApi.tc1_env tc in
  let hf = tc1_as_bdhoareF tc in
  let f = hf.bhf_f in
  let m, st, r, a = ToCodeLow.to_code env f mhr in
  let spr = ToCodeLow.add_var_tuple env pv_arg mhr a m PVM.empty in
  let spo = ToCodeLow.add_var env pv_res mhr r m PVM.empty in
  let pre  = PVM.subst env spr hf.bhf_pr in
  let post = PVM.subst env spo hf.bhf_po in
  let bd   = PVM.subst env spr hf.bhf_bd in
  let concl = f_bdHoareS m pre st post hf.bhf_cmp bd in
  FApi.xmutate1 tc `FunToCode [concl]

(* -------------------------------------------------------------------- *)
let t_fun_to_code_equiv_r tc =
  let env = FApi.tc1_env tc in
  let ef = tc1_as_equivF tc in
  let (fl,fr) = ef.ef_fl, ef.ef_fr in
  let ml, sl, rl, al = ToCodeLow.to_code env fl mleft in
  let mr, sr, rr, ar = ToCodeLow.to_code env fr mright in
  let spr =
    let s = PVM.empty in
    let s = ToCodeLow.add_var_tuple env pv_arg mleft  al ml s in
    let s = ToCodeLow.add_var_tuple env pv_arg mright ar mr s in
    s in
  let spo =
    let s = PVM.empty in
    let s = ToCodeLow.add_var env pv_res mleft  rl ml s in
    let s = ToCodeLow.add_var env pv_res mright rr mr s in
    s in
  let pre   = PVM.subst env spr ef.ef_pr in
  let post  = PVM.subst env spo ef.ef_po in
  let concl = f_equivS ml mr pre sl sr post in

  FApi.xmutate1 tc `FunToCode [concl]

let t_fun_to_code_eager_r tc =
  let env = FApi.tc1_env tc in
  let eg = tc1_as_eagerF tc in
  let (fl,fr) = eg.eg_fl, eg.eg_fr in
  let ml, sl, rl, al = ToCodeLow.to_code env fl mleft in
  let mr, sr, rr, ar = ToCodeLow.to_code env fr mright in
  let spr =
    let s = PVM.empty in
    let s = ToCodeLow.add_var_tuple env pv_arg mleft  al ml s in
    let s = ToCodeLow.add_var_tuple env pv_arg mright ar mr s in
    s in
  let spo =
    let s = PVM.empty in
    let s = ToCodeLow.add_var env pv_res mleft  rl ml s in
    let s = ToCodeLow.add_var env pv_res mright rr mr s in
    s in
  let pre   = PVM.subst env spr eg.eg_pr in
  let post  = PVM.subst env spo eg.eg_po in
  let concl =
    f_equivS ml mr pre (s_seq eg.eg_sl sl) (s_seq sr eg.eg_sr) post in
  FApi.xmutate1 tc `FunToCode [concl]

(* -------------------------------------------------------------------- *)
let t_fun_to_code_hoare   = FApi.t_low0 "hoare-fun-to-code"   t_fun_to_code_hoare_r
let t_fun_to_code_choare  = FApi.t_low0 "choare-fun-to-code"  t_fun_to_code_choare_r
let t_fun_to_code_bdhoare = FApi.t_low0 "bdhoare-fun-to-code" t_fun_to_code_bdhoare_r
let t_fun_to_code_equiv   = FApi.t_low0 "equiv-fun-to-code"   t_fun_to_code_equiv_r
let t_fun_to_code_eager   = FApi.t_low0 "eager-fun-to-code"   t_fun_to_code_eager_r

(* -------------------------------------------------------------------- *)
let t_fun_to_code_r tc =
  let th  = t_fun_to_code_hoare in
  let tch = t_fun_to_code_choare in
  let tbh = t_fun_to_code_bdhoare in
  let te  = t_fun_to_code_equiv in
  let teg = t_fun_to_code_eager in
  t_hF_or_chF_or_bhF_or_eF ~th ~tch ~tbh ~te ~teg tc

let t_fun_to_code = FApi.t_low0 "fun-to-code" t_fun_to_code_r

(* -------------------------------------------------------------------- *)
let proj_costabs a = match a with
  | None -> ([])
  | Some (CostAbs b) -> b
  | _ -> assert false

let t_fun_r inv inv_inf tc =
  let th tc =
    assert (inv_inf = None);
    let env = FApi.tc1_env tc in
    let h   = destr_hoareF (FApi.tc1_goal tc) in
      if   NormMp.is_abstract_fun h.hf_f env
      then t_hoareF_abs inv tc
      else t_hoareF_fun_def tc

  and tch tc =
    let env = FApi.tc1_env tc in
    let h   = destr_cHoareF (FApi.tc1_goal tc) in
    if   NormMp.is_abstract_fun h.chf_f env
    then t_choareF_abs inv (proj_costabs inv_inf) tc
    else t_choareF_fun_def tc

  and tbh tc =
    assert (inv_inf = None);
    let env = FApi.tc1_env tc in
    let h   = destr_bdHoareF (FApi.tc1_goal tc) in
      if   NormMp.is_abstract_fun h.bhf_f env
      then t_bdhoareF_abs inv tc
      else t_bdhoareF_fun_def tc

  and te tc =
    assert (inv_inf = None);
    let env = FApi.tc1_env tc in
    let e   = destr_equivF (FApi.tc1_goal tc) in
      if   NormMp.is_abstract_fun e.ef_fl env
      then t_equivF_abs inv tc
      else t_equivF_fun_def tc

  in
    t_hF_or_chF_or_bhF_or_eF ~th ~tch ~tbh ~te tc

let t_fun = FApi.t_low2 "fun" t_fun_r

(* -------------------------------------------------------------------- *)
type p_upto_info = pformula * pformula * (pformula option)

(* -------------------------------------------------------------------- *)
let process_fun_def tc =
  let t_cont tcenv =
    if FApi.tc_count tcenv = 2 then
      FApi.t_sub [EcLowGoal.t_trivial; EcLowGoal.t_id] tcenv
    else tcenv in
  t_cont (t_fun_def tc)

(* -------------------------------------------------------------------- *)
let process_fun_to_code tc =
  t_fun_to_code_r tc

(* -------------------------------------------------------------------- *)
let process_fun_upto_info (bad, p, q) tc =
  let hyps = FApi.tc1_hyps tc in
  let env' = LDecl.inv_memenv hyps in
  let p    = TTC.pf_process_form !!tc env' tbool p in
  let q    = q |> omap (TTC.pf_process_form !!tc env' tbool) |> odfl f_true in
  let bad  =
    let env' = LDecl.push_active (EcMemory.abstract EcFol.mhr) hyps in
    TTC.pf_process_form !!tc env' tbool bad
  in
    (bad, p, q)

(* -------------------------------------------------------------------- *)
let process_fun_upto info g =
  let (bad, p, q) = process_fun_upto_info info g in
    t_equivF_abs_upto bad p q g

(* -------------------------------------------------------------------- *)
let ensure_none tc = function
  | None -> ()
  | Some _ ->
    tc_error !!tc "this is not a choare judgement"

let process_inv_pabs_inv_finfo tc inv p_abs_inv_inf : form * abs_inv_inf =
  let hyps = FApi.tc1_hyps tc in
  let env' = LDecl.inv_memenv1 hyps in
  let bds, abs_inv_info = process_p_abs_inv_inf tc env' p_abs_inv_inf in
  let inv =
    EcLocation.mk_loc (EcLocation.loc inv) (EcParsetree.PFlambda(bds, inv))
  in
  let tints = List.map (fun _ -> tint) bds in
  let tinv  = toarrow tints tbool in
  let inv  = TTC.pf_process_form !!tc env' tinv inv in
  inv, abs_inv_info

let process_fun_abs inv p_abs_inv_inf tc =
  let t_hoare tc =
    ensure_none tc p_abs_inv_inf;
    let hyps = FApi.tc1_hyps tc in
    let env' = LDecl.inv_memenv1 hyps in
    let inv  = TTC.pf_process_form !!tc env' tbool inv in
    t_hoareF_abs inv tc

  and t_choare tc =
    if p_abs_inv_inf = None then
      tc_error !!tc "for calls to abstract procedures in choare judgements, \
                     additional information must be provided";
    let inv, abs_inv_info =
      process_inv_pabs_inv_finfo tc inv (oget p_abs_inv_inf)
    in
    t_choareF_abs inv abs_inv_info tc

  and t_bdhoare tc =
    ensure_none tc p_abs_inv_inf;
    let hyps = FApi.tc1_hyps tc in
    let env' = LDecl.inv_memenv1 hyps in
    let inv  = TTC.pf_process_form !!tc env' tbool inv in
    t_bdhoareF_abs inv tc

  and t_equiv tc =
    ensure_none tc p_abs_inv_inf;
    let hyps = FApi.tc1_hyps tc in
    let env' = LDecl.inv_memenv hyps in
    let inv  = TTC.pf_process_form !!tc env' tbool inv in
    t_equivF_abs inv tc

  in
  t_hF_or_chF_or_bhF_or_eF
    ~th:t_hoare ~tch:t_choare ~tbh:t_bdhoare ~te:t_equiv tc
