(* -------------------------------------------------------------------- *)
open EcUtils
open EcTypes
open EcDecl
open EcCoreFol
open EcModules
open EcTheory

module Sp    = EcPath.Sp
module Sm    = EcPath.Sm
module Sx    = EcPath.Sx
module Mx    = EcPath.Mx
module Mp    = EcPath.Mp
module Mid   = EcIdent.Mid

(* -------------------------------------------------------------------- *)
type subst_name_clash = [
  | `Ident of EcIdent.t
]

exception SubstNameClash of subst_name_clash
exception InconsistentSubst

(* -------------------------------------------------------------------- *)
type subst = {
  sb_freshen  : bool;
  sb_modules  : EcPath.mpath Mid.t;
  sb_path     : EcPath.path Mp.t;
  sb_tydef    : (EcIdent.t list * ty) Mp.t;
  sb_opdef    : (EcIdent.t list * expr) Mp.t;
  sb_pddef    : (EcIdent.t list * form) Mp.t;
  sb_moddef   : EcPath.path Mp.t;
  sb_modtydef : EcPath.path Mp.t;
}

(* -------------------------------------------------------------------- *)
let empty ?(freshen = true) () : subst = {
  sb_freshen  = freshen;
  sb_modules  = Mid.empty;
  sb_path     = Mp.empty;
  sb_tydef    = Mp.empty;
  sb_opdef    = Mp.empty;
  sb_pddef    = Mp.empty;
  sb_moddef   = Mp.empty;
  sb_modtydef = Mp.empty;
}

let add_module (s : subst) (x : EcIdent.t) (m : EcPath.mpath) =
  let merger = function
    | None   -> Some m
    | Some _ -> raise (SubstNameClash (`Ident x))
  in
    { s with sb_modules = Mid.change merger x s.sb_modules }

let add_path (s : subst) ~src ~dst =
  assert (Mp.find_opt src s.sb_path = None);
  { s with sb_path = Mp.add src dst s.sb_path }

let add_tydef (s : subst) p (ids, ty) =
  assert (Mp.find_opt p s.sb_tydef = None);
  { s with sb_tydef = Mp.add p (ids, ty) s.sb_tydef }

let add_opdef (s : subst) p (ids, e) =
  assert (Mp.find_opt p s.sb_opdef = None);
  { s with sb_opdef = Mp.add p (ids, e) s.sb_opdef }

let add_pddef (s : subst) p (ids, f) =
  assert (Mp.find_opt p s.sb_pddef = None);
  { s with sb_pddef = Mp.add p (ids, f) s.sb_pddef }

let add_moddef (s : subst) ~(src : EcPath.path) ~(dst : EcPath.path) =
  assert (Mp.find_opt src s.sb_moddef = None);
  { s with sb_moddef = Mp.add src dst s.sb_moddef }

let add_modtydef (s : subst) ~(src : EcPath.path) ~(dst : EcPath.path) =
  assert (Mp.find_opt src s.sb_modtydef = None);
  { s with sb_modtydef = Mp.add src dst s.sb_modtydef }

(* -------------------------------------------------------------------- *)
type _subst = {
  s_s   : subst;
  s_p   : (EcPath.path -> EcPath.path);
  s_fmp : EcPath.smsubst;
  s_sty : ty_subst;
  s_ty  : (ty -> ty);
  s_op  : (EcIdent.t list * expr) Mp.t;
  s_pd  : (EcIdent.t list * form) Mp.t;
  s_mt  : EcPath.path Mp.t;
}

let _subst_of_subst s =
  let sp  = EcPath.p_subst s.sb_path in
  let sm  = EcPath.{
    sms_crt = Mp.union (fun _ _ x -> Some x) s.sb_path s.sb_moddef;
    sms_id = s.sb_modules;
    sms_ag = Mid.empty;
  }
  in
  let sty = { ty_subst_id with ts_p = sp; ts_mp = sm; ts_def = s.sb_tydef; } in
  let st  = EcTypes.ty_subst sty in
    { s_s   = s;
      s_p   = sp;
      s_fmp = sm;
      s_sty = sty;
      s_ty  = st;
      s_op  = s.sb_opdef;
      s_pd  = s.sb_pddef;
      s_mt  = s.sb_modtydef; }

let e_subst_of_subst (s:_subst) =
  { es_freshen = s.s_s.sb_freshen;
    es_p       = s.s_p;
    es_ty      = s.s_ty;
    es_opdef   = s.s_op;
    es_mp      = s.s_fmp;
    es_loc     = Mid.empty; }

let f_subst_of_subst (s:_subst) =
  Fsubst.f_subst_init
    ~freshen:s.s_s.sb_freshen
    ~sty:s.s_sty
    ~opdef:s.s_op
    ~prdef:s.s_pd
    ~modtydef:s.s_mt
    ()

(* -------------------------------------------------------------------- *)
let subst_form (s : _subst) =
  let s = f_subst_of_subst s in
    fun f -> Fsubst.f_subst s f

(* -------------------------------------------------------------------- *)
let subst_ovariable (s : _subst) (x : ovariable) =
  { x with ov_type = s.s_ty x.ov_type; }

let subst_variable (s : _subst) (x : variable) =
  { x with v_type = s.s_ty x.v_type; }

(* -------------------------------------------------------------------- *)
let subst_fun_uses (s : _subst) (u : uses) =
  let x_subst = EcPath.x_subst s.s_fmp in
  let calls  = List.map x_subst u.us_calls
  and reads  = Sx.fold (fun p m -> Sx.add (x_subst p) m) u.us_reads Sx.empty
  and writes = Sx.fold (fun p m -> Sx.add (x_subst p) m) u.us_writes Sx.empty in
  EcModules.mk_uses calls reads writes

(* -------------------------------------------------------------------- *)
let subst_param (s : _subst) : oi_param -> oi_param =
  let s = f_subst_of_subst s in
  fun oi -> Fsubst.subst_param s oi

let subst_params (s : _subst) : oi_params -> oi_params =
  let s = f_subst_of_subst s in
  fun oi -> Fsubst.subst_params s oi

(* -------------------------------------------------------------------- *)
let subst_funsig (s : _subst) (funsig : funsig) =
  let fs_arg = s.s_ty funsig.fs_arg in
  let fs_ret = s.s_ty funsig.fs_ret in
  let fs_anm = List.map (subst_ovariable s) funsig.fs_anames in

  { fs_name   = funsig.fs_name;
    fs_arg    = fs_arg;
    fs_anames = fs_anm;
    fs_ret    = fs_ret; }

(* -------------------------------------------------------------------- *)
let subst_mod_restr (s : _subst) (mr : mod_restr) : mod_restr =
  let rx =
    ur_app (fun set -> EcPath.Sx.fold (fun x r ->
        EcPath.Sx.add (EcPath.x_subst s.s_fmp x) r
      ) set EcPath.Sx.empty) mr.mr_xpaths
  in
  let r =
    ur_app (fun set -> EcPath.Sm.fold (fun x r ->
        EcPath.Sm.add (EcPath.m_subst s.s_fmp x) r
      ) set EcPath.Sm.empty) mr.mr_mpaths
  in
  let mr_params = subst_params s mr.mr_params in
  let mr_cost = subst_form s mr.mr_cost in

  { mr_xpaths = rx; mr_mpaths = r; mr_params; mr_cost; }

(* -------------------------------------------------------------------- *)
let rec subst_modsig_body_item (s : _subst) (item : module_sig_body_item) =
  match item with
  | Tys_function funsig -> Tys_function (subst_funsig s funsig)

(* -------------------------------------------------------------------- *)
and subst_modsig_body (s : _subst) (sbody : module_sig_body) =
  List.map (subst_modsig_body_item s) sbody

(* -------------------------------------------------------------------- *)
and subst_modsig ?params (s : _subst) (comps : module_sig) =
  let sbody, newparams =
    match params with
    | None -> begin
        match comps.mis_params with
        | [] -> (s, [])
        | _  ->
          let aout =
            List.map_fold
              (fun (s : subst) (a, aty) ->
                let a'   = EcIdent.fresh a in
                let decl = (a', subst_modtype (_subst_of_subst s) aty) in
                  add_module s a (EcPath.mident a'), decl)
              s.s_s comps.mis_params
          in
            fst_map _subst_of_subst aout
    end

  | Some params ->
      let aout =
        List.map_fold
          (fun (s : subst) ((a, aty), a') ->
              let decl = (a', subst_modtype (_subst_of_subst s) aty) in
                add_module s a (EcPath.mident a'), decl)
            s.s_s (List.combine comps.mis_params params)
        in
          fst_map _subst_of_subst aout
  in

  let comps =
    EcModules.mk_msig_r
      ~mis_params:newparams
      ~mis_body:(subst_modsig_body sbody comps.mis_body)
      ~mis_restr:(subst_mod_restr sbody comps.mis_restr)
  in
    (sbody, comps)

(* -------------------------------------------------------------------- *)
(* TODO: cost: in_me_decl useful? *)
and subst_modtype
    ?(in_me_decl = false)
    (s     : _subst)
    (modty : module_type)
  : module_type
  =
  (* TODO A: can we improve on this ?*)
  (* In a [ME_Decl], module parameters are binded by the enclosing
     [module_sig] and the [module_type]. Both need to be refreshed
     simultaneously, hence the special behavior.  *)
  let subst_ident (id : EcIdent.t) : EcIdent.t =
    if in_me_decl then
      match
        let mp = Mid.find id s.s_s.sb_modules in
        EcPath.mtop mp
      with
      | `Local newid   -> newid
      | `Concrete _
      | exception Not_found -> id
    else id
  in

  let mt_params =
    if in_me_decl then
      List.map (fun (id, mt) ->
          subst_ident id, subst_modtype s mt
        ) modty.mt_params
    else
      List.map (snd_map (subst_modtype s)) modty.mt_params
  in
  let mt_name    = s.s_p modty.mt_name in
  let mt_args    = List.map (EcPath.m_subst s.s_fmp) modty.mt_args in
  let mt_restr   = subst_mod_restr s modty.mt_restr in
  mk_mt_r ~mt_params ~mt_name ~mt_args ~mt_restr

(* TODO: cost: in main before merging *)
(* and subst_modtype (s : _subst) (modty : module_type) =
 *   { mt_params = List.map (snd_map (subst_modtype s)) modty.mt_params;
 *     mt_name   = ofdfl (fun () -> s.s_p modty.mt_name) (Mp.find_opt modty.mt_name s.s_mt);
 *     mt_args   = List.map (EcPath.m_subst s.s_fmp) modty.mt_args;
 *     mt_restr = subst_mod_restr s modty.mt_restr; } *)

let subst_top_modsig (s : _subst) (ms: top_module_sig) =
  { tms_sig = snd (subst_modsig s ms.tms_sig);
    tms_loca = ms.tms_loca; }

(* -------------------------------------------------------------------- *)
let subst_function_def (s : _subst) (def : function_def) =
  let es = e_subst_of_subst s in
  { f_locals = List.map (subst_variable s) def.f_locals;
    f_body   = s_subst es def.f_body;
    f_ret    =  def.f_ret |> omap (e_subst es);
    f_uses   = subst_fun_uses s def.f_uses; }

(* -------------------------------------------------------------------- *)
let subst_function (s : _subst) (f : function_) =
  let sig' = subst_funsig s f.f_sig in
  let def' =
    match f.f_def with
    | FBdef def -> FBdef (subst_function_def s def)
    | FBalias f -> FBalias (EcPath.x_subst s.s_fmp f)
    | FBabs (params, (mod_cost, symb)) ->
      FBabs (subst_param s params, (subst_form s mod_cost, symb))
  in

  { f_name = f.f_name;
    f_sig  = sig';
    f_def  = def' }


(* -------------------------------------------------------------------- *)
let rec subst_module_item (s : _subst) (item : module_item) =
  match item with
  | MI_Module m ->
      let m' = subst_module s m in
      MI_Module m'

  | MI_Variable x ->
      let x' = subst_variable s x in
      MI_Variable x'

  | MI_Function f ->
      let f' = subst_function s f in
      MI_Function f'

(* -------------------------------------------------------------------- *)
and subst_module_items (s : _subst) (items : module_item list) =
  List.map (subst_module_item s) items

(* -------------------------------------------------------------------- *)
and subst_module_struct (s : _subst) (bstruct : module_structure) =
    { ms_body = subst_module_items s bstruct.ms_body; }

(* -------------------------------------------------------------------- *)
and subst_module_body (s : _subst) (body : module_body) : module_body =
  match body with
  | ME_Alias (arity,m) ->
      ME_Alias (arity, EcPath.m_subst s.s_fmp m)

  | ME_Structure bstruct ->
      ME_Structure (subst_module_struct s bstruct)

  | ME_Decl p -> ME_Decl (subst_modtype ~in_me_decl:true s p)

  | ME_Wrap (id, k, mt) -> assert false (* TODO: cost: *)

(* -------------------------------------------------------------------- *)
and subst_module_comps (s : _subst) (comps : module_comps) =
  (subst_module_items s comps : module_comps)

(* -------------------------------------------------------------------- *)
and subst_module (s : _subst) (m : module_expr) : module_expr =
  let sbody,me_params = match m.me_params with
    | [] -> (s, [])
    | _  ->
      let aout =
        List.map_fold
        (fun (s : subst) (a, aty) ->
          let a'   = EcIdent.fresh a in
          let decl = (a', subst_modtype (_subst_of_subst s) aty) in
           add_module s a (EcPath.mident a'), decl)
        s.s_s m.me_params
      in
      fst_map _subst_of_subst aout in

  let me_body   = subst_module_body sbody m.me_body in
  let me_comps  = subst_module_comps sbody m.me_comps in
  let me_sig_body = subst_modsig_body sbody m.me_sig_body in
  { me_name = m.me_name; me_body; me_comps; me_params; me_sig_body }

(* -------------------------------------------------------------------- *)
let subst_top_module (s : _subst) (m : top_module_expr) =
  { tme_expr = subst_module s m.tme_expr;
    tme_loca = m.tme_loca; }

(* -------------------------------------------------------------------- *)
let add_tparams (s : _subst) (params : ty_params) tys =
  match params with
  | [] -> assert (tys = []); s
  | _  ->
    let styv =
      List.fold_left2 (fun m (p, _) ty -> Mid.add p ty m)
        Mid.empty params tys in
    let sty =
      { ty_subst_id with
          ts_def = s.s_sty.ts_def;
          ts_p   = s.s_p;
          ts_mp  = s.s_fmp;
          ts_v   = Mid.find_opt^~ styv; }
    in
      { s with s_sty = sty; s_ty = EcTypes.ty_subst sty }

let init_tparams (s : _subst) (params : ty_params) (params' : ty_params) =
  add_tparams s params (List.map (fun (p', _) -> tvar p') params')

(* -------------------------------------------------------------------- *)
let subst_typaram (s : _subst) ((id, tc) : ty_param) =
  (EcIdent.fresh id, Sp.fold (fun p tc -> Sp.add (s.s_p p) tc) tc Sp.empty)

let subst_typarams (s : _subst) (typ : ty_params) =
  List.map (subst_typaram s) typ

(* -------------------------------------------------------------------- *)
let subst_agparam (s : _subst) (id : EcIdent.t) =
  (EcIdent.fresh id)

let subst_agparams (s : _subst) (ids : EcIdent.t list) =
  List.map (subst_agparam s) ids

(* -------------------------------------------------------------------- *)
let subst_genty (s : _subst) (typ, ty) =
  let typ' = subst_typarams s typ in
  let s    = init_tparams s typ typ' in
    (typ', s.s_ty ty)

(* -------------------------------------------------------------------- *)
let open_tydecl (s : _subst) (tyd : tydecl) tys =
  let sty = add_tparams s tyd.tyd_params tys in

  match tyd.tyd_type with
  | `Abstract tc ->
      `Abstract (Sp.fold (fun p tc -> Sp.add (s.s_p p) tc) tc Sp.empty)

  | `Concrete ty ->
      `Concrete (sty.s_ty ty)

  | `Datatype dtype ->
      let dtype =
        { tydt_ctors   = List.map (snd_map (List.map sty.s_ty)) dtype.tydt_ctors;
          tydt_schelim = Fsubst.f_subst (f_subst_of_subst sty) dtype.tydt_schelim;
          tydt_schcase = Fsubst.f_subst (f_subst_of_subst sty) dtype.tydt_schcase; }
      in `Datatype dtype

  | `Record (scheme, fields) ->
      `Record (Fsubst.f_subst (f_subst_of_subst sty) scheme,
               List.map (snd_map sty.s_ty) fields)

let subst_tydecl (s : _subst) (tyd : tydecl) =
  let params' = List.map (subst_typaram s) tyd.tyd_params in
  let tys     = List.map (fun (id, _) -> tvar id) params' in
  let body    = open_tydecl s tyd tys in

  { tyd_params  = params';
    tyd_type    = body;
    tyd_resolve = tyd.tyd_resolve;
    tyd_loca    = tyd.tyd_loca; }

(* -------------------------------------------------------------------- *)
let rec subst_op_kind (s : _subst) (kind : operator_kind) =
  match kind with
  | OB_oper (Some body) ->
      OB_oper (Some (subst_op_body s body))

  | OB_pred (Some body) ->
      OB_pred (Some (subst_pr_body s body))

  | OB_nott nott ->
     OB_nott (subst_notation s nott)

  | OB_oper None | OB_pred None -> kind

and subst_notation (s : _subst) (nott : notation) =
  let es = e_subst_of_subst s in
  let es, xs = EcTypes.add_locals es nott.ont_args in
  { ont_args  = xs;
    ont_resty = s.s_ty nott.ont_resty;
    ont_body  = EcTypes.e_subst es nott.ont_body;
    ont_ponly = nott.ont_ponly; }

and subst_op_body (s : _subst) (bd : opbody) =
  match bd with
  | OP_Plain (body, nosmt) ->
      let s = e_subst_of_subst s in
        OP_Plain (EcTypes.e_subst s body, nosmt)

  | OP_Constr (p, i)  -> OP_Constr (s.s_p p, i)
  | OP_Record p       -> OP_Record (s.s_p p)
  | OP_Proj (p, i, j) -> OP_Proj (s.s_p p, i, j)

  | OP_Fix opfix ->
      let (es, args) =
        EcTypes.add_locals (e_subst_of_subst s) opfix.opf_args in

        OP_Fix { opf_args     = args;
                 opf_resty    = s.s_ty opfix.opf_resty;
                 opf_struct   = opfix.opf_struct;
                 opf_branches = subst_branches es opfix.opf_branches;
                 opf_nosmt    = opfix.opf_nosmt; }

  | OP_TC -> OP_TC

and subst_branches es = function
  | OPB_Leaf (locals, e) ->
      let (es, locals) =
        List.map_fold
          (fun es locals -> EcTypes.add_locals es locals)
          es locals
      in
        OPB_Leaf (locals, EcTypes.e_subst es e)

  | OPB_Branch bs ->
      let for1 b =
        let (ctorp, ctori) = b.opb_ctor in
          { opb_ctor = (es.es_p ctorp, ctori);
            opb_sub  = subst_branches es b.opb_sub; }
      in
        OPB_Branch (Parray.map for1 bs)

and subst_pr_body (s : _subst) (bd : prbody) =
  match bd with
  | PR_Plain body ->
      let s = f_subst_of_subst s in
      PR_Plain (Fsubst.f_subst s body)

  | PR_Ind ind ->
      let args    = List.map (snd_map gtty) ind.pri_args in
      let s, args = Fsubst.add_bindings (f_subst_of_subst s) args in
      let args    = List.map (snd_map gty_as_ty) args in
      let ctors   =
        let for1 ctor =
          let s, bds = Fsubst.add_bindings s ctor.prc_bds in
          let spec   = List.map (Fsubst.f_subst s) ctor.prc_spec in
          { ctor with prc_bds = bds; prc_spec = spec; }
        in List.map for1 ind.pri_ctors

      in PR_Ind { pri_args = args; pri_ctors = ctors; }

(* -------------------------------------------------------------------- *)
let open_oper (s:_subst) (op:operator) tys =
  let sty  = add_tparams s op.op_tparams tys in
  let ty   = sty.s_ty op.op_ty in
  let kind = subst_op_kind sty op.op_kind in
  ty, kind

let subst_op (s : _subst) (op : operator) =
  let tparams = List.map (subst_typaram s) op.op_tparams in
  let tys = (List.map (fun (p', _) -> tvar p') tparams) in
  let ty, kind = open_oper s op tys in

  { op_tparams  = tparams       ;
    op_ty       = ty            ;
    op_kind     = kind          ;
    op_loca     = op.op_loca    ;
    op_opaque   = op.op_opaque  ;
    op_clinline = op.op_clinline; }

(* -------------------------------------------------------------------- *)
let subst_ax (s : _subst) (ax : axiom) =
  (* refresh type variables *)
  let params = List.map (subst_typaram s) ax.ax_tparams in
  let s      = init_tparams s ax.ax_tparams params in

  (* refresh agent names *)
  let s = f_subst_of_subst s in
  let s, ax_agents =
    List.fold_left_map (fun s ag ->
        let ag' = EcIdent.fresh ag in
        (Fsubst.f_bind_agent s ag ag', ag')
      ) s ax.ax_agents
  in

  let spec = Fsubst.f_subst s ax.ax_spec in
  { ax_tparams    = params;
    ax_spec       = spec;
    ax_agents;
    ax_kind       = ax.ax_kind;
    ax_loca       = ax.ax_loca;
    ax_visibility = ax.ax_visibility; }

(* -------------------------------------------------------------------- *)
let subst_schema (s : _subst) (ax : ax_schema) =
  (* FIXME: SCHEMA *)
  let params = List.map (subst_typaram s) ax.axs_tparams in
  let s      = init_tparams s ax.axs_tparams params in
  let spec   = Fsubst.f_subst (f_subst_of_subst s) ax.axs_spec in

  { axs_tparams = params;
    axs_pparams = ax.axs_pparams;
    axs_params  = List.map (snd_map s.s_ty) ax.axs_params;
    axs_loca    = ax.axs_loca;
    axs_spec    = spec; }

(* -------------------------------------------------------------------- *)
let subst_ring (s : _subst) cr =
  { r_type  = s.s_ty cr.r_type;
    r_zero  = s.s_p  cr.r_zero;
    r_one   = s.s_p  cr.r_one;
    r_add   = s.s_p  cr.r_add;
    r_opp   = cr.r_opp |> omap s.s_p;
    r_mul   = s.s_p cr.r_mul;
    r_exp   = cr.r_exp |> omap s.s_p;
    r_sub   = cr.r_sub |> omap s.s_p;
    r_embed =
      begin match cr.r_embed with
      | `Direct  -> `Direct
      | `Default -> `Default
      | `Embed p -> `Embed (s.s_p p)
      end;
    r_kind = cr.r_kind
  }

(* -------------------------------------------------------------------- *)
let subst_field (s : _subst) cr =
  { f_ring = subst_ring s cr.f_ring;
    f_inv  = s.s_p cr.f_inv;
    f_div  = cr.f_div |> omap s.s_p; }

(* -------------------------------------------------------------------- *)
let subst_instance (s : _subst) tci =
  match tci with
  | `Ring    cr -> `Ring  (subst_ring  s cr)
  | `Field   cr -> `Field (subst_field s cr)
  | `General p  -> `General (s.s_p p)

(* -------------------------------------------------------------------- *)
let subst_tc (s : _subst) tc =
  let tc_prt = tc.tc_prt |> omap s.s_p in
  let tc_ops = List.map (snd_map s.s_ty) tc.tc_ops in
  let tc_axs = List.map (snd_map (subst_form s)) tc.tc_axs in
    { tc_prt; tc_ops; tc_axs; tc_loca = tc.tc_loca }

(* -------------------------------------------------------------------- *)
(* SUBSTITUTION OVER THEORIES *)
let rec subst_theory_item_r (s : _subst) (item : theory_item_r) =
  match item with
  | Th_type (x, tydecl) ->
      Th_type (x, subst_tydecl s tydecl)

  | Th_operator (x, op) ->
      Th_operator (x, subst_op s op)

  | Th_axiom (x, ax) ->
      Th_axiom (x, subst_ax s ax)

  | Th_schema (x, schema) ->
      Th_schema (x, subst_schema s schema)

  | Th_modtype (x, tymod) ->
      Th_modtype (x, subst_top_modsig s tymod)

  | Th_module m ->
      Th_module (subst_top_module s m)

  | Th_theory (x, th) ->
      Th_theory (x, subst_ctheory s th)

  | Th_export (p, lc) ->
      Th_export (s.s_p p, lc)

  | Th_instance (ty, tci, lc) ->
      Th_instance (subst_genty s ty, subst_instance s tci, lc)

  | Th_typeclass (x, tc) ->
      Th_typeclass (x, subst_tc s tc)

  | Th_baserw _ ->
      item

  | Th_addrw (b, ls, lc) ->
      Th_addrw (s.s_p b, List.map s.s_p ls, lc)

  | Th_reduction rules ->
      let rules =
        List.map (fun (p, opts, _) -> (s.s_p p, opts, None)) rules
      in Th_reduction rules

  | Th_auto (lvl, base, ps, lc) ->
      Th_auto (lvl, base, List.map s.s_p ps, lc)

(* -------------------------------------------------------------------- *)
and subst_theory (s : _subst) (items : theory) =
  List.map (subst_theory_item s) items

(* -------------------------------------------------------------------- *)
and subst_theory_item (s : _subst) (item : theory_item) =
  { ti_item   = subst_theory_item_r s item.ti_item;
    ti_import = item.ti_import; }

(* -------------------------------------------------------------------- *)
and subst_ctheory (s : _subst) (cth : ctheory) =
  { cth_items  = subst_theory s cth.cth_items;
    cth_loca   = cth.cth_loca;
    cth_mode   = cth.cth_mode;
    cth_source = omap (subst_theory_source s) cth.cth_source; }

(* -------------------------------------------------------------------- *)
and subst_theory_source (s : _subst) (ths : thsource) =
  { ths_base = s.s_p ths.ths_base; }

(* -------------------------------------------------------------------- *)
let subst_branches     s = subst_branches (e_subst_of_subst (_subst_of_subst s))
let subst_ax           s = subst_ax (_subst_of_subst s)
let subst_schema       s = subst_schema (_subst_of_subst s)
let subst_op           s = subst_op (_subst_of_subst s)
let subst_tydecl       s = subst_tydecl (_subst_of_subst s)
let subst_tc           s = subst_tc (_subst_of_subst s)
let subst_theory       s = subst_theory (_subst_of_subst s)

let subst_function     s = subst_function (_subst_of_subst s)
let subst_module       s = subst_module (_subst_of_subst s)
let subst_top_module   s = subst_top_module (_subst_of_subst s)
let subst_module_comps s = subst_module_comps (_subst_of_subst s)
let subst_module_body  s = subst_module_body (_subst_of_subst s)

let subst_modtype      s = subst_modtype (_subst_of_subst s)
let subst_modsig         = fun ?params s x -> snd (subst_modsig ?params (_subst_of_subst s) x)
let subst_top_modsig   s = subst_top_modsig (_subst_of_subst s)
let subst_modsig_body  s = subst_modsig_body (_subst_of_subst s)
let subst_mod_restr    s = subst_mod_restr (_subst_of_subst s)

let subst_mpath        s = EcPath.m_subst (_subst_of_subst s).s_fmp
let subst_path         s = (_subst_of_subst s).s_p

let subst_form         s = fun f -> (Fsubst.f_subst (f_subst_of_subst (_subst_of_subst s)) f)
let subst_ty           s = fun t -> ((_subst_of_subst s).s_ty t)
let subst_genty        s = fun t -> (subst_genty (_subst_of_subst s) t)

let subst_instance     s = subst_instance (_subst_of_subst s)

let open_oper   = open_oper   (_subst_of_subst (empty ()))
let open_tydecl = open_tydecl (_subst_of_subst (empty ()))

(* -------------------------------------------------------------------- *)
let freshen_type (typ, ty) =
  let empty = _subst_of_subst (empty ()) in
  let typ' = List.map (subst_typaram empty) typ in
  let s = init_tparams empty typ typ' in
    (typ', s.s_ty ty)
