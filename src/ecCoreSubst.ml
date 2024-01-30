(* -------------------------------------------------------------------- *)
open EcUtils
open EcIdent
open EcPath
open EcUid
open EcAst
open EcTypes
open EcCoreFol
open EcCoreModules

(* -------------------------------------------------------------------- *)
(* form before subst -> form after -> resulting form *)

type sc_instanciate =
  { sc_memtype : memtype;
    sc_mempred : mem_pr Mid.t;
    sc_expr    : expr Mid.t;
  }

type f_subst = {
  fs_freshen : bool; (* true means freshen locals *)
  fs_u       : ty Muid.t;
  fs_v       : ty Mid.t;

  fs_mod     : EcPath.mpath Mid.t;

  fs_loc     : form Mid.t;
  fs_eloc    : expr Mid.t;

  fs_schema  : sc_instanciate option;

  (* free variables in the codom of the substitution *)
  fs_fv      : int Mid.t;
}

type 'a substitute = f_subst -> 'a -> 'a
type tx = form -> form -> form
type 'a tx_substitute = ?tx:tx -> 'a substitute
type 'a subst_binder = f_subst -> 'a -> f_subst * 'a

(* -------------------------------------------------------------------- *)

let fv_Mid fv m s =
  Mid.fold (fun _ t s -> fv_union s (fv t)) m s

let f_subst_init
      ?(freshen=false)
      ?(tu=Muid.empty)
      ?(tv=Mid.empty)
      ?(esloc=Mid.empty)
      ?schema
      () =
  let fv = Mid.empty in
  let fv = Muid.fold (fun _ t s -> fv_union s (ty_fv t)) tu fv in
  let fv = fv_Mid ty_fv tv fv in
  let fv = fv_Mid e_fv esloc fv in
  let fv =
    ofold (fun sc s ->
        let fv = fv_union s (mt_fv sc.sc_memtype) in
        let fv = fv_Mid e_fv sc.sc_expr fv in
        fv_Mid (fun (m,f) -> Mid.remove m (f_fv f)) sc.sc_mempred fv)
      fv schema in

  {
  fs_freshen  = freshen;

  fs_u        = tu;
  fs_v        = tv;

  fs_mod      = Mid.empty;

  fs_loc      = Mid.empty;
  fs_eloc     = esloc;
  fs_schema   = schema;

  fs_fv       = fv;

}

let f_subst_id = f_subst_init ()

(* -------------------------------------------------------------------- *)

let bind_elocal s x e =
  { s with fs_eloc = Mid.add x e s.fs_eloc;
           fs_fv = fv_union (e_fv e) s.fs_fv}

let bind_elocals s esloc =
  let merger _ oe1 oe2 =
    if oe2 = None then oe1
    else oe2 in
  let fs_eloc = Mid.merge merger s.fs_eloc esloc in
  let fs_fv = fv_Mid e_fv esloc s.fs_fv in
  { s with fs_eloc; fs_fv }

let f_bind_local s x t =
  { s with fs_loc = Mid.add x t s.fs_loc;
           fs_fv = fv_union (f_fv t) s.fs_fv }

let f_bind_mem s m1 m2 mt = f_bind_local s m1 (f_mem (m2,mt))

let bind_mod s x mp =
  { s with
    fs_mod   = Mid.add x mp s.fs_mod;
    fs_fv    = m_fv s.fs_fv mp;
  }

let f_bind_absmod s (m1:EcIdent.t) (m2:EcIdent.t) =
  bind_mod s m1 (EcPath.mident m2)

let f_bind_mod s x mp = bind_mod s x mp

let f_bind_rename s xfrom xto ty =
  let xf = f_local xto ty in
  (* FIXME: This work just by luck ... *)
  let xe = e_local xto ty in
  let s  = f_bind_local s xfrom xf in
  (* Free variable already added by f_bind_local *)
  { s with fs_eloc = Mid.add xfrom xe s.fs_eloc; }

(* ------------------------------------------------------------------ *)
let f_rem_local s x =
  { s with fs_loc  = Mid.remove x s.fs_loc;
           fs_eloc = Mid.remove x s.fs_eloc; }

let f_rem_mem s m = f_rem_local s m

let f_rem_mod s x =
  { s with fs_mod = Mid.remove x s.fs_mod }

(* -------------------------------------------------------------------- *)
let mp_subst s = EcPath.m_subst_abs s.fs_mod

let x_subst s x =
    EcPath.x_subst_abs s.fs_mod x

let pv_subst s = pv_subst (x_subst s)

(* -------------------------------------------------------------------- *)
let refresh s x =
  if s.fs_freshen || Mid.mem x s.fs_fv then
    EcIdent.fresh x
  else x

(* -------------------------------------------------------------------- *)
let is_ty_subst_id s =
     Mid.is_empty s.fs_mod
  && Muid.is_empty s.fs_u
  && Mid.is_empty s.fs_v

let is_subst_id s =
    s.fs_freshen = false
  && is_ty_subst_id s
  && Mid.is_empty   s.fs_loc
  && Mid.is_empty   s.fs_eloc
  && s.fs_schema = None

let rec ty_subst ~tx (s : f_subst) ty =
  match ty.ty_node with
  | Tmem mt -> tmem (mt_subst ~tx s mt)

  | Tunivar id    ->
      begin match Muid.find_opt id s.fs_u with
      | None ->
          ty
      | Some ty ->
          ty_subst ~tx s ty
      end
  | Tvar id -> Mid.find_def ty id s.fs_v

  | _ -> ty_map (ty_subst ~tx s) ty

and gty_subst ~tx s gty =
  match gty with
  | GTty ty ->
    let ty' = ty_subst ~tx s ty in
    if ty == ty' then gty else GTty ty'

  | GTmodty mty ->
    let mty' = mty_subst ~tx s mty in
    if mty == mty' then gty else GTmodty mty'

and add_mty_binding ~tx s (x, mty) =
  let mty' = mty_subst ~tx s mty in
  let x'   = refresh s x in

  if x == x' && mty == mty' then f_rem_mod s x, (x, mty)
  else f_bind_absmod s x x', (x', mty')

and add_mty_bindings ~tx s b = List.Smart.map_fold (add_mty_binding ~tx) s b

and add_ty_binding ~tx s (x, ty) =
  let ty' = ty_subst ~tx s ty in
  let x' = refresh s x in
  if x == x' && ty == ty' then f_rem_local s x, (x, ty)
  else f_bind_rename s x x' ty', (x', ty')

and add_ty_bindings ~tx s b = List.Smart.map_fold (add_ty_binding ~tx) s b

and add_binding ~tx s (x, gty as b) =
  match gty with
  | GTty ty ->
    let s, (x', ty') = add_ty_binding ~tx s (x, ty) in
    if x == x' && ty == ty' then s, b
    else s, (x', GTty ty')
  | GTmodty mty ->
    let s, (x', mty') = add_mty_binding ~tx s (x, mty) in
    if x == x' && mty == mty' then s, b
    else s, (x', GTmodty mty')

and add_bindings ~tx = List.Smart.map_fold (add_binding ~tx)

and add_me_binding ~tx s (x, mt as b) =
  let s, (x', ty) = add_ty_binding ~tx s (x, tmem mt) in
  let mt' = destr_tmem ty in
  if x == x' && mt == mt' then s, b
  else s, (x', mt')

and mt_subst ~tx (s : f_subst) (mt : memtype) =
  mk_mt (omap (lmt_subst ~tx s) mt.mt_lmt) (gvs_subst ~tx s mt.mt_gvs)

and lmt_subst ~tx (s : f_subst) (lmt : local_memtype) =
  lmt_map_ty (ty_subst ~tx s) lmt

and gvs_subst ~tx s gvs =
  let node =
    match gvs.gvs_node with
    | (Empty | All | Set _) as x -> x
    | GlobFun ff -> GlobFun (ff_subst ~tx s ff)
    | Union(g1,g2) -> Union(gvs_subst ~tx s g1, gvs_subst ~tx s g2)
    | Diff(g1,g2)  -> Diff(gvs_subst ~tx s g1, gvs_subst ~tx s g2)
    | Inter(g1,g2) -> Inter(gvs_subst ~tx s g1, gvs_subst ~tx s g2)
  in
  mk_gvs node

and vs_subst ~tx s vs =
  mk_vs vs.lvs (gvs_subst ~tx s vs.gvs)

and ff_subst ~tx s ff =
  let s, params = add_mty_bindings ~tx s ff.ff_params in
  let xp = x_subst s ff.ff_xp in
  mk_ff params xp

and mty_subst ~tx s (mty : module_type) =
  (* params are unbound in restr *)
  let mt_restr  = gvs_subst ~tx s mty.mt_restr in

  let s, mt_params = add_mty_bindings ~tx s mty.mt_params in
  let mt_name   = mty.mt_name in
  let mt_args   = List.map (mp_subst s) mty.mt_args in
  let mt_oi     = EcSymbols.Msym.map (oi_subst ~tx s) mty.mt_oi in

  mk_mty mt_restr mt_params mt_name mt_args mt_oi

and oi_subst ~(tx : form -> form -> form) (s : f_subst) (oi : oracle_info) =
  let costs = match PreOI.costs oi with
    | `Unbounded -> `Unbounded
    | `Bounded (self,calls) ->
        let calls = EcPath.Mx.fold (fun x a calls ->
            EcPath.Mx.change
              (fun old -> assert (old = None); Some (f_subst ~tx s a))
              (x_subst s x)
              calls
          ) calls EcPath.Mx.empty in
        let self = f_subst ~tx s self in
       `Bounded (self,calls) in
  PreOI.mk
    (List.map (x_subst s) (PreOI.allowed oi))
    costs

and lp_subst ~tx (s: f_subst) (lp:lpattern) =
  match lp with
  | LSymbol x ->
    let (s, x') = add_ty_binding ~tx s x in
    if x == x' then (s, lp) else (s, LSymbol x')

  | LTuple xs ->
    let (s, xs') = add_ty_bindings ~tx s xs in
    if xs == xs' then (s, lp) else (s, LTuple xs')

  | LRecord (p, xs) ->
    let (s, xs') =
      List.Smart.map_fold
        (fun s ((x, t) as xt) ->
          match x with
          | None ->
            let t' = ty_subst ~tx s t in
            if t == t' then (s, xt) else (s, (x, t'))
          | Some x ->
            let (s, (x', t')) = add_ty_binding ~tx s (x, t) in
            if x == x' && t == t' then (s, xt)
            else (s, (Some x', t')))
        s xs
    in
    if xs == xs' then (s, lp) else (s, LRecord (p, xs'))

and f_subst ~tx s fp =
  tx fp (match fp.f_node with
  | Fquant (q, b, f) ->
    let s, b' = add_bindings ~tx s b in
    let f'    = f_subst ~tx s f in
          f_quant q b' f'

  | Flet (lp, f1, f2) ->
    let f1'    = f_subst ~tx s f1 in
    let s, lp' = lp_subst ~tx s lp in
    let f2'    = f_subst ~tx s f2 in
    f_let lp' f1' f2'

  | Flocal id -> begin
    match Mid.find_opt id s.fs_loc with
    | Some f -> f
    | None ->
      let ty' = ty_subst ~tx s fp.f_ty in
      f_local id ty'
    end

  | Fop (p, tys) ->
    let ty'  = ty_subst ~tx s fp.f_ty in
    let tys' = List.Smart.map (ty_subst ~tx s) tys in
    f_op p tys' ty'

  | Fpvar (pv, m) ->
    let pv' = pv_subst s pv in (* Normally this do nothing *)
    let m'  = f_subst ~tx s m in
    let ty' = ty_subst ~tx s fp.f_ty in
    f_pvar pv' ty' m'

  | Fmrestr (m, mt) ->
    let m' = f_subst ~tx s m in
    let mt' = mt_subst ~tx s mt in
    f_mrestr m' mt'

  | Fupdvar(m, x, v) ->
    let m' = f_subst ~tx s m in
    let x' = pv_subst s x in
    let v' = f_subst ~tx s v in
    f_updvar m' x' v'

  | Fupdmem(m1, on, m2) ->
    let m1' = f_subst ~tx s m1 in
    let on' = vs_subst ~tx s on in
    let m2' = f_subst ~tx s m2 in
    f_updmem m1' on' m2'

  | FhoareF hf ->
    let hf_f  = x_subst s hf.hf_f in
    let s     = f_rem_mem s mhr in
    let hf_pr = f_subst ~tx s hf.hf_pr in
    let hf_po = f_subst ~tx s hf.hf_po in
    f_hoareF hf_pr hf_f hf_po

  | FhoareS hs ->
    let hs_s    = s_subst ~tx s hs.hs_s in
    let s, hs_m = add_me_binding ~tx s hs.hs_m in
    let hs_pr   = f_subst ~tx s hs.hs_pr in
    let hs_po   = f_subst ~tx s hs.hs_po in
    f_hoareS hs_m hs_pr hs_s hs_po

  | FeHoareF hf ->
    let hf_f  = x_subst s hf.ehf_f in
    let s     = f_rem_mem s mhr in
    let hf_pr = f_subst ~tx s hf.ehf_pr in
    let hf_po = f_subst ~tx s hf.ehf_po in
    f_eHoareF hf_pr hf_f hf_po

  | FeHoareS hs ->
    let hs_s    = s_subst ~tx s hs.ehs_s in
    let s, hs_m = add_me_binding ~tx s hs.ehs_m in
    let hs_pr   = f_subst ~tx s hs.ehs_pr in
    let hs_po   = f_subst ~tx s hs.ehs_po in
    f_eHoareS hs_m hs_pr hs_s hs_po

  | FcHoareF hf ->
    let hf_f  = x_subst s hf.chf_f in
    let s     = f_rem_mem s mhr in
    let hf_pr = f_subst ~tx s hf.chf_pr in
    let hf_po = f_subst ~tx s hf.chf_po in
    let hf_co = cost_subst ~tx s hf.chf_co in
    f_cHoareF hf_pr hf_f hf_po hf_co

  | FcHoareS hs ->
    let hs_s    = s_subst ~tx s hs.chs_s in
    let s, hs_m = add_me_binding ~tx s hs.chs_m in
    let hs_pr   = f_subst ~tx s hs.chs_pr in
    let hs_po   = f_subst ~tx s hs.chs_po in
    let hs_co   = cost_subst ~tx s hs.chs_co in
    f_cHoareS hs_m hs_pr hs_s hs_po hs_co

  | FbdHoareF hf ->
    let hf_f  = x_subst s hf.bhf_f in
    let s     = f_rem_mem s mhr in
    let hf_pr = f_subst ~tx s hf.bhf_pr in
    let hf_po = f_subst ~tx s hf.bhf_po in
    let hf_bd = f_subst ~tx s hf.bhf_bd in
    f_bdHoareF hf_pr hf_f hf_po hf.bhf_cmp hf_bd

  | FbdHoareS hs ->
    let hs_s = s_subst ~tx s hs.bhs_s in
    let s, hs_m = add_me_binding ~tx s hs.bhs_m in
    let hs_pr = f_subst ~tx s hs.bhs_pr in
    let hs_po = f_subst ~tx s hs.bhs_po in
    let hs_bd = f_subst ~tx s hs.bhs_bd in
    f_bdHoareS hs_m hs_pr hs_s hs_po hs.bhs_cmp hs_bd

  | FequivF ef ->
    let ef_fl = x_subst s ef.ef_fl in
    let ef_fr = x_subst s ef.ef_fr in
    let s = f_rem_mem s mleft in
    let s = f_rem_mem s mright in
    let ef_pr = f_subst ~tx s ef.ef_pr in
    let ef_po = f_subst ~tx s ef.ef_po in
    f_equivF ef_pr ef_fl ef_fr ef_po

  | FequivS es ->
    let es_sl = s_subst ~tx s es.es_sl in
    let es_sr = s_subst ~tx s es.es_sr in
    let s, es_ml = add_me_binding ~tx s es.es_ml in
    let s, es_mr = add_me_binding ~tx s es.es_mr in
    let es_pr = f_subst ~tx s es.es_pr in
    let es_po = f_subst ~tx s es.es_po in
    f_equivS es_ml es_mr es_pr es_sl es_sr es_po

  | FeagerF eg ->
    let eg_fl = x_subst s eg.eg_fl in
    let eg_fr = x_subst s eg.eg_fr in
    let eg_sl = s_subst ~tx s eg.eg_sl in
    let eg_sr = s_subst ~tx s eg.eg_sr in
    let s = f_rem_mem s mleft in
    let s = f_rem_mem s mright in
    let eg_pr = f_subst ~tx s eg.eg_pr in
    let eg_po = f_subst ~tx s eg.eg_po in
    f_eagerF eg_pr eg_sl eg_fl eg_fr eg_sr eg_po

  | Fcoe coe ->
    if is_schema (snd coe.coe_mem) && s.fs_schema <> None then
      let m' = refresh s (fst coe.coe_mem) in
      (* We instanciate the schema *)
      let sc = oget s.fs_schema in
      let me' = m', sc.sc_memtype in
      (* We add the memory in the subst *)
      let s = f_bind_mem s (fst coe.coe_mem) m' sc.sc_memtype in
      (* We add the predicates in the subst *)
      let doit id (m, p) s =
        let fs_mem = f_bind_mem f_subst_id m m' sc.sc_memtype in
        let p = f_subst ~tx:(fun _ f -> f) fs_mem p in
        f_bind_local s id p in
      (* FIXME:                                      why None ? *)
      let s   = Mid.fold doit sc.sc_mempred {s with fs_schema = None } in
      (* We add the expressions in the subst *)
      let s   = bind_elocals s sc.sc_expr in
      let fm' = f_mem me' in
      let s   = Mid.fold (fun id e s ->
                    f_bind_local s id (form_of_expr ~mem:fm' e)) sc.sc_expr s in
        let pr' = f_subst ~tx s coe.coe_pre in
        let e'  = e_subst ~tx s coe.coe_e in
        f_coe pr' me' e'
      else
        let s, me' = add_me_binding ~tx s coe.coe_mem in
        let pr' = f_subst ~tx s coe.coe_pre in
        let e'  = e_subst ~tx s coe.coe_e in
        f_coe pr' me' e'

    | Fpr pr ->
      let pr_mem   = f_subst ~tx s pr.pr_mem in
      let pr_fun   = x_subst s pr.pr_fun in
      let pr_args  = f_subst ~tx s pr.pr_args in
      let s = f_rem_mem s mhr in
      let pr_event = f_subst ~tx s pr.pr_event in

      f_pr pr_mem pr_fun pr_args pr_event

    | _ ->
      f_map (ty_subst ~tx s) (f_subst ~tx s) fp)

and cost_subst ~tx s cost =
  let c_self = f_subst ~tx s cost.c_self
  and self', c_calls =
    EcPath.Mx.fold (fun x cb (self',calls) ->
      let x' = x_subst s x in
      let cb_cost'   = f_subst ~tx s cb.cb_cost in
      let cb_called' = f_subst ~tx s cb.cb_called in
      match x'.x_top.m_top with
      | `Local _ ->
        let cb' = { cb_cost   = cb_cost';
                    cb_called = cb_called'; } in
        ( self',
          EcPath.Mx.change
           (fun old -> assert (old  = None); Some cb')
           x' calls )
      | `Concrete _ ->
        (* TODO: A: better simplification*)
        ( f_xadd_simpl self' (f_xmuli_simpl cb_called' cb_cost'), calls)
      ) cost.c_calls (f_x0, EcPath.Mx.empty)
  in

  let c_self = f_xadd_simpl c_self self' in
  cost_r c_self c_calls


(* -------------------------------------------------------------------- *)
and add_elocal ~tx s ((x, t) as xt) =
  let x' = refresh s x in
  let t' = ty_subst ~tx s t in
  if   x == x' && t == t' then (s, xt)
  else bind_elocal s x (e_local x' t'), (x',t')

and add_elocals ~tx = List.Smart.map_fold (add_elocal ~tx)

and elp_subst ~tx (s: f_subst) (lp:lpattern) =
  match lp with
  | LSymbol x ->
    let (s, x') = add_elocal ~tx s x in
    (s, LSymbol x')

  | LTuple xs ->
    let (s, xs') = add_elocals ~tx s xs in
    (s, LTuple xs')

  | LRecord (p, xs) ->
    let (s, xs') =
      List.Smart.map_fold
        (fun s ((x, t) as xt) ->
          match x with
          | None ->
            let t' = ty_subst ~tx s t in
            if t == t' then (s, xt) else (s, (x, t'))
          | Some x ->
            let (s, (x', t')) = add_elocal ~tx s (x, t) in
            if   x == x' && t == t' then (s, xt)
            else (s, (Some x', t')))
        s xs
    in
    (s, LRecord (p, xs'))

and e_subst ~tx (s: f_subst) e =
  match e.e_node with
  | Elocal id -> begin
    match Mid.find_opt id s.fs_eloc with
    | Some e' -> e'
    | None    -> e_local id (ty_subst ~tx s e.e_ty)
    end

  | Evar pv ->
    let pv' = pv_subst s pv in (* This should do nothing *)
    let ty' = ty_subst ~tx s e.e_ty in
    e_var pv' ty'

  | Eop (p, tys) ->
    let tys' = List.Smart.map (ty_subst ~tx s) tys in
    let ty'  = ty_subst ~tx s e.e_ty in
    e_op p tys' ty'

  | Elet (lp, e1, e2) ->
    let e1' = e_subst ~tx s e1 in
    let s, lp' = elp_subst ~tx s lp in
    let e2' = e_subst ~tx s e2 in
    e_let lp' e1' e2'

  | Equant (q, b, e1) ->
    let s, b' = add_elocals ~tx s b in
    let e1'   = e_subst ~tx s e1 in
    e_quantif q b' e1'

  | _ -> e_map (ty_subst ~tx s) (e_subst ~tx s) e

(* -------------------------------------------------------------------- *)

and pvt_subst ~tx s (pv,ty as p) =
  let pv' = pv_subst s pv in
  let ty' = ty_subst ~tx s ty in
  if pv == pv' && ty == ty' then p else (pv', ty')

and lv_subst ~tx s lv =
  match lv with
  | LvVar pvt ->
    LvVar (pvt_subst ~tx s pvt)

  | LvTuple pvs ->
    let pvs' = List.Smart.map (pvt_subst ~tx s) pvs in
    LvTuple pvs'

and i_subst ~tx s i =
  match i.i_node with
  | Sasgn (lv, e) ->
    i_asgn (lv_subst ~tx s lv, e_subst ~tx s e)

  | Srnd (lv, e) ->
    i_rnd (lv_subst ~tx s lv, e_subst ~tx s e)

  | Scall (olv, mp, args) ->
    let olv'  = olv |> OSmart.omap (lv_subst ~tx s) in
    let mp'   = x_subst s mp in
    let args' = List.Smart.map (e_subst ~tx s) args in
    i_call (olv', mp', args')

  | Sif (e, s1, s2) ->
    i_if (e_subst ~tx s e, s_subst ~tx s s1, s_subst ~tx s s2)

  | Swhile(e, b) ->
    i_while (e_subst ~tx s e, s_subst ~tx s b)

  | Smatch (e, b) ->
    let forb ((xs, subs) as b1) =
      let s, xs' = add_elocals ~tx s xs in
      let subs'  = s_subst ~tx s subs in
      if xs == xs' && subs == subs' then b1 else (xs', subs')
    in
    i_match (e_subst ~tx s e, List.Smart.map forb b)

  | Sassert e ->
        i_assert (e_subst ~tx s e)

  | Sabstract _ ->
        i

and s_subst ~tx s c =
  stmt (List.Smart.map (i_subst ~tx s) c.s_node)

let ty_subst (s : f_subst) =
  if is_ty_subst_id s then identity
  else ty_subst ~tx:(fun _f1 f2 -> f2) s


(* -------------------------------------------------------------------- *)
(* Expressions                                                          *)
(* -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
let is_e_subst_id s =
     not s.fs_freshen
  && is_ty_subst_id s
  && Mid.is_empty s.fs_eloc

let e_subst s =
  if is_e_subst_id s then identity else e_subst ~tx:(fun _ f -> f) s

let s_subst s =
  if is_e_subst_id s then identity else s_subst ~tx:(fun _ f -> f) s

let add_elocal = add_elocal ~tx:(fun _ f -> f)
let add_elocals = add_elocals ~tx:(fun _ f -> f)

(* -------------------------------------------------------------------- *)
module Fsubst = struct

  let is_subst_id s =
       s.fs_freshen = false
    && is_ty_subst_id s
    && Mid.is_empty   s.fs_loc
    && Mid.is_empty   s.fs_eloc
    && s.fs_schema = None

  (* ------------------------------------------------------------------ *)
  let add_local s (x,t as xt) =
    let x' = refresh s x in
    let t' = ty_subst s t in
    if x == x' && t == t' then (s, xt)
    else f_bind_rename s x x' t', (x',t')

  let add_locals = List.Smart.map_fold add_local

  (* ------------------------------------------------------------------ *)
  (* Wrapper functions                                                  *)
  (* ------------------------------------------------------------------ *)

  let x_subst = x_subst
  let pv_subst = pv_subst

  let f_subst_init  = f_subst_init
  let f_subst_id    = f_subst_id

  let f_bind_local  = f_bind_local
  let f_bind_mem    = f_bind_mem
  let f_bind_absmod = f_bind_absmod
  let f_bind_mod    = f_bind_mod
  let f_bind_rename = f_bind_rename

  let add_binding  = add_binding ~tx:(fun _ f -> f)
  let add_bindings = add_bindings ~tx:(fun _ f -> f)

  (* ------------------------------------------------------------------ *)
  let f_subst ?(tx = fun _ f -> f) s =
    if is_subst_id s then identity else f_subst ~tx s

  let e_subst = e_subst
  let s_subst = s_subst

  let mp_subst  = mp_subst
  let lp_subst  = lp_subst ~tx:(fun _ f -> f)
  let gty_subst = gty_subst ~tx:(fun _ f -> f)
  let mt_subst  = mt_subst ~tx:(fun _ f -> f)
  let mty_subst = mty_subst ~tx:(fun _ f -> f)
  let oi_subst  = oi_subst ~tx:(fun _ f -> f)

  let f_subst_local x t =
    let s = f_bind_local f_subst_id x t in
    fun f -> if Mid.mem x f.f_fv then f_subst s f else f

  let f_subst_mem m1 m2 mt =
    let s = f_bind_mem f_subst_id m1 m2 mt in
    fun f -> if Mid.mem m1 f.f_fv then f_subst s f else f

  (* ------------------------------------------------------------------ *)
  let init_subst_tvar ~freshen s =
    f_subst_init ~freshen ~tv:s ()

  let f_subst_tvar ~freshen s =
    f_subst (init_subst_tvar ~freshen s)

end

(* -------------------------------------------------------------------- *)
module Tuni = struct

  let subst (uidmap : ty Muid.t) =
    f_subst_init ~tu:uidmap ()

  let subst1 ((id, t) : uid * ty) =
    subst (Muid.singleton id t)

  let subst_dom uidmap dom =
    List.map (ty_subst (subst uidmap)) dom

  let occurs u =
    let rec aux t =
      match t.ty_node with
      | Tunivar u' -> uid_equal u u'
      | _ -> ty_sub_exists aux t in
    aux

  let univars =
    let rec doit univars t =
      match t.ty_node with
      | Tunivar uid -> Suid.add uid univars
      | _ -> ty_fold doit univars t

    in fun t -> doit Suid.empty t

  let rec fv_rec fv t =
    match t.ty_node with
    | Tunivar id -> Suid.add id fv
    | _ -> ty_fold fv_rec fv t

  let fv = fv_rec Suid.empty
end

(* -------------------------------------------------------------------- *)
module Tvar = struct
  let subst (s : ty Mid.t) =
    ty_subst { f_subst_id with fs_v = s}

  let subst1 (id,t) =
    subst (Mid.singleton id t)

  let init lv lt =
    assert (List.length lv = List.length lt);
    List.fold_left2 (fun s v t -> Mid.add v t s) Mid.empty lv lt

  let f_subst ~freshen lv lt =
    Fsubst.f_subst_tvar ~freshen (init lv lt)
end
