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

type mod_extra =
  { mex_tglob : ty;
    mex_glob  : memory -> form;
  }

type sc_instanciate =
  { sc_memtype : memtype;
    sc_mempred : mem_pr Mid.t;
    sc_expr    : expr Mid.t;
  }

type f_subst = {
  fs_freshen  : bool; (* true means freshen locals *)

  fs_u         : ty Muid.t;
  fs_v         : ty Mid.t;

  fs_mod     : EcPath.mpath Mid.t;
  fs_modex   : mod_extra Mid.t;


  fs_loc      : form Mid.t;
  fs_eloc     : expr Mid.t;
  fs_mem      : EcIdent.t Mid.t;

  fs_schema   : sc_instanciate option;

  (* free variables in the codom of the substitution *)
  fs_fv       : int Mid.t;
}

type 'a substitute = f_subst -> 'a -> 'a
(* form before subst -> form after -> resulting form *)
type tx = form -> form -> form
type 'a tx_substitute = ?tx:tx -> 'a substitute
type 'a subst_binder = f_subst -> 'a -> f_subst * 'a

(* -------------------------------------------------------------------- *)

let mex_fv mp ex =
  let m = EcIdent.create "m" in
  fv_union (m_fv (ty_fv ex.mex_tglob) mp)
    (Mid.remove m (f_fv (ex.mex_glob m)))

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
  fs_modex    = Mid.empty;

  fs_loc      = Mid.empty;
  fs_eloc     = esloc;
  fs_mem      = Mid.empty;

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
    else (assert (oe1 = None); oe2) in
  let fs_eloc = Mid.merge merger s.fs_eloc esloc in
  let fs_fv = fv_Mid e_fv esloc s.fs_fv in
  { s with fs_eloc; fs_fv }

let f_bind_local s x t =
  let merger o = assert (o = None); Some t in
    { s with fs_loc = Mid.change merger x s.fs_loc;
             fs_fv = fv_union (f_fv t) s.fs_fv }

let f_bind_mem s m1 m2 =
  let merger o = assert (o = None); Some m2 in
    { s with fs_mem = Mid.change merger m1 s.fs_mem;
             fs_fv  = fv_add m2 s.fs_fv }

let f_rebind_mem s m1 m2 =
  let merger _ = Some m2 in
  { s with fs_mem = Mid.change merger m1 s.fs_mem;
           fs_fv  = fv_add m2 s.fs_fv }

let bind_mod s x mp ex =
  let merger o = assert (o = None); Some mp in
  { s with
    fs_mod   = Mid.change merger x s.fs_mod;
    fs_modex = Mid.add x ex s.fs_modex;
    fs_fv    = fv_union (mex_fv mp ex) s.fs_fv;
}

let f_bind_absmod s m1 m2 =
  bind_mod s m1 (EcPath.mident m2)
    { mex_tglob = tglob m2; mex_glob = (fun m -> f_glob m2 m); }

let f_bind_mod s x mp norm_mod =
  match EcPath.mget_ident_opt mp with
  | Some id ->
       f_bind_absmod s x id
  | None ->
     let ex = {
       mex_tglob = (norm_mod mhr).f_ty;
       mex_glob  = norm_mod } in
     bind_mod s x mp ex

let f_bind_rename s xfrom xto ty =
  let xf = f_local xto ty in
  (* FIXME: This work just by luck ... *)
  let xe = e_local xto ty in
  let s  = f_bind_local s xfrom xf in
  let merger o = assert (o = None); Some xe in
  (* Free variable already added by f_bind_local *)
  { s with fs_eloc = Mid.change merger xfrom s.fs_eloc; }

(* ------------------------------------------------------------------ *)
let f_rem_local s x =
  { s with fs_loc  = Mid.remove x s.fs_loc;
           fs_eloc = Mid.remove x s.fs_eloc; }

let f_rem_mem s m =
  assert (not (Mid.mem m s.fs_fv));
  { s with fs_mem = Mid.remove m s.fs_mem }

let f_rem_mod s x =
  { s with
    fs_mod   = Mid.remove x s.fs_mod;
    fs_modex = Mid.remove x s.fs_modex; }

(* -------------------------------------------------------------------- *)

let is_ty_subst_id s =
     Mid.is_empty s.fs_mod
  && Muid.is_empty s.fs_u
  && Mid.is_empty s.fs_v

let rec ty_subst (s : f_subst) ty =
  match ty.ty_node with
  | Tglob m ->
      begin match Mid.find_opt m s.fs_modex with
      | None -> ty
      | Some ex -> ex.mex_tglob
      end
  | Tunivar id    ->
      begin match Muid.find_opt id s.fs_u with
      | None ->
          ty
      | Some ty ->
          ty_subst s ty
      end
  | Tvar id       -> Mid.find_def ty id s.fs_v
  | _ -> ty_map (ty_subst s) ty


let ty_subst (s : f_subst) =
  if is_ty_subst_id s then identity
  else ty_subst s


(* -------------------------------------------------------------------- *)
(* Expressions                                                          *)
(* -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
let is_e_subst_id s =
     not s.fs_freshen
  && is_ty_subst_id s
  && Mid.is_empty s.fs_eloc

(* -------------------------------------------------------------------- *)
let refresh s x =
  if s.fs_freshen || Mid.mem x s.fs_fv then
    EcIdent.fresh x
  else x

(* -------------------------------------------------------------------- *)
let add_elocal s ((x, t) as xt) =
  let x' = refresh s x in
  let t' = ty_subst s t in
  if   x == x' && t == t' then (s, xt)
  else bind_elocal s x (e_local x' t'), (x',t')

let add_elocals = List.Smart.map_fold add_elocal

(* -------------------------------------------------------------------- *)
let elp_subst (s: f_subst) (lp:lpattern) =
  match lp with
  | LSymbol x ->
      let (s, x') = add_elocal s x in
        (s, LSymbol x')

  | LTuple xs ->
      let (s, xs') = add_elocals s xs in
        (s, LTuple xs')

  | LRecord (p, xs) ->
      let (s, xs') =
        List.Smart.map_fold
          (fun s ((x, t) as xt) ->
            match x with
            | None ->
                let t' = ty_subst s t in
                  if t == t' then (s, xt) else (s, (x, t'))
            | Some x ->
                let (s, (x', t')) = add_elocal s (x, t) in
                  if   x == x' && t == t'
                  then (s, xt)
                  else (s, (Some x', t')))
          s xs
      in
        (s, LRecord (p, xs'))

(* -------------------------------------------------------------------- *)
let x_subst s x =
    EcPath.x_subst_abs s.fs_mod x

let pv_subst s = pv_subst (x_subst s)

let rec e_subst (s: f_subst) e =
  match e.e_node with
  | Elocal id -> begin
      match Mid.find_opt id s.fs_eloc with
      | Some e' -> e'
      | None    ->
(* FIXME schema *)
(*        assert (not s.es_freshen); *)
        e_local id (ty_subst s e.e_ty)
  end

  | Evar pv ->
      let pv' = pv_subst s pv in
      let ty' = ty_subst s e.e_ty in
        e_var pv' ty'

  | Eop (p, tys) ->
      let tys' = List.Smart.map (ty_subst s) tys in
      let ty'  = ty_subst s e.e_ty in
        e_op p tys' ty'

  | Elet (lp, e1, e2) ->
      let e1' = e_subst s e1 in
      let s, lp' = elp_subst s lp in
      let e2' = e_subst s e2 in
        e_let lp' e1' e2'

  | Equant (q, b, e1) ->
      let s, b' = add_elocals s b in
      let e1' = e_subst s e1 in
        e_quantif q b' e1'

  | _ -> e_map (ty_subst s) (e_subst s) e

(* -------------------------------------------------------------------- *)
let e_subst s =
  if is_e_subst_id s then identity
  else
    if s.fs_freshen then e_subst s
    else He.memo 107 (e_subst s)

(* -------------------------------------------------------------------- *)
(* Statement                                                            *)
(* -------------------------------------------------------------------- *)
let rec s_subst_top (s : f_subst) =
  let e_subst = e_subst s in

  if e_subst == identity then identity else

  let pvt_subst (pv,ty as p) =
    let pv' = pv_subst s pv in
    let ty' = ty_subst s ty in

    if pv == pv' && ty == ty' then p else (pv', ty') in

  let lv_subst lv =
    match lv with
    | LvVar pvt ->
        LvVar (pvt_subst pvt)

    | LvTuple pvs ->
        let pvs' = List.Smart.map pvt_subst pvs in
        LvTuple pvs'

  in

  let rec i_subst i =
    match i.i_node with
    | Sasgn (lv, e) ->
        i_asgn (lv_subst lv, e_subst e)

    | Srnd (lv, e) ->
        i_rnd (lv_subst lv, e_subst e)

    | Scall (olv, mp, args) ->
        let olv'  = olv |> OSmart.omap lv_subst in
        let mp'   = EcPath.x_subst_abs s.fs_mod mp in
        let args' = List.Smart.map e_subst args in

        i_call (olv', mp', args')

    | Sif (e, s1, s2) ->
        i_if (e_subst e, s_subst s1, s_subst s2)

    | Swhile(e, b) ->
        i_while (e_subst e, s_subst b)

    | Smatch (e, b) ->
        let forb ((xs, subs) as b1) =
          let s, xs' = add_elocals s xs in
          let subs'  = s_subst_top s subs in
          if xs == xs' && subs == subs' then b1 else (xs', subs')
        in

        i_match (e_subst e, List.Smart.map forb b)

    | Sassert e ->
        i_assert (e_subst e)

    | Sabstract _ ->
        i

  and s_subst s =
    stmt (List.Smart.map i_subst s.s_node)

  in s_subst

let s_subst = s_subst_top

(* -------------------------------------------------------------------- *)
module Fsubst = struct

  let has_mem (s : f_subst) (x : ident) =
    Mid.mem x s.fs_mem

  let is_subst_id s =
       s.fs_freshen = false
    && is_ty_subst_id s
    && Mid.is_empty   s.fs_loc
    && Mid.is_empty   s.fs_mem
    && Mid.is_empty   s.fs_eloc
    && s.fs_schema = None

  (* ------------------------------------------------------------------ *)
  let add_local s (x,t as xt) =
    let x' = refresh s x in
    let t' = ty_subst s t in
    if x == x' && t == t' then (s, xt)
    else f_bind_rename s x x' t', (x',t')

  let add_locals = List.Smart.map_fold add_local

  let lp_subst (s: f_subst) (lp:lpattern) =
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
                  let t' = ty_subst s t in
                    if t == t' then (s, xt) else (s, (x, t'))
              | Some x ->
                  let (s, (x', t')) = add_local s (x, t) in
                    if   x == x' && t == t'
                    then (s, xt)
                    else (s, (Some x', t')))
            s xs
        in
          if xs == xs' then (s, lp) else (s, LRecord (p, xs'))

  (* ------------------------------------------------------------------ *)
  let m_subst s m = Mid.find_def m m s.fs_mem

  (* -------------------------------------------------------------------- *)
  let me_subst s me =
    EcMemory.me_subst s.fs_mem (ty_subst s) me

  (* ------------------------------------------------------------------ *)
  let rec f_subst ~tx s fp =
    tx fp (match fp.f_node with
    | Fquant (q, b, f) ->
        let s, b' = add_bindings ~tx s b in
        let f'    = f_subst ~tx s f in
          f_quant q b' f'

    | Flet (lp, f1, f2) ->
        let f1'    = f_subst ~tx s f1 in
        let s, lp' = lp_subst s lp in
        let f2'    = f_subst ~tx s f2 in
          f_let lp' f1' f2'

    | Flocal id -> begin
      match Mid.find_opt id s.fs_loc with
      | Some f -> f
      | None ->
          let ty' = ty_subst s fp.f_ty in
          f_local id ty'
    end

    | Fop (p, tys) ->
        let ty'  = ty_subst s fp.f_ty in
        let tys' = List.Smart.map (ty_subst s) tys in
        f_op p tys' ty'

    | Fpvar (pv, m) ->
        let pv' = pv_subst s pv in
        let m'  = m_subst s m in
        let ty' = ty_subst s fp.f_ty in
        f_pvar pv' ty' m'

    | Fglob (mid, m) ->
        let m'  = m_subst s m in
        begin match Mid.find_opt mid s.fs_mod with
        | None -> f_glob mid m'
        | Some _ -> (Mid.find mid s.fs_modex).mex_glob m'
        end

    | FhoareF hf ->
        let hf_f  = x_subst s hf.hf_f in
        let s     = f_rem_mem s mhr in
        let hf_pr = f_subst ~tx s hf.hf_pr in
        let hf_po = f_subst ~tx s hf.hf_po in
        f_hoareF hf_pr hf_f hf_po

    | FhoareS hs ->
        let hs_s    = s_subst s hs.hs_s in
        let s, hs_m = add_me_binding s hs.hs_m in
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
        let hs_s    = s_subst s hs.ehs_s in
        let s, hs_m = add_me_binding s hs.ehs_m in
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
        let hs_s    = s_subst s hs.chs_s in
        let s, hs_m = add_me_binding s hs.chs_m in
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
        let hs_s = s_subst s hs.bhs_s in
        let s, hs_m = add_me_binding s hs.bhs_m in
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
        let es_sl = s_subst s es.es_sl in
        let es_sr = s_subst s es.es_sr in
        let s, es_ml = add_me_binding s es.es_ml in
        let s, es_mr = add_me_binding s es.es_mr in
        let es_pr = f_subst ~tx s es.es_pr in
        let es_po = f_subst ~tx s es.es_po in
        f_equivS es_ml es_mr es_pr es_sl es_sr es_po

    | FeagerF eg ->
        let eg_fl = x_subst s eg.eg_fl in
        let eg_fr = x_subst s eg.eg_fr in
        let eg_sl = s_subst s eg.eg_sl in
        let eg_sr = s_subst s eg.eg_sr in
        let s = f_rem_mem s mleft in
        let s = f_rem_mem s mright in
        let eg_pr = f_subst ~tx s eg.eg_pr in
        let eg_po = f_subst ~tx s eg.eg_po in
        f_eagerF eg_pr eg_sl eg_fl eg_fr eg_sr eg_po

    | Fcoe coe ->
      if EcMemory.is_schema (snd coe.coe_mem) && s.fs_schema <> None then
        let m' = refresh s (fst coe.coe_mem) in
        (* We instanciate the schema *)
        let sc = oget s.fs_schema in
        let me' = m', sc.sc_memtype in
        (* We add the memory in the subst *)
        let s = f_rebind_mem s (fst coe.coe_mem) m' in
        (* We add the predicates in the subst *)
        let doit id (m, p) s =
          let fs_mem = f_bind_mem f_subst_id m m' in
          let p = f_subst ~tx:(fun _ f -> f) fs_mem p in
          f_bind_local s id p in
        (* FIXME:                                      why None ? *)
        let s   = Mid.fold doit sc.sc_mempred {s with fs_schema = None } in
        (* We add the expressions in the subst *)
        let s   = bind_elocals s sc.sc_expr in
        let s   = Mid.fold (fun id e s ->
                      f_bind_local s id (form_of_expr m' e)) sc.sc_expr s in
        let pr' = f_subst ~tx s coe.coe_pre in
        let e'  = e_subst s coe.coe_e in
        f_coe pr' me' e'
      else
        let s, me' = add_me_binding s coe.coe_mem in
        let pr' = f_subst ~tx s coe.coe_pre in
        let e'  = e_subst s coe.coe_e in
        f_coe pr' me' e'

    | Fpr pr ->
      let pr_mem   = m_subst s pr.pr_mem in
      let pr_fun   = x_subst s pr.pr_fun in
      let pr_args  = f_subst ~tx s pr.pr_args in
      let s = f_rem_mem s mhr in
      let pr_event = f_subst ~tx s pr.pr_event in

      f_pr pr_mem pr_fun pr_args pr_event

    | _ ->
      f_map (ty_subst s) (f_subst ~tx s) fp)

  and oi_subst ~(tx : form -> form -> form) (s : f_subst) (oi : PreOI.t) =
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

  and mr_subst ~tx s mr : mod_restr =
    let sx = x_subst s in
    let sm = EcPath.m_subst_abs s.fs_mod in
    { mr_xpaths = ur_app (fun s -> Sx.fold (fun m rx ->
          Sx.add (sx m) rx) s Sx.empty) mr.mr_xpaths;
      mr_mpaths = ur_app (fun s -> Sm.fold (fun m r ->
          Sm.add (sm m) r) s Sm.empty) mr.mr_mpaths;
      mr_oinfos = EcSymbols.Msym.map (oi_subst ~tx s) mr.mr_oinfos;
    }

  and mp_subst s = EcPath.m_subst_abs s.fs_mod

  and mty_subst ~tx s mty =
    let mt_params = List.map (snd_map (mty_subst ~tx s)) mty.mt_params in
    let mt_name   = mty.mt_name in
    let mt_args   = List.map (mp_subst s) mty.mt_args in
    let mt_restr  = mr_subst ~tx s mty.mt_restr in
    { mt_params; mt_name; mt_args; mt_restr; }

  and gty_subst ~tx s gty =
    if is_subst_id s then gty else

    match gty with
    | GTty ty ->
        let ty' = ty_subst s ty in
        if ty == ty' then gty else GTty ty'

    | GTmodty p ->
        let p' = mty_subst ~tx s p in

        if   p == p'
        then gty
        else GTmodty p'

    | GTmem mt ->
        let mt' = EcMemory.mt_subst (ty_subst s) mt in
        if mt == mt' then gty else GTmem mt'

  and add_binding ~tx s (x, gty as xt) =
    let gty' = gty_subst ~tx s gty in
    let x'   = refresh s x in

    if x == x' && gty == gty' then
      let s = match gty with
        | GTty    _ -> f_rem_local s x
        | GTmodty _ -> f_rem_mod   s x
        | GTmem   _ -> f_rem_mem   s x
      in
        (s, xt)
    else
      let s = match gty' with
        | GTty   ty -> f_bind_rename s x x' ty
        | GTmodty _ -> f_bind_absmod s x x'
        | GTmem   _ -> f_bind_mem s x x'
      in
        (s, (x', gty'))

  and add_bindings ~tx = List.map_fold (add_binding ~tx)

  and add_me_binding s (x, mt as me) =
    let mt' = EcMemory.mt_subst (ty_subst s) mt in
    (* FIXME : it would be better to use refresh instead *)
    let x'  = refresh s x in
    if x == x' && mt == mt' then
      let s = f_rem_mem s x in
      (s, me)
    else
      let s = f_bind_mem s x x' in
      (s, (x', mt'))

  (* When substituting a abstract module (i.e. a mident) by a concrete one,
     we move the module cost from [c_calls] to [c_self]. *)
  and cost_subst ~tx s cost =
    let c_self = f_subst ~tx s cost.c_self
    and self', c_calls = EcPath.Mx.fold (fun x cb (self',calls) ->
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
      ) cost.c_calls (f_x0, EcPath.Mx.empty) in

    let c_self = f_xadd_simpl c_self self' in
    cost_r c_self c_calls

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

  let gty_subst = gty_subst ~tx:(fun _ f -> f)
  let mty_subst = mty_subst ~tx:(fun _ f -> f)
  let oi_subst  = oi_subst ~tx:(fun _ f -> f)

  let f_subst_local x t =
    let s = f_bind_local f_subst_id x t in
    fun f -> if Mid.mem x f.f_fv then f_subst s f else f

  let f_subst_mem m1 m2 =
    let s = f_bind_mem f_subst_id m1 m2 in
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
