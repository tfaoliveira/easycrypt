open EcUtils
open EcIdent
open EcPath
open EcUid
open EcAst
open EcTypes
open EcCoreFol
open EcCoreModules

(* -------------------------------------------------------------------- *)
(* A predicate on memory: λ mem. -> pred                                *)

type mod_extra =
  { mex_tglob : ty;
    mex_glob  : memory -> form;
    mex_fv    : int Mid.t
  }

type sc_instanciate =
  { sc_memtype : memtype;
    sc_mempred : mem_pr Mid.t;
    sc_expr    : expr Mid.t;
  }

type f_subst = {
  s_freshen : bool; (* true means realloc local *)

  s_u       : ty Muid.t;
  s_v       : ty Mid.t;

  s_loc     : form Mid.t;
  s_eloc    : expr Mid.t;
  s_mem     : EcIdent.t Mid.t;
  s_mod     : EcPath.mpath Mid.t;
  s_modex   : mod_extra Mid.t;

  s_schema : sc_instanciate option;

  s_fv      : int Mid.t;
     (* An over approximation of variables occuring in the codomain of the substitution *)
}

type 'a substitute = f_subst -> 'a -> 'a
(* form before subst -> form after -> resulting form *)
type tx = form -> form -> form
type 'a tx_substitute = ?tx:tx -> 'a substitute
type 'a subst_bind = f_subst -> 'a -> f_subst * 'a

module Fsubst = struct

let mid_fv (mkfv:'a -> int Mid.t) fv m =
   Mid.fold (fun _ a fv -> fv_union fv (mkfv a)) m fv

let subst_init ?(freshen = false)
               ?(suid    = Muid.empty)
               ?(sty     = Mid.empty)
               ?(esloc   = Mid.empty)
               ?schema
               () =
  let fv = mid_fv ty_fv Mid.empty sty in
  let fv = mid_fv e_fv fv esloc in
  let fv = Muid.fold (fun _ ty fv -> fv_union fv ty.ty_fv) suid fv in
  let fv =
    ofold (fun sc fv ->
       let doit mkfv (m, f) = Mid.remove m (mkfv f) in
       let fv = mid_fv (doit f_fv) fv sc.sc_mempred in
       let fv = mid_fv e_fv fv sc.sc_expr in
       fv_union (mt_fv sc.sc_memtype) fv)
      fv schema  in
  {
  s_freshen = freshen;
  s_u       = suid;
  s_v       = sty;
  s_loc     = Mid.empty;
  s_eloc    = esloc;
  s_mem     = Mid.empty;
  s_mod     = Mid.empty;
  s_modex   = Mid.empty;
  s_schema  = schema;
  s_fv      = fv;
}

let subst_id = subst_init ()

let is_subst_id s =
  not s.s_freshen &&
  Muid.is_empty s.s_u &&
  Mid.is_empty s.s_v &&
  Mid.is_empty s.s_loc &&
  Mid.is_empty s.s_eloc &&
  Mid.is_empty s.s_mem &&
  Mid.is_empty s.s_mod &&
  Mid.is_empty s.s_modex &&
  s.s_schema = None

let bind_local s x f =
  { s with s_loc = Mid.add x f s.s_loc;
           s_fv = fv_union f.f_fv s.s_fv }

let bind_rename s x x' ty =
  bind_local s x (f_local x' ty)

let bind_locals s xs fs =
  List.fold_left2 (fun s (x, _) f -> bind_local s x f) s xs fs

let bind_olocals s xs fs =
  List.fold_left2 (fun s (ox, _) f ->
      ofold (fun x s -> bind_local s x f) s ox) s xs fs

let bind_elocal s x e =
  { s with s_eloc = Mid.add x e s.s_eloc;
           s_fv = fv_union e.e_fv s.s_fv }

let bind_elocals s esloc =
  let fv = ref s.s_fv in
  let merger _ oe1 oe2 =
    if oe2 = None then oe1
    else (fv := fv_union (oget oe2).e_fv !fv; oe2) in
  let s_eloc =  Mid.merge merger s.s_eloc esloc in
  { s with s_eloc; s_fv = !fv }


let bind_mod s x mp ex =
  { s with
    s_mod   = Mid.add x mp s.s_mod;
    s_modex = Mid.add x ex s.s_modex;
    s_fv    = fv_union s.s_fv (m_fv ex.mex_fv mp); }

let bind_mem s m m' =
  { s with
    s_mem = Mid.add m m' s.s_mem;
    s_fv  = fv_add m' s.s_fv; }

let bind_absmod s x x' =
  let extra = { mex_tglob = tglob x'; mex_glob = (fun m -> f_glob x' m);
                mex_fv = fv_singleton x' } in
  bind_mod s x (mident x') extra

let remove_local ~where s x =
  match where with
  | `Form -> { s with s_loc  = Mid.remove x s.s_loc  }
  | `Expr -> { s with s_eloc = Mid.remove x s.s_eloc }
  | `Mem  -> { s with s_mem  = Mid.remove x s.s_mem  }
  | `Mod  -> { s with s_mod  = Mid.remove x s.s_mod;
                      s_modex = Mid.remove x s.s_modex }

let refresh s x =
  if s.s_freshen || Mid.mem x s.s_fv then
    EcIdent.fresh x
  else x

let remove_predef_mem s m =
  assert (not (Mid.mem m s.s_fv));
  remove_local ~where:`Mem s m

(* -------------------------------------------------------------------- *)
let x_subst (s : f_subst) x =
  EcPath.x_subst_abs s.s_mod x

let m_subst (s : f_subst) x =
  EcPath.m_subst_abs s.s_mod x

let pv_subst (s : f_subst) pv =
  EcTypes.pv_subst (x_subst s) pv

let mem_subst (s : f_subst) m =
  Mid.find_def m m s.s_mem

(* -------------------------------------------------------------------- *)
let rec ty_subst (s : f_subst) ty =
  match ty.ty_node with
  | Tglob m ->
    begin match Mid.find_opt m s.s_modex with
    | None -> ty
    | Some mex -> mex.mex_tglob
    end
  | Tunivar id -> Muid.find_def ty id s.s_u
  | Tvar id    -> Mid.find_def ty id s.s_v
  | _ -> ty_map (ty_subst s) ty

and gty_subst ~tx s gty =
  match gty with
  | GTty ty ->
    let ty' = ty_subst s ty in
    GTty ty'

  | GTmodty p ->
    let p' = mty_subst ~tx s p in
    GTmodty p'

  | GTmem mt ->
    let mt' = mt_subst s mt in
    GTmem mt'

and mr_subst ~tx s mr : mod_restr =
  let sx = x_subst s in
  let sm = m_subst s in
  { mr_xpaths = ur_app (fun s -> Sx.fold (fun m rx ->
      Sx.add (sx m) rx) s Sx.empty) mr.mr_xpaths;
    mr_mpaths = ur_app (fun s -> Sm.fold (fun m r ->
      Sm.add (sm m) r) s Sm.empty) mr.mr_mpaths;
    mr_oinfos = EcSymbols.Msym.map (oi_subst ~tx s) mr.mr_oinfos;
}

and mty_subst ~tx s mty =
  let sm = EcPath.m_subst_abs s.s_mod in

  let mt_params = List.map (snd_map (mty_subst ~tx s)) mty.mt_params in
  let mt_name   = mty.mt_name in
  let mt_args   = List.map sm mty.mt_args in
  let mt_restr  = mr_subst ~tx s mty.mt_restr in
  { mt_params; mt_name; mt_args; mt_restr; }

and mt_subst (s : f_subst) mt =
  EcMemory.mt_subst (ty_subst s) mt

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

(* -------------------------------------------------------------------- *)
and add_local ~where s ((x, t) as xt) =
  let x' = refresh s x in
  let t' = ty_subst s t in
  if x == x' && t == t' then
    remove_local ~where s x, xt
  else
    let s =
      match where with
      | `Form -> bind_local s x (f_local x' t')
      | `Expr -> bind_elocal s x' (e_local x' t')
    in
    s, (x', t')

and add_locals ~where s xs = List.map_fold (add_local ~where) s xs

and add_binding ~tx s (x, gty as xt) =
  let gty' = gty_subst ~tx s gty in
  let x'   = refresh s x in
  if x == x' && gty == gty' then
      let where = match gty with
        | GTty    _ -> `Form
        | GTmodty _ -> `Mod
        | GTmem   _ -> `Mem
      in
      remove_local ~where s x, xt

    else
      let s = match gty' with
        | GTty   t' -> bind_local  s x (f_local x' t')
        | GTmodty _ -> bind_absmod s x x'
        | GTmem   _ -> bind_mem    s x x'
      in
        (s, (x', gty'))

and add_bindings ~tx = List.map_fold (add_binding ~tx)

and add_memenv ~tx s (m, mt) =
  let (s, (m', gty)) = add_binding ~tx s (m, GTmem mt) in
  (s, (m', as_mem gty))

(* -------------------------------------------------------------------- *)
and add_lpattern ~where (s : f_subst) (lp : lpattern) =
  match lp with
  | LSymbol x ->
    let s, x' = add_local ~where s x in
    s, LSymbol x'

  | LTuple xs ->
    let (s, xs') = add_locals ~where s xs in
    s, LTuple xs'

  | LRecord (p, xs) ->
    let s, xs' =
      List.map_fold
        (fun s (x, t) ->
          match x with
          | None ->
            let t' = ty_subst s t in
            s, (x, t')
          | Some x ->
            let s, (x', t') = add_local ~where s (x, t) in
            s, (Some x', t')) s xs
    in
    s, LRecord (p, xs')

(* -------------------------------------------------------------------- *)
and e_subst (s: f_subst) e =
  match e.e_node with
  | Elocal id ->
    begin match Mid.find_opt id s.s_eloc with
    | Some e' -> e'
    | None    -> e_local id (ty_subst s e.e_ty)
    end

  | Evar pv ->
    let pv' = pv_subst s pv in
    let ty' = ty_subst s e.e_ty in
    e_var pv' ty'

  | Eop (p, tys) ->
    let tys' = List.map (ty_subst s) tys in
    let ty'  = ty_subst s e.e_ty in
    e_op p tys' ty'

  | Elet (lp, e1, e2) ->
    let e1' = e_subst s e1 in
    let s, lp' = add_lpattern ~where:`Expr s lp in
    let e2' = e_subst s e2 in
    e_let lp' e1' e2'

  | Equant (q, b, e1) ->
    let s, b' = add_locals ~where:`Expr s b in
    let e1' = e_subst s e1 in
    e_quantif q b' e1'

  | _ -> e_map (ty_subst s) (e_subst s) e

(* -------------------------------------------------------------------- *)

and pvt_subst s (pv,ty as p) =
  let pv' = pv_subst s pv in
  let ty' = ty_subst s ty in
  if pv == pv' && ty == ty' then p else (pv', ty')

and lv_subst s lv =
  match lv with
  | LvVar pvt ->
    LvVar (pvt_subst s pvt)

  | LvTuple pvs ->
    let pvs' = List.map (pvt_subst s) pvs in
    LvTuple pvs'

(* -------------------------------------------------------------------- *)
and i_subst s i =
  match i.i_node with
  | Sasgn (lv, e) ->
    i_asgn (lv_subst s lv, e_subst s e)

  | Srnd (lv, e) ->
    i_rnd (lv_subst s lv, e_subst s e)

  | Scall (olv, mp, args) ->
    let olv'  = olv |> omap (lv_subst s) in
    let mp'   = x_subst s mp in
    let args' = List.map (e_subst s) args in
    i_call (olv', mp', args')

  | Sif (e, s1, s2) ->
    i_if (e_subst s e, s_subst s s1, s_subst s s2)

  | Swhile(e, b) ->
    i_while (e_subst s e, s_subst s b)

  | Smatch (e, b) ->
    let forb (xs, subs) =
      let s, xs' = add_locals ~where:`Expr s xs in
      let subs'  = s_subst s subs in
      (xs', subs')
    in
    i_match (e_subst s e, List.map forb b)

  | Sassert e ->
    i_assert (e_subst s e)

  | Sabstract _ ->
    i

and s_subst s st =
  stmt (List.map (i_subst s) st.s_node )

and f_subst ~tx (s : f_subst) (fp : form) =
  tx fp (match fp.f_node with
    | Fquant (q, b, f) ->
      let s, b' = add_bindings ~tx s b in
      let f'    = f_subst ~tx s f in
      f_quant q b' f'

    | Flet (lp, f1, f2) ->
      let f1'    = f_subst ~tx s f1 in
      let s, lp' = add_lpattern ~where:`Form s lp in
      let f2'    = f_subst ~tx s f2 in
      f_let lp' f1' f2'

    | Flocal id ->
      begin match Mid.find_opt id s.s_loc with
      | Some f -> f
      | None ->
          let ty' = ty_subst s fp.f_ty in
          f_local id ty'
      end

    | Fop (p, tys) ->
      let ty'  = ty_subst s fp.f_ty in
      let tys' = List.map (ty_subst s) tys in
      f_op p tys' ty'

    | Fpvar (pv, m) ->
      let pv' = pv_subst s pv in
      let m'  = mem_subst s m in
      let ty' = ty_subst s fp.f_ty in
      f_pvar pv' ty' m'

    | Fglob (mid, m) ->
        let m' = mem_subst s m in
        begin match Mid.find_opt mid s.s_mod with
        | None -> f_glob mid m'
        | Some _ -> (Mid.find mid s.s_modex).mex_glob m'
        end

    | FhoareF hf ->
      let mp' = x_subst s hf.hf_f in
      let pr', po' =
        let s   = remove_predef_mem s mhr in
        let pr' = f_subst ~tx s hf.hf_pr in
        let po' = f_subst ~tx s hf.hf_po in
        (pr', po')
      in
      f_hoareF pr' mp' po'

    | FhoareS hs ->
      let st' = s_subst s hs.hs_s in
      let me', pr', po' =
        let s, me' = add_memenv ~tx s hs.hs_m in
        let pr' = f_subst ~tx s hs.hs_pr in
        let po' = f_subst ~tx s hs.hs_po in
        me', pr', po' in
      f_hoareS me' pr' st' po'

    | FeHoareF hf ->
      let mp' = x_subst s hf.ehf_f in
      let pr', po' =
        let s   = remove_predef_mem s mhr in
        let pr' = f_subst ~tx s hf.ehf_pr in
        let po' = f_subst ~tx s hf.ehf_po in
        (pr', po') in
      f_eHoareF pr' mp' po'

    | FeHoareS hs ->
      let st' = s_subst s hs.ehs_s in
      let me', pr', po' =
        let s, me' = add_memenv ~tx s hs.ehs_m in
        let pr' = f_subst ~tx s hs.ehs_pr in
        let po' = f_subst ~tx s hs.ehs_po in
        me', pr', po' in
      f_eHoareS me' pr' st' po'

    | FcHoareF chf ->
      let mp' = x_subst s chf.chf_f in
      let pr', po', c' =
        let s   = remove_predef_mem s mhr in
        let pr' = f_subst ~tx s chf.chf_pr in
        let po' = f_subst ~tx s chf.chf_po in
        let c'  = cost_subst ~tx s chf.chf_co in
        (pr', po', c')
      in
      f_cHoareF pr' mp' po' c'

    | FcHoareS chs ->
      let st' = s_subst s chs.chs_s in
      let me', pr', po', c' =
        let s, me' = add_memenv ~tx s chs.chs_m in
        let pr' = f_subst ~tx s chs.chs_pr in
        let po' = f_subst ~tx s chs.chs_po in
        let c'  = cost_subst ~tx s chs.chs_co in
        (me', pr', po', c')
      in
      f_cHoareS me' pr' st' po' c'

    | FbdHoareF bhf ->
      let mp' = x_subst s bhf.bhf_f in
      let pr', po', bd' =
        let s   = remove_predef_mem s mhr in
        let pr' = f_subst ~tx s bhf.bhf_pr in
        let po' = f_subst ~tx s bhf.bhf_po in
        let bd' = f_subst ~tx s bhf.bhf_bd in
        (pr', po', bd') in
      f_bdHoareF_r { bhf with bhf_pr = pr'; bhf_po = po';
                              bhf_f  = mp'; bhf_bd = bd'; }

    | FbdHoareS bhs ->
      let st' = s_subst s bhs.bhs_s in
      let me', pr', po', bd' =
        let s, me' = add_memenv ~tx s bhs.bhs_m in
        let pr' = f_subst ~tx s bhs.bhs_pr in
        let po' = f_subst ~tx s bhs.bhs_po in
        let bd' = f_subst ~tx s bhs.bhs_bd in
        (me', pr', po', bd') in
      f_bdHoareS_r { bhs with bhs_pr = pr'; bhs_po = po'; bhs_s = st';
                              bhs_bd = bd'; bhs_m  = me'; }

    | FequivF ef ->
      let fl' = x_subst s ef.ef_fl in
      let fr' = x_subst s ef.ef_fr in
      let pr', po' =
        let s   = List.fold_left remove_predef_mem s [mleft; mright] in
        let pr' = f_subst ~tx s ef.ef_pr in
        let po' = f_subst ~tx s ef.ef_po in
        (pr', po') in
      f_equivF pr' fl' fr' po'

    | FequivS eqs ->
      let sl' = s_subst s eqs.es_sl in
      let sr' = s_subst s eqs.es_sr in
      let ml', mr', pr', po' =
        let s, ml' = add_memenv ~tx s eqs.es_ml in
        let s, mr' = add_memenv ~tx s eqs.es_mr in
        let pr' = f_subst ~tx s eqs.es_pr in
        let po' = f_subst ~tx s eqs.es_po in
        (ml', mr', pr', po') in
      f_equivS ml' mr' pr' sl' sr' po'

    | FeagerF eg ->
      let fl' = x_subst s eg.eg_fl in
      let fr' = x_subst s eg.eg_fr in
      let sl' = s_subst s eg.eg_sl in
      let sr' = s_subst s eg.eg_sr in
      let pr', po' =
        let s   = List.fold_left remove_predef_mem s [mleft; mright] in
        let pr' = f_subst ~tx s eg.eg_pr in
        let po' = f_subst ~tx s eg.eg_po in
        (pr', po') in
      f_eagerF pr' sl' fl' fr' sr' po'

    | Fcoe coe ->
      if EcMemory.is_schema (snd coe.coe_mem) && s.s_schema <> None then
        (* We instanciate the schema *)
        let sc = oget s.s_schema in
        let m' = refresh s (fst coe.coe_mem) in
        let me' = m', sc.sc_memtype in
        (* We add the memory in the subst *)
        let s = bind_mem s (fst coe.coe_mem) m' in
        (* We add the predicates in the subst *)
        let doit id (m, p) s =
          let fs_mem = bind_mem subst_id m m' in
          let p = f_subst ~tx:(fun _ f -> f) fs_mem p in
          bind_local s id p in
        (* FIXME:                                      why None ? *)
        let s = Mid.fold doit sc.sc_mempred {s with s_schema = None } in
        (* We add the expressions in the subst *)
        let s   = bind_elocals s sc.sc_expr in
        let pr' = f_subst ~tx s coe.coe_pre in
        let e'  = e_subst s coe.coe_e in
        f_coe pr' me' e'
      else
        let s, me' = add_memenv ~tx s coe.coe_mem in
        let pr'    = f_subst ~tx s coe.coe_pre in
        let e'     = e_subst s coe.coe_e in
        f_coe pr' me' e'

    | Fpr pr ->
      let pr_mem   = mem_subst s pr.pr_mem in
      let pr_fun   = x_subst s pr.pr_fun in
      let pr_args  = f_subst ~tx s pr.pr_args in
      let s = remove_predef_mem s mhr in
      let pr_event = f_subst ~tx s pr.pr_event in

      f_pr pr_mem pr_fun pr_args pr_event

    | _ ->
      f_map (ty_subst s) (f_subst ~tx s) fp)

  (* When substituting a abstract module (i.e. a mident) by a concrete one,
     we move the module cost from [c_calls] to [c_self]. *)
and cost_subst ~tx (s : f_subst) cost =
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


(* -------------------------------------------------------------------- *)
(* Wrappers                                                             *)
(* -------------------------------------------------------------------- *)

let wrap_id f s a =
  if is_subst_id s then a
  else f s a

let f_subst ?(tx = fun _ f -> f) =
  wrap_id (f_subst ~tx)


let m_subst   = wrap_id m_subst
let x_subst   = wrap_id x_subst
let pv_subst  = wrap_id pv_subst
let ty_subst  = wrap_id ty_subst
let e_subst   = wrap_id e_subst
let i_subst   = wrap_id i_subst
let s_subst   = wrap_id s_subst
let mem_subst = wrap_id mem_subst

let gty_subst = wrap_id (gty_subst ~tx:(fun _ f -> f))
let mr_subst  = wrap_id (mr_subst  ~tx:(fun _ f -> f))
let mty_subst = wrap_id (mty_subst ~tx:(fun _ f -> f))
let oi_subst  = wrap_id (oi_subst  ~tx:(fun _ f -> f))


let add_binding  = add_binding  ~tx:(fun _ f -> f)
let add_bindings = add_bindings ~tx:(fun _ f -> f)
let add_memenv   = add_memenv   ~tx:(fun _ f -> f)

let add_elocals = add_locals ~where:`Expr

let f_subst_local x t =
  let s = bind_local subst_id x t in
  fun f -> if Mid.mem x f.f_fv then f_subst s f else f

let f_subst_mem m1 m2 =
  let s = bind_mem subst_id m1 m2 in
  fun f -> if Mid.mem m1 f.f_fv then f_subst s f else f

end

module Tuni = struct

  let subst (uidmap : ty Muid.t) =
    Fsubst.subst_init ~suid:uidmap ()

  let subst1 ((id, t) : uid * ty) =
    subst (Muid.singleton id t)

  let subst_dom uidmap dom =
    List.map (Fsubst.ty_subst (subst uidmap)) dom

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

  let ty_subst (sty : ty Mid.t) =
    Fsubst.ty_subst (Fsubst.subst_init ~sty ())


  let subst1 (id,t) =
    ty_subst (Mid.singleton id t)

  let init lv lt =
    assert (List.length lv = List.length lt);
    List.fold_left2 (fun s v t -> Mid.add v t s) Mid.empty lv lt

  let f_subst (sty : ty Mid.t) =
    Fsubst.f_subst (Fsubst.subst_init ~sty ())

end

(* -------------------------------------------------------------------- *)
let e_subst_closure s (params, e) =
  let (s, args) = Fsubst.add_locals ~where:`Expr s params in
  (params, Fsubst.e_subst s e)
