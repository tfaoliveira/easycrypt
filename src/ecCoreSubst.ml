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
type f_subst = {
  fs_freshen  : bool; (* true means freshen locals *)

  fs_u         : ty Muid.t;
  fs_v         : ty Mid.t;

  fs_absmod    : EcIdent.t Mid.t;
  fs_cmod      : EcPath.mpath Mid.t;
  fs_modtglob  : ty Mid.t;
  fs_modglob  : (EcIdent.t -> form) Mid.t; (* Mappings between abstract modules and their globals *)

  fs_loc      : form Mid.t;
  fs_eloc    : expr Mid.t;
  fs_mem      : EcIdent.t Mid.t;

  fs_memtype  : memtype option; (* Only substituted in Fcoe *)
  fs_mempred  : mem_pr Mid.t;  (* For predicates over memories,
                                 only substituted in Fcoe *)
}

let f_subst_id = {
  fs_freshen  = false;

  fs_u        = Muid.empty;
  fs_v        = Mid.empty;

  fs_absmod    = Mid.empty;
  fs_cmod      = Mid.empty;
  fs_modtglob  = Mid.empty;
  fs_modglob  = Mid.empty;

  fs_loc      = Mid.empty;
  fs_eloc    = Mid.empty;
  fs_mem      = Mid.empty;

  fs_memtype  = None;
  fs_mempred  = Mid.empty;
}

let f_subst_init
      ?(freshen=false)
      ?(tu=Muid.empty)
      ?(tv=Mid.empty)
      ?(esloc=Mid.empty)
      ?mt
      ?(mempred=Mid.empty) () = {
  fs_freshen  = freshen;

  fs_u        = tu;
  fs_v        = tv;

  fs_absmod    = Mid.empty;
  fs_cmod      = Mid.empty;
  fs_modtglob  = Mid.empty;
  fs_modglob  = Mid.empty;

  fs_loc      = Mid.empty;
  fs_eloc     = esloc;
  fs_mem      = Mid.empty;

  fs_memtype  = mt;
  fs_mempred  = mempred;
}

(* -------------------------------------------------------------------- *)

let ty_subst_id = f_subst_id

let is_ty_subst_id s =
  Mid.is_empty s.fs_absmod
  && Mid.is_empty s.fs_cmod
  && Mid.is_empty s.fs_modtglob
  && Muid.is_empty s.fs_u
  && Mid.is_empty s.fs_v

let rec ty_subst (s : f_subst) ty =
  match ty.ty_node with
  | Tglob m -> begin
      let m' = Mid.find_def m m s.fs_absmod in
        begin
          match Mid.find_opt m' s.fs_modtglob with
          | None -> tglob m'
          | Some ty -> ty_subst s ty
        end
    end
  | Tunivar id    -> Muid.find_def ty id s.fs_u
  | Tvar id       -> Mid.find_def ty id s.fs_v
  | _ -> ty_map (ty_subst s) ty


let ty_subst (s : f_subst) =
  if is_ty_subst_id s then identity
  else ty_subst s

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

end


(* -------------------------------------------------------------------- *)
(* Expressions                                                          *)
(* -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
let is_e_subst_id s =
     not s.fs_freshen
  && is_ty_subst_id s
  && Mid.is_empty s.fs_eloc

(* -------------------------------------------------------------------- *)

let bind_elocal s x e =
  { s with fs_eloc = Mid.add x e s.fs_eloc }

let add_elocal s ((x, t) as xt) =
  let x' = if s.fs_freshen then EcIdent.fresh x else x in
  let t' = ty_subst s t in

  if   x == x' && t == t'
  then (s, xt)
  else
    let merger o = assert (o = None); Some (e_local x' t') in
      ({ s with fs_eloc = Mid.change merger x s.fs_eloc }, (x', t'))

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
      let pv' = pv_subst (x_subst_abs s.fs_cmod) pv in
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
let e_subst_closure s (args, e) =
  let (s, args) = add_elocals s args in
    (args, e_subst s e)

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
    let pv' = EcTypes.pv_subst (EcPath.x_subst_abs s.fs_cmod) pv in
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
        let mp'   = EcPath.x_subst_abs s.fs_cmod mp in
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

  let f_subst_init = f_subst_init

  let f_subst_id = f_subst_id

  let is_subst_id s =
       s.fs_freshen = false
    && is_ty_subst_id s
    && Mid.is_empty   s.fs_loc
    && Mid.is_empty   s.fs_mem
    && Mid.is_empty   s.fs_modglob
    && Mid.is_empty   s.fs_eloc
    && s.fs_memtype = None

  (* ------------------------------------------------------------------ *)
  let f_bind_local s x t =
    let merger o = assert (o = None); Some t in
      { s with fs_loc = Mid.change merger x s.fs_loc }

  let f_bind_mem s m1 m2 =
    let merger o = assert (o = None); Some m2 in
      { s with fs_mem = Mid.change merger m1 s.fs_mem }

  let has_mem (s : f_subst) (x : ident) =
    Mid.mem x s.fs_mem

  let f_rebind_mem s m1 m2 =
    let merger _ = Some m2 in
    { s with fs_mem = Mid.change merger m1 s.fs_mem }

  let f_bind_absmod s m1 m2 =
    let merger o = assert (o = None); Some m2 in
    { s with
      fs_absmod = Mid.change merger m1 s.fs_absmod;
      fs_cmod = Mid.add m1 (EcPath.mident m2) s.fs_cmod }

  let f_bind_cmod s m mp =
    let merger o = assert (o = None); Some mp in
    { s with
      fs_cmod = Mid.change merger m s.fs_cmod }

  let f_bind_mod s x mp norm_mod =
    match EcPath.mget_ident_opt mp with
    | Some id ->
         f_bind_absmod s x id
    | None ->
       let nm_ty = (norm_mod mhr).f_ty in
       let s = f_bind_cmod s x mp in
       { s with
         fs_modtglob = Mid.add x nm_ty s.fs_modtglob;
         fs_modglob = Mid.add x norm_mod s.fs_modglob }

  let f_bind_rename s xfrom xto ty =
    let xf = f_local xto ty in
    let xe = e_local xto ty in
    let s  = f_bind_local s xfrom xf in

    let merger o = assert (o = None); Some xe in
    { s with fs_eloc = Mid.change merger xfrom s.fs_eloc }

  (* ------------------------------------------------------------------ *)
  let f_rem_local s x =
    { s with fs_loc = Mid.remove x s.fs_loc;
             fs_eloc = Mid.remove x s.fs_eloc; }

  let f_rem_mem s m =
    { s with fs_mem = Mid.remove m s.fs_mem }

  let f_rem_mod s x =
    { s with
      fs_absmod = Mid.remove x s.fs_absmod;
      fs_modtglob = Mid.remove x s.fs_modtglob;
      fs_cmod = Mid.remove x s.fs_cmod;
      fs_modglob = Mid.remove x s.fs_modglob; }

  (* ------------------------------------------------------------------ *)
  let add_local s (x,t as xt) =
    let x' = if s.fs_freshen then EcIdent.fresh x else x in
    let t' = ty_subst s t in
      if   x == x' && t == t'
      then (s, xt)
      else (f_bind_rename s x x' t'), (x',t')

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
  let subst_xpath s f =
    EcPath.x_subst_abs s.fs_cmod f

  let s_subst = s_subst

  let e_subst = e_subst

  let subst_me s me =
    EcMemory.me_subst s.fs_mem (ty_subst s) me

  let m_subst s m = Mid.find_def m m s.fs_mem

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
        let pv' = pv_subst (subst_xpath s) pv in
        let m'  = m_subst s m in
        let ty' = ty_subst s fp.f_ty in
        f_pvar pv' ty' m'

    | Fglob (mid, m) ->
        let m'  = m_subst s m in
        let mid = Mid.find_def mid mid s.fs_absmod in
        begin
          (* Have we computed the globals for this module *)
          match Mid.find_opt mid s.fs_modglob with
          | None -> f_glob mid m'
          | Some f -> f m'
        end

    | FhoareF hf ->
      let pr', po' =
        let s   = f_rem_mem s mhr in
        let pr' = f_subst ~tx s hf.hf_pr in
        let po' = f_subst ~tx s hf.hf_po in
        (pr', po') in
      let mp' = subst_xpath s hf.hf_f in

      f_hoareF pr' mp' po'

    | FhoareS hs ->
        assert (not (Mid.mem (fst hs.hs_m) s.fs_mem));
        let pr' = f_subst ~tx s hs.hs_pr in
        let po' = f_subst ~tx s hs.hs_po in
        let st' = s_subst s hs.hs_s in
        let me' = EcMemory.me_subst s.fs_mem (ty_subst s) hs.hs_m in

        f_hoareS me' pr' st' po'


    | FeHoareF hf ->
        assert (not (Mid.mem mhr s.fs_mem) && not (Mid.mem mhr s.fs_mem));
        let ehf_pr  = f_subst ~tx s hf.ehf_pr in
        let ehf_po  = f_subst ~tx s hf.ehf_po in
        let ehf_f  = subst_xpath s hf.ehf_f in
        f_eHoareF ehf_pr ehf_f ehf_po

    | FeHoareS hs ->
        assert (not (Mid.mem (fst hs.ehs_m) s.fs_mem));
        let ehs_pr  = f_subst ~tx s hs.ehs_pr in
        let ehs_po  = f_subst ~tx s hs.ehs_po in
        let ehs_s  = s_subst s hs.ehs_s in
        let ehs_m = EcMemory.me_subst s.fs_mem (ty_subst s) hs.ehs_m in
        f_eHoareS ehs_m ehs_pr ehs_s ehs_po

    | FcHoareF chf ->
      assert (not (Mid.mem mhr s.fs_mem));
      let pr' = f_subst ~tx s chf.chf_pr in
      let po' = f_subst ~tx s chf.chf_po in
      let mp' = subst_xpath s chf.chf_f in
      let c'  = cost_subst ~tx s chf.chf_co in

      f_cHoareF pr' mp' po' c'

    | FcHoareS chs ->
      assert (not (Mid.mem (fst chs.chs_m) s.fs_mem));
      let pr' = f_subst ~tx s chs.chs_pr in
      let po' = f_subst ~tx s chs.chs_po in
      let st' = s_subst s chs.chs_s in
      let me' = EcMemory.me_subst s.fs_mem (ty_subst s) chs.chs_m in
      let c'  = cost_subst ~tx s chs.chs_co in

      f_cHoareS me' pr' st' po' c'

    | FbdHoareF bhf ->
      let pr', po', bd' =
        let s = f_rem_mem s mhr in
        let pr' = f_subst ~tx s bhf.bhf_pr in
        let po' = f_subst ~tx s bhf.bhf_po in
        let bd' = f_subst ~tx s bhf.bhf_bd in
        (pr', po', bd') in
      let mp' = subst_xpath s bhf.bhf_f in

      f_bdHoareF_r { bhf with bhf_pr = pr'; bhf_po = po';
                              bhf_f  = mp'; bhf_bd = bd'; }

    | FbdHoareS bhs ->
      assert (not (Mid.mem (fst bhs.bhs_m) s.fs_mem));
      let pr' = f_subst ~tx s bhs.bhs_pr in
      let po' = f_subst ~tx s bhs.bhs_po in
      let st' = s_subst s bhs.bhs_s in
      let me' = EcMemory.me_subst s.fs_mem (ty_subst s) bhs.bhs_m in
      let bd' = f_subst ~tx s bhs.bhs_bd in

      f_bdHoareS_r { bhs with bhs_pr = pr'; bhs_po = po'; bhs_s = st';
                              bhs_bd = bd'; bhs_m  = me'; }

    | FequivF ef ->
      let pr', po' =
        let s = f_rem_mem s mleft in
        let s = f_rem_mem s mright in
        let pr' = f_subst ~tx s ef.ef_pr in
        let po' = f_subst ~tx s ef.ef_po in
        (pr', po') in
      let fl' = subst_xpath s ef.ef_fl in
      let fr' = subst_xpath s ef.ef_fr in

      f_equivF pr' fl' fr' po'

    | FequivS eqs ->
      assert (not (Mid.mem (fst eqs.es_ml) s.fs_mem) &&
                not (Mid.mem (fst eqs.es_mr) s.fs_mem));
      let pr' = f_subst ~tx s eqs.es_pr in
      let po' = f_subst ~tx s eqs.es_po in
      let sl' = s_subst s eqs.es_sl in
      let sr' = s_subst s eqs.es_sr in
      let ml' = EcMemory.me_subst s.fs_mem (ty_subst s) eqs.es_ml in
      let mr' = EcMemory.me_subst s.fs_mem (ty_subst s) eqs.es_mr in

      f_equivS ml' mr' pr' sl' sr' po'

    | FeagerF eg ->
      let pr', po' =
        let s = f_rem_mem s mleft in
        let s = f_rem_mem s mright in
        let pr' = f_subst ~tx s eg.eg_pr in
        let po' = f_subst ~tx s eg.eg_po in
        (pr', po') in
      let fl' = subst_xpath s eg.eg_fl in
      let fr' = subst_xpath s eg.eg_fr in

      let sl' = s_subst s eg.eg_sl in
      let sr' = s_subst s eg.eg_sr in

      f_eagerF pr' sl' fl' fr' sr' po'

    | Fcoe coe ->
      (* We freshen the binded memory. *)
      let m = fst coe.coe_mem in
      let m' = EcIdent.fresh m in
      let s = f_rebind_mem s m m' in

      (* We bind the memory of all memory predicates with the fresh memory
         we just created, and add them as local variable substitutions. *)
      let s = Mid.fold (fun id (pmem,p) s ->
          let fs_mem = f_bind_mem f_subst_id pmem m' in
          let p = f_subst ~tx:(fun _ f -> f) fs_mem p in
          f_bind_local s id p
        ) s.fs_mempred { s with fs_mempred = Mid.empty; } in


      (* Then we substitute *)
      let pr' = f_subst ~tx s coe.coe_pre in
      let me' = EcMemory.me_subst s.fs_mem (ty_subst s) coe.coe_mem in
      let e' = e_subst s coe.coe_e in

      (* If necessary, we substitute the memtype. *)
      let me' =
        if EcMemory.is_schema (snd me') && s.fs_memtype <> None
        then (fst me', oget s.fs_memtype)
        else me' in

      f_coe pr' me' e'

    | Fpr pr ->
      let pr_mem   = Mid.find_def pr.pr_mem pr.pr_mem s.fs_mem in
      let pr_fun   = subst_xpath s pr.pr_fun in
      let pr_args  = f_subst ~tx s pr.pr_args in
      let s = f_rem_mem s mhr in
      let pr_event = f_subst ~tx s pr.pr_event in

      f_pr pr_mem pr_fun pr_args pr_event

    | _ ->
      f_map (ty_subst s) (f_subst ~tx s) fp)

  and f_subst_op ~tx freshen fty tys args (tyids, e) =
    (* FIXME: factor this out *)
    (* FIXME: is [mhr] good as a default? *)

    let e =
      let sty = Tvar.init tyids tys in
      let sty = { ty_subst_id with fs_freshen = freshen; fs_v = sty} in
      e_subst sty e
    in

    let (sag, args, e) =
      match e.e_node with
      | Equant (`ELambda, largs, lbody) when args <> [] ->
          let largs1, largs2 = List.takedrop (List.length args  ) largs in
          let  args1,  args2 = List.takedrop (List.length largs1)  args in
            (Mid.of_list (List.combine (List.map fst largs1) args1),
             args2, e_lam largs2 lbody)

      | _ -> (Mid.of_list [], args, e)
    in

    let sag = { f_subst_id with fs_loc = sag } in
      f_app (f_subst ~tx sag (form_of_expr mhr e)) args fty

  and f_subst_pd ~tx fty tys args (tyids, f) =
    (* FIXME: factor this out *)
    (* FIXME: is fd_freshen value correct? *)

    let f =
      let sty = Tvar.init tyids tys in
      let sty = { ty_subst_id with fs_freshen = true; fs_v = sty} in
      f_subst ~tx sty f
    in

    let (sag, args, f) =
      match f.f_node with
      | Fquant (Llambda, largs, lbody) when args <> [] ->
          let largs1, largs2 = List.takedrop (List.length args  ) largs in
          let  args1,  args2 = List.takedrop (List.length largs1)  args in
            (Mid.of_list (List.combine (List.map fst largs1) args1),
             args2, f_lambda largs2 lbody)

      | _ -> (Mid.of_list [], args, f)
    in

    let sag = { f_subst_id with fs_loc = sag } in
    f_app (f_subst ~tx sag f) args fty

  and oi_subst ~(tx : form -> form -> form) (s : f_subst) (oi : PreOI.t) =
    let costs = match PreOI.costs oi with
      | `Unbounded -> `Unbounded
      | `Bounded (self,calls) ->
        let calls = EcPath.Mx.fold (fun x a calls ->
            EcPath.Mx.change
              (fun old -> assert (old = None); Some (f_subst ~tx s a))
              (subst_xpath s x)
              calls
          ) calls EcPath.Mx.empty in
        let self = f_subst ~tx s self in
        `Bounded (self,calls) in

    PreOI.mk
      (List.map (subst_xpath s) (PreOI.allowed oi))
      costs

  and mr_subst ~tx s mr : mod_restr =
    let sx = subst_xpath s in
    let sm = EcPath.m_subst_abs s.fs_cmod in
    { mr_xpaths = ur_app (fun s -> Sx.fold (fun m rx ->
          Sx.add (sx m) rx) s Sx.empty) mr.mr_xpaths;
      mr_mpaths = ur_app (fun s -> Sm.fold (fun m r ->
          Sm.add (sm m) r) s Sm.empty) mr.mr_mpaths;
      mr_oinfos = EcSymbols.Msym.map (oi_subst ~tx s) mr.mr_oinfos;
    }

  and subst_mty ~tx s mty =
    let sm = EcPath.m_subst_abs s.fs_cmod in

    let mt_params = List.map (snd_map (subst_mty ~tx s)) mty.mt_params in
    let mt_name   = mty.mt_name in
    let mt_args   = List.map sm mty.mt_args in
    let mt_restr  = mr_subst ~tx s mty.mt_restr in
    { mt_params; mt_name; mt_args; mt_restr; }

  and gty_subst ~tx s gty =
    if is_subst_id s then gty else

    match gty with
    | GTty ty ->
        let ty' = ty_subst s ty in
        if ty == ty' then gty else GTty ty'

    | GTmodty p ->
        let p' = subst_mty ~tx s p in

        if   p == p'
        then gty
        else GTmodty p'

    | GTmem mt ->
        let mt' = EcMemory.mt_subst (ty_subst s) mt in
        if mt == mt' then gty else GTmem mt'

  and add_binding ~tx s (x, gty as xt) =
    let gty' = gty_subst ~tx s gty in
    let x'   = if s.fs_freshen then EcIdent.fresh x else x in

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

  (* When substituting a abstract module (i.e. a mident) by a concrete one,
     we move the module cost from [c_calls] to [c_self]. *)
  and cost_subst ~tx s cost =
    let c_self = f_subst ~tx s cost.c_self
    and self', c_calls = EcPath.Mx.fold (fun x cb (self',calls) ->
        let x' = subst_xpath s x in
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
  let add_binding  = add_binding ~tx:(fun _ f -> f)
  let add_bindings = add_bindings ~tx:(fun _ f -> f)

  (* ------------------------------------------------------------------ *)
  let f_subst ?(tx = fun _ f -> f) s =
    if is_subst_id s then identity else f_subst ~tx s

  let gty_subst = gty_subst ~tx:(fun _ f -> f)
  let subst_mty = subst_mty ~tx:(fun _ f -> f)
  let oi_subst  = oi_subst ~tx:(fun _ f -> f)

  let f_subst_local x t =
    let s = f_bind_local f_subst_id x t in
    fun f -> if Mid.mem x f.f_fv then f_subst s f else f

  let f_subst_mem m1 m2 =
    let s = f_bind_mem f_subst_id m1 m2 in
    fun f -> if Mid.mem m1 f.f_fv then f_subst s f else f

  (* ------------------------------------------------------------------ *)
  let init_subst_tvar ?es_loc s =
    { f_subst_id with
      fs_freshen = true;
      fs_v = s;
      fs_eloc = odfl Mid.empty es_loc; }

  let subst_tvar ?es_loc s =
    f_subst (init_subst_tvar ?es_loc s)
end
