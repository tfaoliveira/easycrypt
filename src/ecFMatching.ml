open EcUtils
open EcFol
open EcTypes
open EcPath
open EcIdent
open EcEnv
(* open EcGenRegexp *)
(* open EcMatching *)

(* ---------------------------------------------------------------------- *)
exception NoMatches
exception CannotUnify
exception NoNext


module Name = struct
  include EcIdent
  let compare = id_compare
end


(* -------------------------------------------------------------------------- *)

module FPattern = struct

  type name = Name.t

  (* invariant of pattern : if the form is not Pobject, then there is
     at least one of the first set of patterns *)
  type pattern =
    | Panything
    | Pnamed     of pattern * name
    | Psub       of pattern
    | Por        of pattern list

    | Ptype      of pattern * ty

    | Pobject    of tobject

    | Pif        of pattern * pattern * pattern
    | Papp       of pattern * pattern list
    | Ptuple     of pattern list
    | Pproj      of pattern * int
    | Pmatch     of pattern * pattern list
    | Pquant     of quantif * bindings * pattern
    (* | Plet    of lpattern * pattern * pattern *)
    | Ppvar      of pattern * pattern
    | Pglob      of pattern * pattern
    (* | FhoareF of hoareF (\* $hr / $hr *\) *)
    (* | FhoareS of hoareS *)
    (* | FbdHoareF of bdHoareF (\* $hr / $hr *\) *)
    (* | FbdHoareS of bdHoareS *)
    (* | FequivF of equivF (\* $left,$right / $left,$right *\) *)
    (* | FequivS of equivS *)
    (* | FeagerF of eagerF *)
    | Ppr             of pattern * pattern * pattern * pattern

    | Pprog_var       of prog_var

    | Pxpath          of xpath
    (* mpath patterns *)
    (*                   mpath_top, mpath  list *)
    | Pmpath          of pattern * pattern list

   and tobject =
    | Oform      of form
    | Omem       of EcMemory.memory
    (* | Ompath     of mpath *)
    (* | Oxpath     of xpath *)
    | Ompath_top of mpath_top

  type tmatch = tobject * binding Mid.t

  type map = tmatch Mid.t

  type to_match = tmatch * pattern

  type pat_continuation =
    | ZTop
    | Znamed     of tmatch * name * pat_continuation
    (* Zor (cont, e_list, ne) :
       - cont   : the continuation if the matching is correct
       - e_list : if not, the sorted list of next engines to try matching with
       - ne     : if no match at all, then take the nengine to go up
     *)
    | Zor        of pat_continuation * engine list * nengine
    (* Zand (before, after, cont) :
       - before : list of couples (form, pattern) that has already been checked
       - after  : list of couples (form, pattern) to check in the following
       - cont   : continuation if all the matches succeed
     *)
    | Zand       of to_match list * to_match list * pat_continuation

    | Zbinds     of pat_continuation * binding Mid.t

  and engine = {
      e_head         : tmatch;
      e_continuation : pat_continuation;
      e_pattern      : pattern;
      e_map          : map;
      e_hyps         : EcEnv.LDecl.hyps;
    }

  and nengine = {
      ne_continuation : pat_continuation;
      ne_map          : map;
      ne_binds        : binding Mid.t;
      ne_hyps         : EcEnv.LDecl.hyps;
    }

  (* val mkengine    : base -> engine *)
  let mkengine (f : form) (p : pattern) (h : LDecl.hyps) : engine = {
      e_head         = Oform f, Mid.empty ;
      e_continuation = ZTop ;
      e_map          = Mid.empty ;
      e_pattern      = p ;
      e_hyps         = h ;
    }

  type ismatch =
    | Match
    | NoMatch

  let object_equal (o1 : tobject) (o2 : tobject) (h : LDecl.hyps) : bool =
    match o1,o2 with
    | Oform f1, Oform f2 -> EcReduction.is_conv h f1 f2
    | Omem m1, Omem m2 -> EcMemory.mem_equal m1 m2
    | Ompath_top (`Local id1), Ompath_top (`Local id2) -> id_equal id1 id2
    | Ompath_top (`Concrete (p1,None)), Ompath_top (`Concrete (p2,None)) ->
       p_equal p1 p2
    | Ompath_top (`Concrete (p1,Some op1)), Ompath_top (`Concrete (p2,Some op2)) ->
       p_equal p1 p2 && p_equal op1 op2
    | ((Omem _|Ompath_top _|Oform _),
       (Omem _|Ompath_top _|Oform _))
      -> false

  let rec merge_binds bs1 bs2 map = match bs1,bs2 with
    | [], _ | _,[] -> Some (map,bs1,bs2)
    | (_,ty1)::_, (_,ty2)::_ when not(gty_equal ty1 ty2) -> None
    | (id1,_)::_, (_,_)::_ when Mid.mem id1 map -> None
    | (id1,_)::bs1, (id2,ty2)::bs2 ->
       merge_binds bs1 bs2 (Mid.add id1 (id2,ty2) map)

  (* add_match can raise the exception : CannotUnify *)
  (* val add_match : matches -> name -> t_matches -> matches *)
  let add_match (map : map) (name : name) (o : tmatch) h =
    if Mid.set_disjoint (snd o) map
    then
      let (o1,o2) = o in
      let o = o1,match o1 with
                 | Oform      f  -> Mid.set_inter o2 (f_fv f)
                 | Omem       m  -> Mid.set_inter o2 (Sid.singleton m)
                 | Ompath_top mp -> Mid.set_inter o2 (m_fv Mid.empty (mpath mp [])) in
      let map = match Mid.find_opt name map with
        | None   -> Mid.add name o map
        | Some x -> if object_equal (fst x) (fst o) h then map
                    else raise CannotUnify
      in map
    else raise CannotUnify

  let e_next (e : engine) : nengine =
    { ne_continuation = e.e_continuation;
      ne_map = e.e_map;
      ne_binds = snd e.e_head;
      ne_hyps = e.e_hyps;
    }

  let n_engine (tm : tmatch) (e_pattern : pattern) (n : nengine) =
    { e_head = (fst tm, n.ne_binds);
      e_pattern;
      e_continuation = n.ne_continuation;
      e_map = n.ne_map;
      e_hyps = n.ne_hyps;
    }

  let sub_engine e p f =
    { e with e_head = f; e_pattern = Psub p }


  let p_app_simpl p subst =
    let rec aux = function
      | Panything -> Panything
      | Pnamed (p,id2) -> begin
          match Mid.find_opt id2 subst with
          | None -> Pnamed (aux p,id2)
          | Some (Ptype (p,ty1),GTty ty2) when ty_equal ty2 ty1 -> Ptype (p,ty1)
          | Some (Ptype _, GTty _) -> assert false
          | Some (p,GTty ty) -> Ptype (p,ty)
          | Some (p,GTmem _) | Some (p, GTmodty _) -> p
        end
      | Psub p -> Psub (aux p)
      | Por l -> Por (List.map aux l)
      | Ptype (p,ty) -> Ptype (aux p,ty)
      | Pobject o -> Pobject o (* FIXME *)
      | Pif (p1,p2,p3) -> Pif (aux p1,
                               aux p2,
                               aux p3)
      | Papp (op,args) -> Papp (aux op, List.map aux args)
      | Ptuple l -> Ptuple (List.map aux l)
      | Pproj (p,i) -> Pproj (aux p,i)
      | Pmatch (op,l) -> Pmatch (aux op, List.map aux l)
      | Pquant (q,bds,p) when Mid.set_disjoint subst (Mid.of_list bds) ->
         Pquant (q,bds,aux p)
      | Pquant _ ->
         raise (Invalid_argument
                  "in p_app_simpl : invalid argument name, it has been found in a sub quantif.")
      | Ppvar (p1,p2) -> Ppvar (aux p1,aux p2)
      | Pglob (p1,p2) -> Pglob (aux p1,aux p2)
      | Ppr (p1,p2,p3,p4) -> Ppr (aux p1, aux p2, aux p3, aux p4)
      | Pprog_var pv -> Pprog_var pv (* FIXME : when the id is about a module name *)
      | Pxpath xp -> Pxpath xp
      | Pmpath (p1,p2) -> Pmpath (aux p1, List.map aux p2)
    in aux p

  let olist f l =
    let rec aux acc there_is_Some = function
      | [] -> if there_is_Some then Some (List.rev acc) else None
      | x::rest when there_is_Some -> aux ((odfl x (f x))::acc) there_is_Some rest
      | x::rest -> match f x with
                   | None -> aux (x::acc) false rest
                   | Some x -> aux (x::acc) true rest in
    aux [] false l

  let replace_id id subst =
    match Mid.find_opt id subst with
    | None -> None
    | Some (Ptype (p,ty1),GTty ty2) when ty_equal ty2 ty1 -> Some (Ptype (p,ty1))
    | Some (Ptype _, GTty _) -> assert false
    | Some (_,GTty _) -> None
    | Some (p,GTmem _) | Some (p, GTmodty _) -> Some p

  let p_app_simpl_opt p subst =
    let rec aux = function
      | Panything -> None
      | Pnamed (_,id2) -> replace_id id2 subst
      | Psub p -> omap (fun x -> Psub x) (aux p)
      | Por l -> omap (fun x -> Por x) (olist aux l)
      | Ptype (p,ty) -> omap (fun p -> Ptype (p,ty)) (aux p)
      | Pobject o -> Some (Pobject o) (* FIXME *)
      | Pif (p1,p2,p3) ->
         let p = match olist aux [p1;p2;p3] with
           | None -> None
           | Some ([p1;p2;p3]) -> Some (Pif (p1,p2,p3))
           | _ -> assert false in
         p
      | Papp (op,args) ->
         let p = match olist aux (op::args) with
           | None -> None
           | Some (op::args) -> Some (Papp (op,args))
           | _ -> assert false
         in p
      | Ptuple l -> omap (fun x -> Ptuple x) (olist aux l)
      | Pproj (p,i) -> omap (fun x -> Pproj (x,i)) (aux p)
      | Pmatch (op,l) ->
         let p = match olist aux (op::l) with
           | None -> None
           | Some (op::args) -> Some (Pmatch (op,args))
           | _ -> assert false
         in p
      | Pquant (q,bds,p) when Mid.set_disjoint subst (Mid.of_list bds) ->
         omap (fun x -> Pquant (q,bds,x)) (aux p)
      | Pquant _ ->
         raise (Invalid_argument
                  "in p_app_simpl : invalid argument name, it has been found in a sub quantif.")
      | Ppvar (p1,p2) ->
         let p = match aux p1 with
           | None -> None
           | Some p1 -> match aux p2 with
                        | None -> None
                        | Some p2 -> Some (Ppvar (p1,p2)) in p
      | Pglob (p1,p2) ->
         let p = match aux p1 with
           | None -> None
           | Some p1 ->
              match aux p2 with
              | None -> None
              | Some p2 -> Some (Pglob (p1,p2)) in p
      | Ppr (p1,p2,p3,p4) ->
         let p = match olist aux [p1;p2;p3;p4] with
           | None -> None
           | Some [p1;p2;p3;p4] -> Some (Ppr (p1,p2,p3,p4))
           | _ -> assert false in p
      | Pprog_var _ -> None (* FIXME : when the id is about a module name *)
      | Pxpath _ -> None
      | Pmpath (op,args) ->
         let p = match olist aux (op::args) with
           | None -> None
           | Some (op::args) -> Some (Pmpath (op,args))
           | _ -> assert false
         in p
    in aux p


  let obeta_reduce = function
    | Papp (Pquant (Llambda, binds, p), pargs) ->
       let (bs1,bs2), (pargs1,pargs2) = List.prefix2 binds pargs in
       let p = match pargs2 with
         | [] -> p
         | _ -> Papp (p, pargs2) in
       let p = match bs2 with
         | [] -> p
         | _ -> Pquant (Llambda, bs2, p) in
       let subst = Mid.empty in
       let subst =
         try List.fold_left2 (fun a (b,t) c -> Mid.add_new Not_found b (c,t) a) subst bs1 pargs1
         with
         | Not_found -> raise (Invalid_argument "beta_reduce : two bindings has got the same name.")
       in
       p_app_simpl_opt p subst
    | _ -> None


  let beta_reduce = function
    | Papp (Pquant (Llambda, binds, p), pargs) ->
       let (bs1,bs2), (pargs1,pargs2) = List.prefix2 binds pargs in
       let p = match pargs2 with
         | [] -> p
         | _ -> Papp (p, pargs2) in
       let p = match bs2 with
         | [] -> p
         | _ -> Pquant (Llambda, bs2, p) in
       let subst = Mid.empty in
       let subst =
         try List.fold_left2 (fun a (b,t) c -> Mid.add_new Not_found b (c,t) a) subst bs1 pargs1
         with
         | Not_found -> raise (Invalid_argument "beta_reduce : two bindings has got the same name.")
       in
       p_app_simpl p subst
    | p -> p


  let subst_name n1 n2 p =
    let rec aux = function
      | Panything -> Panything
      | Pnamed (p,n) when id_equal n1 n -> Pnamed (p,n2)
      | Pnamed (p,n) -> Pnamed (aux p, n)
      | Psub p -> Psub (aux p)
      | Por pl -> Por (List.map aux pl)
      | Ptype (p,ty) -> Ptype (aux p, ty)
      | Pif (p2,p3,p4) -> Pif (aux p2,aux p3,aux p4)
      | Papp (p2,pl) -> Papp (aux p2,List.map aux pl)
      | Ptuple pl -> Ptuple (List.map aux pl)
      | Pproj (p2,i) -> Pproj (aux p2,i)
      | Pmatch (p2,pl) -> Pmatch (aux p2,List.map aux pl)
      | Pquant (q,bs,p2) -> Pquant (q,bs,aux p2)
      | Ppvar (p2,p3) -> Ppvar (aux p2,aux p3)
      | Pglob (p2,p3) -> Pglob (aux p2,aux p3)
      | Ppr (p2,p3,p4,p5) -> Ppr (aux p2,
                                  aux p3,
                                  aux p4,
                                  aux p5)
      | Pprog_var pv -> Pprog_var pv (* FIXME *)
      | Pxpath xp -> Pxpath xp  (* FIXME *)
      | Pmpath (p2,pl) -> Pmpath (aux p2, List.map aux pl)
      | Pobject (Omem mem) ->
         if id_equal n1 mem then Pobject (Omem n2) else Pobject (Omem n1)
      | Pobject (Ompath_top _) as p -> p
      | Pobject (Oform f) as p2 ->
         if not(Mid.mem n1 f.f_fv) then p2
         else match f.f_node with
              |  Flocal id ->
                  if id_equal id n1 then Pobject (Oform (f_local n2 f.f_ty)) else p2
              | Fquant (quant,bs,f') ->
                 if Mid.mem n1 f'.f_fv then Pquant (quant,bs,aux (Pobject (Oform f')))
                 else p2
              | Fif (f1,f2,f3) ->
                 Pif (aux (Pobject (Oform f1)),
                      aux (Pobject (Oform f2)),
                      aux (Pobject (Oform f3)))
              | Fmatch _ | Flet _-> Pobject (Oform f) (* FIXME *)
              | Fint _ -> Pobject (Oform f)
              | Fpvar (pvar,mem) ->
                 if id_equal mem n1 then Ppvar (Pprog_var pvar, Pobject (Omem n2))
                 else p2
              | Fglob (mpath,mem) ->
                 if id_equal mem n1 then
                   Pglob (aux_mpath mpath, Pobject (Omem n2))
                 else p2
              | Fop _ -> Pobject (Oform f) (* FIXME *)
              | Fapp (f1,fargs) ->
                 Papp (aux (Pobject (Oform f1)),
                       List.map (fun f -> aux (Pobject (Oform f))) fargs)
              | Ftuple t ->
                 Ptuple (List.map (fun f -> aux (Pobject (Oform f))) t)
              | Fproj (f1,i) -> Pproj (aux (Pobject (Oform f1)),i)
              | _ -> (* FIXME *) p2
      and aux_mpath mp =
        Pmpath (Pobject (Ompath_top mp.m_top), List.map aux_mpath mp.m_args)
    in aux p

  let rec substitution n1 p1 p2 = match p2 with
    | Panything -> Panything
    | Pnamed (_,n2) when id_equal n1 n2 -> p1
    | Pnamed (p2,n2) -> Pnamed (substitution n1 p1 p2, n2)
    | Psub p -> Psub (substitution n1 p1 p)
    | Por pl -> Por (List.map (substitution n1 p1) pl)
    | Ptype (p,ty) -> Ptype (substitution n1 p1 p, ty)
    | Pif (p2,p3,p4) -> Pif (substitution n1 p1 p2,
                             substitution n1 p1 p3,
                             substitution n1 p1 p4)
    | Papp (p2,pl) -> Papp (substitution n1 p1 p2,
                            List.map (substitution n1 p1) pl)
    | Ptuple pl -> Ptuple (List.map (substitution n1 p1) pl)
    | Pproj (p2,i) -> Pproj (substitution n1 p1 p2,i)
    | Pmatch (p2,pl) -> Pmatch (substitution n1 p1 p2,
                                List.map (substitution n1 p1) pl)
    | Pquant (q,bs,p2) -> Pquant (q,bs,substitution n1 p1 p2)
    | Ppvar (p2,p3) -> Ppvar (substitution n1 p1 p2,substitution n1 p1 p3)
    | Pglob (p2,p3) -> Pglob (substitution n1 p1 p2,substitution n1 p1 p3)
    | Ppr (p2,p3,p4,p5) -> Ppr (substitution n1 p1 p2,
                                substitution n1 p1 p3,
                                substitution n1 p1 p4,
                                substitution n1 p1 p5)
    | Pprog_var pv ->
       let xp = pv.pv_name in
       let name = xp.x_sub in
       if (EcPath.tostring name) = (EcIdent.tostring n1) then p1 else p2
    | Pxpath xp ->
       let name = xp.x_sub in
       if (EcPath.tostring name) = (EcIdent.tostring n1) then p1 else p2
    | Pmpath (p2,pl) -> Pmpath (substitution n1 p1 p2,
                                List.map (substitution n1 p1) pl)
    | Pobject (Omem mem) ->
       if id_equal n1 mem then p1 else p2
    | Pobject (Ompath_top _) -> p2
    | Pobject (Oform f) ->
       if not(Mid.mem n1 f.f_fv) then p2
       else match f.f_node with
            |  Flocal id ->
                if id_equal id n1 then Ptype (p1,f.f_ty) else p2
            | Fquant (quant,bs,f') ->
               if Mid.mem n1 f'.f_fv then Pquant (quant,bs,substitution n1 p1 (Pobject (Oform f')))
               else p2
            | Fif (f1,f2,f3) ->
               Pif (substitution n1 p1 (Pobject (Oform f1)),
                    substitution n1 p1 (Pobject (Oform f2)),
                    substitution n1 p1 (Pobject (Oform f3)))
            | Fmatch _ | Flet _-> Pobject (Oform f) (* FIXME *)
            | Fint _ -> Pobject (Oform f)
            | Fpvar (pvar,mem) ->
               if id_equal mem n1 then Ppvar (Pprog_var pvar,p1)
               else p2
            | Fglob (mpath,mem) ->
               if id_equal mem n1 then Pglob (substitution_mpath n1 p1 mpath, p1)
               else p2
            | Fop _ -> Pobject (Oform f) (* FIXME *)
            | Fapp (f1,fargs) ->
               Papp (substitution n1 p1 (Pobject (Oform f1)),
                     List.map (fun f -> substitution n1 p1 (Pobject (Oform f))) fargs)
            | Ftuple t ->
               Ptuple (List.map (fun f -> substitution n1 p1 (Pobject (Oform f))) t)
            | Fproj (f1,i) -> Pproj (substitution n1 p1 (Pobject (Oform f1)),i)
            | _ -> (* FIXME *) p2

    and substitution_mpath n1 p1 mpath =
      Pmpath (Pobject (Ompath_top mpath.m_top),
              List.map (substitution_mpath n1 p1) mpath.m_args)

  (* ---------------------------------------------------------------------- *)
  let rec process (e : engine) : nengine =
    match e.e_pattern, e.e_head with
    | Panything, _ -> next Match e

    | Pnamed (p,name), _ ->
       process { e with
                 e_pattern = p;
                 e_continuation = Znamed(e.e_head,name,e.e_continuation);
               }

    | Psub p, _ ->
       let le = sub_engines e p in
       process { e with
                 e_pattern = p;
                 e_continuation = Zor (e.e_continuation,le,e_next e);
               }

    | Ptype (p,ty), (Oform f, _) ->
       if ty_equal ty f.f_ty then
         process { e with e_pattern = p }
       else next NoMatch e

    | Por [], _ -> next NoMatch e
    | Por (p::pl), _ ->
       let f p = { e with
                   e_pattern = p;
                 } in
       process { e with
                 e_pattern = p;
                 e_continuation = Zor (e.e_continuation,List.map f pl,e_next e);
               }

    | Pquant (q1,bs1,p), (Oform f,binds) ->
       begin match f.f_node with
       | Fquant (q2,bs2,f2) ->
          (* FIXME : lambda case to be considered in higher order *)
          if not(q1 = q2) then next NoMatch e
          else begin
              match merge_binds bs1 bs2 binds with
              | None -> next NoMatch e
              | Some (new_binds,[],args) ->
                 let p =
                   Mid.fold_left
                     (fun acc n1 (n2,ty) ->
                       match ty with
                       | GTty ty -> substitution n1 (Pobject (Oform (f_local n2 ty))) acc
                       | _ -> acc)
                     p new_binds in
                 process { e with
                           e_pattern = p;
                           e_head = (Oform (f_quant q2 args f2), new_binds);
                           e_continuation = Zbinds (e.e_continuation, binds);
                         }
              | Some (_new_binds,_args,[]) -> (* FIXME for higher order *)
              (*    let p = *)
              (*      Mid.fold_left *)
              (*        (fun acc n1 (n2,ty) -> *)
              (*          match ty with *)
              (*          | GTty ty -> substitution n1 (Pobject (Oform (f_local n2 ty))) acc *)
              (*          | _ -> acc) *)
              (*        p new_binds in *)
              (*    let p = Pquant (q1,args,p) in *)
              (*    process_higer_order { e with *)
              (*                          e_pattern = p; *)
              (*                          e_head = Oform f2, new_binds; *)
              (*                          e_continuation = Zbinds (e.e_continuation, binds); *)
              (*                        } *)
                 next NoMatch e
              | _ -> assert false
            end
       | _ -> next NoMatch e
       end

    | Pif (pcond,p1,p2), (Oform f,binds) ->
       begin match f_node f with
       | Fif (cond,b1,b2) ->
          let zand = [((Oform b1,binds),p1);((Oform b2,binds),p2)] in
          process { e with
                    e_head = Oform cond, binds;
                    e_pattern = pcond;
                    e_continuation = Zand ([],zand,e.e_continuation);
                  }
       | _ -> next NoMatch e
       end

    | Papp (pop,pargs), (Oform f, binds) ->
       (* FIXME : higher order *)
       begin match f_node f with
       | Fapp (fop,fargs) ->
          let oe =
            let (fargs1,fargs2),(pargs1,pargs2) = List.prefix2 fargs pargs in
            match fargs2,pargs2 with
            | _::_,_::_ -> assert false
            | _, [] ->
               let fop' = f_app fop fargs1 (EcTypes.toarrow (List.map f_ty fargs2) (f_ty fop)) in
               let to_match_args = List.combine (List.map (fun x -> Oform x, binds)fargs2) pargs in
               let pop = match pargs1 with
                 | [] -> pop
                 | _ -> Papp (pop, pargs1) in
               let l = ((Oform fop', binds), pop)::to_match_args in
               let p,h,l = match List.rev l with
                 | [] -> assert false
                 | (o,p)::l -> p,o,l in
               let e_continuation = e.e_continuation in
               let e_continuation = Zand ([],l,e_continuation) in
               let e_list =
                 let rp = obeta_reduce p in
                 let l1 =
                   match rp with
                   | None -> []
                   | Some e_pattern ->
                      [{ e with e_pattern }] in
                 let rf = f_betared f in
                 let l2 = match fop.f_node with
                   | Fquant (Llambda,_,_) ->
                      [{ e with e_head = (Oform rf, binds) }]
                   | _ -> [] in
                 l1@l2 in
               let e_continuation = match e_list with
                 | [] -> e_continuation
                 | _ -> Zor (e_continuation,e_list,e_next e) in
                Some (fun () ->
                    process { e with
                              e_pattern = p;
                              e_head = h;
                              e_continuation; })
            | [], _::_ ->
               let opt = obeta_reduce (Papp (pop,pargs)) in
               omap (fun p () -> process { e with e_pattern = p }) opt
            in
            (odfl (fun () -> next NoMatch e) oe) ()
       | _ -> next NoMatch e (* process_higer_order e *)
       end

    | Ptuple [], (Oform f,_) ->
       begin match f_node f with
       | Ftuple [] -> next Match e
       | _ -> next NoMatch e
       end
    | Ptuple (p::ptuple), (Oform f, binds) ->
       begin match f_node f with
       | Ftuple [] -> next NoMatch e
       | Ftuple (f::ftuple) ->
          if (List.length ptuple = List.length ftuple)
          then
            let zand =
              List.combine (List.map (fun x -> Oform x, binds) ftuple) ptuple in
            let l = ((Oform f,binds),p)::zand in
            let pat,o,l = match List.rev l with
              | [] -> assert false
              | (o,p)::l -> p,o,l in
            process
              { e with
                e_pattern = p;
                e_head = Oform f, binds;
                e_continuation =
                  Zor (Zand ([],zand,e.e_continuation),
                       [{ e with
                          e_pattern = pat;
                          e_head = o;
                          e_continuation = Zand ([],l,e.e_continuation) }],
                       e_next e)
              }
          else next NoMatch e
       | _ -> next NoMatch e
       end

    | Pproj (e_pattern,i), (Oform f, binds) ->
       begin match f_node f with
       | Fproj (f,j) when i = j ->
          process { e with
                    e_pattern;
                    e_head = Oform f, binds;
                  }
       | _ -> next NoMatch e
       end

    | Pmatch (p,pl) , (Oform f,binds) ->
       begin match f_node f with
       | Fmatch (f,fl,_) when (List.length fl = List.length pl) ->
          let zand = List.combine (List.map (fun x -> Oform x, binds) fl) pl in
          process {
              e with
              e_pattern = p;
              e_head = Oform f, binds;
              e_continuation = Zand ([],zand,e.e_continuation);
            }
       | _ -> next NoMatch e
       end

    | Pobject o1, (o2,_) when object_equal o1 o2 e.e_hyps -> next Match e
    | Pobject (Oform f1), (Oform f2, _) -> begin
        match f1.f_node with
        | Flocal id1 -> begin
            match Mid.find_opt id1 e.e_map with
            | None -> next NoMatch e
            | Some (Oform f1, _) when EcReduction.is_conv e.e_hyps f1 f2 ->
               next Match e
            | _ -> next NoMatch e
          end
        | _ -> next NoMatch e
      end
    | Pobject _, _ -> next NoMatch e

    | Ppvar (p1,p2), (Oform f,binds) ->
       begin match f.f_node with
       | Fpvar (_,m) ->
          process { e with
                    e_pattern = p2;
                    e_head = Omem m, binds;
                    e_continuation = Zand ([],[(Oform f,binds),p1],e.e_continuation);
                  }
       | _ -> next NoMatch e
       end

    | Pprog_var x1, (Oform f,_) ->
       begin match f.f_node with
       | Fpvar (x2,_) when pv_equal x1 x2 -> next Match e
       | _ -> next NoMatch e
       end

    | Pglob (p1,p2), (Oform f,binds) ->
       begin match f.f_node with
       | Fglob (x,m) ->
          let zand = [(Ompath_top x.m_top,binds), p1] in
          process { e with
                    e_pattern = p2;
                    e_head = Omem m, binds;
                    e_continuation = Zand ([],zand,e.e_continuation);
                  }
       | _ -> next NoMatch e
       end

    | Pmpath (m,[]), (Ompath_top _,_ as omp) ->
       process { e with
                 e_pattern = m;
                 e_head = omp;
               }
    | Pmpath _,(Ompath_top _,_) -> next NoMatch e

    | Ppr (pmem,pfun,pargs,pevent), (Oform f, binds) ->
       begin match f.f_node with
       | Fpr pr ->
          let zand = [((Oform f, binds), pfun);
                      ((Oform pr.pr_args,binds), pargs);
                      ((Oform pr.pr_event, binds), pevent)] in
          process { e with
                    e_pattern = pmem;
                    e_head = Omem pr.pr_mem, binds;
                    e_continuation = Zand ([], zand, e.e_continuation);
                  }
       | _ -> next NoMatch e
       end

    | Pxpath pxp, (Oform f, _) ->
       begin match f.f_node with
       | Fpr pr when x_equal pr.pr_fun pxp -> next Match e
       | _ -> next NoMatch e
       end

    | ((Pmpath _|Pglob _|Pprog_var _|Ppvar _|Pquant _|Ppr _|Pxpath _),
       ((Oform _|Omem _|Ompath_top _),_))
      | (Pproj _|Ptuple _|Papp _|Pif _|Pmatch _|Ptype _),
        ((Omem _|Ompath_top _),_) ->
       next NoMatch e

  and next (m : ismatch) (e : engine) : nengine = next_n m (e_next e)

  and next_n (m : ismatch) (e : nengine) : nengine =
    match m,e.ne_continuation with
    | NoMatch, ZTop -> raise NoMatches

    | Match, ZTop   -> e

    | NoMatch, Znamed (_f, _name, ne_continuation) ->
       next_n NoMatch { e with ne_continuation }

    | Match, Znamed (f, name, ne_continuation) ->
       let m,e =
         try Match, { e with
                      ne_continuation;
                      ne_map = add_match e.ne_map name f e.ne_hyps;
                    }
         with
         | CannotUnify ->
            NoMatch, { e with
                       ne_continuation;
                     } in
       next_n m e

    | NoMatch, Zand (_,_,ne_continuation) ->
       next_n NoMatch { e with ne_continuation }

    | Match, Zand (_before,[],ne_continuation) -> next_n Match { e with ne_continuation }
    | Match, Zand (before,(f,p)::after,z) ->
       process (n_engine f p { e with ne_continuation = Zand ((f,p)::before,after,z)})

    | Match, Zor (ne_continuation, _, _) -> next_n Match { e with ne_continuation }

    | NoMatch, Zor (_, [], ne) ->
       next_n NoMatch ne

    | NoMatch, Zor (_, e'::engines, ne) ->
       process { e' with e_continuation = Zor (e'.e_continuation, engines, ne); }

    | Match, Zbinds (ne_continuation, ne_binds) ->
       next_n Match { e with ne_continuation; ne_binds }

    | NoMatch, Zbinds (ne_continuation, ne_binds) ->
       next_n NoMatch { e with ne_continuation; ne_binds }

  and sub_engines (e : engine) (p : pattern) : engine list =
    match e.e_head with
    | Omem _,_  -> []
    | Ompath_top _,_ -> []
    | Oform f, binds ->
       match f_node f with
       | Flet _
         | FhoareF _
         | FhoareS _
         | FbdHoareF _
         | FbdHoareS _
         | FequivF _
         | FequivS _
         | FeagerF _
         | Fint _
         | Flocal _
         | Fop _-> []
       | Fif (cond,f1,f2) ->
          List.map (sub_engine e p) [ Oform cond,binds ; Oform f1,binds ; Oform f2,binds ]
       | Fapp (f, args) ->
          List.map (sub_engine e p) ((Oform f,binds)::(List.map (fun x -> Oform x, binds) args))
       | Ftuple args ->
          List.map (sub_engine e p) (List.map (fun x -> Oform x, binds) args)
       | Fproj (f,_) -> [sub_engine e p (Oform f, binds)]
       | Fmatch (f,fl,_) ->
          List.map (sub_engine e p) ((Oform f, binds)::(List.map (fun x -> Oform x, binds) fl))
       | Fpr pr ->
          List.map (sub_engine e p) [ Omem pr.pr_mem   , binds ;
                                      Oform pr.pr_args , binds ;
                                      Oform pr.pr_event, binds ]
       | Fquant (_,bs,f1) ->
          [sub_engine e p (Oform f1, Mid.set_union binds (Mid.of_list (List.map (fun (x,y) -> (x,(x,y)))bs)))]
       | Fglob (mp,mem) ->
          List.map (sub_engine e p) [ Ompath_top mp.m_top,binds ;
                                      Omem mem, binds ]
       | Fpvar (_pv,mem) ->
          List.map (sub_engine e p) [ Omem mem, binds ]

  (* and process_higer_order (e : engine) = match e.e_head with *)
  (*   | Omem _,_ -> next NoMatch e (\* FIXME *\) *)
  (*   | Ompath_top _,_ -> next NoMatch e (\* FIXME *\) *)
  (*   | Oform f, _binds -> *)
  (*      match e.e_pattern,f.f_node with *)
  (*      | Pquant _,Fquant _ -> process e *)
  (*      | Pquant (_,[],p1), _ -> process { e with e_pattern = p1 } *)
  (*      | Pquant ((Lexists|Lforall),_,_),_ -> next NoMatch e *)
  (*      | Pquant (Llambda,(_x,_gty)::_args,_p1), _ -> *)
  (*         next NoMatch e *)

  (*      | Papp (pop, pargs), Fapp (fop,fargs) -> begin *)
  (*          let lp,lf = List.length pargs, List.length fargs in *)
  (*          let m x = min x 0 in *)
  (*          match List.split_at (m (lf-lp)) fargs, *)
  (*                List.split_at (m (lp-lf)) pargs with *)
  (*          | (_::_,_), (_::_,_) -> assert false *)
  (*          | ([],_), (_,_) -> process e *)
  (*          | (args,pargs), ([],fargs) -> *)

  (*          | _ -> next NoMatch e (\* FIXME *\) *)
  (*        end *)

  (*      | _,_ -> next NoMatch e (\* FIXME *\) *)



  let get_matches (e : engine) : map = e.e_map
  let get_n_matches (e : nengine) : map = e.ne_map

  let search_eng e =
    try Some (process e) with
    | NoMatches -> None

  let search (f : form) (p : pattern) (h : LDecl.hyps) =
    try Some (get_n_matches (process (mkengine f p h))) with
    | NoMatches -> None

  let pattern_of_form (bindings: bindings) (f : form) =
    let sbd = Sid.of_list (List.map fst bindings) in
    let rec aux f =
      if Mid.set_disjoint sbd f.f_fv then Pobject (Oform f)
      else
        match f.f_node with
        | Fif(f1,f2,f3)      -> Pif(aux f1, aux f2, aux f3)
        | Fapp(f,args)       -> Papp(aux f, List.map aux args)
        | Ftuple args        -> Ptuple(List.map aux args)
        | Fmatch(f,args,_ty) -> Pmatch(aux f, List.map aux args)
        | Fproj(f,i)         -> Pproj(aux f, i)
        | Flocal id          -> Pnamed (Ptype (Panything,f.f_ty), id)
        | Fpvar(x,m)         -> Ppvar(Pprog_var x, aux_mem m)
        | Fglob(mp, m)       -> Pglob(aux_mp mp, aux_mem m)
        | Fpr(pr)            -> Ppr (aux_mem pr.pr_mem,
                                     aux_xpath pr.pr_fun,
                                     aux pr.pr_args,
                                     aux_event pr.pr_event)
        | Fquant(quant,binds,f) -> Pquant (quant,binds,aux f)
        | _ -> raise (Invalid_argument "match case non-exhaustive in pattern_of_form")

    and aux_mem m =
      if Sid.mem m sbd then Pnamed (Panything, m)
      else Pobject(Omem m)

    and aux_mp mp =
      Pmpath (aux_mp_top mp.m_top, List.map aux_mp mp.m_args)

    and aux_mp_top mpt =
      match mpt with
      | `Local id when Sid.mem id sbd -> Pnamed (Panything, id)
      | _                             -> Pobject (Ompath_top mpt)

    and aux_xpath xpath = Pxpath xpath (* FIXME ?? *)

    and aux_event event = aux event
    in

    aux f




  let rec rewrite_term map f = match f.f_node with
    | Flocal id -> begin
        match Mid.find_opt id map with
        | None -> f
        | Some (Oform f', _) -> rewrite_term map f'
        | _ -> f
      end
    | Fquant (quant,bs,f') ->
       let f' = rewrite_term map f' in
       f_quant quant bs f'
    | Fif (f1,f2,f3) ->
       f_if (rewrite_term map f1) (rewrite_term map f2) (rewrite_term map f3)
    | Fmatch _ | Flet _-> f (* FIXME *)
    | Fint _ -> f
    | Fpvar (pvar,mem) ->
       begin match Mid.find_opt mem map with
       | None -> f
       | Some (Omem mem,_) -> f_pvar pvar f.f_ty mem
       | _ -> f
       end
    | Fglob (mpath,mem) ->
       begin match Mid.find_opt mem map with
       | None -> f
       | Some (Omem mem,_) -> f_glob mpath mem
       | _ -> f
       end
    | Fop _ -> f (* FIXME *)
    | Fapp (f1,fargs) ->
       f_app (rewrite_term map f1) (List.map (rewrite_term map) fargs) f.f_ty
    | Ftuple t -> f_tuple (List.map (rewrite_term map) t)
    | Fproj (f1,i) -> f_proj (rewrite_term map f1) i f.f_ty
    | _ -> (* FIXME *) f


end











(* -------------------------------------------------------------------------- *)
module Unification = struct
  exception No_Match
  module MName = EcMaps.Map.Make(Name)

  type meta_name = Name.t
  type 'a map_meta_names = 'a MName.t

  type only_name = Name.t
  type 'a map_only_names = 'a MName.t

  type axiom =
    | Axiom_Form     of form
    | Axiom_Memory   of EcMemory.memory
    | Axiom_MemEnv   of EcMemory.memenv
    | Axiom_Prog_Var of prog_var
    | Axiom_Local    of ident
    | Axiom_Int      of EcBigInt.zint
    | Axiom_Op       of EcPath.path * EcTypes.ty list
    | Axiom_Module   of mpath_top

  type fun_symbol =
    (* from type form *)
    | Sym_Form_If
    | Sym_Form_App
    | Sym_Form_Tuple
    | Sym_Form_Proj
    | Sym_Form_Match
    | Sym_Form_Quant
    | Sym_Form_Let
    | Sym_Form_Pvar
    | Sym_Form_Glob
    | Sym_Form_Hoare_F
    | Sym_Form_Hoare_S
    | Sym_Form_bd_Hoare_F
    | Sym_Form_bd_Hoare_S
    | Sym_Form_Equiv_F
    | Sym_Form_Equiv_S
    | Sym_Form_Eager_F
    | Sym_Form_Pr
    (* form type stmt*)
    | Sym_Stmt_Seq
    (* from type instr *)
    | Sym_Instr_Assign
    | Sym_Instr_Sample
    | Sym_Instr_Call
    | Sym_Instr_If
    | Sym_Instr_While
    | Sym_Instr_Assert
    (* from type xpath *)
    | Sym_Xpath
    (* from type mpath *)
    | Sym_Mpath

  type pattern =
    | Pat_Anything
    | Pat_Meta_Name  of pattern * meta_name
    (* | Pat_Sub        of pattern *)

    | Pat_Fun_Symbol of fun_symbol * pattern list
    | Pat_Axiom      of axiom

  type environnement = {
      env_hyps : EcEnv.LDecl.hyps
    }

  type continuation =
    | Continuation_None
    | Continuation_Meta_Named of meta_name * continuation
    (* Continuation_Or          (attempt1,     next_attempts, otherwise) *)
    | Continuation_Or         of continuation * engine list * engine
    | Continuation_And        of (pattern * pattern) list * continuation

  (*maybe change the list into a Lazy stream *)
  and backtrack = engine list

  and engine = {
      eng_immutable_left  : pattern;
      eng_immutable_right : pattern;
      eng_unify           : pattern * pattern;
      eng_environnement   : environnement;
      eng_continuation    : continuation;
      eng_backtrack       : backtrack;
      eng_bind_meta_names : pattern map_meta_names;
      eng_bind_only_names : only_name map_only_names;
      (* eng_bind_randoms *)
      (* eng_bind_types *)
    }

  let eq_form (f1 : form) (f2 : form) (_e : engine) =
    (* FIXME *) f1 = f2

  let eq_axiom (a1 : axiom) (a2 : axiom) (e : engine) =
    match a1, a2 with
    | Axiom_Form f1, Axiom_Form f2 -> eq_form f1 f2 e
    | Axiom_Memory m1, Axiom_Memory m2 -> EcMemory.mem_equal m1 m2
    | Axiom_MemEnv m1, Axiom_MemEnv m2 -> EcMemory.me_equal m1 m2
    | Axiom_Prog_Var x1, Axiom_Prog_Var x2 ->
       (* FIXME *) x1 = x2
    | Axiom_Local id1, Axiom_Local id2 ->
       (* FIXME *) EcIdent.id_equal id1 id2
    | Axiom_Int i1, Axiom_Int i2 -> EcBigInt.equal i1 i2
    | Axiom_Op (op1,lty1), Axiom_Op (op2,lty2) ->
       EcPath.p_equal op1 op2
       && (* FIXME *) List.for_all2 EcTypes.ty_equal lty1 lty2
    | Axiom_Module m1, Axiom_Module m2 -> EcPath.mt_equal m1 m2
    | _,_ -> false

  let eq_fun_symbol (f1 : fun_symbol) (f2 : fun_symbol) (_e : engine) = f1 = f2

  let rec unify (e : engine) =
    match e.eng_unify with
    | Pat_Anything, Pat_Anything -> next_match None e
    | Pat_Anything, p | p, Pat_Anything -> next_match (Some p) e

    | Pat_Meta_Name (p1,n1), p2 ->
       unify_meta_name n1 { e with eng_unify = (p1,p2) }

    | p1, Pat_Meta_Name (p2,n2) ->
       unify_meta_name n2 { e with eng_unify = (p1,p2) }

    | Pat_Axiom a1, Pat_Axiom a2 ->
       if (eq_axiom a1 a2 e) then next_match (Some (Pat_Axiom a1)) e
       else next_no_match e

    (* FIXME : add particular cases *)

    | Pat_Fun_Symbol _, Pat_Axiom _
      | Pat_Axiom _, Pat_Fun_Symbol _ -> next_no_match e

    | Pat_Fun_Symbol (f1,l1), Pat_Fun_Symbol (f2,l2) ->
       if (eq_fun_symbol f1 f2 e)
       then next_match None { e with
                eng_continuation =
                  Continuation_And (List.map2 (fun x y -> (x,y)) l1 l2,
                                    e.eng_continuation)}
       else next_no_match e

  and unify_meta_name (name : meta_name) (e : engine) =
    match MName.find_opt name e.eng_bind_meta_names with
    | None -> unify { e with
                  eng_continuation =
                    Continuation_Meta_Named (name, e.eng_continuation) }
    | Some p1 ->
       let p2,p3 = e.eng_unify in
       let cont = Continuation_And
                    ([(Pat_Meta_Name (Pat_Anything,name),p3)],
                     e.eng_continuation) in
       let e = { e with
                 eng_unify = (p1,p2);
                 eng_continuation =
                   Continuation_Meta_Named (name, cont);
               }
       in unify e

  and next_no_match (e : engine) =
    match e.eng_continuation with
    | Continuation_None -> raise No_Match
    | Continuation_Or (_, [], e') -> next_no_match e'
    | Continuation_Or (_, e1::l, e') ->
       unify { e1 with
           eng_continuation = Continuation_Or (e1.eng_continuation,
                                               l, e') }
    | Continuation_And (_, cont)
      | Continuation_Meta_Named (_, cont) ->
       next_no_match { e with eng_continuation = cont }

  and next_match (p : pattern option) (e : engine) =
    match e.eng_continuation with
    | Continuation_None -> e
    | Continuation_Or (cont1, _, _) ->
       next_match (Some (fst e.eng_unify)) { e with eng_continuation = cont1 }
    | Continuation_And ([],cont) ->
       (* FIXME *)
       next_match None { e with eng_continuation = cont }
    | Continuation_And (p1p2::rest, cont) ->
       (* FIXME : (p : pattern option) is not used nor given to
          reconstruct the right pattern *)
       unify { e with
           eng_unify = p1p2;
           eng_continuation = Continuation_And (rest, cont) }
    | Continuation_Meta_Named (name, cont) -> begin
        match MName.find_opt name e.eng_bind_meta_names, p with
        | None, None ->
           let e =
             { e with
               eng_bind_meta_names =
                 MName.add name (fst e.eng_unify) e.eng_bind_meta_names;
               eng_continuation = cont;
             }
           in
           next_match None e
        | Some p, None ->
           let e = { e with
                     eng_continuation = cont } in
           next_match (Some p) e
        | None, Some _p ->
           (* FIXME *) e
        | Some _, Some _ ->
           (* FIXME *) e
      end



end

(* module IPattern = struct *)
(*   open FPattern *)
(*   open EcModules *)
(*   open Zipper *)

(*   exception AtEnd *)

(*   type anchor = Start | End *)

(*   type stmt_pattern = *)
(*     | Anchor of anchor *)
(*     | Any *)
(*     | Base   of instr_pattern *)
(*     | Choice of stmt_pattern list *)
(*     | Named  of stmt_pattern * EcIdent.t *)
(*     | Repeat of stmt_pattern * int option EcUtils.pair * *)
(*                   [ `Greedy | `Lazy ] *)
(*     | Seq    of stmt_pattern list *)

(*    and instr_pattern = *)
(*      | RAssign of pattern * pattern *)
(*      | RSample of pattern * pattern *)
(*      | RCall   of pattern * pattern * pattern *)
(*      | RIf     of pattern * stmt_pattern * stmt_pattern *)
(*      | RWhile  of pattern * stmt_pattern *)


(*   type stmt_engine = { *)
(*       se_head         : instr list; *)
(*       se_pattern      : stmt_pattern; *)
(*       se_zipper       : zipper; *)
(*       se_map          : instr list Mid.t; *)
(*       se_fmap         : tobject Mid.t; *)
(*       se_hyps         : LDecl.hyps; *)
(*       se_continuation : continuation; *)
(*     } *)

(*   and instr_engine = { *)
(*       ie_head         : instr; *)
(*       ie_pattern      : instr_pattern; *)
(*       ie_zipper       : zipper; *)
(*       ie_fmap         : tobject Mid.t; *)
(*       ie_hyps         : LDecl.hyps; *)
(*       ie_continuation : continuation; *)
(*     } *)

(*   and continuation = *)
(*     | Ctop *)
(*     | Cnamed of EcIdent.t * continuation *)
(*     | Cseq   of stmt_pattern list * continuation *)


(*   let mk_engine (stmt : stmt) (ps : stmt_pattern) (hyps : LDecl.hyps) = { *)
(*       se_head         = stmt.s_node; *)
(*       se_pattern      = ps; *)
(*       se_zipper       = zipper [] [] ZTop; *)
(*       se_map          = Mid.empty; *)
(*       se_fmap         = Mid.empty; *)
(*       se_hyps         = hyps; *)
(*       se_continuation = Ctop; *)
(*     } *)

(*   let process_stmt (se : stmt_engine) : instr_engine = *)
(*     match se.se_pattern with *)
(*     | Anchor Start when *)
(*            se.se_zipper.z_head = [] && se.se_zipper.z_path = ZTop -> *)
(*        next Match se *)
(*     | Anchor Start -> next NoMatch se *)

(*     | Anchor End when *)
(*            se.se_zipper.z_tail = [] && se.se_zipper.z_path = ZTop -> *)
(*        next Match se *)
(*     | Anchor End -> next NoMatch se *)
(*     | Seq [] -> next Match se *)
(*     | Seq (p::after) -> *)
(*        process_stmt { se with *)
(*                       se_pattern = p; *)
(*                       se_continuation = Cseq (after,se.se_continuation); *)
(*                     } *)

(*   and next m se = match se.se_continuation, m with *)
(*     | Ctop, Match -> Some se *)
(*     | Ctop, NoMatch -> None *)
(*     | Cnamed  *)


(*   and process_instr (ie : instr_engine) = *)

(* end *)
