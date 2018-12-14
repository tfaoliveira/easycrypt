open EcUtils
open EcEnv
open EcTypes
open EcModules
open EcFol
open EcGenRegexp
open EcMatching

(* -------------------------------------------------------------------------- *)
type regexp_instr = regexp1_instr gen_regexp

and regexp1_instr =
  | RAssign    of EcPattern.pattern * EcPattern.pattern
  | RSample    of EcPattern.pattern * EcPattern.pattern
  | RCall      of EcPattern.pattern * EcPattern.pattern * EcPattern.pattern
  | RIf        of EcPattern.pattern * regexp_instr * regexp_instr
  | RWhile     of EcPattern.pattern * regexp_instr


module RegexpBaseInstr = struct
  open Zipper
  open EcPattern
  open EcFMatching

  type regexp = regexp_instr
  type regexp1 = regexp1_instr

  type pos  = int
  type path = int list

  type subject = instr list

  type engine  = {
    e_zipper : zipper;
    e_pos    : pos;
    e_path   : pos list;
    e_hyps   : LDecl.hyps;
    e_map    : EcPattern.map;
  }

  let mkengine (s : subject) (h : LDecl.hyps) = {
    e_zipper = zipper [] s ZTop;
    e_pos    = 0;
    e_path   = [];
    e_hyps   = h;
    e_map    = EcPattern.MName.empty;
  }

  let position (e : engine) =
    e.e_pos

  let at_start (e : engine) =
    List.is_empty e.e_zipper.z_head

  let at_end (e : engine) =
    List.is_empty e.e_zipper.z_tail

  let path (e : engine) =
    e.e_pos :: e.e_path

  let eat_option (f : 'a -> 'a -> unit) (x : 'a option) (xn : 'a option) =
    match x, xn with
    | None  , Some _ -> raise NoMatch
    | Some _, None   -> raise NoMatch
    | None  , None   -> ()
    | Some x, Some y -> f x y

  let eat_list (f : 'a -> 'a -> unit) (x : 'a list) (xn : 'a list) =
    try  List.iter2 f x xn
    with Invalid_argument _ -> raise NoMatch (* FIXME *)

  let eat_lvalue (lv : lvalue) (lvn : lvalue) =
    if not (lv_equal lv lvn) then raise NoMatch

  let eat_expr (e : expr) (en : expr) =
    if not (e_equal e en) then raise NoMatch

  let eat_xpath (f : EcPath.xpath) (fn : EcPath.xpath) =
    if not (EcPath.x_equal f fn) then raise NoMatch

  let none_fun _ _ = None

  let rec eat_base (eng : engine) (r : regexp1) =
    let z = eng.e_zipper in

    match z.z_tail with
    | [] -> raise NoMatch

    | i :: tail -> begin
       match (i.i_node,r) with
       | Sasgn (x1,e1), RAssign (x2,p2)
         | Srnd  (x1,e1), RSample (x2,p2) ->
           let map = match x1 with
           | LvVar (pv,ty) ->
              let fx1 = f_pvar pv ty mhr in
              let unienv = EcUnify.UniEnv.create None in
              let mtch = EcFMatching.init_match_env ~mtch:eng.e_map ~unienv () in
              let e = EcFMatching.mk_engine ~mtch fx1 x2 eng.e_hyps
                        EcReduction.full_red EcReduction.full_red in
              let map = match EcFMatching.search_eng e with
                | None -> raise NoMatch
                | Some e -> e.ne_env.env_match.me_matches in
              map

           | LvTuple tuple ->
              let f x = f_pvar (fst x) (snd x) mhr in
              let fx1 = f_tuple (List.map f tuple) in
              let unienv = EcUnify.UniEnv.create None in
              let mtch = EcFMatching.init_match_env ~mtch:eng.e_map ~unienv () in
              let e = EcFMatching.mk_engine ~mtch fx1 x2 eng.e_hyps
                        EcReduction.full_red EcReduction.full_red in
              let map = match EcFMatching.search_eng e with
                | None -> raise NoMatch
                | Some e -> e.ne_env.env_match.me_matches in
              map

           | LvMap ((op,tys),_pv,_e,ty) ->
              let _fop = f_op op tys ty in
              raise NoMatch
           in

           let f1 = form_of_expr mhr e1 in
           let unienv = EcUnify.UniEnv.create None in
              let mtch = EcFMatching.init_match_env ~mtch:map ~unienv () in
           let e = EcFMatching.mk_engine ~mtch f1 p2 eng.e_hyps EcReduction.full_red
                     EcReduction.full_red in
           let map = match EcFMatching.search_eng e with
             | None -> raise NoMatch
             | Some e -> e.ne_env.env_match.me_matches in
           { eng with e_map = map }, []

       | Scall (Some x,f,args), RCall (p1,p2,pargs)  ->
          let fx1 = match x with
            | LvVar (pv,ty) -> f_pvar pv ty mhr
            | LvTuple tuple ->
               let f x = f_pvar (fst x) (snd x) mhr in
               f_tuple (List.map f tuple)

            | LvMap ((op,tys),_pv,_e,ty) ->
               let _fop = f_op op tys ty in
               raise NoMatch
          in
          let unienv = EcUnify.UniEnv.create None in
          let mtch = EcFMatching.init_match_env ~mtch:eng.e_map ~unienv () in
          let e = EcFMatching.mk_engine ~mtch fx1 p1 eng.e_hyps
                    EcReduction.full_red EcReduction.full_red in
          let map = match EcFMatching.search_eng e with
            | None -> raise NoMatch
            | Some e -> e.ne_env.env_match.me_matches in
          let args = List.map (form_of_expr mhr) args in
          let f = f_pr mleft f (f_tuple args) f_true in
          let p = pat_fun_symbol Sym_Form_Pr
                    ((mk_pattern Pat_Anything OGTany)::p2::pargs::
                       (mk_pattern Pat_Anything OGTany)::[]) in
          let unienv = EcUnify.UniEnv.create None in
          let mtch = EcFMatching.init_match_env ~mtch:map ~unienv () in
          let e = EcFMatching.mk_engine ~mtch f p eng.e_hyps
                    EcReduction.full_red EcReduction.full_red in
          let map = match EcFMatching.search_eng e with
            | None -> raise NoMatch
            | Some e -> e.ne_env.env_match.me_matches in
          { eng with e_map = map }, []

       | Sif (cond, st, sf), RIf (pcond, stn, sfn) -> begin
           let fcond = form_of_expr mhr cond in
           let unienv = EcUnify.UniEnv.create None in
           let mtch = EcFMatching.init_match_env ~mtch:eng.e_map ~unienv () in
           let e' = EcFMatching.mk_engine ~mtch fcond pcond eng.e_hyps
                      EcReduction.full_red EcReduction.full_red in
           let map = match EcFMatching.search_eng e' with
             | None -> raise NoMatch
             | Some e' -> e'.ne_env.env_match.me_matches in

           let e_t = mkengine st.s_node eng.e_hyps in
           let e_t = { e_t with e_map = map } in
           let e_t =
             let zp = ZIfThen (cond, ((z.z_head, tail), z.z_path), sf) in
             let zp = { e_t.e_zipper with z_path = zp; } in
             { e_t with e_path = 0 :: eng.e_pos :: eng.e_path; e_zipper = zp; } in

           let e_f = mkengine sf.s_node eng.e_hyps in
           let e_f = { e_f with e_map = map } in
           let e_f =
             let zp = ZIfElse (cond, st, ((z.z_head, tail), z.z_path)) in
             let zp = { e_f.e_zipper with z_path = zp; } in
             { e_f with e_path = 1 :: eng.e_pos :: eng.e_path; e_zipper = zp; } in

           (eat eng, [(e_t, stn); (e_f, sfn)])
         end

       | Swhile (e, s), RWhile (pcond,sn) -> begin
           let fcond = form_of_expr mhr e in
           let unienv = EcUnify.UniEnv.create None in
           let mtch = EcFMatching.init_match_env ~mtch:eng.e_map ~unienv () in
           let e' = EcFMatching.mk_engine ~mtch fcond pcond eng.e_hyps
                      EcReduction.full_red EcReduction.full_red in
           let map = match EcFMatching.search_eng e' with
             | None -> raise NoMatch
             | Some e' -> e'.ne_env.env_match.me_matches in
           let es = mkengine s.s_node eng.e_hyps in
           let es = { es with e_map = map } in
           let es =
             let zp = ZWhile (e, ((z.z_head, tail), z.z_path)) in
             let zp = { es.e_zipper with z_path = zp; } in
             { es with e_path = 0 :: eng.e_pos :: eng.e_path; e_zipper = zp; }  in

            (eat eng, [(es, sn)])
         end

       | _, _ -> raise NoMatch
     end

  and eat (e : engine) = {
      e with e_zipper = zip_eat e.e_zipper;
             e_pos    = e.e_pos + 1;
    }

  and zip_eat (z : zipper) =
    match z.z_tail with
    | []        -> raise NoMatch
    | i :: tail -> zipper (i :: z.z_head) tail z.z_path

  let extract (e : engine) ((lo, hi) : pos * pos) =
    if hi <= lo then [] else

      let s = List.rev_append e.e_zipper.z_head e.e_zipper.z_tail in
      List.of_enum (List.enum s |> Enum.skip lo |> Enum.take (hi-lo))

  let rec next_zipper (z : zipper) =
    match z.z_tail with
    | i :: tail ->
       begin match i.i_node with
       | Sif (e, stmttrue, stmtfalse) ->
          let z = (i::z.z_head, tail), z.z_path in
          let path = ZIfThen (e, z, stmtfalse) in
          let z' = zipper [] stmttrue.s_node path in
          Some z'

       | Swhile (e, block) ->
          let z = (i::z.z_head, tail), z.z_path in
          let path = ZWhile (e, z) in
          let z' = zipper [] block.s_node path in
          Some z'

       | Sasgn _ | Srnd _ | Scall _ | _ ->
          Some { z with z_head = i :: z.z_head ; z_tail = tail }
       end

    | [] ->
       match z.z_path with
       | ZTop -> None

       | ZWhile (_e, ((head, tail), path)) ->
          let z' = zipper head tail path in
          next_zipper z'

       | ZIfThen (e, father, stmtfalse) ->
          let stmttrue = stmt (List.rev z.z_head) in
          let z' = zipper [] stmtfalse.s_node (ZIfElse (e, stmttrue, father)) in
          next_zipper z'

       | ZIfElse (_e, _stmttrue, ((head, tail), path)) ->
          let z' = zipper head tail path in
          next_zipper z'

  let next (e : engine) =
    next_zipper e.e_zipper |> omap (fun z ->
      { e with e_zipper = z; e_pos = List.length z.z_head })
end

module RegexpStmt = struct
  open RegexpBaseInstr
  include EcGenRegexp.Regexp(RegexpBaseInstr)
  let search r s h = match search r s h with
    | None -> None
    | Some (e,m) -> Some (e.e_map,m)
end
