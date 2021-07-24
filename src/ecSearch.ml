(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcPath
open EcFol
open EcTypes
open EcTyping

module Mid = EcIdent.Mid

(* -------------------------------------------------------------------- *)
type pattern = (ptnmap * EcUnify.unienv) * form

type search = [
  | `ByName    of string
  | `ByPath    of Sp.t
  | `ByPattern of pattern
  | `ByOr      of search list
]

type context =
  path

(* -------------------------------------------------------------------- *)
let as_bypath (search : search) =
  match search with `ByPath p -> Some p | _ -> None

let as_bypattern (search : search) =
  match search with `ByPattern ptn -> Some ptn | _ -> None

(* -------------------------------------------------------------------- *)
let match_pattern (env : EcEnv.env) (search : search list) path f =
  let module E = struct exception MatchFound end in

  let hyps = EcEnv.LDecl.init env [] in
  let mode = EcMatching.fmsearch in
  let opts = lazy (EcFol.f_ops f) in

  let rec do1 (search : search) =
    match search with
    | `ByPath paths ->
        not (Sp.is_empty paths) &&
        not (Sp.disjoint (Lazy.force opts) paths)

    | `ByPattern ((v, ue), ptn) -> begin
        let ev = EcMatching.MEV.of_idents (Mid.keys !v) `Form in
        let na = List.length (snd (EcFol.destr_app ptn)) in

        let trymatch _bds tp =
          let tp =
            match tp.f_node with
            | Fapp (h, hargs) when List.length hargs > na ->
                let (a1, a2) = List.takedrop na hargs in
                f_app h a1 (toarrow (List.map f_ty a2) tp.f_ty)
            | _ -> tp
          in

          try
            ignore (EcMatching.f_match_core mode hyps (ue, ev) ~ptn tp);
            raise E.MatchFound
          with EcMatching.MatchFailure ->
            `Continue

        in try
            ignore (EcMatching.FPosition.select trymatch f);
            false
          with E.MatchFound -> true
      end

    | `ByOr subs -> List.exists do1 subs

    | `ByName name ->
       String.exists (EcPath.basename path) name

  in List.for_all do1 search

(* -------------------------------------------------------------------- *)
let match_context (_ : EcEnv.env) (ctxt : context list) (path : path) =
  let for1 (ctxt1 : EcPath.path) =
    EcPath.isprefix ctxt1 path
  in List.for_all for1 ctxt

(* -------------------------------------------------------------------- *)
let search (env : EcEnv.env) (ctxt : context list) (search : search list) =
  let check (path : path) (ax : EcDecl.axiom) =
       match_context env ctxt path
    && match_pattern env search path ax.ax_spec
  in EcEnv.Ax.all ~check env

(* -------------------------------------------------------------------- *)
open EcSmt
open EcDecl

let sort (relevant:Sp.t) (res:(path * EcDecl.axiom) list) =
  (* initialisation of the frequency *)
  let unwanted_ops = Sp.empty in
  let fr = Frequency.create unwanted_ops in
  let do1 (p, ax) =
    Frequency.add fr ax;
    let used = Frequency.f_ops unwanted_ops ax.ax_spec in
    (p,ax), used in
  let res = List.map do1 res in

  (* compute the weight of each axiom *)
  let rs = relevant, Sx.empty in
  let frequency_function freq = 1. +. log1p (float_of_int freq) in

  let do1 (ax,cs) =
    let r  = Frequency.r_inter cs rs in
    let ir = Frequency.r_diff cs r in
    let weight path m =
      let freq = Frequency.frequency fr path in
      let w = frequency_function freq in
      m +. w in
    let m = Frequency.r_fold weight r 0. in
    let m = m /. (m +. float_of_int (Frequency.r_card ir)) in
    (ax, m) in
  let res = List.map do1 res in
  let res = List.sort (fun (_,p1) (_,p2) -> compare p1 p2) res in
  List.map fst res
