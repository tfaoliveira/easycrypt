(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcPattern

(*-------------------------------------------------------------------- *)
let any_stmt = p_repeat (None, None) `Greedy (mk_pattern Pat_Anything OGTinstr)

let any_block = (With_anchor, With_anchor), IM_Any

let set_default_name pattern = pat_meta pattern default_name None

let default_start_without_anchor =
  pat_meta (p_repeat (None, None) `Lazy (mk_pattern Pat_Anything OGTinstr))
    default_start_name None

let default_end_without_anchor =
  pat_meta (p_repeat (None, None) `Greedy (mk_pattern Pat_Anything OGTinstr))
    default_end_name None

(*-------------------------------------------------------------------- *)
let default_stmt x = odfl any_stmt x

(*-------------------------------------------------------------------- *)
let add_default_names (at_begin, at_end) pattern =
  let pattern_sequence = [ set_default_name pattern ] in
  let pattern_sequence =
    if   at_begin
    then (pat_meta (p_stmt ~start:true ~finish:true []) default_start_name None)
         :: pattern_sequence
    else default_start_without_anchor :: pattern_sequence in
  let pattern_sequence =
    if   at_end
    then pattern_sequence @ [pat_meta (p_stmt ~start:true ~finish:true [])
                               default_end_name None]
    else pattern_sequence @ [default_end_without_anchor] in
  pattern_sequence

(*-------------------------------------------------------------------- *)
let add_anchors (at_begin, at_end) pattern_sequence =
  p_stmt ~start:(at_begin = With_anchor) ~finish:(at_end = With_anchor) pattern_sequence

let pat_anything ogty =
  (* meta_var (EcIdent.create "") None OGTany *)
  mk_pattern Pat_Anything ogty

(*-------------------------------------------------------------------- *)
let rec trans_block (anchors, pattern_parsed) =
  let pattern = trans_stmt pattern_parsed in
  match pattern.p_node with
  | Pat_Fun_Symbol (Sym_Stmt_Seq _, ps) -> add_anchors anchors ps
  | _                                   -> add_anchors anchors [ pattern ]

(*-------------------------------------------------------------------- *)
and trans_stmt = function
  | IM_Any      -> any_stmt
  | IM_Parens r -> trans_stmt r
  | IM_Assign   -> p_assign (pat_anything OGTlv) (pat_anything (OGTty None))
  | IM_Sample   -> p_sample (pat_anything OGTlv) (pat_anything (OGTty None))
  | IM_Call     -> p_call (Some (pat_anything OGTlv))
                     (pat_anything OGTxpath) (pat_anything (OGTty None))

  | IM_If (bt, bf)  ->
     let branch_true  = trans_block (odfl any_block bt) in
     let branch_false = trans_block (odfl any_block bf) in
     p_instr_if (pat_anything (OGTty (Some EcTypes.tbool))) branch_true branch_false

  | IM_While b     ->
     let branch = odfl any_block b in
     let branch = trans_block branch in
     p_while (pat_anything (OGTty (Some EcTypes.tbool))) branch

  | IM_Named (s, r) ->
     let r = odfl IM_Any r in
     let r = trans_stmt r in
     pat_meta r (EcIdent.create (EcLocation.unloc s)) None

  | IM_Repeat ((a,b),c) ->
     trans_repeat ((a,b),c)

  | IM_Seq l ->
     p_stmt (List.map trans_stmt l)

  | IM_Choice l    ->
     pat_or (List.map trans_stmt l)

(*-------------------------------------------------------------------- *)
and trans_repeat ((is_greedy, repeat_kind), r) =
  match r with
  | IM_Any -> begin
      let greed = if is_greedy then `Greedy else `Lazy in
      match repeat_kind with
      | IM_R_Repeat info ->
         p_repeat info greed (pat_anything OGTinstr)
      | IM_R_May    info ->
         p_repeat (None,info) greed (pat_anything OGTinstr)
    end

  | IM_Named (s, r) ->
     let r = odfl IM_Any r in
     let r = trans_repeat ((is_greedy, repeat_kind), r) in
     pat_meta r (EcIdent.create (EcLocation.unloc s)) None

  | _ -> begin
      let r = trans_stmt r in
      let greed = if is_greedy then `Greedy else `Lazy in
      match repeat_kind with
      | IM_R_Repeat info ->
         p_repeat info greed r
      | IM_R_May    info ->
         p_repeat (None,info) greed r
    end

(*-------------------------------------------------------------------- *)
let trans_block ((a,b), pattern_parsed) =
  let pattern = trans_stmt pattern_parsed in
  add_anchors (a,b) (add_default_names (a=With_anchor,b=With_anchor) pattern)
