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
open EcGenRegexp
open EcMaps

(*-------------------------------------------------------------------- *)
let any_stmt = p_repeat (None, None) `Greedy Any

let any_block = (With_anchor, With_anchor), IM_Any

let set_default_name pattern = Named (pattern, default_name)

let default_start_without_anchor =
  Named (p_repeat (None, None) `Lazy Any, default_start_name)

let default_end_without_anchor =
  Named (p_repeat (None, None) `Greedy Any, default_end_name)

(*-------------------------------------------------------------------- *)
let default_stmt x = odfl any_stmt x

(*-------------------------------------------------------------------- *)
let add_default_names (at_begin, at_end) pattern =
  let pattern_sequence = [ set_default_name pattern ] in
  let pattern_sequence =
    let p = if   at_begin = With_anchor
            then Seq []
            else p_repeat (None, None) `Lazy Any in
    (Named (p, default_start_name)) :: pattern_sequence in
  let pattern_sequence =
    let p = if   at_end = With_anchor
            then Seq []
            else p_repeat (None, None) `Greedy Any in
    pattern_sequence @ [Named (p, default_end_name)] in
  pattern_sequence

(*-------------------------------------------------------------------- *)
let add_anchors (at_begin, at_end) pattern_sequence =
  let pattern_sequence =
    if   at_begin = With_anchor
    then pattern_sequence
    else (p_repeat (None, None) `Lazy Any) :: pattern_sequence
  in
  let pattern_sequence =
    if   at_end = With_anchor
    then pattern_sequence
    else pattern_sequence @ [p_repeat (None, None) `Greedy Any]
  in
  Seq pattern_sequence

let pat_anything ogty =
  meta_var (EcIdent.create "$anything") None ogty

(*-------------------------------------------------------------------- *)
let rec trans_block names (anchors, pattern_parsed) =
  let names, pattern = trans_stmt names pattern_parsed in
  match pattern with
  | Seq ps -> names, add_anchors anchors ps
  | _      -> names, add_anchors anchors [ pattern ]

(*-------------------------------------------------------------------- *)
and trans_stmt names = function
  | IM_Any      -> names, any_stmt
  | IM_Parens r -> trans_stmt names r
  | IM_Assign   -> names, Base (p_assign (pat_anything (OGTty None)) (pat_anything (OGTty None)))
  | IM_Sample   -> names, Base (p_sample (pat_anything (OGTty None)) (pat_anything (OGTty None)))
  | IM_Call     -> names, Base (p_call (Some (pat_anything (OGTty None)))
                                  (pat_anything OGTxpath)
                                  (pat_anything (OGTty None)))

  | IM_If (bt, bf)  ->
     let names, branch_true  = trans_block names (odfl any_block bt) in
     let names, branch_false = trans_block names (odfl any_block bf) in
     let        branch_true  = p_gen_stmt branch_true in
     let        branch_false = p_gen_stmt branch_false in
     names, Base (p_instr_if (pat_anything (OGTty (Some EcTypes.tbool)))
                    branch_true branch_false)

  | IM_While b     ->
     let        branch = odfl any_block b in
     let names, branch = trans_block names branch in
     let        branch = p_gen_stmt branch in
     names, Base (p_while (pat_anything (OGTty (Some EcTypes.tbool))) branch)

  | IM_Named (s, r) ->
     let r     = odfl IM_Any r in
     let name  = EcLocation.unloc s in
     let names =
       Mstr.change (function
           | Some t -> Some t
           | None -> Some (EcIdent.create name)) name names in
     let names, r = trans_stmt names r in
     names, Named (r, Mstr.find name names)

  | IM_Repeat ((a,b),c) ->
     trans_repeat names ((a,b),c)

  | IM_Seq l ->
     let names, l = List.fold_left_map trans_stmt names l in
     names, Seq l

  | IM_Choice l    ->
     let names, l = List.fold_left_map trans_stmt names l in
     names, Choice l

(*-------------------------------------------------------------------- *)
and trans_repeat names ((is_greedy, repeat_kind), r) =
  match r with
  | IM_Any -> begin
      let greed = if is_greedy then `Greedy else `Lazy in
      match repeat_kind with
      | IM_R_Repeat info -> names, p_repeat info greed Any
      | IM_R_May    info -> names, p_repeat (None,info) greed Any
    end

  | IM_Named (s, r) ->
     let r = odfl IM_Any r in
     let name  = EcLocation.unloc s in
     let names =
       Mstr.change (function
           | Some t -> Some t
           | None -> Some (EcIdent.create name)) name names in
     let names, r = trans_repeat names ((is_greedy, repeat_kind), r) in
     names, Named (r, Mstr.find name names)

  | _ -> begin
      let names, r = trans_stmt names r in
      let greed = if is_greedy then `Greedy else `Lazy in
      match repeat_kind with
      | IM_R_Repeat info -> names, p_repeat info greed r
      | IM_R_May    info -> names, p_repeat (None,info) greed r
    end

let trans_stmt p = trans_stmt Mstr.empty p

(*-------------------------------------------------------------------- *)
let trans_block ((a,b), pattern_parsed) =
  let names, pattern = trans_stmt pattern_parsed in
  let names = Mstr.add (EcIdent.name (EcPattern.default_end_name))
                EcPattern.default_end_name names in
  let names = Mstr.add (EcIdent.name (EcPattern.default_start_name))
                EcPattern.default_start_name names in
  names, p_gen_stmt (Seq (add_default_names (a,b) pattern))
