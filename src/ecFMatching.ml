(* -------------------------------------------------------------------- *)
open EcUtils
open EcFol
open EcTypes
open EcPath
open EcIdent
open EcEnv
open EcModules
open EcPattern
open Psubst
open EcGenRegexp


type verbose = {
    verbose_match           : bool;
    verbose_rule            : bool;
    verbose_type            : bool;
    verbose_bind_restr      : bool;
    verbose_add_meta        : bool;
    verbose_abstract        : bool;
    verbose_reduce          : bool;
    verbose_conv            : bool;
    verbose_show_ignored_or : bool;
    verbose_show_or         : bool;
    verbose_begin_match     : bool;
    verbose_translate_error : bool;
    verbose_subst           : bool;
    verbose_unienv          : bool;
    verbose_eta             : bool;
    verbose_show_match      : bool;
    verbose_add_reduce      : bool;
    verbose_saturate        : bool;
  }

let no_verbose : verbose = {
    verbose_match           = false;
    verbose_rule            = false;
    verbose_type            = false;
    verbose_bind_restr      = false;
    verbose_add_meta        = false;
    verbose_abstract        = false;
    verbose_reduce          = false;
    verbose_conv            = false;
    verbose_show_ignored_or = false;
    verbose_show_or         = false;
    verbose_begin_match     = false;
    verbose_translate_error = false;
    verbose_subst           = false;
    verbose_unienv          = false;
    verbose_eta             = false;
    verbose_show_match      = false;
    verbose_add_reduce      = false;
    verbose_saturate        = false;
  }

let full_verbose : verbose = {
    verbose_match           = true;
    verbose_rule            = true;
    verbose_type            = true;
    verbose_bind_restr      = true;
    verbose_add_meta        = true;
    verbose_abstract        = true;
    verbose_reduce          = true;
    verbose_conv            = true;
    verbose_show_ignored_or = true;
    verbose_show_or         = true;
    verbose_begin_match     = true;
    verbose_translate_error = true;
    verbose_subst           = true;
    verbose_unienv          = true;
    verbose_eta             = true;
    verbose_show_match      = true;
    verbose_add_reduce      = true;
    verbose_saturate        = true;
  }

let debug_verbose : verbose = {
    verbose_match           = true;
    verbose_rule            = true;
    verbose_type            = false;
    verbose_bind_restr      = false;
    verbose_add_meta        = false;
    verbose_abstract        = false;
    verbose_reduce          = false;
    verbose_conv            = false;
    verbose_show_ignored_or = false;
    verbose_show_or         = false;
    verbose_begin_match     = true;
    verbose_translate_error = false;
    verbose_subst           = false;
    verbose_unienv          = false;
    verbose_eta             = false;
    verbose_show_match      = false;
    verbose_add_reduce      = false;
    verbose_saturate        = false;
  }

let env_verbose = no_verbose

(* ---------------------------------------------------------------------- *)
exception Matches
exception NoMatches
exception CannotUnify
exception NoNext

type match_env = {
    me_unienv    : EcUnify.unienv;
    me_meta_vars : ogty Mid.t;
    me_matches   : pattern Mid.t;
  }

type stmt_engine = pattern list Mid.t

type environment = {
    env_hyps               : EcEnv.LDecl.hyps;
    env_match              : match_env;
    env_red_info_match     : EcReduction.reduction_info;
    env_red_info_same_meta : EcReduction.reduction_info;
    env_red_info_conv      : EcReduction.reduction_info;
    env_meta_restr_binds   : pbindings Mid.t;
    env_stmt               : stmt_engine;
    env_verbose            : verbose;
  }

type pat_continuation =
  | ZTop

  | Znamed     of pattern * meta_name * pbindings option * pat_continuation

  (* Zor (cont, e_list, ne) :
       - cont   : the continuation if the matching is correct
       - e_list : if not, the reverted sorted list of next engines to try matching with
       - ne     : if no match at all, then take the nengine to go up *)
  | Zor        of pat_continuation * engine list * nengine

  (* Zand (before, after, cont) :
       - before : list of couples (pattern, pattern) that has already been checked
       - after  : list of couples (pattern, pattern) to check in the following
       - reductions : list of possible reduction before asking zand
       - cont   : continuation if all the matches succeed *)
  | Zand       of (pattern * pattern) list
                  * (pattern * pattern) list
                  * pat_continuation

  | Zreduce    of pat_continuation * engine * nengine
  | Zconv      of pat_continuation * engine * nengine

and engine = {
    e_pattern1     : pattern;
    e_pattern2     : pattern;
    e_continuation : pat_continuation;
    e_env          : environment;
  }

and nengine = {
    ne_continuation : pat_continuation;
    ne_env          : environment;
  }

type ismatch =
  | Match
  | NoMatch

(* -------------------------------------------------------------------- *)
let menv_copy (me : match_env) =
  { me with me_unienv = EcUnify.UniEnv.copy me.me_unienv }

let env_copy (e : environment) =
  { e with env_match = menv_copy e.env_match }

(* -------------------------------------------------------------------- *)
let menv_of_hyps (hy : LDecl.hyps) =
  { me_unienv    = EcProofTyping.unienv_of_hyps hy;
    me_meta_vars = Mid.empty;
    me_matches   = Mid.empty; }

(* -------------------------------------------------------------------- *)
let menv_add_form x ty menv =
  assert (not (Mid.mem x menv.me_meta_vars));
  { menv with
      me_meta_vars = Mid.add x (OGTty (Some ty)) menv.me_meta_vars; }

(* -------------------------------------------------------------------- *)
let menv_add_mem x menv =
  assert (not (Mid.mem x menv.me_meta_vars));
  { menv with
      me_meta_vars = Mid.add x (OGTmem None) menv.me_meta_vars; }

(* -------------------------------------------------------------------------- *)
let saturate (me : match_env) =
  let ue    = me.me_unienv in
  let mtch  = me.me_matches in
  let sty   = { EcTypes.ty_subst_id with ts_u = EcUnify.UniEnv.assubst ue } in
  let subst = { ps_patloc = mtch; ps_sty = sty } in
  let seen  = ref Sid.empty in

  let rec for_ident id value subst =
    if Sid.mem id !seen then subst else begin
        seen := Sid.add id !seen;
        let subst =
          Mid.fold2_inter (fun x bdx _ -> for_ident x bdx)
            subst.ps_patloc (pat_fv value) subst in
        { subst with
          ps_patloc =
            Mid.add id (Psubst.p_subst ~meta:false subst value) subst.ps_patloc }
      end
  in
  let subst = Mid.fold_left (fun acc x bd -> for_ident x bd acc)
                subst subst.ps_patloc in
  { me with me_matches = subst.ps_patloc }

let psubst_of_menv env =
  let sty   = { EcTypes.ty_subst_id with
                ts_u = EcUnify.UniEnv.assubst env.me_unienv } in
  { ps_patloc = env.me_matches; ps_sty = sty }

let e_copy e = { e with e_env = env_copy e.e_env }

let zor e = function
  | [] -> e
  | l ->
     match e.e_continuation with
     | Zor (c, l1, ne) ->
        { e with e_continuation = Zor (c, l1 @ (List.map e_copy l), ne) }
     | c ->
        let ne = e_copy e in
        let ne = { ne_env = ne.e_env ;
                   ne_continuation = ne.e_continuation; } in
        { e with e_continuation = Zor (c, List.map e_copy l, ne) }


(* -------------------------------------------------------------------- *)
module Debug : sig
  val debug_h_red_strat              : environment -> pattern -> pattern -> int -> unit
  val debug_h_red_strat_next         : environment -> unit
  val debug_type                     : environment -> ty -> ty -> unit
  val debug_ogty                     : environment -> pattern -> pattern -> bool -> unit
  val debug_bind_restr               : environment -> ident -> unit
  val debug_add_match                : environment -> bool -> ident -> pattern -> unit
  val debug_higher_order_abstract_eq : environment -> bool -> pattern -> pattern -> unit
  val debug_higher_order_to_abstract : environment -> pattern -> pattern -> unit
  val debug_higher_order_is_abstract : environment -> pattern -> pattern -> unit
  val debug_try_match                : environment -> pattern -> pattern -> pat_continuation -> unit
  val debug_which_rule               : environment -> string -> unit
  val debug_result_match             : environment -> ismatch -> unit
  val debug_try_reduce               : environment -> pattern -> pattern -> unit
  val debug_try_conv                 : environment -> pattern -> pattern -> unit
  val debug_reduce                   : environment -> pattern -> pattern -> pattern -> pattern -> bool -> unit
  val debug_reduce_incorrect         : environment -> pattern -> pattern -> unit
  val debug_found_match              : environment -> unit
  val debug_no_match_found           : environment -> unit
  val debug_ignore_ors               : environment -> unit
  val debug_another_or               : environment -> unit
  val debug_different_forms          : environment -> form -> form -> unit
  val debug_try_translate_higher_order : environment -> pattern -> string -> unit
  val debug_begin_match              : environment -> pattern -> pattern -> unit
  val debug_show_pattern             : environment -> pattern -> unit
  val debug_translate_error          : environment -> string -> unit
  val debug_eta_expansion            : environment -> meta_name -> ogty -> unit
  val debug_unienv                   : environment -> unit
  val debug_subst                    : environment -> pattern -> pattern -> unit
  val debug_no_eta                   : environment -> pbinding -> pattern -> bool -> unit
  val debug_show_matches             : environment -> unit
  val debug_add_reduce               : environment -> int -> unit
  val debug_saturate                 : environment -> bool -> unit
end = struct

  let debug_saturate menv is_before =
    if menv.env_verbose.verbose_saturate then
      let env = LDecl.toenv menv.env_hyps in

      if is_before then EcEnv.notify env `Warning "----- try saturate"
      else  EcEnv.notify env `Warning "----- finish saturate"

  let debug_add_reduce menv i =
    if menv.env_verbose.verbose_add_reduce then
      let env = LDecl.toenv menv.env_hyps in
      (* let ppe = EcPrinting.PPEnv.ofenv env in *)

      EcEnv.notify env `Warning "--- add_reduce : %i" i

  let debug_no_eta menv (_id,_ogty) _p _b =
    if menv.env_verbose.verbose_eta then
      let env = LDecl.toenv menv.env_hyps in
      (* let ppe = EcPrinting.PPEnv.ofenv env in *)

      EcEnv.notify env `Warning
        "--- eta could not be applied because of type restrictions"


  let debug_h_red_strat_next menv =
    if menv.env_verbose.verbose_reduce then
      let env = LDecl.toenv menv.env_hyps in
      EcEnv.notify env `Warning "----- next red"

  let debug_h_red_strat menv p1 p2 i =
    if menv.env_verbose.verbose_reduce then
      let env = LDecl.toenv menv.env_hyps in
      let ppe = EcPrinting.PPEnv.ofenv env in

      let pcompat =
        match oget menv.env_red_info_match.EcReduction.logic
        with `Full -> true | `ProductCompat -> false
      in
      let f op args =
        match op_kind op, args with
        | Some (`Not), [_]    when pcompat ->
           EcEnv.notify env `Warning "try to reduce !"
        | Some (`Imp), [_;_] when pcompat ->
           EcEnv.notify env `Warning "try to reduce =>"
        | Some (`Iff), [_;_] when pcompat ->
           EcEnv.notify env `Warning "try to reduce <=>"


        | Some (`And `Asym), [_;_] ->
           EcEnv.notify env `Warning "try to reduce a&&"
        | Some (`Or  `Asym), [_;_] ->
           EcEnv.notify env `Warning "try to reduce a||"
        | Some (`And `Sym ), [_;_] ->
           EcEnv.notify env `Warning "try to reduce &&"
        | Some (`Or  `Sym ), [_;_] ->
           EcEnv.notify env `Warning "try to reduce ||"
        | Some (`Int_le   ), [_;_] ->
           EcEnv.notify env `Warning "try to reduce i <="
        | Some (`Int_lt   ), [_;_] ->
           EcEnv.notify env `Warning "try to reduce i <"
        | Some (`Real_le  ), [_;_] ->
           EcEnv.notify env `Warning "try to reduce r <="
        | Some (`Real_lt  ), [_;_] ->
           EcEnv.notify env `Warning "try to reduce r <"
        | Some (`Int_add  ), [f1;f2] ->
           EcEnv.notify env `Warning "try to reduce i : (%a) + (%a)"
             (EcPrinting.pp_pattern ppe) f1
             (EcPrinting.pp_pattern ppe) f2
        | Some (`Int_opp  ), [_]     ->
           EcEnv.notify env `Warning "try to reduce i -"
        | Some (`Int_mul  ), [_;_] ->
           EcEnv.notify env `Warning "try to reduce i *"
        | Some (`Real_add ), [_;_] ->
           EcEnv.notify env `Warning "try to reduce r +"
        | Some (`Real_opp ), [_]     ->
           EcEnv.notify env `Warning "try to reduce r -"
        | Some (`Real_mul ), [_;_] ->
           EcEnv.notify env `Warning "try to reduce r *"
        | Some (`Real_inv ), [_]     ->
           EcEnv.notify env `Warning "try to reduce inv"
        | Some (`Eq       ), [_;_] ->
           EcEnv.notify env `Warning "try to reduce ="
        | _ ->
           EcEnv.notify env `Warning "try to reduce other"
      in

      match i with
      | 3 -> begin
          match p1.p_node with
          | Pat_Fun_Symbol
                 (Sym_Form_App _, { p_node = Pat_Axiom (Axiom_Op (_, p,_tys,_))} :: args)
               when is_some menv.env_red_info_match.EcReduction.logic
                    && is_logical_op p ->
             f p args;
             EcEnv.notify env `Warning "hr- h_red_strat step %i,%i" i 3
          | _ ->
             EcEnv.notify env `Warning "hr- h_red_strat step %i : %i" i 5;
          match p2.p_node with
          | Pat_Fun_Symbol
                 (Sym_Form_App _, { p_node = Pat_Axiom (Axiom_Op (_, p,_tys,_))} :: args)
               when is_some menv.env_red_info_match.EcReduction.logic
                    && is_logical_op p ->
             f p args;
             EcEnv.notify env `Warning "hr- h_red_strat step %i,%i" i 4
          | _ ->
             EcEnv.notify env `Warning "hr- h_red_strat step %i : %i" i 6

        end
      | _ ->
         EcEnv.notify env `Warning "hr- h_red_strat step %i" i


  let debug_subst menv p1 p2 =
    if menv.env_verbose.verbose_subst then
      let env = LDecl.toenv menv.env_hyps in
      let ppe = EcPrinting.PPEnv.ofenv env in

      EcEnv.notify env `Warning "-s- Subst : %a -> %a"
        (EcPrinting.pp_pattern ppe) p1
        (EcPrinting.pp_pattern ppe) p2

  let debug_eta_expansion menv i t =
    if menv.env_verbose.verbose_type then
      let env = LDecl.toenv menv.env_hyps in
      let ppe = EcPrinting.PPEnv.ofenv env in

      let p = p_quant Llambda [i,t] (meta_var (EcIdent.create "") None OGTany) in
      let f = match t with
        | OGTty (Some t) -> f_quant Llambda [i,GTty t] (f_local (EcIdent.create "") t)
        | _ -> f_local (EcIdent.create "no type") tbool in

      EcEnv.notify env `Warning "--! Eta-expansion with bindings : %a != %a"
        (EcPrinting.pp_pattern ppe) p
        (EcPrinting.pp_form ppe) f

  let debug_translate_error menv s =
    if menv.env_verbose.verbose_type then
      let env = LDecl.toenv menv.env_hyps in

      EcEnv.notify env `Warning "--! Translate error %s" s

  let debug_show_pattern menv p =
    if menv.env_verbose.verbose_type then
      let env = LDecl.toenv menv.env_hyps in
      let ppe = EcPrinting.PPEnv.ofenv env in

      EcEnv.notify env `Warning
        "### pattern is %a"
        (EcPrinting.pp_pattern ppe) p

  let debug_type menv ty1 ty2 =
    if menv.env_verbose.verbose_type then
      let env = LDecl.toenv menv.env_hyps in
      let ppe = EcPrinting.PPEnv.ofenv env in

      EcEnv.notify env `Warning
        "-ty %a ?= %a"
        (EcPrinting.pp_type ppe) ty1
        (EcPrinting.pp_type ppe) ty2

  let debug_ogty menv p1 p2 b =
    if menv.env_verbose.verbose_type then
      let env = LDecl.toenv menv.env_hyps in
      let ppe = EcPrinting.PPEnv.ofenv env in

      let s = psubst_of_menv menv.env_match in
      let s = Psubst.p_subst_init ~sty:s.Psubst.ps_sty () in
      let p1 = Psubst.p_subst s p1 in

      EcEnv.notify env `Warning
        "--- ogty: %a %s %a"
        (EcPrinting.pp_ogty ppe) p1.p_ogty
        (if b then "=" else "!=")
        (EcPrinting.pp_ogty ppe) p2.p_ogty

  let debug_bind_restr menv x =
    if menv.env_verbose.verbose_bind_restr then
      let env = LDecl.toenv menv.env_hyps in
      let ppe = EcPrinting.PPEnv.ofenv env in

      EcEnv.notify env `Warning
        "Binding restrictions prevents using : %a"
        (EcPrinting.pp_local ppe) x

  let debug_add_match menv b name p =
    if menv.env_verbose.verbose_add_meta then
      let env = LDecl.toenv menv.env_hyps in
      let ppe = EcPrinting.PPEnv.ofenv env in

      if b then
        EcEnv.notify env `Warning
          "--- Name %a binded to %a"
          (EcPrinting.pp_local ppe) name
          (EcPrinting.pp_pattern ppe) p
      else
        EcEnv.notify env `Warning
          "-!- Name %a already exists and cannot be unified with %a"
          (EcPrinting.pp_local ppe) name
          (EcPrinting.pp_pattern ppe) p

  let debug_higher_order_abstract_eq menv b p1 p2 =
    if menv.env_verbose.verbose_abstract then
      let env = LDecl.toenv menv.env_hyps in
      let ppe = EcPrinting.PPEnv.ofenv env in

      if b then
        EcEnv.notify env `Warning
          "--- %a is convertible to %a\n"
          (EcPrinting.pp_pattern ppe) p1
          (EcPrinting.pp_pattern ppe) p2
      else
        EcEnv.notify env `Warning
          "-!- %a is not convertible to %a\n"
          (EcPrinting.pp_pattern ppe) p1
          (EcPrinting.pp_pattern ppe) p2

  let debug_unienv menv =
    if menv.env_verbose.verbose_unienv then
      let env = LDecl.toenv menv.env_hyps in
      let ppe = EcPrinting.PPEnv.ofenv env in

      let vars = EcUnify.UniEnv.uvars menv.env_match.me_unienv in
      let vars = EcUid.Suid.elements vars in
      let s = EcUnify.UniEnv.assubst menv.env_match.me_unienv in

      let pp_names ppe fmt name =
        match s name with
        | Some t ->
           Format.fprintf fmt "%a <- %a"
             (EcPrinting.pp_tyunivar ppe) name
             (EcPrinting.pp_type ppe) t
        | None ->
           Format.fprintf fmt "%a : not unified"
             (EcPrinting.pp_tyunivar ppe) name
      in

      EcEnv.notify env `Warning "Unienv: %a"
        (EcPrinting.pp_list "@ and@ " (pp_names ppe)) vars

  let debug_show_matches menv =
    if menv.env_verbose.verbose_show_match then
      let env = LDecl.toenv menv.env_hyps in
      let ppe = EcPrinting.PPEnv.ofenv env in

      let pp_names ppe fmt (name,p) =
        Format.fprintf fmt "%a <- (%a : %a)"
          (EcPrinting.pp_local ppe) name
          (EcPrinting.pp_pattern ppe) p
          (EcPrinting.pp_ogty ppe) p.p_ogty in

      EcEnv.notify env `Warning "Current matching: %a"
        (EcPrinting.pp_list "@ and@ " (pp_names ppe))
        (Mid.bindings menv.env_match.me_matches);
      debug_unienv menv

  let debug_higher_order_to_abstract menv p1 p2 =
    if menv.env_verbose.verbose_abstract then
      let env = LDecl.toenv menv.env_hyps in
      let ppe = EcPrinting.PPEnv.ofenv env in

      EcEnv.notify env `Warning
        "try to abstract (%a) in : %a"
        (EcPrinting.pp_pattern ppe) p1
        (EcPrinting.pp_pattern ppe) p2

  let debug_higher_order_is_abstract menv p1 p2 =
    if menv.env_verbose.verbose_abstract then
      let env = LDecl.toenv menv.env_hyps in
      let ppe = EcPrinting.PPEnv.ofenv env in

      EcEnv.notify env `Warning
        "Abstracted (%a) in : %a"
        (EcPrinting.pp_pattern ppe) p1
        (EcPrinting.pp_pattern ppe) p2

  let debug_try_translate_higher_order menv p s  =
    if menv.env_verbose.verbose_abstract then
      let env = LDecl.toenv menv.env_hyps in
      let ppe = EcPrinting.PPEnv.ofenv env in

      EcEnv.notify env `Warning
        "Try to translate to form (%s) : %a" s
        (EcPrinting.pp_pattern ppe) p

  let rec compute_zands c = function
    | ZTop -> c
    | Zor (ct,_,_) -> compute_zands c ct
    | Zand (_,l,ct) -> compute_zands (c + List.length l) ct
    | Znamed (_,_,_,ct) -> compute_zands c ct
    | Zreduce (ct,_,_) -> compute_zands c ct
    | Zconv (ct,_,_) -> compute_zands c ct

  let debug_try_match menv p a c =
    if menv.env_verbose.verbose_match then
      let env = LDecl.toenv menv.env_hyps in
      let ppe = EcPrinting.PPEnv.ofenv env in

      EcEnv.notify env `Warning
        "---- (%i) try match : %a : %a"
        (compute_zands 0 c)
        (EcPrinting.pp_pattern ppe) p
        (EcPrinting.pp_ogty ppe) p.p_ogty;

      EcEnv.notify env `Warning "---- with %a : %a"
        (EcPrinting.pp_pattern ppe) a
        (EcPrinting.pp_ogty ppe) a.p_ogty

  let debug_which_rule menv s =
    if menv.env_verbose.verbose_rule then
      let env = LDecl.toenv menv.env_hyps in

      EcEnv.notify env `Warning "rule %s" s

  let debug_result_match menv m =
    if menv.env_verbose.verbose_match then
      let env = LDecl.toenv menv.env_hyps in

      EcEnv.notify env `Warning (match m with
                                 | Match -> "Match"
                                 | NoMatch -> "No match")

  let debug_try_reduce menv p a =
    if menv.env_verbose.verbose_reduce then
      let env = LDecl.toenv menv.env_hyps in
      let ppe = EcPrinting.PPEnv.ofenv env in

      EcEnv.notify env `Warning "Later : try reduce (%a,%a)"
        (EcPrinting.pp_pattern ppe) p
        (EcPrinting.pp_pattern ppe) a

  let debug_try_conv menv p a =
    if menv.env_verbose.verbose_conv then
      let env = LDecl.toenv menv.env_hyps in
      let ppe = EcPrinting.PPEnv.ofenv env in

      EcEnv.notify env `Warning "Later : try conv (%a,%a)"
        (EcPrinting.pp_pattern ppe) p
        (EcPrinting.pp_pattern ppe) a

  let debug_reduce menv p1 p2 a1 a2 b =
    if menv.env_verbose.verbose_reduce then
      let env = LDecl.toenv menv.env_hyps in
      let ppe = EcPrinting.PPEnv.ofenv env in

      if b then begin
          EcEnv.notify env `Warning "Reduction (%s beta, %s delta):"
            (if menv.env_red_info_match.EcReduction.beta then "with" else "without")
            (if menv.env_red_info_match.EcReduction.delta_p (EcPath.psymbol "toto")
             then "with" else "without");
          EcEnv.notify env `Warning "***1: before %a"
            (EcPrinting.pp_pattern ppe) p1;
          EcEnv.notify env `Warning "***1: after  %a"
            (EcPrinting.pp_pattern ppe) p2;
          EcEnv.notify env `Warning "***2: before %a"
            (EcPrinting.pp_pattern ppe) a1
        end
      else begin
          EcEnv.notify env `Warning "Ignore reduction (%s beta, %s delta):"
            (if menv.env_red_info_match.EcReduction.beta then "with" else "without")
            (if menv.env_red_info_match.EcReduction.delta_p (EcPath.psymbol "toto")
             then "with" else "without");
          EcEnv.notify env `Warning "***1: before %a"
            (EcPrinting.pp_pattern ppe) p1
        end;
      EcEnv.notify env `Warning "***2: after  %a"
        (EcPrinting.pp_pattern ppe) a2;
      debug_show_matches menv

  let debug_reduce_incorrect menv p a =
    if menv.env_verbose.verbose_reduce then
      let env = LDecl.toenv menv.env_hyps in
      let ppe = EcPrinting.PPEnv.ofenv env in

      EcEnv.notify env `Warning "Incorrect reduction for (%a,%a)"
        (EcPrinting.pp_pattern ppe) p
        (EcPrinting.pp_pattern ppe) a

  let debug_found_match menv =
    if menv.env_verbose.verbose_match then
      let env = LDecl.toenv menv.env_hyps in
      let ppe = EcPrinting.PPEnv.ofenv env in

      let pp_names ppe fmt (name,p) =
        Format.fprintf fmt "%a <- (%a : %a)"
          (EcPrinting.pp_local ppe) name
          (EcPrinting.pp_pattern ppe) p
          (EcPrinting.pp_ogty ppe) p.p_ogty in

      EcEnv.notify env `Warning "Matching successful: %a"
        (EcPrinting.pp_list "@ and@ " (pp_names ppe))
        (Mid.bindings menv.env_match.me_matches);
      debug_unienv menv

  let debug_no_match_found menv =
    if menv.env_verbose.verbose_match then
      let env = LDecl.toenv menv.env_hyps in

      EcEnv.notify env `Warning
        "--- Matching unsuccessful"

  let debug_ignore_ors menv =
    if menv.env_verbose.verbose_show_ignored_or then
      let env = LDecl.toenv menv.env_hyps in

      EcEnv.notify env `Warning "Ignore some Or"

  let debug_another_or menv =
    if menv.env_verbose.verbose_show_or then
      let env = LDecl.toenv menv.env_hyps in

      EcEnv.notify env `Warning "Another Or's case"

  let debug_different_forms menv f1 f2 =
    if menv.env_verbose.verbose_match then
      let env = LDecl.toenv menv.env_hyps in
      let ppe = EcPrinting.PPEnv.ofenv env in

      EcEnv.notify env `Warning "form(%a : %a) != form(%a : %a)"
          (EcPrinting.pp_form ppe) f1
          (EcPrinting.pp_type ppe) f1.f_ty
          (EcPrinting.pp_form ppe) f2
          (EcPrinting.pp_type ppe) f2.f_ty

  let debug_begin_match menv p a =
    if menv.env_verbose.verbose_begin_match then
      let env = LDecl.toenv menv.env_hyps in
      let ppe = EcPrinting.PPEnv.ofenv env in

      EcEnv.notify env `Warning
        "========================= Begin new match ===========================";

      EcEnv.notify env `Warning "=== %a"
        (EcPrinting.pp_pattern ppe) p;

      EcEnv.notify env `Warning "=== %a ==="
        (EcPrinting.pp_pattern ppe) a

end


let saturate env =
  (* Debug.debug_saturate env true;
   * Debug.debug_show_matches env; *)
  let env = { env with env_match = saturate env.env_match } in
  (* Debug.debug_show_matches env;
   * Debug.debug_saturate env false; *)
  env

(* -------------------------------------------------------------------------- *)

let my_mem = EcIdent.create "new_mem"

let form_of_expr = EcFol.form_of_expr my_mem

let suffix2 (l1 : 'a list) (l2 : 'b list) : ('a list * 'a list) * ('b list * 'b list) =
  let (l12,l11), (l22,l21) = List.prefix2 (List.rev l1) (List.rev l2) in
  (List.rev l11,List.rev l12), (List.rev l21,List.rev l22)

let mem_ty_univar (ty : ty) =
  try ty_check_uni ty; true
  with
  | FoundUnivar -> false


let is_modty (env : EcEnv.env) (m : mpath) (mt : module_type) (mr : mod_restr) =
  let ms = EcEnv.Mod.by_mpath_opt m env in
  match ms with
  | None -> false
  | Some ms ->
    let ms = ms.me_sig in
    try EcTyping.check_modtype_with_restrictions env m ms mt mr; true
    with EcTyping.TymodCnvFailure _ -> false

(* -------------------------------------------------------------------------- *)
module Translate = struct

  exception Invalid_Type of string

  let rec form_of_pattern env (p : pattern) =
    match p.p_node with
    | Pat_Meta_Name (Some p,_,_) -> form_of_pattern env p
    | Pat_Meta_Name (_,_,_)   -> raise (Invalid_Type "formula")
    | Pat_Sub _               -> raise (Invalid_Type "sub in form")
    | Pat_Or [p]              -> form_of_pattern env p
    | Pat_Or _                -> raise (Invalid_Type "formula")
    | Pat_Red_Strat (p,_)     -> form_of_pattern env p
    | Pat_Axiom (Axiom_Int z) -> f_int z
    | Pat_Axiom (Axiom_Local (id,ty)) -> f_local id ty
    | Pat_Axiom (Axiom_Op (_, op,lty, Some ty)) -> f_op op lty ty
    | Pat_Axiom _             -> raise (Invalid_Type "formula : other axiom")
    | Pat_Stmt _              -> raise (Invalid_Type "formula : stmt")
    | Pat_Fun_Symbol (s, lp)  ->
       match s, lp with
       | Sym_Form_If, [p1;p2;p3]   -> f_if (form_of_pattern env p1)
                                        (form_of_pattern env p2)
                                        (form_of_pattern env p3)
       | Sym_Form_App _, p::lp    -> f_ty_app env (form_of_pattern env p)
                                       (List.map (form_of_pattern env) lp)
       | Sym_Form_Tuple, t         -> f_tuple (List.map (form_of_pattern env) t)
       | Sym_Form_Proj (i,ty), [p] -> f_proj (form_of_pattern env p) i ty
       | Sym_Form_Match ty, p::lp  -> mk_form (Fmatch (form_of_pattern env p,
                                                       List.map (form_of_pattern env) lp,
                                                       ty)) ty
       | Sym_Form_Let lp, [p1;p2]  -> f_let lp (form_of_pattern env p1)
                                        (form_of_pattern env p2)
       | Sym_Form_Pvar ty, [pv;pm] -> f_pvar (prog_var_of_pattern env pv) ty
                                        (memory_of_pattern pm)
       | Sym_Form_Prog_var _, _    -> raise (Invalid_Type "formula : prog_var")
       | Sym_Form_Glob, [mp;mem]   -> f_glob (mpath_of_pattern env mp) (memory_of_pattern mem)
       | Sym_Form_Hoare_F, [pr;xp;po] ->
          f_hoareF (form_of_pattern env pr) (xpath_of_pattern env xp) (form_of_pattern env po)
       | Sym_Form_Hoare_S, [pm;pr;s;po] ->
          f_hoareS (memenv_of_pattern pm) (form_of_pattern env pr) (stmt_of_pattern env s)
            (form_of_pattern env po)
       | Sym_Form_bd_Hoare_F, [pr;xp;po;cmp;bd] ->
          f_bdHoareF (form_of_pattern env pr) (xpath_of_pattern env xp) (form_of_pattern env po)
            (cmp_of_pattern cmp) (form_of_pattern env bd)
       | Sym_Form_bd_Hoare_S, [pm;pr;s;po;cmp;bd] ->
          f_bdHoareS (memenv_of_pattern pm) (form_of_pattern env pr) (stmt_of_pattern env s)
            (form_of_pattern env po) (cmp_of_pattern cmp) (form_of_pattern env bd)
       | Sym_Form_Equiv_F, [pr;f1;f2;po] ->
          f_equivF (form_of_pattern env pr) (xpath_of_pattern env f1) (xpath_of_pattern env f2)
            (form_of_pattern env po)
       | Sym_Form_Equiv_S, [pm1;pm2;pr;s1;s2;po] ->
          f_equivS (memenv_of_pattern pm1) (memenv_of_pattern pm2) (form_of_pattern env pr)
            (stmt_of_pattern env s1) (stmt_of_pattern env s2) (form_of_pattern env po)
       | Sym_Form_Eager_F, [po;s1;f1;f2;s2;pr] ->
          f_eagerF (form_of_pattern env po) (stmt_of_pattern env s1) (xpath_of_pattern env f1)
            (xpath_of_pattern env f2) (stmt_of_pattern env s2) (form_of_pattern env pr)
       | Sym_Form_Pr, [pm;f;args;event] ->
          f_pr (memory_of_pattern pm) (xpath_of_pattern env f) (form_of_pattern env args)
            (form_of_pattern env event)
       | Sym_Quant (q,pb), [p] ->
          let f (id,ogt) = match gty_of_ogty ogt with
            | Some gty -> id, gty
            | _        -> raise (Invalid_Type "formula : quant binds")
          in
          f_quant q (List.map f pb) (form_of_pattern env p)
       | _ -> raise (Invalid_Type "formula : other fun symbol")

  and memory_of_pattern p = match p.p_node with
    | Pat_Axiom (Axiom_Memory m) -> m
    | _ -> raise (Invalid_Type "memory")

  and prog_var_of_pattern env p = match p.p_node with
    | Pat_Axiom (Axiom_Prog_Var pv) -> pv
    | Pat_Fun_Symbol (Sym_Form_Prog_var k, [xp]) ->
       pv (xpath_of_pattern env xp) k
    | _ -> raise (Invalid_Type "prog_var")

  and xpath_of_pattern env p = match p.p_node with
    | Pat_Axiom (Axiom_Xpath xp) -> xp
    | Pat_Fun_Symbol (Sym_Xpath, [mp;p]) ->
       EcPath.xpath (mpath_of_pattern env mp) (path_of_pattern p)
    | _ -> raise (Invalid_Type "xpath")

  and path_of_pattern p = match p.p_node with
    | Pat_Axiom (Axiom_Op (_, p,[],_)) -> p
    | _ -> raise (Invalid_Type "path")

  and mpath_of_pattern env p = match p.p_node with
    | Pat_Axiom (Axiom_Mpath mp) -> mp
    | Pat_Fun_Symbol (Sym_Mpath, mp::margs) ->
       mpath (mpath_top_of_pattern env mp) (List.map (mpath_of_pattern env) margs)
    | _ -> raise (Invalid_Type "mpath")

  and mpath_top_of_pattern _env p = match p.p_node with
    | Pat_Axiom (Axiom_Mpath_top m) -> m
    | _ -> raise (Invalid_Type "mpath_top")

  and memenv_of_pattern p = match p.p_node with
    | Pat_Axiom (Axiom_MemEnv m) -> m
    | _ -> raise (Invalid_Type "memenv")

  and stmt_of_pattern env p = match p.p_node with
    | Pat_Stmt g -> stmt (list_of_gen_pattern env g)
    | _ -> raise (Invalid_Type "stmt")

  and list_of_gen_pattern env g = match g with
    | Anchor _     -> []
    | Any          -> raise (Invalid_Type "gen_stmt : any")
    | Base p       -> instr_of_pattern env p
    | Choice [g]   -> list_of_gen_pattern env g
    | Choice _     -> raise (Invalid_Type "gen_stmt : choice")
    | Named (g, _) -> list_of_gen_pattern env g
    | Repeat _     -> raise (Invalid_Type "gen_stmt : repeat")
    | Seq l        -> List.flatten (List.map (list_of_gen_pattern env) l)

  and instr_of_pattern env p = match p.p_node with
    | Pat_Fun_Symbol (Sym_Instr_Assign, [lv;e]) ->
       [i_asgn (lvalue_of_pattern env lv, expr_of_pattern env e)]
    | Pat_Fun_Symbol (Sym_Instr_Sample, [lv;e]) ->
       [i_rnd  (lvalue_of_pattern env lv, expr_of_pattern env e)]
    | Pat_Fun_Symbol (Sym_Instr_Call, [f;args]) ->
       let args = match args.p_node with
         | Pat_Fun_Symbol (Sym_Form_Tuple, lp) -> lp
         | _ -> [args] in
       [i_call (None, xpath_of_pattern env f, List.map (expr_of_pattern env) args)]
    | Pat_Fun_Symbol (Sym_Instr_If, [cond;s1;s2]) ->
       [i_if (expr_of_pattern env cond, stmt_of_pattern env s1, stmt_of_pattern env s2)]
    | Pat_Fun_Symbol (Sym_Instr_While, [cond;s]) ->
       [i_while (expr_of_pattern env cond, stmt_of_pattern env s)]
    | Pat_Fun_Symbol (Sym_Instr_Assert, [e]) ->
       [i_assert (expr_of_pattern env e)]
    | Pat_Stmt g -> list_of_gen_pattern env g
    | _ -> raise (Invalid_Type "instr")

  and lvalue_of_pattern env p =
    match p.p_ogty with
    | OGTlv -> begin
        match p.p_node with
        | Pat_Axiom (Axiom_Lvalue lv) -> lv
        | Pat_Fun_Symbol (Sym_Form_Tuple, t) ->
           let t = List.map (lvalue_of_pattern env) t in
           let t = List.map (function LvVar (x,t) -> (x,t)
                                    | _ -> raise (Invalid_Type "lvalue tuple")) t in
           LvTuple t
        | _ -> raise (Invalid_Type "lvalue")
      end
    | _ -> raise (Invalid_Type "lvalue")

  and expr_of_pattern env p =
    try match expr_of_form (form_of_pattern env p) with
        | Some e -> e
        | None -> raise (Invalid_Type "expr from form")
    with
    | Invalid_Type s -> raise (Invalid_Type (String.concat " in " [s;"expr"]))

  and cmp_of_pattern p = match p.p_node with
    | Pat_Axiom (Axiom_Hoarecmp cmp) -> cmp
    | _ -> raise (Invalid_Type "hoarecmp")

  let form_of_pattern env p =
    match p.p_node with
    | Pat_Sub p -> begin
        try form_of_pattern env p with
        | Invalid_Type "sub in form" -> assert false
      end
    | _ -> form_of_pattern env p

end

(* let simplify env p =
 *   try pat_form (Translate.form_of_pattern (LDecl.toenv env.env_hyps) p)
 *   with Translate.Invalid_Type s ->
 *     Debug.debug_translate_error env s;
 *     p *)


module EQ : sig
  val ty        : environment -> ty -> ty -> bool
  val memtype   : environment -> EcMemory.memtype -> EcMemory.memtype -> bool
  val memory    : environment -> EcMemory.memory -> EcMemory.memory -> bool
  val memenv    : environment -> EcMemory.memenv -> EcMemory.memenv -> bool
  val mpath     : environment -> mpath -> mpath -> bool
  val mpath_top : environment -> mpath_top -> mpath_top -> bool
  val xpath     : environment -> xpath -> xpath -> bool
  val name      :                meta_name -> meta_name -> bool
  val instr     : environment -> instr -> instr -> bool
  val stmt      : environment -> stmt -> stmt -> bool
  val lvalue    : environment -> lvalue -> lvalue -> bool
  val op        : environment -> path * ty list -> path * ty list -> bool
  val prog_var  : environment -> prog_var -> prog_var -> bool
  val hoarecmp  : environment -> hoarecmp -> hoarecmp -> bool
  val gty       : environment -> gty -> gty -> bool
  val ogty      : environment -> ogty -> ogty -> bool
  val binding   : environment -> binding -> binding -> bool
  val pbinding  : environment -> pbinding -> pbinding -> bool
  val symbol    : environment -> fun_symbol -> fun_symbol -> bool
  (* val form      : environment -> EcReduction.reduction_info -> form -> form -> bool *)
  val axiom     : environment -> EcReduction.reduction_info -> axiom -> axiom -> bool
  val pattern   : environment -> EcReduction.reduction_info -> pattern -> pattern -> bool
end = struct
  let rec ty (env : environment) (ty1 : ty) (ty2 : ty) : bool =
    try EcUnify.unify (EcEnv.LDecl.toenv env.env_hyps) env.env_match.me_unienv ty1 ty2;
        true
    with EcUnify.UnificationFailure _ -> false

  let memtype (_env : environment) (m1 : EcMemory.memtype) (m2 : EcMemory.memtype) =
    EcMemory.mt_equal m1 m2

  let memory (_env : environment) (m1 : EcMemory.memory) (m2 : EcMemory.memory) =
    EcMemory.mem_equal m1 m2

  let memenv (_env : environment) (m1 : EcMemory.memenv) (m2 : EcMemory.memenv) =
    EcMemory.me_equal m1 m2

  let mpath (env : environment) (m1 : mpath) (m2 : mpath) : bool =
    EcReduction.EqTest.for_mp (EcEnv.LDecl.toenv env.env_hyps) m1 m2

  let mpath_top (_env : environment) (mt1 : mpath_top) (mt2 : mpath_top) =
    EcPath.mt_equal mt1 mt2

  let xpath (env : environment) (x1 : xpath) (x2 : xpath) : bool =
    EcReduction.EqTest.for_xp (EcEnv.LDecl.toenv env.env_hyps) x1 x2

  let name (n1 : meta_name) (n2 : meta_name) = 0 = id_compare n1 n2

  let instr (env : environment) (i1 : EcModules.instr) (i2 : EcModules.instr) =
    EcReduction.EqTest.for_instr (EcEnv.LDecl.toenv env.env_hyps) i1 i2

  let stmt (env : environment) (s1 : EcModules.stmt) (s2 : EcModules.stmt) =
    EcReduction.EqTest.for_stmt (EcEnv.LDecl.toenv env.env_hyps) s1 s2

  let lvalue (_env : environment) (lv1 : lvalue) (lv2 :lvalue) : bool =
    lv_equal lv1 lv2

  let op (env : environment)
        ((op1, lty1) : EcPath.path * EcTypes.ty list)
        ((op2, lty2) : EcPath.path * EcTypes.ty list) =
    EcPath.p_equal op1 op2 && List.for_all2 (ty env) lty1 lty2

  let prog_var (env : environment) (x1 : prog_var) (x2 : prog_var) =
    pv_equal x1 x2 || (x1.pv_kind = x2.pv_kind && xpath env x1.pv_name x2.pv_name)

  let hoarecmp (_env : environment) (c1 : hoarecmp) (c2 : hoarecmp) : bool =
    c1 = c2

  let gty (env : environment) (gty1 : gty) (gty2 : gty) : bool =
    match gty1, gty2 with
    | GTty ty1, GTty ty2 -> ty env ty1 ty2
    | _,_ -> EcCoreFol.gty_equal gty1 gty2

  let ogty (env : environment) (gty1 : ogty) (gty2 : ogty) : bool =
    match gty1, gty2 with
    | OGTty (Some ty1), OGTty (Some ty2) -> ty env ty1 ty2
    | _,_ -> ogty_equal gty1 gty2

  let binding env (id1,gt1) (id2,gt2) =
    if not (id_equal id1 id2) then false
    else gty env gt1 gt2

  let pbinding env (id1,ogt1) (id2,ogt2) =
    id_equal id1 id2 && ogty env ogt1 ogt2

  let symbol (env : environment) (s1 : fun_symbol) (s2 : fun_symbol) : bool =
    match s1,s2 with
    | Sym_Form_Proj (i1,t1), Sym_Form_Proj (i2,t2) ->
       if not (i1 = i2) then false
       else ty env t1 t2
    | Sym_Form_Pvar t1, Sym_Form_Pvar t2
      | Sym_Form_App (Some t1, _), Sym_Form_App (Some t2, _)
      | Sym_Form_Match t1, Sym_Form_Match t2 -> ty env t1 t2
    | Sym_Form_Let lp1, Sym_Form_Let lp2 -> lp_equal lp1 lp2
    | Sym_Form_Prog_var k1, Sym_Form_Prog_var k2 -> k1 = k2
    | Sym_Quant (q1,b1), Sym_Quant (q2,b2) ->
       if not (q1 = q2) then false
       else List.for_all2 (pbinding env) b1 b2
    | _,_ -> s1 = s2

  let form (env : environment) ri (f1 : form) (f2 : form) =
    if ty env f1.f_ty f2.f_ty then begin
      Debug.debug_type env f1.f_ty f2.f_ty;
      let sty    = { EcTypes.ty_subst_id with
                     ts_u = EcUnify.UniEnv.assubst env.env_match.me_unienv } in
      let sf     = Fsubst.f_subst_init ~sty () in
      let f1, f2 = Fsubst.f_subst sf f1, Fsubst.f_subst sf f2 in
      if EcReduction.is_conv_param ri env.env_hyps f1 f2 then true
      else begin Debug.debug_different_forms env f1 f2; false end
      end
    else false

  let rec axiom (env : environment) _ (o1 : axiom) (o2 : axiom) : bool =
    let aux o1 o2 =
      match o1,o2 with
      | Axiom_Int f1, Axiom_Int f2 ->
         EcBigInt.equal f1 f2
      | Axiom_Memory m1, Axiom_Memory m2 ->
         memory env m1 m2
      | Axiom_MemEnv m1, Axiom_MemEnv m2 ->
         memenv env m1 m2
      | Axiom_Prog_Var x1, Axiom_Prog_Var x2 ->
         prog_var env x1 x2
      | Axiom_Op (_, op1, lty1, Some t1), Axiom_Op (_, op2, lty2, Some t2) ->
         ty env t1 t2 && op env (op1,lty1) (op2,lty2)
      | Axiom_Mpath_top m1, Axiom_Mpath_top m2 ->
         mpath_top env m1 m2
      | Axiom_Mpath m1, Axiom_Mpath m2 ->
         mpath env m1 m2
      | Axiom_Mpath { m_top = mt1 ; m_args = [] }, Axiom_Mpath_top mt2
        | Axiom_Mpath_top mt1, Axiom_Mpath { m_top = mt2 ; m_args = [] } ->
         mpath_top env mt1 mt2
      | Axiom_Lvalue lv1, Axiom_Lvalue lv2 ->
         lvalue env lv1 lv2
      | Axiom_Xpath x1, Axiom_Xpath x2 ->
         xpath env x1 x2
      | Axiom_Hoarecmp c1, Axiom_Hoarecmp c2 ->
         hoarecmp env c1 c2
      | Axiom_Local (id1,ty1), Axiom_Local (id2,ty2) ->
         if ty env ty1 ty2 then name id1 id2 else false
      | _,_ -> false
    in
    aux o1 o2

  and pattern (env : environment) ri (p1 : pattern) (p2 : pattern) : bool =
    let try_translate_eq eq trans p1 p2 =
      try  eq (trans p1) (trans p2)
      with Translate.Invalid_Type _ -> false in

       (try_translate_eq (form env ri)
          (Translate.form_of_pattern (EcEnv.LDecl.toenv env.env_hyps)) p1 p2)
    || (try_translate_eq (memory env)
          Translate.memory_of_pattern p1 p2)
    || (try_translate_eq (mpath env)
          (Translate.mpath_of_pattern (EcEnv.LDecl.toenv env.env_hyps)) p1 p2)
    ||
      match p1.p_node, p2.p_node with
      | Pat_Red_Strat (p1,red1), Pat_Red_Strat (p2,red2) ->
         if red1 == red2 then pattern env ri p1 p2 else false
      | Pat_Or lp1, Pat_Or lp2 ->
         List.for_all2 (pattern env ri) lp1 lp2
      | Pat_Sub p1, Pat_Sub p2 -> pattern env ri p1 p2
      | Pat_Axiom a1, Pat_Axiom a2 ->
         axiom env ri a1 a2
      | Pat_Fun_Symbol (s1, lp1), Pat_Fun_Symbol (s2, lp2) ->
         if symbol env s1 s2 then List.for_all2 (pattern env ri) lp1 lp2
         else false
      | Pat_Meta_Name (p1,n1,b1), Pat_Meta_Name (p2,n2,b2) ->
         if not (name n1 n2) then false
         else
           let eq = match b1, b2 with
             | Some b1, Some b2 -> List.for_all2 (pbinding env) b1 b2
             | _                -> true in
           if eq then
             match p1, p2 with
             | Some p1, Some p2 -> pattern env ri p1 p2
             | _ -> true
           else false
      | Pat_Meta_Name (_,n1,_), _ -> begin
          match Mid.find_opt n1 (saturate env).env_match.me_matches with
          | Some p1' ->
             if pattern env ri p1 p1' then false
             else pattern env ri p1' p2
          | None -> false
        end
      | _, Pat_Meta_Name (_,n2,_) -> begin
          match Mid.find_opt n2 (saturate env).env_match.me_matches with
          | Some p2' ->
             if pattern env ri p2 p2' then false
             else pattern env ri p1 p2'
          | None -> false
        end
      | Pat_Axiom a, Pat_Fun_Symbol (s,lp)
        | Pat_Fun_Symbol (s,lp), Pat_Axiom a -> begin
          match s, lp, a with

          | Sym_Form_Prog_var k1, [p1],
            Axiom_Prog_Var { pv_name = xp ; pv_kind = k2 } when k1 = k2 ->
             pattern env ri p1 (pat_xpath xp)

          | Sym_Xpath, [mp1;p1],
            Axiom_Xpath { x_top = mp2; x_sub = p2 } ->
             pattern env ri p1 (pat_op p2 [] None)
             && pattern env ri mp1 (pat_mpath mp2)

          | Sym_Mpath, [m1], Axiom_Mpath _ ->
             pattern env ri m1 p2

          | Sym_Mpath, [mtop1], Axiom_Mpath_top _ ->
             pattern env ri mtop1 p2

          | Sym_Mpath, mtop1::margs1,
            Axiom_Mpath { m_top = mtop2; m_args = margs2 } ->
             let (margs11,margs12), (margs21,margs22) = suffix2 margs1 margs2 in
             let mtop1 = p_mpath mtop1 margs11 in
             let mtop2 = if margs21 = [] then pat_mpath_top mtop2
                         else pat_mpath (EcPath.mpath mtop2 margs21) in
             List.for_all2 (pattern env ri) (mtop1::margs12)
               (mtop2::(List.map pat_mpath margs22))

          | Sym_Mpath, _, _ -> false

          | _ -> false

        end
      | _, _ -> false

end

(* -------------------------------------------------------------------------- *)
let get_ty = function
  | OGTty (Some ty) -> ty
  | _ -> raise NoMatches

(* --------------------------------------------------------------------- *)
let restr_bds_check (env : environment) (p : pattern) (restr : pbindings) =
  let mr = Sid.of_list (List.map fst restr) in
  let m  = Mid.set_diff (FV.pattern0 p) mr in
  let m  = Mid.set_diff m (env.env_match.me_meta_vars) in

  let check1 (x : ident) =
    let aout =
      let lookup () =
        is_some (EcEnv.Mod.by_mpath_opt
                   (mpath (`Local x) [])
                   (LDecl.toenv env.env_hyps)) in

      EcIdent.id_equal x mhr ||
        LDecl.has_id x env.env_hyps || lookup () in

    if not aout then
      Debug.debug_bind_restr env x;
    aout

  in Mid.for_all (fun x _ -> check1 x) m

let e_next (e : engine) : nengine =
  { ne_continuation = e.e_continuation;
    ne_env          = e.e_env;
  }

let n_engine (e_pattern1) (e_pattern2 : pattern) (n : nengine) =
  { e_pattern1;
    e_pattern2;
    e_continuation = n.ne_continuation;
    e_env          = n.ne_env;
  }

let sub_engine1 e p f =
  e_copy { e with e_pattern2 = f; e_pattern1 = mk_pattern (Pat_Sub p) OGTany; }

let omap_list (default : 'a -> 'b) (f : 'a -> 'b option) (l : 'a list) : 'b list option =
  let rec aux acc there_is_Some = function
    | [] -> if there_is_Some then Some (List.rev acc) else None
    | x::rest when there_is_Some -> aux ((odfl (default x) (f x))::acc) there_is_Some rest
    | x::rest -> match f x with
                 | None -> aux ((default x)::acc) false rest
                 | Some x -> aux (x::acc) true rest in
  aux [] false l

let olist f (l : 'a list) = omap_list (fun x -> x) f l

let ofold_list default (f : 'env -> 'p -> 'a option * 'env) (e : 'env) (lp : 'p list) =
  let rec aux e acc there_is_Some = function
    | [] -> if there_is_Some then Some (List.rev acc),e else None,e
    | x::rest ->
       match f e x with
       | None,e -> aux e ((default x)::acc) there_is_Some rest
       | Some x,e -> aux e (x::acc) true rest
  in aux e [] false lp

(* let rec mpath_to_pattern (m : mpath) =
 *   Pat_Fun_Symbol (Sym_Mpath, (Pat_Axiom (Axiom_Mpath_top m.m_top))
 *                              ::(List.map mpath_to_pattern m.m_args))
 *
 * let rec pat_of_mpath (m : mpath) =
 *   let args = List.map pat_of_mpath m.m_args in
 *   let m = Pat_Axiom (Axiom_Mpath_top m.m_top) in
 *   Pat_Fun_Symbol (Sym_Mpath, m::args)
 *
 * let rec pat_of_xpath (x : xpath) =
 *   Pat_Fun_Symbol (Sym_Xpath, [Pat_Axiom (Axiom_Op (x.x_sub,[])); pat_of_mpath x.x_top]) *)

let rewrite_term e f =
  let env   = saturate e.e_env in
  let subst = psubst_of_menv env.env_match in
  let p1 = pat_form f in
  let p2 = Psubst.p_subst subst p1 in
  Debug.debug_subst env p1 p2;
  p2

let rec pattern_contain_meta_var p = match p.p_node with
  | Pat_Axiom _ -> false
  | Pat_Sub p -> pattern_contain_meta_var p
  | Pat_Or lp -> List.exists pattern_contain_meta_var lp
  | Pat_Meta_Name _ -> true
  | Pat_Red_Strat (p,_) -> pattern_contain_meta_var p
  | Pat_Fun_Symbol (_, lp) -> List.exists pattern_contain_meta_var lp

let all_map2 (f : 'a -> 'b -> 'c -> bool * 'a) (a : 'a) (lb : 'b list)
      (lc : 'c list) : bool * 'a =
  let rec aux a1 a lb lc =
    match lb, lc with
    | [], [] -> true, a
    | [], _ | _, [] -> raise NoMatches
    | b::lb, c::lc ->
       match f a b c with
       | false, _ -> false, a1
       | true, a -> aux a1 a lb lc
  in aux a a lb lc

let change_ogty ogty p = mk_pattern p.p_node ogty


let try_reduce (e : engine) : engine =
  Debug.debug_try_reduce e.e_env e.e_pattern1 e.e_pattern2;
  let copy = e_copy e in
  let ne = e_next (e_copy e) in
  let e_continuation = Zreduce (e.e_continuation,copy,ne) in
  { e with e_continuation }

let try_conv (e : engine) : engine =
  Debug.debug_try_conv e.e_env e.e_pattern1 e.e_pattern2;
  let copy = e_copy e in
  let ne = e_next (e_copy e) in
  let e_continuation = Zconv (e.e_continuation,copy,ne) in
  { e with e_continuation }

let rec check_arrow e b t = match b, t.ty_node with
  | [], _ -> true
  | (_,OGTty (Some t1)) :: b, Tfun (t2, t) ->
     EQ.ty e t1 t2 && check_arrow e b t
  | _ -> false

let check_arrow e b o = match o with
  | OGTty (Some ty) -> check_arrow e b ty
  | _ -> false

let rec parrow (args : pattern list) = function
  | None -> None
  | Some ty ->
     match args with
     | [] -> Some ty
     | p :: args ->
        match p.p_ogty with
        | OGTty (Some t1) -> parrow args (Some (tfun t1 ty))
        | _ -> None

let parrow args t = parrow (List.rev args) t


let pattern_is_higher_order_decidable pargs =
  let eq = (=) in
  let different_2by2 l =
    let rec aux rest1 rest2 = match rest1, rest2 with
      | _, [] -> true
      | [], _ :: r2 -> aux rest2 r2
      | a1 :: rest1, a2 ::_ ->
         not (eq a1 a2) || aux rest1 rest2
    in aux l l
  in
  let rec contain_meta_var p = match p.p_node with
    | Pat_Meta_Name (_,_,_) -> true
    | _ -> fst (p_fold_map (fun b p -> b || contain_meta_var p, p) false p)
  in
  not (List.exists contain_meta_var pargs)
  && different_2by2 pargs

let init_match_env ?mtch ?unienv ?metas () =
  { me_matches   = odfl Mid.empty mtch;
    me_unienv    = odfl (EcUnify.UniEnv.create None) unienv;
    me_meta_vars = odfl Mid.empty metas;
  }

let empty_matches_env () =
  { me_matches   = Mid.empty;
    me_meta_vars = Mid.empty;
    me_unienv    = EcUnify.UniEnv.create None; }

let mk_engine ?mtch f pattern hyps rim ris ric =
  let gstate  = EcEnv.gstate (EcEnv.LDecl.toenv hyps) in
  let verbose = EcGState.getflag "debug" gstate in

  let env_match = ofdfl empty_matches_env (omap menv_copy mtch) in
  let verbose   = if verbose then debug_verbose else env_verbose in
  let e_env     = {
      env_hyps               = hyps;
      env_red_info_match     = rim;
      env_red_info_same_meta = ris;
      env_red_info_conv      = ric;
      env_meta_restr_binds   = Mid.empty;
      env_match              = env_match;
      env_verbose            = verbose;
      env_stmt               = Mid.empty;
    } in

  { e_pattern1     = pattern;
    e_pattern2     = f;
    e_continuation = ZTop;
    e_env          = e_env;
  }

let init_env_stmt env name =
  { env with env_stmt = Mid.add name [] env.env_stmt }

let add_env_stmt (e : nengine) _p1 p2 =
  (* FIXME : this is an arbitrary choice *)
  let env_stmt = Mid.map (fun stmt -> p2 :: stmt) e.ne_env.env_stmt in
  { e with ne_env = { e.ne_env with env_stmt }}

(* ---------------------------------------------------------------------- *)
let rec process (e : engine) : nengine =
  let eq = EQ.ogty e.e_env e.e_pattern1.p_ogty e.e_pattern2.p_ogty in
  Debug.debug_try_match e.e_env e.e_pattern1 e.e_pattern2 e.e_continuation;
  Debug.debug_ogty e.e_env e.e_pattern1 e.e_pattern2 eq;
  Debug.debug_unienv e.e_env;
  if   not eq
  then next NoMatch e
  else
    let e = try_conv e in

    match e.e_pattern1.p_node, e.e_pattern2.p_node with
    | Pat_Meta_Name (None, n1, _), Pat_Meta_Name (None, n2, _) when EQ.name n1 n2 ->
       Debug.debug_which_rule e.e_env "same meta variable 1";
       next Match e

    | Pat_Meta_Name (Some p1, n1, ob), Pat_Meta_Name (None, n2, _) when EQ.name n1 n2 ->
       Debug.debug_which_rule e.e_env "same meta variable 2";
       next Match { e with e_continuation = Znamed (p1, n1, ob, e.e_continuation) }

    | Pat_Meta_Name (None, n2, _), Pat_Meta_Name (Some p1, n1, ob) when EQ.name n1 n2 ->
       Debug.debug_which_rule e.e_env "same meta variable 3";
       next Match { e with e_continuation = Znamed (p1, n1, ob, e.e_continuation) }

    | Pat_Meta_Name (Some p1, n1, _), Pat_Meta_Name (Some p2, n2, ob) when EQ.name n1 n2 ->
       Debug.debug_which_rule e.e_env "same meta variable 4";
       process { e with e_pattern1 = p1; e_pattern2 = p2;
                        e_continuation = Znamed (p2, n1, ob, e.e_continuation) }

   | Pat_Meta_Name (None, name, ob), _ ->
       let env_meta_restr_binds =
         odfl e.e_env.env_meta_restr_binds
           (omap (fun b -> Mid.add name b e.e_env.env_meta_restr_binds) ob) in
       let e_env = { e.e_env with env_meta_restr_binds; } in
       let e = { e with e_env } in
       Debug.debug_which_rule e.e_env "meta variable : 1 none";
       next Match { e with
           e_continuation = Znamed (e.e_pattern2, name, ob, e.e_continuation) }

    | _ , Pat_Meta_Name (None, name, ob) ->
       let env_meta_restr_binds =
         odfl e.e_env.env_meta_restr_binds
           (omap (fun b -> Mid.add name b e.e_env.env_meta_restr_binds) ob) in
       let e_env = { e.e_env with env_meta_restr_binds; } in
       let e = { e with e_env } in
       Debug.debug_which_rule e.e_env "meta variable : 2 none";
       next Match { e with
           e_continuation = Znamed (e.e_pattern1, name, ob, e.e_continuation) }


    | Pat_Meta_Name (Some p,name,ob), _ ->
       let env_meta_restr_binds =
         odfl e.e_env.env_meta_restr_binds
           (omap (fun b -> Mid.add name b e.e_env.env_meta_restr_binds) ob) in
       let e_env = { e.e_env with env_meta_restr_binds; } in
       let e = { e with e_env } in
       Debug.debug_which_rule e.e_env "meta variable : 1 some";
       process { e with
           e_pattern1 = p; e_env;
           e_continuation = Znamed(e.e_pattern2, name, ob, e.e_continuation);
         }

    | _, Pat_Meta_Name (Some p,name,ob) ->
       let env_meta_restr_binds =
         odfl e.e_env.env_meta_restr_binds
           (omap (fun b -> Mid.add name b e.e_env.env_meta_restr_binds) ob) in
       let e_env = { e.e_env with env_meta_restr_binds; } in
       let e = { e with e_env } in
       Debug.debug_which_rule e.e_env "meta variable : 2 some";
       process { e with
           e_pattern2 = p; e_env;
           e_continuation = Znamed(e.e_pattern1, name, ob, e.e_continuation);
         }

    | Pat_Sub p, _ ->
       let le = sub_engines1 e p in
       Debug.debug_which_rule e.e_env "sub 1";
       let e    = { e with e_pattern1 = p } in
       process (zor e le)

    | _, Pat_Sub p ->
       let le = sub_engines2 e p in
       Debug.debug_which_rule e.e_env "sub 2";
       let e    = { e with e_pattern2 = p } in
       process (zor e le)

    | Pat_Or [], _ -> next NoMatch e

    | _, Pat_Or [] -> next NoMatch e

    | Pat_Or (p::pl), _ ->
       Debug.debug_which_rule e.e_env "or 1";
       let update_pattern p = { e with e_pattern1 = p; } in
       let l = List.map update_pattern pl in
       let e = update_pattern p  in
       process (zor e l)

    | _, Pat_Or (p::pl) ->
       Debug.debug_which_rule e.e_env "or 2";
       let update_pattern p = { e with e_pattern2 = p; } in
       let l = List.map update_pattern pl in
       let e = update_pattern p  in
       process (zor e l)

    | Pat_Red_Strat (e_pattern1, f),_ ->
       Debug.debug_which_rule e.e_env "reduction strategy : 1";
       let env_red_info_match, env_red_info_same_meta =
         f e.e_env.env_red_info_match e.e_env.env_red_info_same_meta in
       let e_env = { e.e_env with env_red_info_match; env_red_info_same_meta } in
       process { e with e_pattern1; e_env }

    | _, Pat_Red_Strat (e_pattern2, f) ->
       Debug.debug_which_rule e.e_env "reduction strategy : 2";
       let env_red_info_match, env_red_info_same_meta =
         f e.e_env.env_red_info_match e.e_env.env_red_info_same_meta in
       let e_env = { e.e_env with env_red_info_match; env_red_info_same_meta } in
       process { e with e_pattern2; e_env }

    | Pat_Axiom o1, Pat_Axiom o2 ->
       Debug.debug_which_rule e.e_env "axiom 1&2";
       if EQ.axiom e.e_env e.e_env.env_red_info_match o1 o2
       then next   Match e
       else next NoMatch e

    | Pat_Fun_Symbol (Sym_Form_App (t, _),
                      { p_node = Pat_Meta_Name(None, name, _)} :: pargs), _
         when Mid.mem name e.e_env.env_match.me_matches ->
       Debug.debug_which_rule e.e_env "replace in app meta variable 1";
       let e_env = saturate e.e_env in
       let e_pattern1 = p_app (Mid.find name e_env.env_match.me_matches) pargs t in
       process { e with e_env; e_pattern1; }

    | _, Pat_Fun_Symbol (Sym_Form_App (t, _),
                         { p_node = Pat_Meta_Name(None, name, _)} :: pargs)
         when Mid.mem name e.e_env.env_match.me_matches ->
       Debug.debug_which_rule e.e_env "replace in app meta variable 2";
       let e_env = saturate e.e_env in
       let e_pattern2 = p_app (Mid.find name e_env.env_match.me_matches) pargs t in
       process { e with e_env; e_pattern2; }

    | Pat_Fun_Symbol (Sym_Form_App (_, MaybeHO), pop :: pargs), _ ->
       Debug.debug_which_rule e.e_env
         "application 1 : test both without and with higher order";
       let e_pattern1 = pat_fun_symbol (Sym_Form_App (None, HO)) (pop::pargs) in
       let e_or = { e with e_pattern1; } in
       let e_pattern1 = pat_fun_symbol (Sym_Form_App (None, NoHO)) (pop::pargs) in
       let e = { e with e_pattern1; } in
       process (zor e [e_or])

    | _ ,Pat_Fun_Symbol (Sym_Form_App (_, MaybeHO), pop :: pargs) ->
       Debug.debug_which_rule e.e_env
         "application 2 : test both without and with higher order";
       let e_pattern2 = pat_fun_symbol (Sym_Form_App (None, HO)) (pop::pargs) in
       let e_or = { e with e_pattern2; } in
       let e_pattern2 = pat_fun_symbol (Sym_Form_App (None, NoHO)) (pop::pargs) in
       let e = { e with e_pattern2; } in
       process (zor e [e_or])

    | Pat_Fun_Symbol (Sym_Form_App (ot1, NoHO), op1 :: args1),
      Pat_Fun_Symbol (Sym_Form_App (ot2, NoHO), op2 :: args2) ->
       Debug.debug_which_rule e.e_env
         "application 1&2 : without higher order";
       let e = try_reduce e in
       let (args11,args12),(args21,args22) = suffix2 args1 args2 in
       if args12 = [] && args22 = [] then assert false;
       let zand = List.combine args12 args22 in
       let op1 = p_app op1 args11 (parrow args12 ot1) in
       let op2 = p_app op2 args21 (parrow args22 ot2) in
       let e_pattern1, e_pattern2, zand = op1, op2, zand in
       let e_continuation =
         Zand ([e_pattern1,e_pattern2],zand,e.e_continuation) in
       process { e with e_pattern1; e_pattern2; e_continuation; }

    (* FIXME *)
    | Pat_Fun_Symbol (Sym_Form_App (_, HO),
                      { p_node = Pat_Meta_Name(None, name, ob)}
                      ::pargs), _ ->
       begin
         try
           Debug.debug_which_rule e.e_env "form : application : with higher order";
           let e = try_reduce e in
           (* higher order *)
           let env = saturate e.e_env in
           let s = psubst_of_menv env.env_match in
           let p_subst s p =
             let p2 = Psubst.p_subst s p in
             Debug.debug_subst env p p2;
             p2 in
           let pargs = List.map (p_subst s) pargs in
           (* if not(pattern_is_higher_order_decidable pargs)
            * then raise NoMatches
            * else *)

           let pargs, env =
             (* let meta_pargs = List.filter pattern_contain_meta_var pargs in *)
             let find_sub env p =
               try
                 let ne = process
                            { e_env          = env_copy env;
                              e_pattern1     = mk_pattern (Pat_Sub p) OGTany;
                              e_pattern2     = e.e_pattern2;
                              e_continuation = ZTop; } in
                 ne.ne_env
               with NoMatches -> env
             in
             let env = List.fold_left find_sub env pargs in
             let s = psubst_of_menv env.env_match in
             let env_match = { e.e_env.env_match with
                               me_matches = e.e_env.env_match.me_matches } in
             List.map (Psubst.p_subst s) pargs, { env with env_match } in
           if not(pattern_is_higher_order_decidable pargs)
           then raise NoMatches
           else
             let add_ident i x =
               EcIdent.create (String.concat "" ["t";string_of_int i]), x in
             let args = List.mapi add_ident pargs in
             (* let args = List.map (fun (i,p) -> i, pat_meta p i ob) args in *)
             let env_meta_restr_binds =
               odfl env.env_meta_restr_binds
                 (omap (fun b -> Mid.add name b env.env_meta_restr_binds) ob) in
             let e = { e with e_env = { env with env_meta_restr_binds } } in
             let abstract (e, p) arg =
               Debug.debug_higher_order_to_abstract e.e_env (snd arg) p;
               let env, p = abstract_opt e p ob arg in
               { e with e_env = env }, p
             in
             let e', pat =
               (* FIXME : add strategies to adapt the order of the arguments *)
               List.fold_left abstract (e, e.e_pattern2) args in
             EcUnify.UniEnv.restore ~src:e'.e_env.env_match.me_unienv
               ~dst:e.e_env.env_match.me_unienv;
             let f (name,p) = (name,p.p_ogty) in
             let args = List.map f args in
             let pat = p_quant Llambda args pat in
             let s = psubst_of_menv { e.e_env.env_match with me_matches = Mid.empty } in
             let pat = p_subst s pat in
             let m,e =
               try
                 let e = add_match e name pat ob in
                   let me_matches =
                     List.fold_left (fun m (id,_) -> Mid.remove id m)
                       e.e_env.env_match.me_matches args in
                   let env_match = { e.e_env.env_match with me_matches } in
                   let e_env = { e.e_env with env_match } in
                   let e = { e with e_env } in
                   Match, e
               with CannotUnify -> raise NoMatches
             in next m e
         with
         | NoMatches -> next NoMatch e
       end

    | Pat_Fun_Symbol (Sym_Quant (q1,bs1), [p1]),
      Pat_Fun_Symbol (Sym_Quant (q2,bs2), [p2]) when q1 = q2 ->
       begin
         Debug.debug_which_rule e.e_env "quantif 1&2";
         let e = try_reduce e in
         let (b11,b12), (b21,b22) = List.prefix2 bs1 bs2 in
         if   not (List.for_all2
                     (EQ.ogty e.e_env) (List.map snd b21) (List.map snd b11))
         then next NoMatch e
         else
           let f s (id1,_) (id2,gty1) = Psubst.p_bind_ogty s id1 id2 gty1 in
           let e_env      = saturate e.e_env in
           let subst      = psubst_of_menv { e.e_env.env_match with me_matches = Mid.empty }in
           let s          = List.fold_left2 f subst b11 b21 in
           let e_pattern1 = Psubst.p_subst s p1 in
           let e_pattern1 = p_quant q1 b12 e_pattern1 in
           Debug.debug_subst e_env p1 e_pattern1;
           let e_pattern2 = p_quant q2 b22 (Psubst.p_subst subst p2) in
           process { e with e_pattern1; e_pattern2; e_env; }
       end

    | Pat_Fun_Symbol (Sym_Mpath, p1 :: args1),
      Pat_Fun_Symbol (Sym_Mpath, p2 :: args2) ->
       begin Debug.debug_which_rule e.e_env "mpath 1&2";
             let e = try_reduce e in
             let (args11,args12),(args21,args22) = suffix2 args1 args2 in
             let zand = List.combine args12 args22 in
             let e_continuation = match zand with
               | [] -> e.e_continuation
               | _  -> Zand ([],zand,e.e_continuation) in
             let e_pattern1 = p_mpath p1 args11 in
             let e_pattern2 = p_mpath p2 args21 in
             process { e with e_pattern1; e_pattern2; e_continuation; }
       end

    | Pat_Fun_Symbol (s1, lp1), Pat_Fun_Symbol (s2, lp2)
         when EQ.symbol e.e_env s1 s2 && 0 = List.compare_lengths lp1 lp2 ->
       Debug.debug_which_rule e.e_env "same fun symbol";
       let e_continuation = Zand ([], List.combine lp1 lp2, e.e_continuation) in
       next Match { e with e_continuation }

    (* Pattern / Axiom *)
    | Pat_Fun_Symbol (Sym_Mpath, p::rest), Pat_Axiom (Axiom_Mpath m) ->
       begin Debug.debug_which_rule e.e_env "mpath : pat ax";
             let e = try_reduce e in
             let (pargs1,pargs2),(margs1,margs2) = suffix2 rest m.m_args in
             let zand = List.map2 (fun x y -> (pat_mpath x),y) margs2 pargs2 in
             let e_continuation = match zand with
               | [] -> e.e_continuation
               | _  -> Zand ([],zand,e.e_continuation) in
             let m = match margs1 with
               | [] -> pat_mpath_top m.m_top
               | _  -> if margs2 = [] then pat_mpath m
                       else pat_mpath (mpath m.m_top margs1)
             in
             let p = match pargs1 with
               | [] -> p
               | _ -> p_mpath p pargs1
             in
             process { e with e_pattern1 = p; e_pattern2 = m; e_continuation; }
       end

    | Pat_Axiom (Axiom_Mpath m), Pat_Fun_Symbol (Sym_Mpath, p::rest) ->
       begin Debug.debug_which_rule e.e_env "mpath : ax pat";
             let e = try_reduce e in
             let (pargs1,pargs2),(margs1,margs2) = suffix2 rest m.m_args in
             let zand = List.map2 (fun x y -> (pat_mpath x),y) margs2 pargs2 in
             let e_continuation = match zand with
               | [] -> e.e_continuation
               | _  -> Zand ([],zand,e.e_continuation) in
             let m = match margs1 with
               | [] -> pat_mpath_top m.m_top
               | _  -> if margs2 = [] then pat_mpath m
                       else pat_mpath (mpath m.m_top margs1)
             in
             let p = match pargs1 with
               | [] -> p
               | _ -> p_mpath p pargs1
             in
             process { e with e_pattern2 = p; e_pattern1 = m; e_continuation; }
       end

    | Pat_Fun_Symbol (Sym_Mpath, [p]),
      Pat_Axiom (Axiom_Mpath_top _) ->
       begin Debug.debug_which_rule e.e_env "mpath_top : 1";
             let e = try_reduce e in
             process { e with e_pattern1 = p }
       end

    | Pat_Axiom (Axiom_Mpath_top _),
      Pat_Fun_Symbol (Sym_Mpath, [p]) ->
       begin Debug.debug_which_rule e.e_env "mpath_top : 2";
             let e = try_reduce e in
             process { e with e_pattern2 = p }
       end

    | Pat_Fun_Symbol (Sym_Form_Prog_var k, [p]),
      Pat_Axiom (Axiom_Prog_Var x2)
         when k = x2.pv_kind -> begin
        Debug.debug_which_rule e.e_env "form : prog_var 1";
        process { e with e_pattern1 = p; e_pattern2 = pat_xpath x2.pv_name; }
      end

    | Pat_Axiom (Axiom_Prog_Var x2),
      Pat_Fun_Symbol (Sym_Form_Prog_var k, [p])
         when k = x2.pv_kind -> begin
        Debug.debug_which_rule e.e_env "form : prog_var 2";
        process { e with e_pattern2 = p; e_pattern1 = pat_xpath x2.pv_name; }
      end

    | Pat_Fun_Symbol (Sym_Xpath, [pm;pf]),
      Pat_Axiom (Axiom_Xpath x) ->
       begin Debug.debug_which_rule e.e_env "xpath 1";
             let zand = [pat_mpath x.x_top,pm] in
             process { e with
                 e_pattern1 = pf;
                 e_pattern2 = pat_op x.x_sub [] None;
                 e_continuation = Zand ([],zand,e.e_continuation); }
       end

    | Pat_Axiom (Axiom_Xpath x),
      Pat_Fun_Symbol (Sym_Xpath, [pm;pf]) ->
       begin Debug.debug_which_rule e.e_env "xpath 2";
             let zand = [pat_mpath x.x_top,pm] in
             process { e with
                 e_pattern2 = pf;
                 e_pattern1 = pat_op x.x_sub [] None;
                 e_continuation = Zand ([],zand,e.e_continuation); }
       end

    | Pat_Fun_Symbol
        (Sym_Form_App _,
         { p_node = Pat_Fun_Symbol (Sym_Quant (Llambda,_),[_])}::_), _
         when e.e_env.env_red_info_match.EcReduction.beta -> begin
       match p_betared_opt e.e_pattern1 with
       | Some e_pattern1 ->
          process { e with e_pattern1 }
       | None -> next NoMatch e
      end

    | _, Pat_Fun_Symbol
           (Sym_Form_App _,
            { p_node = Pat_Fun_Symbol (Sym_Quant (Llambda,_),[_])}::_)
         when e.e_env.env_red_info_match.EcReduction.beta -> begin
       match p_betared_opt e.e_pattern2 with
       | Some e_pattern2 ->
          process { e with e_pattern2 }
       | None -> next NoMatch e
      end

    | _ -> begin
        Debug.debug_which_rule e.e_env "default";
        let e = try_reduce e in
        next NoMatch e
      end

and next (m : ismatch) (e : engine) : nengine =
  Debug.debug_result_match e.e_env m;
  next_n m (e_next e)

and next_n (m : ismatch) (e : nengine) : nengine =
  match m,e.ne_continuation with
  | NoMatch, ZTop -> raise NoMatches

  | NoMatch, Zreduce (_, e',ne) -> begin
      Debug.debug_show_matches e.ne_env;
      Debug.debug_which_rule e.ne_env "next : no match, then try to reduce";
      Debug.debug_show_matches e'.e_env;
      match h_red_strat e'.e_env e'.e_pattern1 e'.e_pattern2 with
      | None -> Debug.debug_reduce e'.e_env e'.e_pattern1 e'.e_pattern1
                  e'.e_pattern2 e'.e_pattern2 false;
                next_n NoMatch ne
      | Some (e_pattern1, e_pattern2) ->
         Debug.debug_reduce e'.e_env e'.e_pattern1 e_pattern1
           e'.e_pattern2 e_pattern2 true;
         let e = { e' with e_pattern1; e_pattern2 } in
         process e
    end

  | NoMatch, Zconv (_, e',ne) -> begin
      Debug.debug_show_matches e.ne_env;
      Debug.debug_which_rule e.ne_env "next : no match, then try to convert";
      Debug.debug_show_matches e'.e_env;

      let env = saturate e'.e_env in
      let s   = psubst_of_menv env.env_match in
      let r   = env.env_red_info_conv in
      let p1  = Psubst.p_subst s e'.e_pattern1 in
      let p2  = Psubst.p_subst s e'.e_pattern2 in
      try
        let f1  = Translate.form_of_pattern (EcEnv.LDecl.toenv env.env_hyps) p1 in
        let f2  = Translate.form_of_pattern (EcEnv.LDecl.toenv env.env_hyps) p2 in
        if EcReduction.is_conv_param r env.env_hyps f1 f2 then
          next Match e'
        else next_n NoMatch ne
      with Translate.Invalid_Type _ ->
        next_n NoMatch ne
    end

  | NoMatch, Znamed (_f, _name, _ob, ne_continuation) ->
     Debug.debug_which_rule e.ne_env "next : no match in named";
     next_n NoMatch { e with ne_continuation; }

  | NoMatch, Zand (_,_,ne_continuation) ->
     Debug.debug_which_rule e.ne_env "next : no match in zand";
     next_n NoMatch { e with ne_continuation; }

  | NoMatch, Zor (_, [], ne) ->
     Debug.debug_which_rule e.ne_env "next : no match in zor, no more matches";
     next_n NoMatch ne

  | NoMatch, Zor (_, e'::engines, ne) ->
     Debug.debug_another_or e.ne_env;
     EcUnify.UniEnv.restore
       ~src:ne.ne_env.env_match.me_unienv
       ~dst: e.ne_env.env_match.me_unienv;
     process { e' with e_continuation = Zor (e'.e_continuation, engines, ne); }

  | Match, ZTop   ->
     Debug.debug_found_match e.ne_env;
     let ne_env = saturate e.ne_env in
     { e with ne_env }

  | Match, Zreduce (ne_continuation, _, _) ->
     Debug.debug_which_rule e.ne_env "next : skip reduce";
     next_n Match { e with ne_continuation }

  | Match, Zconv (ne_continuation, _, _) ->
     Debug.debug_which_rule e.ne_env "next : skip conv";
     next_n Match { e with ne_continuation }

  | Match, Znamed (f, name, ob, ne_continuation) ->
     let m,e =
       try
         let ne = nadd_match e name f ob in
         Match, { ne with ne_continuation; }
       with
       | CannotUnify ->
          Debug.debug_which_rule e.ne_env "next : cannot unify in named";
          NoMatch, { e with ne_continuation; } in
     next_n m e

  | Match, Zand ((p1,p2)::_before,[],ne_continuation) ->
     Debug.debug_which_rule e.ne_env "next : all match in zand";
     let e = add_env_stmt e p1 p2 in
     next_n Match { e with ne_continuation; }

  | Match, Zand ([],[],_) -> assert false

  | Match, Zand (before,(f,p)::after,z) ->
     Debug.debug_which_rule e.ne_env "next : next match in zand";
     let ne_env = saturate e.ne_env in
     let e      = { e with ne_env } in
     (* let s      = psubst_of_menv e.ne_env.env_match in
      * let f, p   = Psubst.p_subst s f, Psubst.p_subst s p in *)
     process (n_engine f p
                { e with ne_continuation = Zand ((f,p)::before,after,z);})

  | Match, Zor (ne_continuation, _, _) ->
     Debug.debug_which_rule e.ne_env "next : match in zor";
     Debug.debug_ignore_ors e.ne_env;
     next_n Match { e with ne_continuation }


and sub_engines2 e p =
  let f e = { e with e_pattern1 = e.e_pattern2; e_pattern2 = e.e_pattern1; } in
  let e = f e in
  let l = sub_engines1 e p in
  List.map f l

and sub_engines1 (e : engine) (p : pattern) : engine list =
  match e.e_pattern2.p_node, p.p_node with
  | Pat_Meta_Name (_, _, _) , _ -> []
  | Pat_Sub _               , _ -> []
  | Pat_Or _                , _ -> []
  | Pat_Red_Strat (_,_)     , _ -> []
  | Pat_Axiom (Axiom_Local (id1, { ty_node = Ttuple lt })),
    Pat_Fun_Symbol (Sym_Form_Proj _, [{ p_node = Pat_Axiom (Axiom_Local (id2, _))}])
       when EQ.name id1 id2     ->
     List.mapi (fun i t -> sub_engine1 e p (p_proj e.e_pattern2 i t)) lt
  | Pat_Fun_Symbol (Sym_Form_Proj _, [{ p_node = Pat_Axiom (Axiom_Local (id1, _))}]),
    Pat_Fun_Symbol (Sym_Form_Proj _, [{ p_node = Pat_Axiom (Axiom_Local (id2, _))}])
       when EQ.name id1 id2     -> []
  | Pat_Axiom _             , _ -> []
  | Pat_Fun_Symbol (_, lp)  , _ -> List.map (sub_engine1 e p) lp

(* add_match can raise the exception : CannotUnify *)
and nadd_match (e : nengine) (name : meta_name) (p : pattern)
      (orb : pbindings option) : nengine =
  let env = e.ne_env in
  let env = saturate env in
  let subst = psubst_of_menv env.env_match in
  let p' = Psubst.p_subst subst p in
  Debug.debug_subst env p p';
  let p = p' in
  let p_fv = FV.pattern0 p in
  Debug.debug_subst env p p';
  if Mid.mem name p_fv then
    raise CannotUnify
  else if odfl true (omap (fun r -> restr_bds_check env p r) orb)
  then
    let me_matches =
      match Mid.find_opt name e.ne_env.env_match.me_matches with
      | None ->
         Debug.debug_which_rule e.ne_env "nadd_match for the first time";
         Debug.debug_add_match e.ne_env true name p;
         Mid.add name p e.ne_env.env_match.me_matches
      | Some p' ->
         (* raise CannotUnify *)
         Debug.debug_which_rule e.ne_env "start new unification";
         let engine_try_unification =
           let env = env_copy e.ne_env in
           let env = { env with env_red_info_match = env.env_red_info_same_meta } in
           n_engine p p' { e with ne_env = env; ne_continuation = ZTop } in
         try
           let ne_unification = process engine_try_unification in
           ne_unification.ne_env.env_match.me_matches
         with
         | NoMatches ->
            Debug.debug_add_match e.ne_env false name p;
            raise CannotUnify
    in
    { e with ne_env = { env with env_match = { env.env_match with me_matches; }; }; }
  else raise CannotUnify

and add_match (e : engine) n p b =
  n_engine e.e_pattern1 e.e_pattern2 (nadd_match (e_next e) n p b)

and abstract_opt (e : engine) (p : pattern) (ob : pbindings option)
                 ((arg,parg) : Name.t * pattern) : environment * pattern =
  match parg.p_node with
  | Pat_Axiom (Axiom_Local (id,ty)) ->
     let s = psubst_of_menv { e.e_env.env_match with me_matches = Mid.empty } in
     let s = p_bind_rename s id arg (ty_subst s.ps_sty ty) in
     let p2 = Psubst.p_subst s p in
     Debug.debug_subst e.e_env p p2;
     e.e_env, p2
  | Pat_Fun_Symbol (Sym_Form_Proj (i, { ty_node = Ttuple lt }), [parg']) ->
     let name = EcIdent.create "" in
     let env, p = abstract_opt e p ob (name,parg') in
     let replace_name =
       p_tuple (List.mapi (fun j t -> if i = j
                                      then meta_var arg ob (OGTty (Some t))
                                      else p_proj parg j t) lt) in
     let s = Psubst.p_bind_local Psubst.p_subst_id name replace_name in
     let p = Psubst.p_subst s p in
     env, p
  | _ ->
     let rec f env p = try
         let eng_unif = e_copy { e_env = env; e_continuation = ZTop;
                                 e_pattern1 = parg; e_pattern2 = p; } in
         let ne = process eng_unif in
         let env = ne.ne_env in
         let s = psubst_of_menv
                   (saturate { env with
                        env_match = { env.env_match with
                                      me_matches = Mid.empty }}).env_match in
         let p = meta_var arg ob p.p_ogty in
         let p = Psubst.p_subst s p in
         let p = match p.p_ogty with
           | OGTty (Some ty) -> pat_local arg ty
           | _ -> p in
         env, p
       with NoMatches -> p_fold_map f env p
     in
     f e.e_env p

and h_red_strat env p1 p2 =
  let env = saturate env in
  let s   = psubst_of_menv env.env_match in
  let h   = env.env_hyps in
  let r   = env.env_red_info_match in
  let eq h r p1 p2 =
    let eng = mk_engine ~mtch:env.env_match p1 p2 h r
                env.env_red_info_same_meta env.env_red_info_conv in
    let env = eng.e_env in
    EQ.pattern env r p1 p2 in
  match EcPReduction.h_red_pattern_opt ~verbose:env.env_verbose.verbose_reduce
          eq h r s p1 with
  | Some p1 ->
     Debug.debug_h_red_strat env p1 p2 1;
     Some (p1, p2)
  | None ->
     Debug.debug_h_red_strat_next env;
     match EcPReduction.h_red_pattern_opt ~verbose:env.env_verbose.verbose_reduce
             eq h r s p2 with
     | Some p2 ->
        Debug.debug_h_red_strat env p1 p2 2;
        Some (p1, p2)
     | None ->
        match p1.p_node, p2.p_node with
        (* eta-expansion in the case where the types of e_pattern2 is some tarrow *)
        | Pat_Fun_Symbol (Sym_Quant (Llambda, (id, OGTty (Some ty) as b1)::bs), [_]), _
             when check_arrow env [b1] p2.p_ogty ->
           Debug.debug_which_rule env "eta-expansion 1";
           let x = pat_local (EcIdent.create (EcIdent.tostring id)) ty in
           let codom = toarrow (List.map (get_ty |- snd) bs) (get_ty p1.p_ogty) in
           let p1 = p_app_simpl p1 [x] (Some codom) in
           let p2 = p_app_simpl p2 [x] (Some codom) in
           Some (p1,p2)

        (* eta-expansion in the case where the types of e_pattern1 is some tarrow *)
        | _, Pat_Fun_Symbol (Sym_Quant (Llambda, (id, OGTty (Some ty) as b2)::bs), [_])
             when check_arrow env [b2] p1.p_ogty ->
           Debug.debug_which_rule env "eta-expansion 1";
           let x = pat_local (EcIdent.create (EcIdent.tostring id)) ty in
           let codom = toarrow (List.map (get_ty |- snd) bs) (get_ty p2.p_ogty) in
           let p1 = p_app_simpl p1 [x] (Some codom) in
           let p2 = p_app_simpl p2 [x] (Some codom) in
           Some (p1,p2)

        | _ ->
           Debug.debug_h_red_strat env p1 p2 3;
           None

and search_eng e =
  let s = psubst_of_menv e.e_env.env_match in
  let e_pattern1 = Psubst.p_subst s e.e_pattern1 in
  let e_pattern2 = Psubst.p_subst s e.e_pattern2 in
  let e = { e with e_pattern1; e_pattern2; } in
  Debug.debug_begin_match e.e_env e.e_pattern1 e.e_pattern2;
  Debug.debug_show_matches e.e_env;
  Debug.debug_reduce e.e_env e.e_pattern1 e.e_pattern1 e.e_pattern2
    e.e_pattern2 false;
  try
    let unienv = e.e_env.env_match.me_unienv in
       let e' = process (e_copy e) in
       EcUnify.UniEnv.restore ~src:e'.ne_env.env_match.me_unienv ~dst:unienv;
       Debug.debug_unienv e'.ne_env;
       Debug.debug_show_matches e'.ne_env;
       Debug.debug_unienv {e'.ne_env with env_match = { e'.ne_env.env_match with me_unienv = unienv } };
       Some e'
  with
  | NoMatches ->
     None


let no_delta p = match p.p_node with
  | Pat_Fun_Symbol (Sym_Form_App (t1,ho),
                    { p_node = Pat_Axiom (Axiom_Op (_,p,lt,t))} :: lp) ->
     p_app ~ho (pat_op ~delta:false p lt t) lp t1
  | _ -> p

let search_eng_head_no_delta e =
  search_eng { e with e_pattern1 = no_delta e.e_pattern1 }

let get_matches (e : engine) : match_env = (saturate e.e_env).env_match
let get_n_matches (e : nengine) : match_env = (saturate e.ne_env).env_match

let abstract_pattern (sbd: ogty Mid.t) (p : pattern) =
  let s = Mid.fold (fun name gty s ->
              Psubst.p_bind_local s name (meta_var name None gty)) sbd
            Psubst.p_subst_id in
  Psubst.p_subst s p

let rec prefix_binds bs1 bs2 =
  let rec aux acc bs1 bs2 = match bs1,bs2 with
    | (x,ty1)::r1, (y,ty2)::r2 when EQ.name x y && gty_equal ty1 ty2 ->
       aux ((x,ty1)::acc) r1 r2
    | _ -> List.rev acc
  in aux [] bs1 bs2

let rec prefix_pbinds bs1 bs2 =
  let rec aux acc bs1 bs2 = match bs1,bs2 with
    | (x,OGTty (Some ty1))::r1, (y,OGTty (Some ty2))::r2
         when EQ.name x y && gty_equal (GTty ty1) (GTty ty2) ->
       aux ((x,OGTty (Some ty1))::acc) r1 r2
    | (x,OGTty t1)::r1, (y,OGTty t2)::r2 when EQ.name x y ->
       let t = match t1 with
         | Some _ -> t1
         | None ->
            match t2 with
            | Some _ -> t2
            | None -> None in
       aux ((x,OGTty t)::acc) r1 r2
    | (x,OGTmem (Some ty1))::r1, (y,OGTmem (Some ty2))::r2
         when EQ.name x y && gty_equal (GTmem ty1) (GTmem ty2) ->
       aux ((x,OGTmem (Some ty1))::acc) r1 r2
    | (x,OGTmem t1)::r1, (y,OGTmem t2)::r2 when EQ.name x y ->
       let t = match t1 with
         | Some _ -> t1
         | None ->
            match t2 with
            | Some _ -> t2
            | None -> None in
       aux ((x,OGTmem t)::acc) r1 r2
    | (x,OGTmodty (Some (t1,mr1)))::r1, (y,OGTmodty (Some (t2,mr2)))::r2
         when EQ.name x y && gty_equal (GTmodty (t1,mr1)) (GTmodty (t2,mr2)) ->
       aux ((x,OGTmodty (Some (t1,mr1)))::acc) r1 r2
    | (x,OGTmodty t1)::r1, (y,OGTmodty t2)::r2 when EQ.name x y ->
       let t = match t1 with
         | Some _ -> t1
         | None ->
            match t2 with
            | Some _ -> t2
            | None -> None in
       aux ((x,OGTmodty t)::acc) r1 r2
    | _ -> List.rev acc
  in aux [] bs1 bs2

let add_meta_bindings (name : meta_name) (b : pbindings)
      (mbs : pbindings Mid.t) =
  match Mid.find_opt name mbs with
  | None -> Mid.add name b mbs
  | Some b' -> Mid.add name (prefix_pbinds b' b) mbs

let get_meta_bindings (p : pattern) : pbindings Mid.t =
  let rec aux current_bds meta_bds p = match p.p_node with
    | Pat_Meta_Name (None, n, _) -> add_meta_bindings n current_bds meta_bds
    | Pat_Meta_Name (Some p, n, _) ->
       aux current_bds (add_meta_bindings n current_bds meta_bds) p
    | Pat_Sub p -> aux current_bds meta_bds p
    | Pat_Or lp -> List.fold_left (aux current_bds) meta_bds lp
    | Pat_Red_Strat (p,_) -> aux current_bds meta_bds p
    | Pat_Axiom _ -> meta_bds
    | Pat_Fun_Symbol (Sym_Quant (_,b),[p]) ->
       aux (current_bds @ b) meta_bds p
    | Pat_Fun_Symbol (Sym_Form_Let lp, [p1;p2]) ->
       let m = aux current_bds meta_bds p1 in
       let current_bds = match lp with
         | LSymbol (id,ty) -> (id, OGTty (Some ty)) :: current_bds
         | LTuple l -> (List.map (snd_map (fun t -> OGTty (Some t))) l) @ current_bds
         | _ -> current_bds in
       aux current_bds m p2
    | Pat_Fun_Symbol (Sym_Form_Pr, [p1;p2;p3;p4]) ->
       let m = aux ((mhr,OGTmem None)::current_bds) meta_bds p4 in
       List.fold_left (aux current_bds) m [p1;p2;p3]
    | Pat_Fun_Symbol (Sym_Form_Hoare_F, [p1;p2;p3]) ->
       let m = List.fold_left (aux ((mhr,OGTmem None)::current_bds)) meta_bds [p1;p3] in
       aux current_bds m p2
    | Pat_Fun_Symbol (Sym_Form_bd_Hoare_F, [p1;p2;p3;p4;p5]) ->
       let m = List.fold_left (aux ((mhr,OGTmem None)::current_bds)) meta_bds [p1;p3;p5] in
       List.fold_left (aux current_bds) m [p2;p4]
    | Pat_Fun_Symbol (Sym_Form_Equiv_F, [p1;p2;p3;p4]) ->
       let m = List.fold_left
                 (aux ((mleft,OGTmem None)::(mright,OGTmem None)::current_bds))
                 meta_bds [p1;p4] in
       List.fold_left (aux current_bds) m [p2;p3]
    | Pat_Fun_Symbol (_,lp) -> List.fold_left (aux current_bds) meta_bds lp
  in aux [] Mid.empty p

let rec write_meta_bindings (m : pbindings Mid.t) (p : pattern) =
  let aux = write_meta_bindings m in
  match p.p_node with
  | Pat_Meta_Name (None, n, _) -> meta_var n (Mid.find_opt n m) p.p_ogty
  | Pat_Meta_Name (Some p,n,_) -> pat_meta (aux p) n (Mid.find_opt n m)
  | Pat_Sub p                  -> mk_pattern (Pat_Sub (aux p)) OGTany
  | Pat_Or lp                  -> mk_pattern (Pat_Or (List.map aux lp)) OGTany
  | Pat_Red_Strat (p,f)        -> let p = aux p in
                                  mk_pattern (Pat_Red_Strat (p,f)) p.p_ogty
  | Pat_Axiom _                -> p
  | Pat_Fun_Symbol
      (Sym_Form_App (ty,_),
       ({ p_node = Pat_Meta_Name (None, _, _) } :: _ as args)) ->
     pat_fun_symbol (Sym_Form_App (ty,MaybeHO)) args
  | Pat_Fun_Symbol (s,lp)      -> pat_fun_symbol s (List.map aux lp)

let abstract_pattern b a =
  let p = abstract_pattern b a in
  let m = get_meta_bindings p in
  write_meta_bindings m p

let pattern_of_form me f = abstract_pattern me.me_meta_vars (pat_form f)

let pattern_of_memory me m =
  abstract_pattern me.me_meta_vars (pat_memory m)

(* -------------------------------------------------------------------- *)
let menv_is_full (e : match_env) =
  let matches   = e.me_matches in
  let meta_vars = e.me_meta_vars in

  let f n _ = match Mid.find_opt n matches with
    | None   -> false
    | Some p -> let fv = FV.pattern0 p in
                Mid.for_all (fun n _ -> not (Mid.mem n meta_vars)) fv in

  Mid.for_all f meta_vars && EcUnify.UniEnv.closed e.me_unienv

(* -------------------------------------------------------------------- *)
let fsubst_of_menv (me : match_env) (env : env) =
  let ps = psubst_of_menv me in
  let fs = Fsubst.f_subst_init ~sty:ps.ps_sty () in
  let bind_pattern id p s =
    try Fsubst.f_bind_local s id (Translate.form_of_pattern env p)
    with Translate.Invalid_Type _ ->
      try Fsubst.f_bind_mem s id (Translate.memory_of_pattern p)
      with Translate.Invalid_Type _ ->
        try Fsubst.f_bind_mod s id (Translate.mpath_of_pattern env p)
        with Translate.Invalid_Type _ -> s in

  Mid.fold bind_pattern me.me_matches fs

(* -------------------------------------------------------------------- *)
let menv_get_form x env menv =
  obind
    (fun p ->
      try  Some (Translate.form_of_pattern env p)
      with Translate.Invalid_Type _ -> None)
    (Mid.find_opt x menv.me_matches)

(* -------------------------------------------------------------------- *)
let menv_has_form x menv =
  match Mid.find_opt x menv.me_meta_vars with
  | Some (OGTty _) -> true | _ -> false

(* -------------------------------------------------------------------- *)
let menv_has_memory x menv =
  match Mid.find_opt x menv.me_meta_vars with
  | Some (OGTmem _) -> true | _ -> false


(* -------------------------------------------------------------------------- *)
let copy_environment = env_copy
