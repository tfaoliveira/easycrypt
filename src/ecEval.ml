(* -------------------------------------------------------------------- *)
(* Evaluation of closed expressions and of concrete procedures.         *)
(*                                                                      *)
(* This is a testing facility: it runs outside of the logical kernel    *)
(* and never produces proofs. Its trusted base is:                      *)
(*  - the native semantics of the core operators (int, bool, iteri);    *)
(*  - the native semantics of the bitstring / bit-vector operators      *)
(*    given by [bind bitstring] and [bind op] declarations, whose side  *)
(*    conditions are lemmas of the environment;                         *)
(*  - the lemmas of the [eval] simplification database                  *)
(*    ([hint simplify in eval : ...]), used as definitions for abstract *)
(*    or inefficient operators.                                         *)
(* Everything else is evaluated by unfolding definitions.               *)
(* -------------------------------------------------------------------- *)
open EcUtils
open EcPath
open EcAst
open EcTypes
open EcCoreFol
open EcDecl
open EcModules

module CI    = EcCoreLib
module Mid   = EcIdent.Mid
module ER    = EcTheory

(* -------------------------------------------------------------------- *)
exception EvalError of string

(* Raised when the step budget ([pragma Eval:steps = n]) is exhausted.  *)
(* Distinct from [EvalError], which rule matching recovers from.        *)
exception StepLimit of int

let error fmt = Format.kasprintf (fun s -> raise (EvalError s)) fmt

(* -------------------------------------------------------------------- *)
type value =
  | VInt   of Z.t
  | VBool  of bool
  | VBits  of int * Z.t                  (* size, unsigned value *)
  | VCtor  of path * int * value list    (* constructor, index, fields *)
  | VTuple of value list
  | VFun   of (value -> value)
  | VNeu   of path * value list * int    (* stuck application of an abstract op, *)
                                         (* with a unique identifier             *)
  | VWitness

(* -------------------------------------------------------------------- *)
let rec pp_value (fmt : Format.formatter) (v : value) =
  match v with
  | VInt z ->
      Format.pp_print_string fmt (Z.to_string z)
  | VBool b ->
      Format.pp_print_bool fmt b
  | VBits (n, z) ->
      Format.fprintf fmt "0x%s" (Z.format (Printf.sprintf "%%0%dx" ((n + 3) / 4)) z)
  | VCtor _ when Option.is_some (as_list v) ->
      let vs = oget (as_list v) in
      Format.fprintf fmt "[@[<hov>%a@]]"
        (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt ";@ ") pp_value) vs
  | VCtor (p, _, []) ->
      Format.pp_print_string fmt (basename p)
  | VCtor (p, _, vs) ->
      Format.fprintf fmt "@[<hov 2>(%s@ %a)@]" (basename p)
        (Format.pp_print_list ~pp_sep:Format.pp_print_space pp_value) vs
  | VTuple vs ->
      Format.fprintf fmt "(@[<hov>%a@])"
        (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt ",@ ") pp_value) vs
  | VFun _ ->
      Format.pp_print_string fmt "<fun>"
  | VNeu (p, [], _) ->
      Format.pp_print_string fmt (tostring p)
  | VNeu (p, vs, _) ->
      Format.fprintf fmt "@[<hov 2>(%s@ %a)@]" (tostring p)
        (Format.pp_print_list ~pp_sep:Format.pp_print_space pp_value) vs
  | VWitness ->
      Format.pp_print_string fmt "witness"

and as_list (v : value) : value list option =
  match v with
  | VCtor (p, _, []) when p_equal p CI.CI_List.p_empty -> Some []
  | VCtor (p, _, [x; xs]) when p_equal p CI.CI_List.p_cons ->
      omap (fun xs -> x :: xs) (as_list xs)
  | _ -> None

let string_of_value (v : value) =
  Format.asprintf "%a" pp_value v

(* -------------------------------------------------------------------- *)
let rec value_eq (v1 : value) (v2 : value) : bool =
  match v1, v2 with
  | VInt z1, VInt z2 -> Z.equal z1 z2
  | VBool b1, VBool b2 -> b1 = b2
  | VBits (n1, z1), VBits (n2, z2) -> n1 = n2 && Z.equal z1 z2
  | VCtor (_, i1, vs1), VCtor (_, i2, vs2) ->
      i1 = i2 && List.for_all2 value_eq vs1 vs2
  | VTuple vs1, VTuple vs2 ->
      List.for_all2 value_eq vs1 vs2
  | VFun _, _ | _, VFun _ ->
      error "cannot decide the equality of two functions"
  | VWitness, _ | _, VWitness ->
      error "cannot decide an equality involving `witness'"
  | VNeu (_, _, id1), VNeu (_, _, id2) when id1 = id2 ->
      true
  | VNeu (p1, vs1, _), VNeu (p2, vs2, _)
      when p_equal p1 p2 && List.for_all2 value_eq vs1 vs2 ->
      true
  | VNeu _, _ | _, VNeu _ ->
      error "cannot decide the equality of %s and %s (abstract operator)"
        (string_of_value v1) (string_of_value v2)
  | _, _ ->
      error "ill-typed equality: %s = %s"
        (string_of_value v1) (string_of_value v2)

(* -------------------------------------------------------------------- *)
let as_int = function
  | VInt z -> z
  | v -> error "expecting an integer, got %s" (string_of_value v)

let as_bool = function
  | VBool b -> b
  | v -> error "expecting a boolean, got %s" (string_of_value v)

let rec as_bool_list (v : value) : bool list =
  match v with
  | VCtor (p, _, []) when p_equal p CI.CI_List.p_empty -> []
  | VCtor (p, _, [x; xs]) when p_equal p CI.CI_List.p_cons ->
      as_bool x :: as_bool_list xs
  | _ -> error "expecting a list, got %s" (string_of_value v)

let v_nil  = VCtor (CI.CI_List.p_empty, 0, [])
let v_cons = fun x xs -> VCtor (CI.CI_List.p_cons, 1, [x; xs])

let v_of_list (vs : value list) =
  List.fold_right v_cons vs v_nil

(* The remaining number of steps (function applications) of the current *)
(* evaluation; negative means unlimited.                                 *)
let steps = ref (-1)
let budget = ref 0
let used = ref 0                        (* steps used, for the profile *)

let tick () =
  incr used;
  if !steps >= 0 then begin
    if !steps = 0 then raise (StepLimit !budget);
    decr steps
  end

(* [n] steps at once: the same as [n] calls of [tick] in a row. *)
let tick_n (n : int) =
  used := !used + n;
  if !steps >= 0 then begin
    if !steps < n then (steps := 0; raise (StepLimit !budget));
    steps := !steps - n
  end

let apply (f : value) (v : value) : value =
  tick ();
  match f with
  | VFun f -> f v
  | _ -> error "expecting a function, got %s" (string_of_value f)

let apply_n (f : value) (vs : value list) : value =
  List.fold_left apply f vs

(* A curried function of [n] arguments. *)
let nary (n : int) (f : value list -> value) : value =
  let rec aux n acc =
    if n <= 0 then f (List.rev acc) else
    VFun (fun v -> aux (n - 1) (v :: acc))
  in aux n []

let fun1 f = nary 1 (function [a] -> f a | _ -> assert false)
let fun2 f = nary 2 (function [a; b] -> f a b | _ -> assert false)
let fun3 f = nary 3 (function [a; b; c] -> f a b c | _ -> assert false)

(* -------------------------------------------------------------------- *)
(* Memoisation of the functions given to abstract operators, such as    *)
(* [init f] for arrays: [(init f).[i]] is computed by the rule          *)
(* [(init f).[i] = f i], and without memoisation, an array defined in   *)
(* terms of another one would recompute every element of the latter on  *)
(* each read (exponential time for iterated array functions). The       *)
(* evaluation of operators is pure, so memoisation is transparent.      *)
let rec first_order (v : value) =
  match v with
  | VInt _ | VBool _ | VBits _ -> true
  | VCtor (_, _, vs) | VTuple vs -> List.for_all first_order vs
  | VFun _ | VNeu _ | VWitness -> false

let fresh_id : unit -> int =
  let counter = ref 0 in fun () -> incr counter; !counter

(* -------------------------------------------------------------------- *)
(* Memoisation of the applications of operators defined by a body (plain *)
(* definitions and fixpoints), per command. Keys are compared            *)
(* structurally, except for stuck applications (e.g. arrays), compared   *)
(* by identifier: this shares, e.g., the states of a sponge that is      *)
(* squeezed again from the start for each output byte. Applications to   *)
(* functions are not memoised. EC_EVAL_NOMEMO disables this.             *)
(* An environment variable is set when it has a non-empty value. *)
let env_flag (x : string) =
  match Sys.getenv_opt x with None | Some "" -> false | Some _ -> true

let no_op_memo = env_flag "EC_EVAL_NOMEMO"

(* The applications of operators evaluated by [eval] rules are memoised  *)
(* too (see [with_rules]); EC_EVAL_NORULEMEMO disables this.            *)
let no_rule_memo = no_op_memo || env_flag "EC_EVAL_NORULEMEMO"

(* Operators with few memo hits are no longer memoised (see [memo_op]); *)
(* EC_EVAL_NOADAPTIVE disables this.                                     *)
let adaptive_memo = not (env_flag "EC_EVAL_NOADAPTIVE")

let rec memo_eq (v1 : value) (v2 : value) =
  v1 == v2 ||
  match v1, v2 with
  | VInt z1, VInt z2 -> Z.equal z1 z2
  | VBool b1, VBool b2 -> b1 = b2
  | VBits (n1, z1), VBits (n2, z2) -> n1 = n2 && Z.equal z1 z2
  | VCtor (p1, i1, vs1), VCtor (p2, i2, vs2) ->
      (* the paths matter: an operator value is shared by all the type *)
      (* instances of a polymorphic operator ([None] vs. [[]])          *)
      i1 = i2 && p_equal p1 p2 && memo_eq_list vs1 vs2
  | VTuple vs1, VTuple vs2 -> memo_eq_list vs1 vs2
  | VNeu (_, _, id1), VNeu (_, _, id2) -> id1 = id2
  | VWitness, VWitness -> true
  | _, _ -> false

and memo_eq_list (vs1 : value list) (vs2 : value list) =
  match vs1, vs2 with
  | [], [] -> true
  | v1 :: vs1, v2 :: vs2 -> memo_eq v1 v2 && memo_eq_list vs1 vs2
  | _, _ -> false

(* A hash of the values, up to 2^20 nodes. It must not stop at a few    *)
(* nodes: the keys of an operator often share a long prefix (the inputs *)
(* of a hash function that start with the same key), and keys that hash *)
(* alike make every lookup compare with all of them.                     *)
let memo_hash (vs : value list) : int =
  let budget = ref (1 lsl 20) in
  let mix acc h = (acc * 65599 + h) land max_int in
  let rec doit acc v =
    if !budget <= 0 then acc else begin
      decr budget;
      match v with
      | VInt z -> mix acc (Z.hash z)
      | VBool b -> mix acc (if b then 1 else 2)
      | VBits (n, z) -> mix (mix acc n) (Z.hash z)
      | VCtor (_, i, vs) -> List.fold_left doit (mix acc i) vs
      | VTuple vs -> List.fold_left doit (mix acc 3) vs
      | VNeu (_, _, id) -> mix acc id
      | VFun _ -> mix acc 5
      | VWitness -> mix acc 7
    end
  in List.fold_left doit 17 vs

module MH = Hashtbl.Make (struct
  type t = value list
  let equal = memo_eq_list
  let hash = memo_hash
end)

(* The number of nodes of the values, at most [limit]. *)
let memo_size ?(limit = 1 lsl 20) (vs : value list) : int =
  let n = ref 0 in
  let rec doit v =
    if !n < limit then begin
      incr n;
      match v with
      | VCtor (_, _, vs) | VTuple vs -> List.iter doit vs
      | _ -> ()
    end
  in List.iter doit vs; !n

(* A memoisation table holds at most 65536 entries, and keys of at most *)
(* 2^22 nodes in all: keys can be long lists (the bits of the inputs of  *)
(* a hash function), and the tables of a long command would otherwise   *)
(* keep gigabytes alive. A full table is emptied: this costs only the   *)
(* recomputation of later hits.                                          *)
let memo_add (tbl : value MH.t) (nodes : int ref) (vs : value list) (r : value) =
  let k = memo_size vs in
  if MH.length tbl >= 65536 || !nodes + k > 1 lsl 22 then
    (MH.reset tbl; nodes := 0);
  nodes := !nodes + k;
  MH.add tbl vs r

let memo_stats : (string, int ref * int ref) Hashtbl.t = Hashtbl.create 16

(* Errors report the operators being evaluated (at most 8 of them). *)
let in_context (name : string) (f : unit -> 'a) : 'a =
  try f () with EvalError msg ->
    let depth = List.length (String.split_on_char '\n' msg) in
    if depth > 8 then raise (EvalError msg)
    else raise (EvalError (Printf.sprintf "%s\n  in %s" msg name))

(* The memoised version of [inner], a function of [n] arguments: the   *)
(* body of [memo_op], shared by the two engines.                         *)
let memo_call ~(name : string) (n : int) (inner : value list -> value) : value list -> value =
  if no_op_memo then (fun vs -> in_context name (fun () -> inner vs)) else
  let tbl = MH.create 64 in
  let (hits, misses) =
    match Hashtbl.find_opt memo_stats name with
    | Some c -> c
    | None -> let c = (ref 0, ref 0) in Hashtbl.add memo_stats name c; c in
  (* Adaptive: an operator whose applications are almost never repeated *)
  (* (fewer than 1 hit for 8 misses, after 1024 misses) is no longer     *)
  (* memoised in this command, and its table is freed.                   *)
  let on = ref true and h = ref 0 and m = ref 0 and nodes = ref 0 in
  ignore n;
  (fun vs ->
    if not !on || List.exists (function VFun _ -> true | _ -> false) vs then
      in_context name (fun () -> inner vs) else
    match MH.find_opt tbl vs with
    | Some r -> incr hits; incr h; r
    | None ->
        incr misses; incr m;
        let r = in_context name (fun () -> inner vs) in
        if adaptive_memo && !m >= 1024 && 8 * !h < !m then
          (on := false; MH.reset tbl)
        else memo_add tbl nodes vs r; r)

let memo_op ?(name = "") (n : int) (v : value) : value =
  if n = 0 then v else
  nary n (memo_call ~name n (fun vs -> apply_n v vs))

(* Keys of the memoisation of the functions given to abstract operators *)
module VH = Hashtbl.Make (struct
  type t = value
  let equal = memo_eq
  let hash v = memo_hash [v]
end)

let rec memo (v : value) : value =
  match v with
  | VFun f ->
      let tbl = VH.create 16 in
      VFun (fun x ->
        if not (first_order x) then f x else
        match VH.find_opt tbl x with
        | Some r -> r
        | None -> let r = memo (f x) in VH.add tbl x r; r)
  | _ -> v

(* -------------------------------------------------------------------- *)
(* Bitstrings                                                           *)
let bits_mask (n : int) = Z.pred (Z.shift_left Z.one n)

let v_bits (n : int) (z : Z.t) =
  VBits (n, Z.logand z (bits_mask n))

let bits_to_sint (n : int) (z : Z.t) =
  if Z.testbit z (n - 1) then Z.sub z (Z.shift_left Z.one n) else z

let bits_to_list (n : int) (z : Z.t) : value =
  v_of_list (List.init n (fun i -> VBool (Z.testbit z i)))

let bits_of_list (bs : bool list) : Z.t =
  List.fold_right
    (fun b acc -> Z.logor (Z.shift_left acc 1) (if b then Z.one else Z.zero))
    bs Z.zero

(* -------------------------------------------------------------------- *)
(* Program memories                                                     *)
type memory = {
  mutable locals  : value EcSymbols.Msym.t;
}

(* The compiled engine (see [comp] below) translates each formula once  *)
(* into a closure of the frame of its local variables.                   *)
type code = value array -> value

(* An operator, for the compiled engine: its value, and the function of  *)
(* its first [o_ar] arguments that the application of [o_val] to them    *)
(* runs after [o_ar] steps. Call sites with [o_ar] arguments count the   *)
(* steps and call [o_call] directly, without building the curried        *)
(* closures.                                                             *)
type opv = {
  o_val  : value;
  o_ar   : int;                       (* 0: no direct entry *)
  o_call : value list -> value;
  o_tmp  : bool;                      (* placeholder while resolving *)
}

(* A rule of the [eval] database, compiled on its first use: the frame  *)
(* holds its pattern variables, in the slots [cr_slots].                 *)
type crule = {
  cr_rule  : ER.rule;
  cr_arity : int;
  cr_slots : int Mid.t;
  cr_code  : (int * code list * code) Lazy.t;  (* frame size, conditions, rhs *)
  cr_pats  : (value array -> value -> unit) list option;
                                        (* matchers of the arguments *)
}

(* A procedure, compiled: its local variables are in a frame. *)
type cproc = {
  cp_name    : string;
  cp_size    : int;
  cp_params  : int option list;              (* slots of the parameters *)
  cp_body    : value array -> unit;
  cp_ret     : code option;
}

type state = {
  env      : EcEnv.env;
  profile  : (path, int ref) Hashtbl.t option;  (* calls per operator *)
  ops      : value EcPath.Hp.t;             (* tables keyed by path tags *)
  eqrules  : ER.rule list EcPath.Hp.t;      (* [eval] rules on [=], by type *)
  tynorm   : ty EcTypes.Hty.t;              (* [ty_hnorm], by type *)
  globals  : value EcSymbols.Msym.t ref;
  fuel     : int ref;                  (* bound on the procedure call depth *)
  native_words : bool;                 (* pragma Eval:native_words *)
  native_zmod  : bool;                 (* pragma Eval:native_zmod *)
  native_arrays : bool;                (* pragma Eval:native_arrays *)
  cops     : opv EcPath.Hp.t;          (* compiled engine: operators *)
  ceqrules : crule list EcPath.Hp.t;   (* compiled engine: [eqrules] *)
  cprocs   : (string, cproc) Hashtbl.t; (* compiled engine: procedures *)
}

(* [le_mem] and [le_glob] are the program variables visible from an    *)
(* expression: a snapshot of the frame taken when the evaluation of the *)
(* expression starts, so that the closures it builds do not observe the *)
(* later assignments of the procedure.                                  *)
type lenv = {
  le_locals : value Mid.t;
  le_mem    : memory option;
  le_glob   : value EcSymbols.Msym.t option;
}

let empty_lenv = { le_locals = Mid.empty; le_mem = None; le_glob = None; }

let bind_local (le : lenv) (x : EcIdent.t) (v : value) =
  { le with le_locals = Mid.add x v le.le_locals }

(* -------------------------------------------------------------------- *)
let ctor_arity (ty : ty) : int =
  List.length (fst (tyfun_flat ty))

let op_arity (op : operator) : int =
  List.length (fst (tyfun_flat op.op_ty))

(* -------------------------------------------------------------------- *)
(* Subtypes: [insub] and [val] of a [subtype] declaration are evaluated *)
(* on the underlying representation.                                    *)
let subtype_of (env : EcEnv.env) (ty : ty) =
  match ty.ty_node with
  | Tconstr (p, []) -> begin
      match EcEnv.Ty.by_path_opt p env with
      | Some { tyd_subtype = Some (carrier, pred) } -> Some (p, carrier, pred)
      | _ -> None
    end
  | _ -> None

let same_theory (sty : path) (op : path) =
  match prefix sty, prefix op with
  | Some ps, Some po ->
      p_equal ps po || (match prefix po with Some po -> p_equal ps po | None -> false)
  | _, _ -> false

let subtype_role (env : EcEnv.env) (p : path) (op : operator) =
  match op.op_kind, tyfun_flat op.op_ty with
  | OB_oper None, ([dom], codom) -> begin
      match codom.ty_node with
      | Tconstr (po, [sty]) when p_equal po CI.CI_Option.p_option -> begin
          match subtype_of env sty with
          | Some (sp, carrier, pred)
              when same_theory sp p && EcReduction.EqTest.for_type env carrier dom ->
              Some (`Insub pred)
          | _ -> None
        end
      | _ -> begin
          match subtype_of env dom with
          | Some (sp, carrier, _)
              when same_theory sp p && EcReduction.EqTest.for_type env carrier codom ->
              Some `Val
          | _ -> None
        end
    end
  | _ -> None

(* -------------------------------------------------------------------- *)
(* Native semantics of the core operators.                              *)
let p_modexp = EcPath.extend CI.p_top ["IntDiv"; "modexp"]

(* The core operators, as functions of their arguments with their      *)
(* number (0: constants, the value of [f []]).                           *)
let core_ops_n : (path * (int * (value list -> value))) list Lazy.t = lazy (
  let int1 f = (1, function [a] -> f (as_int a) | _ -> assert false) in
  let int2 f = (2, function [a; b] -> f (as_int a) (as_int b) | _ -> assert false) in
  let int3 f = (3, function [a; b; c] -> f (as_int a) (as_int b) (as_int c) | _ -> assert false) in
  let const v = (0, fun _ -> v) in
  let edivz m d =
    if Z.equal d Z.zero then (Z.zero, m) else Z.ediv_rem m d in
  let iteri = (3, function
    | [n; f; x] ->
        let n = as_int n in
        if Z.gt n (Z.of_int max_int) then error "iteri: too many iterations";
        let n = Z.to_int n in
        let x = ref x in
        for i = 0 to n - 1 do
          x := apply_n f [VInt (Z.of_int i); !x]
        done; !x
    | _ -> assert false) in
  let ipow_f x n =
    if Z.lt n Z.zero then error "negative exponent";
    if Z.gt n (Z.of_int max_int) then error "exponent too large";
    VInt (Z.pow x (Z.to_int n)) in
  let ipow = int2 ipow_f in
  let ipow_v = nary 2 (snd ipow) in
  CI.CI_Int.[
    p_int_add  , int2 (fun a b -> VInt (Z.add a b));
    p_int_mul  , int2 (fun a b -> VInt (Z.mul a b));
    p_int_opp  , int1 (fun a -> VInt (Z.neg a));
    p_int_lt   , int2 (fun a b -> VBool (Z.lt a b));
    p_int_le   , int2 (fun a b -> VBool (Z.leq a b));
    p_int_edivz, int2 (fun a b ->
                   let (q, r) = edivz a b in VTuple [VInt q; VInt r]);
    p_int_pow  , ipow;
    p_iteri    , iteri;
  ] @ CI.CI_Bool.[
    p_true , const (VBool true);
    p_false, const (VBool false);
    p_not  , (1, function [a] -> VBool (not (as_bool a)) | _ -> assert false);
    p_eq   , (2, function [a; b] -> VBool (value_eq a b) | _ -> assert false);
    p_iff  , (2, function [a; b] -> VBool (as_bool a = as_bool b) | _ -> assert false);
  ] @ [
    CI.CI_Witness.p_witness, const VWitness;
    p_modexp, int3 (fun b e m ->
      (* modexp b e m = (b ^ e) %% m *)
      if Z.lt e Z.zero then error "modexp: negative exponent";
      if Z.equal m Z.zero then
        apply_n ipow_v [VInt b; VInt e]
      else
        let m = Z.abs m in VInt (Z.erem (Z.powm b e m) m));
  ])

let core_ops : (path * value) list Lazy.t = lazy (
  List.map (fun (p, (n, f)) -> (p, if n = 0 then f [] else nary n f))
    (Lazy.force core_ops_n))

(* -------------------------------------------------------------------- *)
(* Native list primitives: the same functions as the fixpoints of       *)
(* List.ec, on lists whose spine is concrete; otherwise ([Stuck]), the  *)
(* definition of the operator is used.                                  *)
exception Stuck

let rec spine (v : value) : value list =
  match v with
  | VCtor (p, _, []) when p_equal p CI.CI_List.p_empty -> []
  | VCtor (p, _, [x; xs]) when p_equal p CI.CI_List.p_cons -> x :: spine xs
  | _ -> raise Stuck

let p_list (x : string) = EcPath.extend CI.p_top ["List"; x]

(* [drop], [take] and [nth] walk the first n cells only, and [drop]     *)
(* shares the rest of the list.                                          *)
let rec drop_v (n : int) (v : value) : value =
  if n <= 0 then v else
  match v with
  | VCtor (p, _, [_; xs]) when p_equal p CI.CI_List.p_cons -> drop_v (n - 1) xs
  | VCtor (p, _, []) when p_equal p CI.CI_List.p_empty -> v
  | _ -> raise Stuck

let take_v (n : int) (v : value) : value list =
  let rec doit acc n v =
    if n <= 0 then List.rev acc else
    match v with
    | VCtor (p, _, [x; xs]) when p_equal p CI.CI_List.p_cons -> doit (x :: acc) (n - 1) xs
    | VCtor (p, _, []) when p_equal p CI.CI_List.p_empty -> List.rev acc
    | _ -> raise Stuck in
  doit [] n v

let rec nth_v (dfl : value) (n : int) (v : value) : value =
  match v with
  | VCtor (p, _, [x; xs]) when p_equal p CI.CI_List.p_cons ->
      if n = 0 then x else nth_v dfl (n - 1) xs
  | VCtor (p, _, []) when p_equal p CI.CI_List.p_empty -> dfl
  | _ -> raise Stuck

let native_list_ops : (path * (int * (value list -> value))) list Lazy.t = lazy (
  let small n = if Z.fits_int n then Z.to_int n else if Z.sign n < 0 then min_int else max_int in
  [ p_list "size", (1, function
      | [l] -> VInt (Z.of_int (List.length (spine l)))
      | _ -> assert false);

    p_list "nth", (3, function
      | [x; l; n] ->
          let n = small (as_int n) in
          if n < 0 then x else nth_v x n l
      | _ -> assert false);

    p_list "drop", (2, function
      | [n; l] ->
          drop_v (small (as_int n)) l
      | _ -> assert false);

    p_list "take", (2, function
      | [n; l] -> v_of_list (take_v (small (as_int n)) l)
      | _ -> assert false);

    p_list "++", (2, function
      | [l1; l2] -> List.fold_right v_cons (spine l1) l2
      | _ -> assert false);

    p_list "catrev", (2, function
      | [l1; l2] -> List.fold_left (fun acc x -> v_cons x acc) l2 (spine l1)
      | _ -> assert false);

    p_list "map", (2, function
      | [f; l] -> v_of_list (List.map (apply f) (spine l))
      | _ -> assert false);

    p_list "filter", (2, function
      | [p; l] -> v_of_list (List.filter (fun x -> as_bool (apply p x)) (spine l))
      | _ -> assert false);

    p_list "foldr", (3, function
      | [f; z; l] -> List.fold_right (fun x acc -> apply_n f [x; acc]) (spine l) z
      | _ -> assert false);

    p_list "foldl", (3, function
      | [f; z; l] -> List.fold_left (fun acc x -> apply_n f [acc; x]) z (spine l)
      | _ -> assert false);

    p_list "rcons", (2, function
      | [l; z] -> List.fold_right v_cons (spine l) (v_cons z v_nil)
      | _ -> assert false);

    (* last x s: the last element of s, x if s is empty *)
    p_list "last", (2, function
      | [x; l] -> List.fold_left (fun _ y -> y) x (spine l)
      | _ -> assert false);

    (* zip s t: the pairs of the elements of s and t, as many as the shorter *)
    p_list "zip", (2, function
      | [s; t] ->
          let rec zip s t = match s, t with
            | x :: s, y :: t -> VTuple [x; y] :: zip s t
            | _, _ -> [] in
          v_of_list (zip (spine s) (spine t))
      | _ -> assert false);

    (* has, all and find stop at the first element that decides, as the *)
    (* lazy connectives of their definitions                             *)
    p_list "has", (2, function
      | [p; l] -> VBool (List.exists (fun x -> as_bool (apply p x)) (spine l))
      | _ -> assert false);

    p_list "all", (2, function
      | [p; l] -> VBool (List.for_all (fun x -> as_bool (apply p x)) (spine l))
      | _ -> assert false);

    p_list "find", (2, function
      | [p; l] ->
          let rec find i = function
            | [] -> i
            | x :: xs -> if as_bool (apply p x) then i else find (i + 1) xs in
          VInt (Z.of_int (find 0 (spine l)))
      | _ -> assert false);

    (* int2bs N n = [(n %/ 2^0) %% 2 <> 0; ...], of size N (bits of n in *)
    (* two's complement); bs2int s = sum of the 2^i * b2i s_i            *)
    EcPath.extend CI.p_top ["BitEncoding"; "BS2Int"; "int2bs"], (2, function
      | [nb; n] ->
          let n = as_int n in
          v_of_list (List.init (max 0 (small (as_int nb))) (fun i -> VBool (Z.testbit n i)))
      | _ -> assert false);

    EcPath.extend CI.p_top ["BitEncoding"; "BS2Int"; "bs2int"], (1, function
      | [l] ->
          let bits = List.map as_bool (spine l) in
          VInt (List.fold_right (fun b acc ->
            Z.logor (Z.shift_left acc 1) (if b then Z.one else Z.zero)) bits Z.zero)
      | _ -> assert false);

    EcPath.extend CI.p_top ["List"; "Iota"; "iota_"], (2, function
      (* iota_ i n = [i; ...; i + n - 1], [] when n <= 0 *)
      | [i; n] ->
          let i = as_int i and n = small (as_int n) in
          v_of_list (List.init (max 0 n) (fun k -> VInt (Z.add i (Z.of_int k))))
      | _ -> assert false);
  ])

let native_list_table : (int * (value list -> value)) EcPath.Mp.t Lazy.t =
  lazy (EcPath.Mp.of_list (Lazy.force native_list_ops))

(* -------------------------------------------------------------------- *)
(* Optional (pragma Eval:native_arrays): reads of the arrays of the      *)
(* Jasmin library (theories ArrayN.ArrayN, clones of PolyArray with      *)
(* size N): (init f).[i] = f i for 0 <= i < N (lemma initiE of           *)
(* PolyArray), without going through the eval rules. TRUSTED: a theory   *)
(* named ArrayN whose operators init and _.[_] are abstract is such a    *)
(* clone. Other reads (out of range, or of arrays not built by init)     *)
(* are left to the rules.                                                *)
let native_array_get (env : EcEnv.env) (p : path) : (value list -> value) option =
  match EcPath.prefix p with
  | Some th when EcPath.basename p = "_.[_]" -> begin
      let x = EcPath.basename th in
      let n =
        if String.length x > 5 && String.sub x 0 5 = "Array" then
          int_of_string_opt (String.sub x 5 (String.length x - 5))
        else None in
      let init = EcPath.pqname th "init" in
      let abstract q = match EcEnv.Op.by_path_opt q env with
        | Some { op_kind = OB_oper None } -> true | _ -> false in
      match n with
      | Some n when n > 0 && abstract p && abstract init ->
          Some (function
            | [VNeu (q, [f], _); VInt i]
                when p_equal q init && Z.leq Z.zero i && Z.lt i (Z.of_int n) ->
                apply f (VInt i)
            | _ -> raise Stuck)
      | _ -> None
    end
  | _ -> None

(* -------------------------------------------------------------------- *)
(* Optional (pragma Eval:native_words): the shifts and rotations of the *)
(* words of the Jasmin library (JWord.W8 ... W256), computed on the     *)
(* bound bitstrings instead of by their [eval] rules. TRUSTED: these    *)
(* functions must agree with the definitions of JWord.BitWord:          *)
(*   (x `>>>` i).[j] = x.[j + i]      (x `<<<` i).[j] = x.[j - i]       *)
(*   (ror x i).[j] = x.[(j + i) %% n]  (rol x i).[j] = x.[(j - i) %% n]  *)
(* where x.[k] = false outside [0, n).                                  *)
let native_word_op (p : path) : (value list -> value) option =
  let shift n x i =                     (* bit j of the result: x.[j - i] *)
    let i = if Z.fits_int i then Z.to_int i else if Z.sign i < 0 then -n else n in
    if i >= n || i <= -n then v_bits n Z.zero
    else if i >= 0 then v_bits n (Z.shift_left x i)
    else VBits (n, Z.shift_right x (-i)) in
  let rotl n x i =                      (* bit j of the result: x.[(j - i) %% n] *)
    let r = Z.to_int (Z.erem i (Z.of_int n)) in
    v_bits n (Z.logor (Z.shift_left x r) (Z.shift_right x (n - r))) in
  match EcPath.tolist p with
  | ["Top"; "JWord"; w; op]
    when List.mem w ["W8"; "W16"; "W32"; "W64"; "W128"; "W256"] -> begin
      let n = int_of_string (String.sub w 1 (String.length w - 1)) in
      let op2 f = Some (function
        | [VBits (m, x); VInt i] when m = n -> f x i
        | _ -> raise Stuck) in
      match op with
      | ">>>" | "`>>>`" -> op2 (fun x i -> shift n x (Z.neg i))
      | "<<<" | "`<<<`" -> op2 (fun x i -> shift n x i)
      | "rol" -> op2 (fun x i -> rotl n x i)
      | "ror" -> op2 (fun x i -> rotl n x (Z.neg i))
      | _ -> None
    end
  | _ -> None

let core_table : value EcPath.Mp.t Lazy.t =
  lazy (EcPath.Mp.of_list (Lazy.force core_ops))

(* Lazy boolean connectives, handled at application sites. *)
let lazy_bool (p : path) =
  if p_equal p CI.CI_Bool.p_and || p_equal p CI.CI_Bool.p_anda then Some `And
  else if p_equal p CI.CI_Bool.p_or || p_equal p CI.CI_Bool.p_ora then Some `Or
  else if p_equal p CI.CI_Bool.p_imp then Some `Imp
  else None

(* -------------------------------------------------------------------- *)
(* Bindings: bitstrings and bit-vector operators                        *)
let binding_size ((_, n) : binding_size) =
  match n with
  | Some n -> n
  | None -> error "bitstring binding without a concrete size"

(* Values of a bitstring type: [bool], when bound as a 1-bit bitstring, *)
(* keeps its native representation.                                     *)
let z_of_bits (v : value) : Z.t =
  match v with
  | VBits (_, z) -> z
  | VBool b -> if b then Z.one else Z.zero
  | _ -> error "expecting a bitstring, got %s" (string_of_value v)

let is_bool_type (p : path) =
  p_equal p CI.CI_Bool.p_bool

let mk_bits (isbool : bool) (n : int) (z : Z.t) : value =
  if isbool then VBool (Z.testbit z 0) else v_bits n z

let un_n f = (1, function [a] -> f a | _ -> assert false)
let bin_n f = (2, function [a; b] -> f a b | _ -> assert false)

let bitstring_op_n (bs : crb_bitstring) kind : int * (value list -> value) =
  let n = binding_size bs.size in
  match kind with
  | `To -> un_n (fun w -> bits_to_list n (z_of_bits w))
  | `From -> raise Not_found          (* handled by [from_bits] below *)
  | `OfInt -> un_n (fun i -> mk_bits (is_bool_type bs.type_) n (as_int i))
  | `ToUInt -> un_n (fun w -> VInt (z_of_bits w))
  | `ToSInt -> un_n (fun w -> VInt (bits_to_sint n (z_of_bits w)))

let bitstring_op (bs : crb_bitstring) kind : value =
  let (n, f) = bitstring_op_n bs kind in nary n f

let bvoperator_n (env : EcEnv.env) (bo : crb_bvoperator) : (int * (value list -> value)) option =
  let size_of (v : value) =
    match v with
    | VBits (n, _) -> (false, n)
    | VBool _ -> (true, 1)
    | _ -> error "expecting a bitstring, got %s" (string_of_value v) in
  let un f = Some (un_n (fun a ->
    let (b, n) = size_of a in mk_bits b n (f n (z_of_bits a)))) in
  let bin f = Some (bin_n (fun a1 a2 ->
    let (b, n) = size_of a1 in mk_bits b n (f n (z_of_bits a1) (z_of_bits a2)))) in
  let bitstring_type i =
    let p = List.nth bo.types i in
    match EcEnv.Circuit.lookup_bitstring_path env p with
    | Some bs -> (is_bool_type p, binding_size bs.size)
    | None -> error "no bitstring binding for %s" (tostring p) in
  match bo.kind with
  | `Add _ -> bin (fun _ -> Z.add)
  | `Sub _ -> bin (fun _ -> Z.sub)
  | `Mul _ -> bin (fun _ -> Z.mul)
  | `Opp _ -> un  (fun _ -> Z.neg)
  | `And _ -> bin (fun _ -> Z.logand)
  | `Or  _ -> bin (fun _ -> Z.logor)
  | `Xor _ -> bin (fun _ -> Z.logxor)
  | `Not _ -> un  (fun n x -> Z.logxor x (bits_mask n))

  | `Get _ ->
      (* bvget : BV1.bv -> int -> BV2.bv, BV2 of size 1 *)
      let (isbool, _) = bitstring_type 1 in
      Some (bin_n (fun w i ->
        let (_, n) = size_of w in
        let i = as_int i in
        let bit = Z.leq Z.zero i && Z.lt i (Z.of_int n)
                  && Z.testbit (z_of_bits w) (Z.to_int i) in
        mk_bits isbool 1 (if bit then Z.one else Z.zero)))

  | `Init _ ->
      (* bvinit : (int -> BV1.bv) -> BV2.bv, BV1 of size 1 *)
      let (isbool, n) = bitstring_type 1 in
      Some (un_n (fun f ->
        let z = ref Z.zero in
        for i = n - 1 downto 0 do
          let b = z_of_bits (apply f (VInt (Z.of_int i))) in
          z := Z.logor (Z.shift_left !z 1) (Z.logand b Z.one)
        done;
        mk_bits isbool n !z))

  | _ -> None

let bvoperator (env : EcEnv.env) (bo : crb_bvoperator) : value option =
  omap (fun (n, f) -> nary n f) (bvoperator_n env bo)

(* -------------------------------------------------------------------- *)
(* Rules of the [eval] database                                         *)
let eval_base = "eval"

(* -------------------------------------------------------------------- *)
(* EC_EVAL_PROFILE=time: the time spent in the applications of each      *)
(* operator, excluding the applications it makes itself (self time).     *)
let profile_time =
  match Sys.getenv_opt "EC_EVAL_PROFILE" with Some "time" -> true | _ -> false

let self_time : (path, float ref * int ref) Hashtbl.t = Hashtbl.create 256
let prof_stack : float ref list ref = ref []         (* time of the callees *)

let timed (p : path) (k : unit -> value) : value =
  let callees = ref 0.0 in
  prof_stack := callees :: !prof_stack;
  let t0 = Unix.gettimeofday () in
  let finish () =
    let dt = Unix.gettimeofday () -. t0 in
    prof_stack := List.tl !prof_stack;
    (match !prof_stack with c :: _ -> c := !c +. dt | [] -> ());
    let (t, n) =
      match Hashtbl.find_opt self_time p with
      | Some x -> x
      | None -> let x = (ref 0.0, ref 0) in Hashtbl.add self_time p x; x in
    t := !t +. (dt -. !callees); incr n in
  match k () with
  | v -> finish (); v
  | exception e -> finish (); raise e

let int_binop (p : path) : (Z.t -> Z.t -> value) option =
  let open CI.CI_Int in
  if p_equal p p_int_add then Some (fun a b -> VInt (Z.add a b))
  else if p_equal p p_int_mul then Some (fun a b -> VInt (Z.mul a b))
  else if p_equal p p_int_lt then Some (fun a b -> VBool (Z.lt a b))
  else if p_equal p p_int_le then Some (fun a b -> VBool (Z.leq a b))
  else None

let count_app (st : state) (p : path) =
  match st.profile with
  | Some tbl -> begin
      match Hashtbl.find_opt tbl p with
      | Some n -> incr n
      | None -> Hashtbl.add tbl p (ref 1)
    end
  | None -> ()

(* Optional (pragma Eval:native_zmod): integers modulo p, as in the     *)
(* clones of ZModP.ZModRing, whatever the names of their operators.     *)
(* Operators are recognised by their definitions, and their native      *)
(* versions compute exactly these definitions:                          *)
(*   inzmod z = S.insubd (z %% p) (that is, (edivz z p).`2), where the  *)
(*     predicate of the subtype S is 0 <= x < p: then z %% p satisfies  *)
(*     it, and inzmod z = z %% p;                                        *)
(*   asint z = S.val z: the identity (as for every subtype);             *)
(*   x + y = inzmod (asint x + asint y), x * y = inzmod (asint x * asint *)
(*     y), [-] x = inzmod (- asint x): (x + y) %% p, ... on the values.  *)
(*   exp x n = iterop n ( * ) x one for n >= 0 (Ring.ComRing.exp), with  *)
(*     ( * ) as above: x ^ n %% p for n > 0, one for n = 0; for n < 0,   *)
(*     the definition (or the eval rules).                               *)
(* p is the value of the two (closed) expressions, which must agree.     *)
(* [ev] evaluates closed formulas.                                       *)
let native_zmod_op (ev : form -> value) (env : EcEnv.env) (p : path)
  : (int * (value list -> value)) option =
  let rec lam (f : form) =
    match f.f_node with
    | Fquant (Llambda, bds, b) ->
        let (xs, b) = lam b in (List.map fst bds @ xs, b)
    | _ -> ([], f) in
  let app (f : form) =
    match f.f_node with
    | Fapp ({ f_node = Fop (q, _) }, args) -> Some (q, args)
    | _ -> None in
  let is_local x (f : form) =
    match f.f_node with Flocal y -> EcIdent.id_equal x y | _ -> false in
  let body (q : path) =
    match EcEnv.Op.by_path_opt q env with
    | Some { op_kind = OB_oper (Some (OP_Plain f)) } -> Some (lam f)
    | _ -> None in
  let closed_int (f : form) =
    try (match ev f with VInt z -> Some z | _ -> None)
    with EvalError _ | Stuck -> None in
  (* the modulus of an operator [inzmod], if it is one *)
  let inzmod (q : path) : Z.t option =
    match body q with
    | Some ([z], b) -> begin
        match app b with
        | Some (ins, [a]) when EcPath.basename ins = "insubd" -> begin
            (* z %% e is an abbreviation for (edivz z e).`2 *)
            let modz = match a.f_node with
              | Fproj (d, 1) -> (match app d with
                  | Some (m, [x; e]) when p_equal m CI.CI_Int.p_int_edivz -> Some (x, e)
                  | _ -> None)
              | _ -> None in
            match modz, EcPath.prefix ins with
            | Some (x, e), Some sub when is_local z x -> begin
                let insub = EcPath.pqname sub "insub" in
                match EcEnv.Op.by_path_opt insub env with
                | None -> None
                | Some iop ->
                match subtype_role env insub iop with
                | Some (`Insub pred) -> begin
                    match lam pred with
                    | ([y], pb) -> begin
                        match app pb with
                        | Some (a, [l; r]) when p_equal a CI.CI_Bool.p_and || p_equal a CI.CI_Bool.p_anda -> begin
                            match app l, app r with
                            | Some (le, [zero; y1]), Some (lt, [y2; e2])
                                when p_equal le CI.CI_Int.p_int_le && p_equal lt CI.CI_Int.p_int_lt
                                  && is_local y y1 && is_local y y2
                                  && (match zero.f_node with Fint z -> Z.equal (EcBigInt.to_zt z) Z.zero | _ -> false) -> begin
                                match closed_int e, closed_int e2 with
                                | Some m1, Some m2 when Z.equal m1 m2 && Z.sign m1 > 0 -> Some m1
                                | _ -> None
                              end
                            | _ -> None
                          end
                        | _ -> None
                      end
                    | _ -> None
                  end
                | _ -> None
              end
            | _ -> None
          end
        | _ -> None
      end
    | _ -> None in
  let asint (q : path) : bool =
    match body q with
    | Some ([z], b) -> begin
        match app b with
        | Some (v, [x]) when is_local z x -> begin
            match EcEnv.Op.by_path_opt v env with
            | Some vop -> subtype_role env v vop = Some `Val
            | None -> false
          end
        | _ -> false
      end
    | _ -> false in
  (* [i (f (a x) ...)], with i an inzmod and a an asint *)
  let lifted (q : path) =
    match body q with
    | Some (xs, b) -> begin
        match app b with
        | Some (i, [e]) -> begin
            match inzmod i, app e with
            | Some m, Some (f, args)
                when List.length args = List.length xs
                  && List.for_all2 (fun x a ->
                       match app a with
                       | Some (c, [y]) -> is_local x y && asint c
                       | _ -> false) xs args -> Some (m, f, List.length xs)
            | _ -> None
          end
        | _ -> None
      end
    | None -> None in
  (* exp x n = if n < 0 then ... else iterop n mul x one (Ring.ComRing), *)
  (* with mul a native multiplication: for n >= 0, iterop gives one when *)
  (* n = 0 and the product of n copies of x otherwise                   *)
  let exp (q : path) =
    match body q with
    | Some ([x; n], { f_node = Fif (_, _, e) }) -> begin
        match app e with
        | Some (it, [nn; { f_node = Fop (mul, _) }; xx; one])
            when EcPath.basename it = "iterop"
              && (match EcPath.prefix it with Some t -> EcPath.basename t = "IterOp" | None -> false)
              && is_local n nn && is_local x xx -> begin
            match lifted mul with
            | Some (m, f, 2) when p_equal f CI.CI_Int.p_int_mul -> begin
                try Some (m, ev one) with EvalError _ | Stuck -> None
              end
            | _ -> None
          end
        | _ -> None
      end
    | _ -> None in
  let int1 f = function [VInt a] -> f a | _ -> raise Stuck in
  let int2 f = function [VInt a; VInt b] -> f a b | _ -> raise Stuck in
  match inzmod p with
  | Some m -> Some (1, int1 (fun z -> VInt (Z.erem z m)))
  | None ->
  if asint p then Some (1, function [v] -> v | _ -> raise Stuck) else
  match lifted p with
  | Some (m, f, 2) when p_equal f CI.CI_Int.p_int_add ->
      Some (2, int2 (fun a b -> VInt (Z.erem (Z.add a b) m)))
  | Some (m, f, 2) when p_equal f CI.CI_Int.p_int_mul ->
      Some (2, int2 (fun a b -> VInt (Z.erem (Z.mul a b) m)))
  | Some (m, f, 1) when p_equal f CI.CI_Int.p_int_opp ->
      Some (1, int1 (fun a -> VInt (Z.erem (Z.neg a) m)))
  | _ ->
  match exp p with
  | Some (m, one) ->
      Some (2, int2 (fun a n ->
        if Z.sign n < 0 then raise Stuck
        else if Z.sign n = 0 then one
        else VInt (Z.powm (Z.erem a m) n m)))
  | None -> None

(* The memoised version of [try_rules] (see [with_rules]), shared by the *)
(* two engines.                                                          *)
let rules_memo (try_rules : value list -> value) : value list -> value =
  if no_rule_memo then try_rules else
  (* Memoised on first-order arguments, as for the operators defined by *)
  (* a body: the rules are equations, so this is transparent.           *)
  (* adaptive, as in [memo_op] *)
  let tbl = MH.create 64 in
  let on = ref true and h = ref 0 and m = ref 0 and nodes = ref 0 in
  (fun vs ->
    if not !on || not (List.for_all first_order vs) then try_rules vs else
    match MH.find_opt tbl vs with
    | Some r -> incr h; r
    | None ->
        incr m;
        let r = try_rules vs in
        if adaptive_memo && !m >= 1024 && 8 * !h < !m then
          (on := false; MH.reset tbl)
        else memo_add tbl nodes vs r; r)

let rec eval (st : state) (le : lenv) (f : form) : value =
  match f.f_node with
  | Fint z ->
      VInt (EcBigInt.to_zt z)

  | Flocal x -> begin
      match Mid.find_opt x le.le_locals with
      | Some v -> v
      | None -> error "unbound local variable: %s" (EcIdent.name x)
    end

  | Fpvar (pv, _) ->
      read_pvar st le pv

  | Fop (p, _) ->
      op_value st p

  | Fapp ({ f_node = Fop (p, [ty]) }, [a1; a2]) when p_equal p CI.CI_Bool.p_eq ->
      let v1 = eval st le a1 in
      let v2 = eval st le a2 in
      VBool (eq_typed st ty v1 v2)

  | Fapp ({ f_node = Fop (p, _) }, a1 :: args) when Option.is_some (lazy_bool p) ->
      let b1 = as_bool (eval st le a1) in
      let rest () =
        match args with
        | a2 :: args -> (eval st le a2, args)
        | [] -> error "partial application of a boolean connective" in
      let res, args =
        match oget (lazy_bool p) with
        | `And -> if b1 then rest () else (VBool false, List.tl args)
        | `Or  -> if b1 then (VBool true, List.tl args) else rest ()
        | `Imp -> if b1 then rest () else (VBool true, List.tl args) in
      apply_n res (List.map (eval st le) args)

  (* Integer arithmetic and comparisons, and [m %% d] and [m %/ d]       *)
  (* (abbreviations for the projections of [edivz m d]), computed        *)
  (* directly: the same functions as [core_ops], without looking up the  *)
  (* operator and building its curried closure.                          *)
  | Fapp ({ f_node = Fop (p, _) }, [a1; a2])
      when not profile_time && Option.is_some (int_binop p) -> begin
      match eval st le a1, eval st le a2 with
      | VInt z1, VInt z2 ->
          count_app st p; tick (); tick ();
          (oget (int_binop p)) z1 z2
      | _, _ -> error "expecting integers"
    end

  | Fproj ({ f_node = Fapp ({ f_node = Fop (p, _) }, [a1; a2]) }, i)
      when not profile_time && p_equal p CI.CI_Int.p_int_edivz -> begin
      match eval st le a1, eval st le a2 with
      | VInt m, VInt d ->
          count_app st p; tick (); tick ();
          let (q, r) = if Z.equal d Z.zero then (Z.zero, m) else Z.ediv_rem m d in
          VInt (if i = 0 then q else r)
      | _, _ -> error "expecting integers"
    end

  | Fapp (f, args) ->
      let fv = eval st le f in
      (match st.profile, f.f_node with
       | Some tbl, Fop (p, _) -> begin
           match Hashtbl.find_opt tbl p with
           | Some n -> incr n
           | None -> Hashtbl.add tbl p (ref 1)
         end
       | _, _ -> ());
      let vs = List.map (eval st le) args in
      (match profile_time, f.f_node with
       | true, Fop (p, _) -> timed p (fun () -> apply_n fv vs)
       | _, _ -> apply_n fv vs)

  | Fquant (Llambda, bds, body) ->
      let xs = List.map fst bds in
      let rec mk le = function
        | [] -> eval st le body
        | x :: xs -> VFun (fun v -> mk (bind_local le x v) xs)
      in mk le xs

  | Fquant ((Lforall | Lexists), _, _) ->
      error "cannot evaluate a quantifier"

  | Fif (c, f1, f2) ->
      if as_bool (eval st le c) then eval st le f1 else eval st le f2

  | Fmatch (c, bs, _) -> begin
      match eval st le c with
      | VCtor (_, i, vs) -> apply_n (eval st le (List.nth bs i)) vs
      | v -> error "cannot match on %s" (string_of_value v)
    end

  | Flet (lp, f1, f2) ->
      let v1 = eval st le f1 in
      eval st (bind_lpattern le lp v1) f2

  | Ftuple fs ->
      VTuple (List.map (eval st le) fs)

  | Fproj (f1, i) -> begin
      match eval st le f1 with
      | VTuple vs -> List.nth vs i
      | v -> error "cannot project %s" (string_of_value v)
    end

  | Fglob _ | Fpr _
  | FhoareF _ | FhoareS _ | FbdHoareF _ | FbdHoareS _
  | FeHoareF _ | FeHoareS _ | FequivF _ | FequivS _ | FeagerF _ ->
      error "cannot evaluate a program logic formula"

and bind_lpattern (le : lenv) (lp : lpattern) (v : value) =
  match lp, v with
  | LSymbol (x, _), _ -> bind_local le x v
  | LTuple xs, VTuple vs ->
      List.fold_left2 (fun le (x, _) v -> bind_local le x v) le xs vs
  | LRecord (_, xs), VCtor (_, _, vs) ->
      List.fold_left2
        (fun le (x, _) v -> ofold (fun x le -> bind_local le x v) le x) le xs vs
  | _, _ ->
      error "cannot destructure %s" (string_of_value v)

(* -------------------------------------------------------------------- *)
and op_value (st : state) (p : path) : value =
  match EcPath.Hp.find_opt st.ops p with
  | Some v -> v
  | None ->
      (* Recursive operators refer to themselves: tie the knot lazily. *)
      let cell = ref None in
      EcPath.Hp.replace st.ops p (VFun (fun v ->
        match !cell with
        | Some f -> apply f v
        | None -> error "ill-founded definition of %s" (tostring p)));
      let v =
        try in_context (tostring p) (fun () -> op_value_r st p)
        with e -> EcPath.Hp.remove st.ops p; raise e in
      cell := Some v;
      EcPath.Hp.replace st.ops p v; v

and op_value_r (st : state) (p : path) : value =
  let env = st.env in

  match EcPath.Mp.find_opt p (Lazy.force core_table) with
  | Some v -> v
  | None ->

  let op =
    match EcEnv.Op.by_path_opt p env with
    | Some op -> op
    | None -> error "unknown operator: %s" (tostring p) in

  match (if st.native_words then native_word_op p else None) with
  | Some f ->
      let dfl = lazy (
        match EcEnv.Reduction.get ~base:eval_base (`Path p) env with
        | (_ :: _) as rules -> with_rules st rules (fun () -> definition st p op)
        | [] -> definition st p op) in
      nary 2 (fun vs -> try f vs with Stuck -> apply_n (Lazy.force dfl) vs)
  | None ->

  match (if st.native_arrays then native_array_get env p else None) with
  | Some f ->
      let dfl = lazy (
        match EcEnv.Reduction.get ~base:eval_base (`Path p) env with
        | (_ :: _) as rules -> with_rules st rules (fun () -> definition st p op)
        | [] -> definition st p op) in
      nary 2 (fun vs -> try f vs with Stuck -> apply_n (Lazy.force dfl) vs)
  | None ->

  match (if st.native_zmod then native_zmod_op (eval st empty_lenv) env p else None) with
  | Some (0, f) -> f []
  | Some (n, f) ->
      let dfl = lazy (
        match EcEnv.Reduction.get ~base:eval_base (`Path p) env with
        | (_ :: _) as rules -> with_rules st rules (fun () -> definition st p op)
        | [] -> definition st p op) in
      nary n (fun vs -> try f vs with Stuck -> apply_n (Lazy.force dfl) vs)
  | None ->

  match EcPath.Mp.find_opt p (Lazy.force native_list_table) with
  | Some (n, f) ->
      let dfl = lazy (
        match EcEnv.Reduction.get ~base:eval_base (`Path p) env with
        | (_ :: _) as rules -> with_rules st rules (fun () -> definition st p op)
        | [] -> definition st p op) in
      nary n (fun vs -> try f vs with Stuck -> apply_n (Lazy.force dfl) vs)
  | None ->

  match EcEnv.Circuit.reverse_bitstring_operator env p with
  | Some (bs, `From) -> from_bits st bs p op
  | Some (bs, kind) -> bitstring_op bs kind
  | None ->

  match obind (bvoperator env) (EcEnv.Circuit.reverse_bvoperator env p) with
  | Some v -> v
  | None ->

  match EcEnv.Reduction.get ~base:eval_base (`Path p) env with
  | (_ :: _) as rules -> with_rules st rules (fun () -> definition st p op)
  | [] ->

  (* Abstract operators fall back on the default simplification rules, *)
  (* e.g. [(init f).[i] = f i] for the arrays of the Jasmin library.    *)
  match op.op_kind with
  | OB_oper None when Option.is_none (subtype_role env p op) -> begin
      match EcEnv.Reduction.get (`Path p) env with
      | (_ :: _) as rules -> with_rules st rules (fun () -> definition st p op)
      | [] -> definition st p op
    end
  | _ -> definition st p op

(* A bitstring from its list of bits; lists of the wrong size are       *)
(* handed over to the definition of the operator, if any.               *)
and from_bits (st : state) (bs : crb_bitstring) (p : path) (op : operator) =
  let n = binding_size bs.size in
  let bs_type = bs.type_ in
  let dfl = lazy (
    match EcEnv.Reduction.get ~base:eval_base (`Path p) st.env with
    | (_ :: _) as rules -> with_rules st rules (fun () -> definition st p op)
    | [] -> definition st p op) in
  fun1 (fun l ->
    let bs = as_bool_list l in
    if List.length bs = n then mk_bits (is_bool_type bs_type) n (bits_of_list bs)
    else apply (Lazy.force dfl) l)

and definition (st : state) (p : path) (op : operator) : value =
  match op.op_kind with
  | OB_oper (Some (OP_Plain f)) ->
      memo_op ~name:(tostring p) (op_arity op) (eval st empty_lenv f)

  | OB_oper (Some (OP_Constr (_, i))) ->
      let n = ctor_arity op.op_ty in
      nary n (fun vs -> VCtor (p, i, vs))

  | OB_oper (Some (OP_Record _)) ->
      let n = ctor_arity op.op_ty in
      nary n (fun vs -> VCtor (p, 0, vs))

  | OB_oper (Some (OP_Proj (_, i, _))) ->
      fun1 (function
        | VCtor (_, _, vs) -> List.nth vs i
        | v -> error "cannot project %s" (string_of_value v))

  | OB_oper (Some (OP_Fix fix)) ->
      memo_op ~name:(tostring p) (op_arity op) (fixdef st fix)

  | OB_oper (Some (OP_TC | OP_Exn _)) ->
      error "cannot evaluate operator %s" (tostring p)

  | OB_pred (Some (PR_Plain f)) ->
      eval st empty_lenv f

  | OB_pred (Some (PR_Ind _)) ->
      error "cannot evaluate inductive predicate %s" (tostring p)

  | OB_nott nt ->
      let body = form_of_expr nt.ont_body in
      let xs = List.map fst nt.ont_args in
      nary (List.length xs) (fun vs ->
        let le = List.fold_left2 bind_local empty_lenv xs vs in
        eval st le body)

  | OB_oper None | OB_pred None -> begin
      match subtype_role st.env p op with
      | Some (`Insub pred) ->
          let pred = lazy (eval st empty_lenv pred) in
          fun1 (fun v ->
            if as_bool (apply (Lazy.force pred) v)
            then VCtor (CI.CI_Option.p_some, 1, [v])
            else VCtor (CI.CI_Option.p_none, 0, []))
      | Some `Val -> fun1 (fun v -> v)
      | None ->
          let n = op_arity op in
          nary n (fun vs -> VNeu (p, List.map memo vs, fresh_id ()))
    end

and fixdef (st : state) (fix : opfix) : value =
  let xs = List.map fst fix.opf_args in
  let pos = fst fix.opf_struct in
  nary (List.length xs) (fun vs ->
    let le = List.fold_left2 bind_local empty_lenv xs vs in
    let args = Array.of_list vs in
    let rec descend br ps acc =
      match br, ps with
      | OPB_Leaf (bds, body), [] ->
          let le =
            List.fold_left2
              (fun le bds cvs -> List.fold_left2 (fun le (x, _) v -> bind_local le x v) le bds cvs)
              le bds (List.rev acc) in
          eval st le (form_of_expr body)
      | OPB_Branch bs, i :: ps -> begin
          match args.(i) with
          | VCtor (_, idx, cvs) ->
              descend (Parray.get bs idx).opb_sub ps (cvs :: acc)
          | v -> error "cannot match on %s" (string_of_value v)
        end
      | _, _ -> error "ill-formed fixpoint definition"
    in descend fix.opf_branches pos [])

(* Use the rules of the [eval] database, falling back to [dfl] when no  *)
(* rule applies.                                                        *)
and with_rules (st : state) (rules : ER.rule list) (dfl : unit -> value) =
  let arity = function
    | { ER.rl_ptn = ER.Rule (`Op _, args) } -> List.length args
    | _ -> 0 in
  let n = List.fold_left (fun n r -> max n (arity r)) 0 rules in
  let rules = List.sort (fun r1 r2 -> compare r1.ER.rl_prio r2.ER.rl_prio) rules in
  let dfl = lazy (dfl ()) in
  let rec try_rules vs = function
    | [] -> apply_n (Lazy.force dfl) vs
    | r :: rules ->
        let k = arity r in
        let args, extra = List.split_at k vs in
        match match_rule st r args with
        | Some le -> apply_n (eval st le r.ER.rl_tg) extra
        | None -> try_rules vs rules
        | exception EvalError _ -> try_rules vs rules
  in
  if n = 0 then try_rules [] rules else
  nary n (rules_memo (fun vs -> try_rules vs rules))

and match_rule (st : state) (r : ER.rule) (args : value list) : lenv option =
  let exception NoMatch in
  let rec doit le ptn v =
    match ptn, v with
    | ER.Var x, _ -> begin
        match Mid.find_opt x le.le_locals with
        | None -> bind_local le x v
        | Some v' -> if value_eq v v' then le else raise NoMatch
      end
    | ER.Int z, VInt z' ->
        if Z.equal (EcBigInt.to_zt z) z' then le else raise NoMatch
    | ER.Rule (`Tuple, ps), VTuple vs when List.length ps = List.length vs ->
        List.fold_left2 doit le ps vs
    | ER.Rule (`Op (q, _), ps), VCtor (q', _, vs)
        when p_equal q q' && List.length ps = List.length vs ->
        List.fold_left2 doit le ps vs
    | ER.Rule (`Op (q, _), ps), VNeu (q', vs, _)
        when p_equal q q' && List.length ps = List.length vs ->
        List.fold_left2 doit le ps vs
    | ER.Rule (`Op (q, []), []), VBool b
        when p_equal q (if b then CI.CI_Bool.p_true else CI.CI_Bool.p_false) ->
        le
    | _, _ -> raise NoMatch
  in
  match r.ER.rl_ptn with
  | ER.Rule (`Op _, ps) -> begin
      try
        let le = List.fold_left2 doit empty_lenv ps args in
        if List.for_all (fun c -> as_bool (eval st le c)) r.ER.rl_cond
        then Some le else None
      with NoMatch -> None
    end
  | _ -> None

(* -------------------------------------------------------------------- *)
(* Equality at type [ty]: componentwise on tuples; for a type [p], the  *)
(* rules of the [eval] database whose left-hand side is an equality at  *)
(* type [p] (e.g. [(a = b) <=> (to_list a = to_list b)] for arrays);    *)
(* structural otherwise.                                                *)
and hnorm (st : state) (ty : ty) : ty =
  match EcTypes.Hty.find_opt st.tynorm ty with
  | Some ty -> ty
  | None -> let n = EcEnv.ty_hnorm ty st.env in EcTypes.Hty.add st.tynorm ty n; n

and eq_typed (st : state) (ty : ty) (v1 : value) (v2 : value) : bool =
  let ty = hnorm st ty in
  match ty.ty_node, v1, v2 with
  | Ttuple tys, VTuple vs1, VTuple vs2 when List.length tys = List.length vs1 ->
      List.for_all2 (fun ty (v1, v2) -> eq_typed st ty v1 v2)
        tys (List.combine vs1 vs2)
  | Tconstr (p, _), _, _ -> begin
      let rule_ty (r : ER.rule) =
        match r.ER.rl_ptn with
        | ER.Rule (`Op (_, [rty]), [_; _]) -> begin
            match (hnorm st rty).ty_node with
            | Tconstr (q, _) -> Some q
            | _ -> None
          end
        | _ -> None in
      let rules =
        match EcPath.Hp.find_opt st.eqrules p with
        | Some rules -> rules
        | None ->
            let rules =
              EcEnv.Reduction.get ~base:eval_base (`Path CI.CI_Bool.p_eq) st.env
              |> List.filter (fun r -> ofold (fun q _ -> p_equal p q) false (rule_ty r))
              |> List.sort (fun r1 r2 -> compare r1.ER.rl_prio r2.ER.rl_prio) in
            EcPath.Hp.replace st.eqrules p rules; rules in
      let rec try_rules = function
        | [] -> value_eq v1 v2
        | r :: rules -> begin
            match match_rule st r [v1; v2] with
            | Some le -> as_bool (eval st le r.ER.rl_tg)
            | None -> try_rules rules
            | exception EvalError _ -> try_rules rules
          end
      in try_rules rules
    end
  | _, _, _ -> value_eq v1 v2

(* -------------------------------------------------------------------- *)
(* Procedures                                                           *)
and gkey (st : state) (xp : xpath) =
  match EcEnv.NormMp.norm_pvar st.env (pv_glob xp) with
  | PVglob xp -> x_tostring xp
  | PVloc _ -> assert false

and read_pvar (st : state) (le : lenv) (pv : prog_var) : value =
  match pv with
  | PVloc x -> begin
      let mem = oget ~exn:(EvalError "program variable outside of a procedure") le.le_mem in
      match EcSymbols.Msym.find_opt x mem.locals with
      | Some v -> v
      | None -> error "read of uninitialized local variable `%s'" x
    end
  | PVglob xp -> begin
      let globals = odfl !(st.globals) le.le_glob in
      match EcSymbols.Msym.find_opt (gkey st xp) globals with
      | Some v -> v
      | None -> error "read of uninitialized global variable `%s'" (x_tostring xp)
    end

let write_pvar (st : state) (mem : memory) (pv : prog_var) (v : value) =
  match pv with
  | PVloc x -> mem.locals <- EcSymbols.Msym.add x v mem.locals
  | PVglob xp -> st.globals := EcSymbols.Msym.add (gkey st xp) v !(st.globals)

let write_lvalue (st : state) (mem : memory) (lv : lvalue) (v : value) =
  match lv, v with
  | LvVar (pv, _), _ -> write_pvar st mem pv v
  | LvTuple pvs, VTuple vs when List.length pvs = List.length vs ->
      List.iter2 (fun (pv, _) v -> write_pvar st mem pv v) pvs vs
  | LvTuple _, _ -> error "cannot destructure %s" (string_of_value v)

(* The memory of program variables is irrelevant: [Fpvar] is looked up *)
(* in the current procedure frame.                                      *)
let exec_mem = EcIdent.create "&exec"

let eval_expr (st : state) (le : lenv) (e : expr) : value =
  let le = {
    le with
      le_mem  = omap (fun m -> { locals = m.locals }) le.le_mem;
      le_glob = Some !(st.globals);
  } in
  eval st le (form_of_expr ~m:exec_mem e)

let rec exec_stmt (st : state) (le : lenv) (s : stmt) : unit =
  List.iter (exec_instr st le) s.s_node

and exec_instr (st : state) (le : lenv) (i : instr) : unit =
  let mem = oget le.le_mem in
  match i.i_node with
  | Sasgn (lv, e) ->
      write_lvalue st mem lv (eval_expr st le e)

  | Srnd _ ->
      error "cannot execute a random sampling"

  | Scall (lv, xp, args) ->
      let args = List.map (eval_expr st le) args in
      let res = call st xp args in
      oiter (fun lv -> write_lvalue st mem lv res) lv

  | Sif (c, s1, s2) ->
      if as_bool (eval_expr st le c)
      then exec_stmt st le s1
      else exec_stmt st le s2

  | Swhile (c, s) ->
      while as_bool (eval_expr st le c) do
        exec_stmt st le s
      done

  | Smatch (e, bs) -> begin
      match eval_expr st le e with
      | VCtor (_, i, vs) ->
          let (xs, s) = List.nth bs i in
          let le = List.fold_left2 (fun le (x, _) v -> bind_local le x v) le xs vs in
          exec_stmt st le s
      | v -> error "cannot match on %s" (string_of_value v)
    end

  | Sraise _ ->
      error "exception raised"

  | Sabstract _ ->
      error "cannot execute an abstract statement"

and call (st : state) (xp : xpath) (args : value list) : value =
  let xp = EcEnv.NormMp.norm_xfun st.env xp in
  let fn =
    match EcEnv.Fun.by_xpath_opt xp st.env with
    | Some fn -> fn
    | None -> error "unknown procedure: %s" (x_tostring xp) in
  match fn.f_def with
  | FBalias xp' -> call st xp' args
  | FBabs _ -> error "cannot execute abstract procedure %s" (x_tostring xp)
  | FBdef def ->
      if !(st.fuel) <= 0 then error "maximal call depth reached";
      decr st.fuel;
      let mem = { locals = EcSymbols.Msym.empty } in
      let params = fn.f_sig.fs_anames in
      if List.length params <> List.length args then
        error "%s: expecting %d argument(s), got %d"
          (x_tostring xp) (List.length params) (List.length args);
      List.iter2 (fun ov v ->
          oiter (fun x -> mem.locals <- EcSymbols.Msym.add x v mem.locals) ov.ov_name)
        params args;
      let le = { empty_lenv with le_mem = Some mem } in
      exec_stmt st le def.f_body;
      let res =
        match def.f_ret with
        | None -> VTuple []
        | Some e -> eval_expr st le e in
      incr st.fuel; res

(* -------------------------------------------------------------------- *)
(* The compiled engine ("compile once, run many").                      *)
(*                                                                      *)
(* A formula is translated once into an OCaml closure ([code]) of the   *)
(* frame (an array) of its local variables, whose slots are fixed at    *)
(* translation time. The semantics is the one of [eval] above, step for *)
(* step: same values, same steps (one per argument of each application, *)
(* in the same order), same memoisation, same rules and pragmas. What   *)
(* changes is the cost of a step:                                       *)
(*  - local variables are array slots, not [Mid] lookups; a lambda      *)
(*    copies the variables it uses into its own frame when it is built  *)
(*    (flat closures), which is also the snapshot of the program        *)
(*    variables that [eval_expr] takes;                                 *)
(*  - each occurrence of an operator caches the operator, resolved on   *)
(*    its first evaluation (as [op_value]), instead of looking it up at *)
(*    each evaluation;                                                  *)
(*  - an application of an operator to its arity counts its steps and   *)
(*    calls the operator directly ([opv]), without the curried closures *)
(*    of [nary] and [apply_n];                                          *)
(*  - the body of an operator is translated once per command, when the  *)
(*    operator is resolved, and a definition [fun x1 .. xn => b] of an  *)
(*    operator of arity n runs [b] in a frame filled with the arguments.*)
let engine_compiled =
  match Sys.getenv_opt "EC_EVAL_ENGINE" with
  | Some "compiled" -> true
  | _ -> false

(* Ablations, to measure what each piece buys: EC_EVAL_C_NOCELL looks   *)
(* the operators up at each occurrence; EC_EVAL_C_NODIRECT applies them  *)
(* as curried values ([apply_n]), and their bodies as lambdas.           *)
let c_nocell = env_flag "EC_EVAL_C_NOCELL"
let c_nodirect = env_flag "EC_EVAL_C_NODIRECT"

let core_table_n : (int * (value list -> value)) EcPath.Mp.t Lazy.t =
  lazy (EcPath.Mp.of_list (Lazy.force core_ops_n))

(* The memoisation of [memo_call], for the compiled engine: the same    *)
(* tables, hits and misses, with a hash function that computes the same *)
(* values as [memo_hash] without closures, and without the closure of   *)
(* [in_context] at each call.                                           *)
let memo_hash_fast (vs : value list) : int =
  let budget = ref (1 lsl 20) in
  let mix acc h = (acc * 65599 + h) land max_int in
  let rec doit acc v =
    if !budget <= 0 then acc else begin
      decr budget;
      match v with
      | VInt z -> mix acc (Z.hash z)
      | VBool b -> mix acc (if b then 1 else 2)
      | VBits (n, z) -> mix (mix acc n) (Z.hash z)
      | VCtor (_, i, vs) -> doits (mix acc i) vs
      | VTuple vs -> doits (mix acc 3) vs
      | VNeu (_, _, id) -> mix acc id
      | VFun _ -> mix acc 5
      | VWitness -> mix acc 7
    end
  and doits acc vs =
    match vs with
    | [] -> acc
    | v :: vs -> doits (doit acc v) vs
  in doits 17 vs

module MHF = Hashtbl.Make (struct
  type t = value list
  let equal = memo_eq_list
  let hash = memo_hash_fast
end)

let memo_add_fast (tbl : value MHF.t) (nodes : int ref) (vs : value list) (r : value) =
  let k = memo_size vs in
  if MHF.length tbl >= 65536 || !nodes + k > 1 lsl 22 then
    (MHF.reset tbl; nodes := 0);
  nodes := !nodes + k;
  MHF.add tbl vs r

let in_context_msg (name : string) (msg : string) =
  let depth = List.length (String.split_on_char '\n' msg) in
  if depth > 8 then EvalError msg
  else EvalError (Printf.sprintf "%s\n  in %s" msg name)

let rec has_fun (vs : value list) =
  match vs with
  | [] -> false
  | VFun _ :: _ -> true
  | _ :: vs -> has_fun vs

let c_memo_call ~(name : string) (inner : value list -> value) : value list -> value =
  let call vs = try inner vs with EvalError msg -> raise (in_context_msg name msg) in
  if no_op_memo then call else
  let tbl = MHF.create 64 in
  let (hits, misses) =
    match Hashtbl.find_opt memo_stats name with
    | Some c -> c
    | None -> let c = (ref 0, ref 0) in Hashtbl.add memo_stats name c; c in
  let on = ref true and h = ref 0 and m = ref 0 and nodes = ref 0 in
  (fun vs ->
    if not !on || has_fun vs then call vs else
    match MHF.find_opt tbl vs with
    | Some r -> incr hits; incr h; r
    | None ->
        incr misses; incr m;
        let r = call vs in
        if adaptive_memo && !m >= 1024 && 8 * !h < !m then
          (on := false; MHF.reset tbl)
        else memo_add_fast tbl nodes vs r; r)

let c_rules_memo (try_rules : value list -> value) : value list -> value =
  if no_rule_memo then try_rules else
  let tbl = MHF.create 64 in
  let on = ref true and h = ref 0 and m = ref 0 and nodes = ref 0 in
  (fun vs ->
    if not !on || not (List.for_all first_order vs) then try_rules vs else
    match MHF.find_opt tbl vs with
    | Some r -> incr h; r
    | None ->
        incr m;
        let r = try_rules vs in
        if adaptive_memo && !m >= 1024 && 8 * !h < !m then
          (on := false; MHF.reset tbl)
        else memo_add_fast tbl nodes vs r; r)

(* Unassigned slots (program variables, rule variables). Compared with  *)
(* [==].                                                                *)
let unset : value = VTuple [VWitness]

let mk_opv (n : int) (f : value list -> value) : opv =
  if n = 0 then { o_val = f []; o_ar = 0; o_call = f; o_tmp = false; }
  else { o_val = nary n f; o_ar = n; o_call = f; o_tmp = false; }

let const_opv (v : value) : opv =
  { o_val = v; o_ar = 0; o_call = (fun _ -> assert false); o_tmp = false; }

(* [apply_n o.o_val vs], [vs] of length [n] *)
let call_slow (o : opv) (n : int) (vs : value list) : value =
  if o.o_ar > 0 && n > o.o_ar then begin
    let args, extra = List.split_at o.o_ar vs in
    tick_n o.o_ar;
    apply_n (o.o_call args) extra
  end else apply_n o.o_val vs

let call_known (o : opv) (n : int) (vs : value list) : value =
  if o.o_ar = n then (tick_n n; o.o_call vs) else call_slow o n vs

let call_list (o : opv) (vs : value list) : value =
  call_known o (List.length vs) vs

(* -------------------------------------------------------------------- *)
(* Translation-time scopes. Keys: local variables (by tag), program     *)
(* variables (-1, name) and global variables (-2, normalised name).     *)
module Mk = Map.Make (struct
  type t = int * string
  let compare ((i1, s1) : t) ((i2, s2) : t) =
    let c = Int.compare i1 i2 in if c <> 0 then c else String.compare s1 s2
end)

type cframe = {
  mutable size  : int;
  mutable caps  : (int * int) list;   (* (slot in the enclosing frame, slot) *)
  mutable capm  : int Mk.t;           (* captured variables *)
  outer         : (cframe * int Mk.t) option;
  pvars         : bool;               (* the frame of a procedure *)
  mutable pvm   : int Mk.t;           (* program variables (procedure frame) *)
  mutable globs : (int * string) list;(* slots of the global variables *)
}

type scope = cframe * int Mk.t

let new_frame ?outer ?(pvars = false) () = {
  size = 0; caps = []; capm = Mk.empty; outer; pvars;
  pvm = Mk.empty; globs = [];
}

let alloc (fr : cframe) =
  let i = fr.size in fr.size <- i + 1; i

let key_id (x : EcIdent.t) = (EcIdent.tag x, "")

let rec lookup ((fr, vm) : scope) (k : Mk.key) : int option =
  match Mk.find_opt k vm with
  | Some i -> Some i
  | None ->
  match Mk.find_opt k fr.capm with
  | Some i -> Some i
  | None ->
  if fr.pvars && fst k < 0 then begin
    match Mk.find_opt k fr.pvm with
    | Some i -> Some i
    | None ->
        let i = alloc fr in
        fr.pvm <- Mk.add k i fr.pvm;
        if fst k = -2 then fr.globs <- (i, snd k) :: fr.globs;
        Some i
  end else
  match fr.outer with
  | None -> None
  | Some o -> begin
      match lookup o k with
      | None -> None
      | Some pi ->
          let j = alloc fr in
          fr.caps <- (pi, j) :: fr.caps;
          fr.capm <- Mk.add k j fr.capm;
          Some j
    end

let bind ((fr, vm) : scope) (x : EcIdent.t) : scope * int =
  let i = alloc fr in ((fr, Mk.add (key_id x) i vm), i)

let bind_list (sc : scope) (xs : EcIdent.t list) : scope * int list =
  let sc, is = List.fold_left (fun (sc, is) x ->
    let sc, i = bind sc x in (sc, i :: is)) (sc, []) xs in
  (sc, List.rev is)

let rec fill (fr : value array) (is : int list) (vs : value list) =
  match is, vs with
  | i :: is, v :: vs -> Array.unsafe_set fr i v; fill fr is vs
  | [], [] -> ()
  | _, _ -> invalid_arg "fill"

(* The slots 0 .. n-1 of [fr] from [vs] *)
let rec fill_from (fr : value array) (i : int) (vs : value list) =
  match vs with
  | [] -> ()
  | v :: vs -> Array.unsafe_set fr i v; fill_from fr (i + 1) vs

exception CNoMatch

type ocell = { mutable oc : opv option; oc_p : path; }

type cbr =                              (* compiled branches of a fixpoint *)
  | CLeaf   of int list list * int * code   (* binder slots, frame size, body *)
  | CBranch of int * cbr array
  | CErr

let rec comp (st : state) (sc : scope) (f : form) : code =
  match f.f_node with
  | Fint z ->
      let v = VInt (EcBigInt.to_zt z) in fun _ -> v

  | Flocal x -> begin
      match lookup sc (key_id x) with
      | Some i -> fun env -> Array.unsafe_get env i
      | None ->
          let x = EcIdent.name x in
          fun _ -> error "unbound local variable: %s" x
    end

  | Fpvar (pv, _) ->
      comp_pvar st sc pv

  | Fop (p, _) ->
      let cell = { oc = None; oc_p = p } in
      fun _ -> (get_op st cell).o_val

  | Fapp ({ f_node = Fop (p, [ty]) }, [a1; a2]) when p_equal p CI.CI_Bool.p_eq ->
      let c1 = comp st sc a1 in
      let c2 = comp st sc a2 in
      fun env ->
        let v1 = c1 env in
        let v2 = c2 env in
        VBool (c_eq_typed st ty v1 v2)

  | Fapp ({ f_node = Fop (p, _) }, a1 :: args) when Option.is_some (lazy_bool p) -> begin
      let c1 = comp st sc a1 in
      let cargs = List.map (comp st sc) args in
      match oget (lazy_bool p), cargs with
      | `And, [c2] -> fun env -> if as_bool (c1 env) then c2 env else VBool false
      | `Or , [c2] -> fun env -> if as_bool (c1 env) then VBool true else c2 env
      | `Imp, [c2] -> fun env -> if as_bool (c1 env) then c2 env else VBool true
      | kind, _ ->
          fun env ->
            let b1 = as_bool (c1 env) in
            let rest () =
              match cargs with
              | c2 :: cs -> (c2 env, cs)
              | [] -> error "partial application of a boolean connective" in
            let res, cs =
              match kind with
              | `And -> if b1 then rest () else (VBool false, List.tl cargs)
              | `Or  -> if b1 then (VBool true, List.tl cargs) else rest ()
              | `Imp -> if b1 then rest () else (VBool true, List.tl cargs) in
            apply_n res (List.map (fun c -> c env) cs)
    end

  | Fapp ({ f_node = Fop (p, _) }, [a1; a2])
      when not profile_time && Option.is_some (int_binop p) ->
      let op = oget (int_binop p) in
      let c1 = comp st sc a1 in
      let c2 = comp st sc a2 in
      (* the same order of evaluation as [eval]; one closure per operator *)
      (* when not profiling                                              *)
      let open CI.CI_Int in
      if Option.is_some st.profile then
        fun env -> begin
          match c1 env, c2 env with
          | VInt z1, VInt z2 ->
              count_app st p; tick_n 2;
              op z1 z2
          | _, _ -> error "expecting integers"
        end
      else if p_equal p p_int_add then
        fun env -> begin
          match c1 env, c2 env with
          | VInt z1, VInt z2 -> tick_n 2; VInt (Z.add z1 z2)
          | _, _ -> error "expecting integers"
        end
      else if p_equal p p_int_mul then
        fun env -> begin
          match c1 env, c2 env with
          | VInt z1, VInt z2 -> tick_n 2; VInt (Z.mul z1 z2)
          | _, _ -> error "expecting integers"
        end
      else if p_equal p p_int_lt then
        fun env -> begin
          match c1 env, c2 env with
          | VInt z1, VInt z2 -> tick_n 2; VBool (Z.lt z1 z2)
          | _, _ -> error "expecting integers"
        end
      else begin
        assert (p_equal p p_int_le); ignore op;
        fun env -> begin
          match c1 env, c2 env with
          | VInt z1, VInt z2 -> tick_n 2; VBool (Z.leq z1 z2)
          | _, _ -> error "expecting integers"
        end
      end

  | Fproj ({ f_node = Fapp ({ f_node = Fop (p, _) }, [a1; a2]) }, i)
      when not profile_time && p_equal p CI.CI_Int.p_int_edivz ->
      let c1 = comp st sc a1 in
      let c2 = comp st sc a2 in
      fun env -> begin
        match c1 env, c2 env with
        | VInt m, VInt d ->
            count_app st p; tick_n 2;
            let (q, r) = if Z.equal d Z.zero then (Z.zero, m) else Z.ediv_rem m d in
            VInt (if i = 0 then q else r)
        | _, _ -> error "expecting integers"
      end

  | Fapp ({ f_node = Fop (p, _) }, args) -> begin
      let cell = { oc = None; oc_p = p } in
      let cargs = List.map (comp st sc) args in
      let n = List.length args in
      let prof = Option.is_some st.profile in
      if profile_time || c_nodirect then
        fun env ->
          let o = get_op st cell in
          count_app st p;
          let vs = List.map (fun c -> c env) cargs in
          if c_nodirect then apply_n o.o_val vs else
          timed p (fun () -> call_known o n vs)
      else
      match cargs with
      | [c1] ->
          fun env ->
            let o = get_op st cell in
            if prof then count_app st p;
            let v1 = c1 env in
            if o.o_ar = 1 then (tick_n 1; o.o_call [v1])
            else call_slow o 1 [v1]
      | [c1; c2] ->
          fun env ->
            let o = get_op st cell in
            if prof then count_app st p;
            let v1 = c1 env in
            let v2 = c2 env in
            if o.o_ar = 2 then (tick_n 2; o.o_call [v1; v2])
            else call_slow o 2 [v1; v2]
      | [c1; c2; c3] ->
          fun env ->
            let o = get_op st cell in
            if prof then count_app st p;
            let v1 = c1 env in
            let v2 = c2 env in
            let v3 = c3 env in
            if o.o_ar = 3 then (tick_n 3; o.o_call [v1; v2; v3])
            else call_slow o 3 [v1; v2; v3]
      | _ ->
          fun env ->
            let o = get_op st cell in
            if prof then count_app st p;
            let vs = List.map (fun c -> c env) cargs in
            call_known o n vs
    end

  | Fapp (f, args) ->
      let cf = comp st sc f in
      let cargs = List.map (comp st sc) args in
      fun env ->
        let fv = cf env in
        apply_n fv (List.map (fun c -> c env) cargs)

  | Fquant (Llambda, bds, body) ->
      let (mk, _, _) = comp_lambda st sc (List.map fst bds) body in mk

  | Fquant ((Lforall | Lexists), _, _) ->
      fun _ -> error "cannot evaluate a quantifier"

  | Fif (c, f1, f2) ->
      let c = comp st sc c in
      let c1 = comp st sc f1 in
      let c2 = comp st sc f2 in
      fun env -> if as_bool (c env) then c1 env else c2 env

  | Fmatch (c, bs, _) ->
      let cc = comp st sc c in
      let cbs = Array.of_list (List.map (comp_branch st sc) bs) in
      fun env -> begin
        match cc env with
        | VCtor (_, i, vs) -> cbs.(i) env vs
        | v -> error "cannot match on %s" (string_of_value v)
      end

  | Flet (lp, f1, f2) -> begin
      let c1 = comp st sc f1 in
      match lp with
      | LSymbol (x, _) ->
          let sc, i = bind sc x in
          let c2 = comp st sc f2 in
          fun env -> let v = c1 env in Array.unsafe_set env i v; c2 env
      | LTuple xs ->
          let sc, is = bind_list sc (List.map fst xs) in
          let c2 = comp st sc f2 in
          fun env -> begin
            match c1 env with
            | VTuple vs -> fill env is vs; c2 env
            | v -> error "cannot destructure %s" (string_of_value v)
          end
      | LRecord (_, xs) ->
          let sc, is = List.fold_left (fun (sc, is) (x, _) ->
            match x with
            | None -> (sc, None :: is)
            | Some x -> let sc, i = bind sc x in (sc, Some i :: is)) (sc, []) xs in
          let is = List.rev is in
          let c2 = comp st sc f2 in
          fun env -> begin
            match c1 env with
            | VCtor (_, _, vs) ->
                List.iter2 (fun i v -> oiter (fun i -> env.(i) <- v) i) is vs;
                c2 env
            | v -> error "cannot destructure %s" (string_of_value v)
          end
    end

  | Ftuple fs ->
      let cs = List.map (comp st sc) fs in
      fun env -> VTuple (List.map (fun c -> c env) cs)

  | Fproj (f1, i) ->
      let c1 = comp st sc f1 in
      fun env -> begin
        match c1 env with
        | VTuple vs -> List.nth vs i
        | v -> error "cannot project %s" (string_of_value v)
      end

  | Fglob _ | Fpr _
  | FhoareF _ | FhoareS _ | FbdHoareF _ | FbdHoareS _
  | FeHoareF _ | FeHoareS _ | FequivF _ | FequivS _ | FeagerF _ ->
      fun _ -> error "cannot evaluate a program logic formula"

(* A lambda [fun xs => body]: its value, its number of binders and its  *)
(* direct entry (given the values it captures, and the arguments).      *)
and comp_lambda (st : state) (sc : scope) (xs : EcIdent.t list) (body : form)
  : code * int * (value array -> value list -> value)
=
  let fr = new_frame ~outer:sc () in
  let (sc', _) = bind_list (fr, Mk.empty) xs in
  let cbody = comp st sc' body in
  let size = fr.size in
  let caps = Array.of_list (List.rev fr.caps) in
  let srcs = Array.map fst caps and dsts = Array.map snd caps in
  let ncaps = Array.length caps in
  let k = List.length xs in
  let enter (cv : value array) : value array =
    let fr = Array.make size unset in
    for j = 0 to ncaps - 1 do
      Array.unsafe_set fr (Array.unsafe_get dsts j) (Array.unsafe_get cv j)
    done; fr in
  let direct cv vs = let fr = enter cv in fill_from fr 0 vs; cbody fr in
  let capture env = Array.map (fun i -> Array.unsafe_get env i) srcs in
  let mk =
    match k with
    | 0 -> fun env -> cbody (enter (capture env))
    | 1 -> fun env ->
        let cv = capture env in
        VFun (fun v -> let fr = enter cv in Array.unsafe_set fr 0 v; cbody fr)
    | 2 -> fun env ->
        let cv = capture env in
        VFun (fun v1 -> VFun (fun v2 ->
          let fr = enter cv in
          Array.unsafe_set fr 0 v1; Array.unsafe_set fr 1 v2; cbody fr))
    | _ -> fun env ->
        let cv = capture env in
        let rec aux i acc =
          if i = k then direct cv (List.rev acc)
          else VFun (fun v -> aux (i + 1) (v :: acc)) in
        aux 0 []
  in (mk, k, direct)

(* A closed lambda (the body of an operator): its direct entry. *)
and comp_closed_lambda (st : state) (xs : EcIdent.t list) (body : form)
  : value list -> value
=
  let fr = new_frame () in
  let (sc, _) = bind_list (fr, Mk.empty) xs in
  let cbody = comp st sc body in
  let size = fr.size in
  fun vs -> let fr = Array.make size unset in fill_from fr 0 vs; cbody fr

(* A branch of a match, applied to the fields of the constructor. A     *)
(* branch [fun xs => b] applied to as many fields binds them in the     *)
(* current frame; otherwise, it is applied as a curried function, built *)
(* on a copy of the frame.                                              *)
and comp_branch (st : state) (sc : scope) (b : form) : value array -> value list -> value =
  match b.f_node with
  | Fquant (Llambda, bds, body) ->
      let xs = List.map fst bds in
      let k = List.length xs in
      let (sc', is) = bind_list sc xs in
      let cbody = comp st sc' body in
      fun env vs ->
        if List.compare_length_with vs k = 0 then
          (tick_n k; fill env is vs; cbody env)
        else
          let rec aux i acc =
            if i = k then begin
              let env = Array.copy env in
              fill env is (List.rev acc); cbody env
            end else VFun (fun v -> aux (i + 1) (v :: acc)) in
          apply_n (aux 0 []) vs
  | _ ->
      let cb = comp st sc b in
      fun env vs -> apply_n (cb env) vs

and comp_pvar (st : state) (sc : scope) (pv : prog_var) : code =
  match pv with
  | PVloc x -> begin
      match lookup sc (-1, x) with
      | Some i ->
          fun env ->
            let v = Array.unsafe_get env i in
            if v == unset then error "read of uninitialized local variable `%s'" x
            else v
      | None ->
          fun _ -> raise (EvalError "program variable outside of a procedure")
    end
  | PVglob xp -> begin
      let g = gkey st xp in
      match lookup sc (-2, g) with
      | Some i ->
          fun env ->
            let v = Array.unsafe_get env i in
            if v == unset then
              error "read of uninitialized global variable `%s'" (x_tostring xp)
            else v
      | None ->
          fun _ ->
            match EcSymbols.Msym.find_opt g !(st.globals) with
            | Some v -> v
            | None -> error "read of uninitialized global variable `%s'" (x_tostring xp)
    end

(* -------------------------------------------------------------------- *)
and get_op (st : state) (c : ocell) : opv =
  if c_nocell then c_op_value st c.oc_p else
  match c.oc with
  | Some o -> o
  | None ->
      let o = c_op_value st c.oc_p in
      if not o.o_tmp then c.oc <- Some o; o

and c_op_value (st : state) (p : path) : opv =
  match EcPath.Hp.find_opt st.cops p with
  | Some o -> o
  | None ->
      (* Recursive operators refer to themselves: tie the knot lazily. *)
      let cell = ref None in
      EcPath.Hp.replace st.cops p {
        o_val = VFun (fun v ->
          match !cell with
          | Some f -> apply f v
          | None -> error "ill-founded definition of %s" (tostring p));
        o_ar = 0; o_call = (fun _ -> assert false); o_tmp = true; };
      let o =
        try in_context (tostring p) (fun () -> c_op_value_r st p)
        with e -> EcPath.Hp.remove st.cops p; raise e in
      cell := Some o.o_val;
      EcPath.Hp.replace st.cops p o; o

and c_op_value_r (st : state) (p : path) : opv =
  let env = st.env in

  match EcPath.Mp.find_opt p (Lazy.force core_table_n) with
  | Some (n, f) -> mk_opv n f
  | None ->

  let op =
    match EcEnv.Op.by_path_opt p env with
    | Some op -> op
    | None -> error "unknown operator: %s" (tostring p) in

  let rules_or_def () =
    match EcEnv.Reduction.get ~base:eval_base (`Path p) env with
    | (_ :: _) as rules -> c_with_rules st rules (fun () -> c_definition st p op)
    | [] -> c_definition st p op in

  match (if st.native_words then native_word_op p else None) with
  | Some f ->
      let dfl = lazy (rules_or_def ()) in
      mk_opv 2 (fun vs -> try f vs with Stuck -> call_list (Lazy.force dfl) vs)
  | None ->

  match (if st.native_arrays then native_array_get env p else None) with
  | Some f ->
      let dfl = lazy (rules_or_def ()) in
      mk_opv 2 (fun vs -> try f vs with Stuck -> call_list (Lazy.force dfl) vs)
  | None ->

  match (if st.native_zmod then native_zmod_op (c_eval_closed st) env p else None) with
  | Some (0, f) -> const_opv (f [])
  | Some (n, f) ->
      let dfl = lazy (rules_or_def ()) in
      mk_opv n (fun vs -> try f vs with Stuck -> call_list (Lazy.force dfl) vs)
  | None ->

  match EcPath.Mp.find_opt p (Lazy.force native_list_table) with
  | Some (n, f) ->
      let dfl = lazy (rules_or_def ()) in
      mk_opv n (fun vs -> try f vs with Stuck -> call_list (Lazy.force dfl) vs)
  | None ->

  match EcEnv.Circuit.reverse_bitstring_operator env p with
  | Some (bs, `From) -> c_from_bits st bs p op
  | Some (bs, kind) -> let (n, f) = bitstring_op_n bs kind in mk_opv n f
  | None ->

  match obind (bvoperator_n env) (EcEnv.Circuit.reverse_bvoperator env p) with
  | Some (n, f) -> mk_opv n f
  | None ->

  match EcEnv.Reduction.get ~base:eval_base (`Path p) env with
  | (_ :: _) as rules -> c_with_rules st rules (fun () -> c_definition st p op)
  | [] ->

  match op.op_kind with
  | OB_oper None when Option.is_none (subtype_role env p op) -> begin
      match EcEnv.Reduction.get (`Path p) env with
      | (_ :: _) as rules -> c_with_rules st rules (fun () -> c_definition st p op)
      | [] -> c_definition st p op
    end
  | _ -> c_definition st p op

and c_from_bits (st : state) (bs : crb_bitstring) (p : path) (op : operator) : opv =
  let n = binding_size bs.size in
  let bs_type = bs.type_ in
  let dfl = lazy (
    match EcEnv.Reduction.get ~base:eval_base (`Path p) st.env with
    | (_ :: _) as rules -> c_with_rules st rules (fun () -> c_definition st p op)
    | [] -> c_definition st p op) in
  mk_opv 1 (function
    | [l] ->
        let bs = as_bool_list l in
        if List.length bs = n then mk_bits (is_bool_type bs_type) n (bits_of_list bs)
        else call_known (Lazy.force dfl) 1 [l]
    | _ -> assert false)

(* The value of a closed formula, with a direct entry when it is a      *)
(* lambda.                                                              *)
and c_value_opv (st : state) (f : form) : opv =
  match f.f_node with
  | Fquant (Llambda, bds, body) ->
      let xs = List.map fst bds in
      let direct = comp_closed_lambda st xs body in
      mk_opv (List.length xs) direct
  | _ -> const_opv (c_eval_closed st f)

(* [fun vs -> apply_n v vs], [v] the value of [f] *)
and c_apply_inner (st : state) (n : int) (f : form) : value list -> value =
  match f.f_node with
  | Fquant (Llambda, bds, body) when not c_nodirect && List.compare_length_with bds n = 0 ->
      let direct = comp_closed_lambda st (List.map fst bds) body in
      fun vs -> tick_n n; direct vs
  | _ ->
      let v = c_eval_closed st f in
      fun vs -> apply_n v vs

and c_definition (st : state) (p : path) (op : operator) : opv =
  match op.op_kind with
  | OB_oper (Some (OP_Plain f)) ->
      let n = op_arity op in
      if n = 0 then c_value_opv st f else
      let inner = c_apply_inner st n f in
      mk_opv n (c_memo_call ~name:(tostring p) inner)

  | OB_oper (Some (OP_Constr (_, i))) ->
      let n = ctor_arity op.op_ty in
      mk_opv n (fun vs -> VCtor (p, i, vs))

  | OB_oper (Some (OP_Record _)) ->
      let n = ctor_arity op.op_ty in
      mk_opv n (fun vs -> VCtor (p, 0, vs))

  | OB_oper (Some (OP_Proj (_, i, _))) ->
      mk_opv 1 (function
        | [VCtor (_, _, vs)] -> List.nth vs i
        | [v] -> error "cannot project %s" (string_of_value v)
        | _ -> assert false)

  | OB_oper (Some (OP_Fix fix)) ->
      let n = op_arity op in
      let k = List.length fix.opf_args in
      let fixf = c_fixdef st fix in
      let fixv = nary k fixf in
      if n = 0 then const_opv fixv else
      let inner =
        if k = n then (fun vs -> tick_n n; fixf vs)
        else (fun vs -> apply_n fixv vs) in
      mk_opv n (c_memo_call ~name:(tostring p) inner)

  | OB_oper (Some (OP_TC | OP_Exn _)) ->
      error "cannot evaluate operator %s" (tostring p)

  | OB_pred (Some (PR_Plain f)) ->
      c_value_opv st f

  | OB_pred (Some (PR_Ind _)) ->
      error "cannot evaluate inductive predicate %s" (tostring p)

  | OB_nott nt ->
      let body = form_of_expr nt.ont_body in
      let xs = List.map fst nt.ont_args in
      mk_opv (List.length xs) (comp_closed_lambda st xs body)

  | OB_oper None | OB_pred None -> begin
      match subtype_role st.env p op with
      | Some (`Insub pred) ->
          let pred = lazy (c_eval_closed st pred) in
          mk_opv 1 (function
            | [v] ->
                if as_bool (apply (Lazy.force pred) v)
                then VCtor (CI.CI_Option.p_some, 1, [v])
                else VCtor (CI.CI_Option.p_none, 0, [])
            | _ -> assert false)
      | Some `Val -> mk_opv 1 (function [v] -> v | _ -> assert false)
      | None ->
          let n = op_arity op in
          mk_opv n (fun vs -> VNeu (p, List.map memo vs, fresh_id ()))
    end

(* A fixpoint, as a function of its arguments (no steps counted). *)
and c_fixdef (st : state) (fix : opfix) : value list -> value =
  let xs = List.map fst fix.opf_args in
  let pos = fst fix.opf_struct in
  let rec cdesc br ps =
    match br, ps with
    | OPB_Leaf (bds, body), [] ->
        let fr = new_frame () in
        let (sc, _) = bind_list (fr, Mk.empty) xs in
        let sc, lvls = List.fold_left (fun (sc, lvls) bd ->
          let sc, is = bind_list sc (List.map fst bd) in (sc, is :: lvls)) (sc, []) bds in
        let cbody = comp st sc (form_of_expr body) in
        CLeaf (List.rev lvls, fr.size, cbody)
    | OPB_Branch bs, i :: ps ->
        CBranch (i, Array.of_list (List.map (fun b -> cdesc b.opb_sub ps) (Parray.to_list bs)))
    | _, _ -> CErr in
  let tree = cdesc fix.opf_branches pos in
  fun vs ->
    let args = Array.of_list vs in
    let rec run br acc =
      match br with
      | CLeaf (lvls, size, cbody) ->
          let fr = Array.make size unset in
          fill_from fr 0 vs;
          List.iter2 (fun is cvs -> fill fr is cvs) lvls (List.rev acc);
          cbody fr
      | CBranch (i, subs) -> begin
          match args.(i) with
          | VCtor (_, idx, cvs) -> run subs.(idx) (cvs :: acc)
          | v -> error "cannot match on %s" (string_of_value v)
        end
      | CErr -> error "ill-formed fixpoint definition"
    in run tree []

(* -------------------------------------------------------------------- *)
and c_rule (st : state) (r : ER.rule) : crule =
  let arity =
    match r.ER.rl_ptn with
    | ER.Rule (`Op _, args) -> List.length args
    | _ -> 0 in
  (* the variables of the pattern, in order *)
  let rec vars acc = function
    | ER.Var x -> if List.exists (EcIdent.id_equal x) acc then acc else x :: acc
    | ER.Int _ -> acc
    | ER.Rule (_, ps) -> List.fold_left vars acc ps in
  let xs = List.rev (vars [] r.ER.rl_ptn) in
  let slots = List.fold_left (fun (m, i) x -> (Mid.add x i m, i + 1)) (Mid.empty, 0) xs in
  let code = lazy (
    let fr = new_frame () in
    let (sc, _) = bind_list (fr, Mk.empty) xs in
    let conds = List.map (comp st sc) r.ER.rl_cond in
    let tg = comp st sc r.ER.rl_tg in
    (fr.size, conds, tg)) in
  let slots = fst slots in
  let rec cpat (ptn : ER.rule_pattern) : value array -> value -> unit =
    match ptn with
    | ER.Var x ->
        let i = Mid.find x slots in
        fun fr v ->
          let v' = Array.unsafe_get fr i in
          if v' == unset then Array.unsafe_set fr i v
          else if not (value_eq v v') then raise CNoMatch
    | ER.Int z ->
        let z = EcBigInt.to_zt z in
        fun _ v -> begin
          match v with
          | VInt z' when Z.equal z z' -> ()
          | _ -> raise CNoMatch
        end
    | ER.Rule (`Tuple, ps) ->
        let ms = List.map cpat ps in
        let n = List.length ps in
        fun fr v -> begin
          match v with
          | VTuple vs when List.compare_length_with vs n = 0 ->
              List.iter2 (fun m v -> m fr v) ms vs
          | _ -> raise CNoMatch
        end
    | ER.Rule (`Op (q, tys), ps) ->
        let ms = List.map cpat ps in
        let n = List.length ps in
        let as_bool =
          if List.is_empty tys && List.is_empty ps then
            if p_equal q CI.CI_Bool.p_true then Some true
            else if p_equal q CI.CI_Bool.p_false then Some false
            else None
          else None in
        fun fr v -> begin
          match v with
          | VCtor (q', _, vs)
              when p_equal q q' && List.compare_length_with vs n = 0 ->
              List.iter2 (fun m v -> m fr v) ms vs
          | VNeu (q', vs, _)
              when p_equal q q' && List.compare_length_with vs n = 0 ->
              List.iter2 (fun m v -> m fr v) ms vs
          | VBool b when as_bool = Some b -> ()
          | _ -> raise CNoMatch
        end
    | ER.Rule (_, _) -> fun _ _ -> raise CNoMatch in
  let pats =
    match r.ER.rl_ptn with
    | ER.Rule (`Op _, ps) -> Some (List.map cpat ps)
    | _ -> None in
  { cr_rule = r; cr_arity = arity; cr_slots = slots; cr_code = code;
    cr_pats = pats; }

and c_match_rule (st : state) (cr : crule) (args : value list) : value array option =
  ignore st;
  match cr.cr_pats with
  | None -> None
  | Some ms ->
      let (size, conds, _) = Lazy.force cr.cr_code in
      let fr = Array.make size unset in
      try
        List.iter2 (fun m v -> m fr v) ms args;
        if List.for_all (fun c -> as_bool (c fr)) conds
        then Some fr else None
      with CNoMatch -> None

and c_with_rules (st : state) (rules : ER.rule list) (dfl : unit -> opv) : opv =
  let arity = function
    | { ER.rl_ptn = ER.Rule (`Op _, args) } -> List.length args
    | _ -> 0 in
  let n = List.fold_left (fun n r -> max n (arity r)) 0 rules in
  let rules = List.sort (fun r1 r2 -> compare r1.ER.rl_prio r2.ER.rl_prio) rules in
  let crs = List.map (c_rule st) rules in
  let dfl = lazy (dfl ()) in
  let rec try_rules vs = function
    | [] -> call_list (Lazy.force dfl) vs
    | cr :: crs ->
        let args, extra = List.split_at cr.cr_arity vs in
        match c_match_rule st cr args with
        | Some fr ->
            let (_, _, tg) = Lazy.force cr.cr_code in
            apply_n (tg fr) extra
        | None -> try_rules vs crs
        | exception EvalError _ -> try_rules vs crs
  in
  if n = 0 then const_opv (try_rules [] crs) else
  mk_opv n (c_rules_memo (fun vs -> try_rules vs crs))

and c_eq_typed (st : state) (ty : ty) (v1 : value) (v2 : value) : bool =
  let ty = hnorm st ty in
  match ty.ty_node, v1, v2 with
  | Ttuple tys, VTuple vs1, VTuple vs2 when List.length tys = List.length vs1 ->
      List.for_all2 (fun ty (v1, v2) -> c_eq_typed st ty v1 v2)
        tys (List.combine vs1 vs2)
  | Tconstr (p, _), _, _ -> begin
      let rule_ty (r : ER.rule) =
        match r.ER.rl_ptn with
        | ER.Rule (`Op (_, [rty]), [_; _]) -> begin
            match (hnorm st rty).ty_node with
            | Tconstr (q, _) -> Some q
            | _ -> None
          end
        | _ -> None in
      let rules =
        match EcPath.Hp.find_opt st.ceqrules p with
        | Some rules -> rules
        | None ->
            let rules =
              EcEnv.Reduction.get ~base:eval_base (`Path CI.CI_Bool.p_eq) st.env
              |> List.filter (fun r -> ofold (fun q _ -> p_equal p q) false (rule_ty r))
              |> List.sort (fun r1 r2 -> compare r1.ER.rl_prio r2.ER.rl_prio)
              |> List.map (c_rule st) in
            EcPath.Hp.replace st.ceqrules p rules; rules in
      let rec try_rules = function
        | [] -> value_eq v1 v2
        | cr :: rules -> begin
            match c_match_rule st cr [v1; v2] with
            | Some fr -> let (_, _, tg) = Lazy.force cr.cr_code in as_bool (tg fr)
            | None -> try_rules rules
            | exception EvalError _ -> try_rules rules
          end
      in try_rules rules
    end
  | _, _, _ -> value_eq v1 v2

and c_eval_closed (st : state) (f : form) : value =
  let fr = new_frame () in
  let c = comp st (fr, Mk.empty) f in
  c (Array.make fr.size unset)

(* -------------------------------------------------------------------- *)
(* Procedures: the program variables of a procedure are slots of its    *)
(* frame (the scope of its statements and expressions); the global      *)
(* variables that it reads are loaded in their slots before each        *)
(* expression, which is the snapshot of [eval_expr].                    *)
let c_expr (st : state) (sc : scope) (e : expr) : code =
  let c = comp st sc (form_of_expr ~m:exec_mem e) in
  let (pfr, _) = sc in
  fun env ->
    begin match pfr.globs with
    | [] -> ()
    | gs ->
        List.iter (fun (i, g) ->
          env.(i) <- odfl unset (EcSymbols.Msym.find_opt g !(st.globals))) gs
    end;
    c env

let c_write_pvar (st : state) (sc : scope) (pv : prog_var) : value array -> value -> unit =
  match pv with
  | PVloc x ->
      let i = oget (lookup sc (-1, x)) in
      fun env v -> env.(i) <- v
  | PVglob xp ->
      let g = gkey st xp in
      fun _ v -> st.globals := EcSymbols.Msym.add g v !(st.globals)

let c_write (st : state) (sc : scope) (lv : lvalue) : value array -> value -> unit =
  match lv with
  | LvVar (pv, _) -> c_write_pvar st sc pv
  | LvTuple pvs ->
      let ws = List.map (fun (pv, _) -> c_write_pvar st sc pv) pvs in
      let n = List.length ws in
      fun env v -> begin
        match v with
        | VTuple vs when List.length vs = n -> List.iter2 (fun w v -> w env v) ws vs
        | _ -> error "cannot destructure %s" (string_of_value v)
      end

let rec c_stmt (st : state) (sc : scope) (s : stmt) : value array -> unit =
  match List.map (c_instr st sc) s.s_node with
  | [] -> fun _ -> ()
  | [i] -> i
  | is -> let is = Array.of_list is in fun env -> Array.iter (fun i -> i env) is

and c_instr (st : state) (sc : scope) (i : instr) : value array -> unit =
  match i.i_node with
  | Sasgn (lv, e) ->
      let ce = c_expr st sc e in
      let w = c_write st sc lv in
      fun env -> w env (ce env)

  | Srnd _ ->
      fun _ -> error "cannot execute a random sampling"

  | Scall (lv, xp, args) ->
      let cargs = List.map (c_expr st sc) args in
      let w = omap (c_write st sc) lv in
      let site = ref None in
      fun env ->
        let args = List.map (fun c -> c env) cargs in
        let res = c_call_site st site xp args in
        oiter (fun w -> w env res) w

  | Sif (c, s1, s2) ->
      let cc = c_expr st sc c in
      let c1 = c_stmt st sc s1 in
      let c2 = c_stmt st sc s2 in
      fun env -> if as_bool (cc env) then c1 env else c2 env

  | Swhile (c, s) ->
      let cc = c_expr st sc c in
      let cs = c_stmt st sc s in
      fun env -> while as_bool (cc env) do cs env done

  | Smatch (e, bs) ->
      let ce = c_expr st sc e in
      let cbs = Array.of_list (List.map (fun (xs, s) ->
        let sc, is = bind_list sc (List.map fst xs) in
        (is, c_stmt st sc s)) bs) in
      fun env -> begin
        match ce env with
        | VCtor (_, i, vs) ->
            let (is, cs) = cbs.(i) in
            fill env is vs; cs env
        | v -> error "cannot match on %s" (string_of_value v)
      end

  | Sraise _ ->
      fun _ -> error "exception raised"

  | Sabstract _ ->
      fun _ -> error "cannot execute an abstract statement"

(* The compiled definition of a procedure, after the aliases. *)
and c_resolve (st : state) (xp : xpath) : cproc =
  let xp = EcEnv.NormMp.norm_xfun st.env xp in
  let fn =
    match EcEnv.Fun.by_xpath_opt xp st.env with
    | Some fn -> fn
    | None -> error "unknown procedure: %s" (x_tostring xp) in
  match fn.f_def with
  | FBalias xp' -> c_resolve st xp'
  | FBabs _ -> error "cannot execute abstract procedure %s" (x_tostring xp)
  | FBdef def ->
      let name = x_tostring xp in
      match Hashtbl.find_opt st.cprocs name with
      | Some cp -> cp
      | None ->
          let fr = new_frame ~pvars:true () in
          let sc = (fr, Mk.empty) in
          let params =
            List.map (fun ov ->
              omap (fun x -> oget (lookup sc (-1, x))) ov.ov_name)
              fn.f_sig.fs_anames in
          let body = c_stmt st sc def.f_body in
          let ret = omap (c_expr st sc) def.f_ret in
          let cp = {
            cp_name = name; cp_size = fr.size; cp_params = params;
            cp_body = body; cp_ret = ret; } in
          Hashtbl.replace st.cprocs name cp; cp

and c_call_site (st : state) (site : cproc option ref) (xp : xpath) (args : value list) =
  let cp =
    match !site with
    | Some cp -> cp
    | None -> let cp = c_resolve st xp in site := Some cp; cp in
  c_run st cp args

and c_run (st : state) (cp : cproc) (args : value list) : value =
  if !(st.fuel) <= 0 then error "maximal call depth reached";
  decr st.fuel;
  let nparams = List.length cp.cp_params in
  let nargs = List.length args in
  if nparams <> nargs then
    error "%s: expecting %d argument(s), got %d" cp.cp_name nparams nargs;
  let fr = Array.make cp.cp_size unset in
  List.iter2 (fun i v -> oiter (fun i -> fr.(i) <- v) i) cp.cp_params args;
  cp.cp_body fr;
  let res =
    match cp.cp_ret with
    | None -> VTuple []
    | Some c -> c fr in
  incr st.fuel; res

let c_call (st : state) (xp : xpath) (args : value list) : value =
  c_run st (c_resolve st xp) args

(* -------------------------------------------------------------------- *)
(* With EC_EVAL_PROFILE set, the number of applications of each        *)
(* operator is printed on stderr at the end of each command.            *)
let profiling = env_flag "EC_EVAL_PROFILE"

let report (st : state) =
  oiter (fun tbl ->
    let all = Hashtbl.fold (fun p n acc -> (p, !n) :: acc) tbl [] in
    let all = List.sort (fun (_, n1) (_, n2) -> compare n2 n1) all in
    Format.eprintf "eval profile: %d steps@." !used;
    Format.eprintf "eval profile (applications per operator):@.";
    List.iteri (fun i (p, n) ->
      if i < 40 then Format.eprintf "  %10d  %s@." n (tostring p)) all;
    let stats = Hashtbl.fold (fun x (h, m) acc -> (x, !h, !m) :: acc) memo_stats [] in
    let stats = List.sort (fun (_, h1, m1) (_, h2, m2) -> compare (h2 + m2) (h1 + m1)) stats in
    Format.eprintf "eval memo (hits / misses per operator):@.";
    List.iteri (fun i (x, h, m) ->
      if i < 20 then Format.eprintf "  %10d / %-10d  %s@." h m x) stats;
    if profile_time then begin
      let all = Hashtbl.fold (fun p (t, n) acc -> (p, !t, !n) :: acc) self_time [] in
      let all = List.sort (fun (_, t1, _) (_, t2, _) -> compare t2 t1) all in
      let total = List.fold_left (fun a (_, t, _) -> a +. t) 0.0 all in
      Format.eprintf "eval profile (self time per operator, total %.2f s):@." total;
      List.iteri (fun i (p, t, n) ->
        if i < 30 then Format.eprintf "  %8.3f s %5.1f%%  %10d  %s@." t (100.0 *. t /. total) n (tostring p)) all;
      Hashtbl.reset self_time
    end)
    st.profile

let mkstate (env : EcEnv.env) =
  Hashtbl.reset memo_stats;
  used := 0;
  budget := EcGState.asint ~default:0 (EcGState.getvalue "Eval:steps" (EcEnv.gstate env));
  steps  := if !budget > 0 then !budget else -1; {
  env;
  profile = if profiling then Some (Hashtbl.create 256) else None;
  ops     = EcPath.Hp.create 1024;
  eqrules = EcPath.Hp.create 16;
  tynorm  = EcTypes.Hty.create 64;
  globals = ref EcSymbols.Msym.empty;
  fuel    = ref 10_000;
  native_words = EcGState.getflag "Eval:native_words" (EcEnv.gstate env);
  native_zmod  = EcGState.getflag "Eval:native_zmod" (EcEnv.gstate env);
  native_arrays = EcGState.getflag "Eval:native_arrays" (EcEnv.gstate env);
  cops     = EcPath.Hp.create 1024;
  ceqrules = EcPath.Hp.create 16;
  cprocs   = Hashtbl.create 16;
}

(* EC_EVAL_ENGINE=tree (the default) selects the tree-walking engine    *)
(* ([eval]), and EC_EVAL_ENGINE=compiled the compiled one ([comp]).      *)
let eval_closed (st : state) (f : form) : value =
  if engine_compiled then c_eval_closed st f else eval st empty_lenv f

let eval_form (env : EcEnv.env) (f : form) : value =
  let st = mkstate env in
  let v = eval_closed st f in report st; v

let check_eq (env : EcEnv.env) (ty : ty) (v1 : value) (v2 : value) : bool =
  if engine_compiled then c_eq_typed (mkstate env) ty v1 v2
  else eq_typed (mkstate env) ty v1 v2

let run_proc (env : EcEnv.env) (xp : xpath) (args : form list) : value =
  let st = mkstate env in
  let args = List.map (eval_closed st) args in
  let v = if engine_compiled then c_call st xp args else call st xp args in
  report st; v
