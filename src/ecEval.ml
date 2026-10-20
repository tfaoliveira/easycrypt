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

let apply (f : value) (v : value) : value =
  incr used;
  if !steps >= 0 then begin
    if !steps = 0 then raise (StepLimit !budget);
    decr steps
  end;
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

(* A hash of the first nodes of the values. *)
let memo_hash (vs : value list) : int =
  let budget = ref 64 in
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

let memo_stats : (string, int ref * int ref) Hashtbl.t = Hashtbl.create 16

(* Errors report the operators being evaluated (at most 8 of them). *)
let in_context (name : string) (f : unit -> value) : value =
  try f () with EvalError msg ->
    let depth = List.length (String.split_on_char '\n' msg) in
    if depth > 8 then raise (EvalError msg)
    else raise (EvalError (Printf.sprintf "%s\n  in %s" msg name))

let memo_op ?(name = "") (n : int) (v : value) : value =
  if n = 0 then v else
  if no_op_memo then nary n (fun vs -> in_context name (fun () -> apply_n v vs)) else
  let tbl = MH.create 64 in
  let (hits, misses) =
    match Hashtbl.find_opt memo_stats name with
    | Some c -> c
    | None -> let c = (ref 0, ref 0) in Hashtbl.add memo_stats name c; c in
  nary n (fun vs ->
    if List.exists (function VFun _ -> true | _ -> false) vs then
      in_context name (fun () -> apply_n v vs) else
    match MH.find_opt tbl vs with
    | Some r -> incr hits; r
    | None ->
        incr misses;
        let r = in_context name (fun () -> apply_n v vs) in
        if MH.length tbl >= 65536 then MH.reset tbl;
        MH.add tbl vs r; r)

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

type state = {
  env      : EcEnv.env;
  profile  : (path, int ref) Hashtbl.t option;  (* calls per operator *)
  ops      : (path, value) Hashtbl.t;
  eqrules  : (path, ER.rule list) Hashtbl.t;  (* [eval] rules on [=], by type *)
  globals  : value EcSymbols.Msym.t ref;
  fuel     : int ref;                  (* bound on the procedure call depth *)
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

let core_ops : (path * value) list Lazy.t = lazy (
  let int2 f = fun2 (fun a b -> f (as_int a) (as_int b)) in
  let int3 f = fun3 (fun a b c -> f (as_int a) (as_int b) (as_int c)) in
  let edivz m d =
    if Z.equal d Z.zero then (Z.zero, m) else Z.ediv_rem m d in
  let iteri = fun3 (fun n f x ->
    let n = as_int n in
    if Z.gt n (Z.of_int max_int) then error "iteri: too many iterations";
    let n = Z.to_int n in
    let x = ref x in
    for i = 0 to n - 1 do
      x := apply_n f [VInt (Z.of_int i); !x]
    done; !x) in
  let ipow = int2 (fun x n ->
    if Z.lt n Z.zero then error "negative exponent";
    if Z.gt n (Z.of_int max_int) then error "exponent too large";
    VInt (Z.pow x (Z.to_int n))) in
  CI.CI_Int.[
    p_int_add  , int2 (fun a b -> VInt (Z.add a b));
    p_int_mul  , int2 (fun a b -> VInt (Z.mul a b));
    p_int_opp  , fun1 (fun a -> VInt (Z.neg (as_int a)));
    p_int_lt   , int2 (fun a b -> VBool (Z.lt a b));
    p_int_le   , int2 (fun a b -> VBool (Z.leq a b));
    p_int_edivz, int2 (fun a b ->
                   let (q, r) = edivz a b in VTuple [VInt q; VInt r]);
    p_int_pow  , ipow;
    p_iteri    , iteri;
  ] @ CI.CI_Bool.[
    p_true , VBool true;
    p_false, VBool false;
    p_not  , fun1 (fun a -> VBool (not (as_bool a)));
    p_eq   , fun2 (fun a b -> VBool (value_eq a b));
    p_iff  , fun2 (fun a b -> VBool (as_bool a = as_bool b));
  ] @ [
    CI.CI_Witness.p_witness, VWitness;
    p_modexp, int3 (fun b e m ->
      (* modexp b e m = (b ^ e) %% m *)
      if Z.lt e Z.zero then error "modexp: negative exponent";
      if Z.equal m Z.zero then
        apply_n ipow [VInt b; VInt e]
      else
        let m = Z.abs m in VInt (Z.erem (Z.powm b e m) m));
  ])

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

let native_list_ops : (path * (int * (value list -> value))) list Lazy.t = lazy (
  let small n = if Z.fits_int n then Z.to_int n else if Z.sign n < 0 then min_int else max_int in
  [ p_list "size", (1, function
      | [l] -> VInt (Z.of_int (List.length (spine l)))
      | _ -> assert false);

    p_list "nth", (3, function
      | [x; l; n] ->
          let n = small (as_int n) in
          let l = spine l in
          if n < 0 then x else odfl x (List.nth_opt l n)
      | _ -> assert false);

    p_list "drop", (2, function
      | [n; l] ->
          let rec drop n l = if n <= 0 then l else
            match l with [] -> [] | _ :: l -> drop (n - 1) l in
          v_of_list (drop (small (as_int n)) (spine l))
      | _ -> assert false);

    p_list "take", (2, function
      | [n; l] -> v_of_list (List.take (max 0 (small (as_int n))) (spine l))
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

let bitstring_op (bs : crb_bitstring) kind : value =
  let n = binding_size bs.size in
  match kind with
  | `To -> fun1 (fun w -> bits_to_list n (z_of_bits w))
  | `From -> raise Not_found          (* handled by [from_bits] below *)
  | `OfInt -> fun1 (fun i -> mk_bits (is_bool_type bs.type_) n (as_int i))
  | `ToUInt -> fun1 (fun w -> VInt (z_of_bits w))
  | `ToSInt -> fun1 (fun w -> VInt (bits_to_sint n (z_of_bits w)))

let bvoperator (env : EcEnv.env) (bo : crb_bvoperator) : value option =
  let size_of (v : value) =
    match v with
    | VBits (n, _) -> (false, n)
    | VBool _ -> (true, 1)
    | _ -> error "expecting a bitstring, got %s" (string_of_value v) in
  let un f = Some (fun1 (fun a ->
    let (b, n) = size_of a in mk_bits b n (f n (z_of_bits a)))) in
  let bin f = Some (fun2 (fun a1 a2 ->
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
      Some (fun2 (fun w i ->
        let (_, n) = size_of w in
        let i = as_int i in
        let bit = Z.leq Z.zero i && Z.lt i (Z.of_int n)
                  && Z.testbit (z_of_bits w) (Z.to_int i) in
        mk_bits isbool 1 (if bit then Z.one else Z.zero)))

  | `Init _ ->
      (* bvinit : (int -> BV1.bv) -> BV2.bv, BV1 of size 1 *)
      let (isbool, n) = bitstring_type 1 in
      Some (fun1 (fun f ->
        let z = ref Z.zero in
        for i = n - 1 downto 0 do
          let b = z_of_bits (apply f (VInt (Z.of_int i))) in
          z := Z.logor (Z.shift_left !z 1) (Z.logand b Z.one)
        done;
        mk_bits isbool n !z))

  | _ -> None

(* -------------------------------------------------------------------- *)
(* Rules of the [eval] database                                         *)
let eval_base = "eval"

(* -------------------------------------------------------------------- *)
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

  | Fapp (f, args) ->
      let fv = eval st le f in
      (match st.profile, f.f_node with
       | Some tbl, Fop (p, _) -> begin
           match Hashtbl.find_opt tbl p with
           | Some n -> incr n
           | None -> Hashtbl.add tbl p (ref 1)
         end
       | _, _ -> ());
      apply_n fv (List.map (eval st le) args)

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
  match Hashtbl.find_opt st.ops p with
  | Some v -> v
  | None ->
      (* Recursive operators refer to themselves: tie the knot lazily. *)
      let cell = ref None in
      Hashtbl.replace st.ops p (VFun (fun v ->
        match !cell with
        | Some f -> apply f v
        | None -> error "ill-founded definition of %s" (tostring p)));
      let v =
        try in_context (tostring p) (fun () -> op_value_r st p)
        with e -> Hashtbl.remove st.ops p; raise e in
      cell := Some v;
      Hashtbl.replace st.ops p v; v

and op_value_r (st : state) (p : path) : value =
  let env = st.env in

  match EcPath.Mp.find_opt p (Lazy.force core_table) with
  | Some v -> v
  | None ->

  let op =
    match EcEnv.Op.by_path_opt p env with
    | Some op -> op
    | None -> error "unknown operator: %s" (tostring p) in

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
  if n = 0 then try_rules [] rules else nary n (fun vs -> try_rules vs rules)

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
and eq_typed (st : state) (ty : ty) (v1 : value) (v2 : value) : bool =
  let ty = EcEnv.ty_hnorm ty st.env in
  match ty.ty_node, v1, v2 with
  | Ttuple tys, VTuple vs1, VTuple vs2 when List.length tys = List.length vs1 ->
      List.for_all2 (fun ty (v1, v2) -> eq_typed st ty v1 v2)
        tys (List.combine vs1 vs2)
  | Tconstr (p, _), _, _ -> begin
      let rule_ty (r : ER.rule) =
        match r.ER.rl_ptn with
        | ER.Rule (`Op (_, [rty]), [_; _]) -> begin
            match (EcEnv.ty_hnorm rty st.env).ty_node with
            | Tconstr (q, _) -> Some q
            | _ -> None
          end
        | _ -> None in
      let rules =
        match Hashtbl.find_opt st.eqrules p with
        | Some rules -> rules
        | None ->
            let rules =
              EcEnv.Reduction.get ~base:eval_base (`Path CI.CI_Bool.p_eq) st.env
              |> List.filter (fun r -> ofold (fun q _ -> p_equal p q) false (rule_ty r))
              |> List.sort (fun r1 r2 -> compare r1.ER.rl_prio r2.ER.rl_prio) in
            Hashtbl.replace st.eqrules p rules; rules in
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
      if i < 20 then Format.eprintf "  %10d / %-10d  %s@." h m x) stats)
    st.profile

let mkstate (env : EcEnv.env) =
  Hashtbl.reset memo_stats;
  used := 0;
  budget := EcGState.asint ~default:0 (EcGState.getvalue "Eval:steps" (EcEnv.gstate env));
  steps  := if !budget > 0 then !budget else -1; {
  env;
  profile = if profiling then Some (Hashtbl.create 256) else None;
  ops     = Hashtbl.create 1024;
  eqrules = Hashtbl.create 16;
  globals = ref EcSymbols.Msym.empty;
  fuel    = ref 10_000;
}

let eval_form (env : EcEnv.env) (f : form) : value =
  let st = mkstate env in
  let v = eval st empty_lenv f in report st; v

let check_eq (env : EcEnv.env) (ty : ty) (v1 : value) (v2 : value) : bool =
  eq_typed (mkstate env) ty v1 v2

let run_proc (env : EcEnv.env) (xp : xpath) (args : form list) : value =
  let st = mkstate env in
  let args = List.map (eval st empty_lenv) args in
  let v = call st xp args in report st; v
