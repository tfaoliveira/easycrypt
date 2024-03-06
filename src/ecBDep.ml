(* -------------------------------------------------------------------- *)
open EcUtils
open EcBigInt
open EcSymbols
open EcPath
open EcParsetree
open EcEnv
open EcTypes
open EcModules

(* -------------------------------------------------------------------- *)
module Map = Batteries.Map
module Hashtbl = Batteries.Hashtbl
module Set = Batteries.Set

(* -------------------------------------------------------------------- *)
module C = struct
  include Lospecs.Aig
  include Lospecs.Circuit
  include Lospecs.Circuit_avx2.FromSpec ()
  include Lospecs.Circuit_spec
end

(* -------------------------------------------------------------------- *)
module IdentMap = Lospecs.Ast.IdentMap
module Ident = Lospecs.Ast.Ident

type ident = Ident.ident
type deps = ((int * int) * int C.VarRange.t) list

(* -------------------------------------------------------------------- *)
module CircEnv : sig
  type env

  val empty : env
  val lookup : env -> symbol -> ident option
  val lookup_id : env -> int -> ident option
  val push : env -> symbol -> env * ident
  val bind : env -> ident -> C.reg -> env
  val get : env -> ident -> C.reg option
  val bind_s : env -> symbol -> C.reg -> env
  val get_s : env -> symbol -> C.reg option
end = struct
  type env = { vars : (symbol, ident) Map.t;
               bindings : C.reg IdentMap.t;
               ids : (int, ident) Map.t }

(* -------------------------------------------------------------------- *)
  let empty : env = { vars = Map.empty;
                      bindings = IdentMap.empty;
                      ids = Map.empty }

(* -------------------------------------------------------------------- *)
  let lookup (env : env) (x: symbol) = Map.find_opt x env.vars

(* -------------------------------------------------------------------- *)
  let lookup_id (env: env) (i: int) = Map.find_opt i env.ids

(* -------------------------------------------------------------------- *)
  let push (env : env) (x : symbol) =
    let idx = Ident.create x in
    let env = { vars = Map.add x idx env.vars ;
                bindings = env.bindings;
                ids  = Map.add (Ident.id idx) idx env.ids } in
    (env, idx)

(* -------------------------------------------------------------------- *)
  let push_ident (env: env) (idx: ident) : env =
    let (name, id) = (Ident.name idx, Ident.id idx) in
    let env = { vars = Map.add name idx env.vars ;
                bindings = env.bindings;
                ids  = Map.add id idx env.ids } in
    env

(* -------------------------------------------------------------------- *)
  let bind (env: env) (x : ident) (r : C.reg) =
    let env =
      match Map.find_opt (Ident.name x) env.vars with
              | Some _ -> env
              | None -> push_ident env x
    in let env = {
      vars = env.vars;
      ids  = env.ids;
      bindings = IdentMap.add x r env.bindings; }
    in env

(* -------------------------------------------------------------------- *)
  let get (env: env) (x: ident) =
    IdentMap.find_opt x env.bindings

(* -------------------------------------------------------------------- *)
  let bind_s (env: env) (x : symbol) (r : C.reg) =
    match lookup env x with
    | Some idx -> bind env idx r
    | None -> bind env (Ident.create x) r

(* -------------------------------------------------------------------- *)
  let get_s (env: env) (x : symbol) =
    match lookup env x with
    | Some idx -> get env idx
    | None -> None
end

(* -------------------------------------------------------------------- *)
type width = int

type bprgm =
  bstmt list

and bstmt =
  vsymbol * brhs

and vsymbol =
  symbol * width

and brhs =
  | Const of width * zint
  | Copy  of vsymbol
  | Op    of symbol * bargs

and barg =
  | Const of width * zint
  | Var   of vsymbol

and bargs = barg list

type cp_env = CircEnv.env

(* -------------------------------------------------------------------- *)
let pp_barg (fmt : Format.formatter) (b : barg) =
  match b with
  | Const (w, i) ->
     Format.fprintf fmt "%a@%d" EcBigInt.pp_print i w

  | Var (x, w) ->
     Format.fprintf fmt "%s@%d" x w

(* -------------------------------------------------------------------- *)
let pp_brhs (fmt : Format.formatter) (rhs : brhs) =
  match rhs with
  | Const (w, i) ->
     Format.fprintf fmt "%a@%d" EcBigInt.pp_print i w

  | Copy (x, w) ->
     Format.fprintf fmt "%s@%d" x w

  | Op (op, args) ->
     Format.fprintf fmt "%s%a"
       op
       (Format.pp_print_list
          (fun fmt a -> Format.fprintf fmt "@ %a" pp_barg a))
       args

(* -------------------------------------------------------------------- *)
let pp_bstmt (fmt : Format.formatter) (((x, w), rhs) : bstmt) =
  Format.fprintf fmt "%s@%d = %a" x w pp_brhs rhs

(* -------------------------------------------------------------------- *)
let pp_bprgm (fmt : Format.formatter) (bprgm : bprgm) =
  List.iter (Format.fprintf fmt "%a;@." pp_bstmt) bprgm

(* -------------------------------------------------------------------- *)
let register_of_barg (env : cp_env) (arg : barg) : C.reg =
  match arg with
  | Const (w, i) ->
    C.of_bigint ~size:w (EcBigInt.to_zt i)

  | Var (x, i) ->
    Option.get (CircEnv.get_s env x)

(* -------------------------------------------------------------------- *)
let registers_of_bargs (env : cp_env) (args : bargs) : C.reg list =
  List.map (register_of_barg env) args

(* -------------------------------------------------------------------- *)
let circuit_of_bstmt (env : cp_env) (((v, s), rhs) : bstmt) : cp_env * C.reg =
  let (env, idx) = CircEnv.push env v in

  let r =
    match rhs with
    | Const (w, i) ->
      C.of_bigint ~size:w (EcBigInt.to_zt i)

    | Copy (x, w) -> Option.get (CircEnv.get_s env x)

    | Op (op, args) ->
      args |> registers_of_bargs env |> (C.func_from_spec op)
  in

  let env = CircEnv.bind env idx r in

  (env, r)

(* -------------------------------------------------------------------- *)
let circuit_from_bprgm (env: cp_env) (prg : bprgm) =
  List.fold_left_map circuit_of_bstmt env prg

(* -------------------------------------------------------------------- *)
let print_deps ~name (env : cp_env) (r : C.reg)  =
  let deps = C.deps r in

  List.iter (fun ((lo, hi), deps) ->
    let vs =
         Enum.(--) lo hi
      |> Enum.fold (fun vs i ->
           let name = Format.sprintf "%s_%03d" name (i / 256) in
           C.VarRange.push vs (name, i mod 256)
         ) C.VarRange.empty in

    Format.eprintf "%a: %a@."
      (C.VarRange.pp Format.pp_print_string) vs
      (C.VarRange.pp
         (fun fmt i ->
            let name = Ident.name (Option.get (CircEnv.lookup_id env i)) in
            Format.fprintf fmt "%s" name))
      deps
  ) deps


(* FIXME: TEMPORARY DEV FUNCTION, TO BE DELETED *)
let print_deps_alt ~name (r : C.reg)  =
  let deps = C.deps r in

  List.iter (fun ((lo, hi), deps) ->
    let vs =
         Enum.(--) lo hi
      |> Enum.fold (fun vs i ->
           let name = Format.sprintf "%s_%03d" name (i / 256) in
           C.VarRange.push vs (name, i mod 256)
         ) C.VarRange.empty in

    Format.eprintf "%a: %a@."
      (C.VarRange.pp Format.pp_print_string) vs
      (C.VarRange.pp
         (fun fmt i ->
            Format.fprintf fmt "%d" i))
      deps
  ) deps



(* -------------------------------------------------------------------- *)
let print_deps_ric (env : cp_env) (r : string) =
  let circ = Option.get (CircEnv.get_s env r) in
  print_deps env circ ~name:r

(* -------------------------------------------------------------------- *)
let circ_dep_split (r : C.reg) : C.reg list =
  let deps = C.deps r in

  List.fold_left_map (fun acc ((lo, hi), _) ->
    swap (List.split_nth (hi - lo + 1) acc)
  ) r deps |> snd

let compare_deps (d1: deps) (d2: deps) : bool =
  List.for_all2 (fun ((lo1, hi1), deps1) ((lo2, hi2), deps2) ->
    (hi1 - lo1 == hi2 - lo2) && 
    (List.for_all2 (fun (_, l1) (_, l2) -> 
      List.for_all2 
        (fun (a1, b1) (a2, b2) -> b1 - a1 == b2 - a2) 
        l1 
        l2) 
      (C.VarRange.contents deps1)
      (C.VarRange.contents deps1)))
    d1
    d2

let rec inputs_of_node : _ -> C.var Set.t =
  let cache : (int, C.var Set.t) Hashtbl.t = Hashtbl.create 0 in
  
  let rec doit (n : C.node) : C.var Set.t =
    match Hashtbl.find_option cache (Int.abs n.id) with
    | None ->
      let mn = doit_r n.gate in
      Hashtbl.add cache (Int.abs n.id) mn;
      mn
    | Some mn -> 
      mn

  and doit_r (n : C.node_r) = 
    match n with
    | False -> Set.empty
    | Input v -> Set.singleton v
    | And (n1, n2) -> Set.union (doit n1) (doit n2)

  in fun n -> doit n

let inputs_of_reg (r : C.reg) : C.var Set.t =
  List.fold_left (fun acc x -> Set.union acc (inputs_of_node x)) Set.empty r

let circ_equiv (r1 : C.reg) (r2 : C.reg) : bool = 
  if List.compare_lengths r1 r2 <> 0 then false 
  else 
    let d1 = C.deps r1 in 
    let d2 = C.deps r2 in
    if not (compare_deps d1 d2) then false
    else 

      let inps = List.combine (inputs_of_reg r1 |> Set.to_list) (inputs_of_reg r2 |> Set.to_list) in
      C.equivs inps r1 r2

let bruteforce (r : C.reg) (vars : C.var list) : unit = 
  let rec doit (acc : bool list) (n : int) : unit =
    match n with
    | 0 -> let eval = ((List.combine vars acc) |> List.to_seq |> Map.of_seq) in
           let eval = C.eval (fun x -> Map.find x eval) in 
           List.map eval r |> C.uint_of_bools |> Format.eprintf "@.@.ERROR: -> %d: %d@." (C.uint_of_bools acc) 
    | n -> doit (false::acc) (n-1); doit (true::acc) (n-1)

  in doit [] (List.length vars)

let bools_of_int (n : int) ~(size: int) : bool list =
  List.init size (fun i -> ((n lsl i) land 1) <> 0) 

let bruteforce_equiv (r1 : C.reg) (r2 : C.reg) (range: int) : bool = 
  let eval (r : C.reg) (n: int) : int =
    let inp = inputs_of_reg r |> Set.to_list in
    let vals = bools_of_int n ~size:(List.length inp) in
    let env = List.combine inp vals |> List.to_seq |> Map.of_seq in
    let eval = C.eval (fun x -> Map.find x env) in
    List.map eval r |> C.uint_of_bools
  in
  Enum.(--^) 0 range |> Enum.map (fun i -> (eval r1 i) == (eval r2 i)) |> Enum.fold (&&) true

(* -------------------------------------------------------------------- *)
exception BDepError

(* -------------------------------------------------------------------- *)
let decode_op (p : path) : symbol =
  match EcPath.toqsymbol p with
  | ["Top"; "JWord"; "W16u16"], ("VPSUB_16u16"       as op)
  | ["Top"; "JWord"; "W16u16"], ("VPSRA_16u16"       as op)
  | ["Top"; "JWord"; "W16u16"], ("VPADD_16u16"       as op)
  | ["Top"; "JWord"; "W16u16"], ("VPBROADCAST_16u16" as op)
  | ["Top"; "JWord"; "W16u16"], ("VPMULH_16u16"      as op)

     -> op

  | ["Top"; "JModel_x86"], ("VPMULHRS_16u16" as op)
  | ["Top"; "JModel_x86"], ("VPACKUS_16u16"  as op)
  | ["Top"; "JModel_x86"], ("VPMADDUBSW_256" as op)
  | ["Top"; "JModel_x86"], ("VPERMD"         as op)

     -> op

  | ["Top"; "JWord"; "W256"], "andw" -> "AND_u256"

  | _ ->
     Format.eprintf "%s@." (EcPath.tostring p);
     raise BDepError



let rec circuit_of_form (env: env) (f : EcAst.form) : C.reg =
  let trans_wtype (ty : ty) : width =
    match (EcEnv.Ty.hnorm ty env).ty_node with
    | Tconstr (p, []) -> begin
        match EcPath.toqsymbol p with
        | (["Top"; "JWord"; "W256"], "t") -> 256
        | (["Top"; "JWord"; "W128"], "t") -> 128
        | (["Top"; "JWord"; "W64" ], "t") ->  64
        | (["Top"; "JWord"; "W32" ], "t") ->  32
        | (["Top"; "JWord"; "W16" ], "t") ->  16
        | (["Top"; "JWord"; "W8"  ], "t") ->   8
        | (["Top"; "Pervasive"], "int") -> 256
        | (qs, q) -> List.iter (Format.eprintf "%s ") qs; Format.eprintf "@. %s@." q; raise BDepError
        | _ -> raise BDepError
      end

    | _ ->
       raise BDepError in

  let trans_jops (pth: qsymbol) : C.reg list -> C.reg =
    (* TODO: Check if we need regs to be of correct size or not *)
    match pth with
    | (["Top"; "JWord"; "W32"], "to_uint") -> 
        fun rs ->
        assert (List.length rs == 1); 
        (List.hd rs)
    | (["Top"; "JWord"; "W16"], "to_uint") -> 
        fun rs ->
        assert (List.length rs == 1); 
        (List.hd rs)
    | (["Top"; "JWord"; "W8"], "to_uint") -> 
        fun rs ->
        assert (List.length rs == 1); 
        (List.hd rs)
    | (["Top"; "JWord"; "W32"], "of_int") -> 
        fun rs ->
        assert (List.length rs == 1); 
        (rs |> List.hd |> List.take 32)
    | (["Top"; "JWord"; "W16"], "of_int") -> 
        fun rs ->
        assert (List.length rs == 1); 
        (rs |> List.hd |> List.take 16)
    | (["Top"; "JWord"; "W8"], "of_int") -> 
        fun rs ->
        assert (List.length rs == 1); 
        (rs |> List.hd |> List.take 16)
    | (["Top"; "JWord"; "W32"], "*") 
    | (["Top"; "JWord"; "W16"], "*") -> 
        fun rs ->
        assert (List.length rs == 2); 
        let a = List.hd rs in 
        let b = (rs |> List.tl |> List.hd) in
        C.umull a b 
    | (["Top"; "JWord"; "W32"], "+") 
    | (["Top"; "JWord"; "W16"], "+") -> 
        fun rs ->
        assert (List.length rs == 2); 
        let a = List.hd rs in 
        let b = (rs |> List.tl |> List.hd) in
        C.add a b |> snd
    | (["Top"; "JWord"; "W32"], "[-]") ->
        fun rs -> begin
          match List.length rs with
          | 2 ->
            let a = List.hd rs in
            let b = (rs |> List.tl |> List.hd) in
            C.sub_dropc a b
          | n -> Format.eprintf "Got %d args for sub" n; failwith "Wrong args"
        end
    | (["Top"; "JWord"; "W32"], "`<<`") 
    | (["Top"; "JWord"; "W16"], "`<<`") -> 
        fun rs ->
        assert (List.length rs == 2);
        let a = List.hd rs in 
        let b = (rs |> List.tl |> List.hd) in
        C.shift ~side:`L ~sign:`L a b 
    | (["Top"; "JWord"; "W32"], "`>>`")     (*  assuming logical shift right for words   *)
    | (["Top"; "JWord"; "W16"], "`>>`") ->  (* TODO: need to check if this is correct or *)  
        fun rs ->                           (* if we need to apply a mask                *)
        assert (List.length rs == 2);
        let a = List.hd rs in 
        let b = (rs |> List.tl |> List.hd) in
        C.shift ~side:`R ~sign:`L a b 
    | (["Top"; "JWord"; "W32"], "`&`") 
    | (["Top"; "JWord"; "W32"], "andw")  
    | (["Top"; "JWord"; "W16"], "`&`") 
    | (["Top"; "JWord"; "W16"], "andw") -> 
        fun rs ->
        assert (List.length rs == 2);
        let a = List.hd rs in 
        let b = (rs |> List.tl |> List.hd) in
        C.land_ a b 


    | _ -> List.iter (Format.eprintf "%s ") (fst pth);
        Format.eprintf "%s@." (snd pth);
        failwith "Operator not implemented yet?"
  in

  match f.f_node with
  (* hardcoding size for now FIXME *)
  | Fint z -> C.of_bigint ~size:256 (EcAst.BI.to_zt z) 
  | Fif (c_f, t_f, f_f) -> 
      let c_c = circuit_of_form env c_f in
      let t_c = circuit_of_form env t_f in
      let f_c = circuit_of_form env f_f in
      let () = assert (List.length c_c == 1) in
      let c_c = List.hd c_c in
      C.mux2_reg f_c t_c c_c
  (* hardcoding size for now FIXME *)
  | Flocal idn -> 
      C.reg ~size:(trans_wtype f.f_ty) ~name:idn.id_tag 
      (* TODO: Check name after *)
  | Fop (pth, _) -> 
    let (pth, pth2) = EcPath.toqsymbol pth in
    let () = List.iter (Format.eprintf "%s ") pth in
    let () = Format.eprintf "@.%s@.------------@." pth2 in

    C.reg ~size:0 ~name:0
  | Fapp _ as f_ -> 
    let (f, fs) = EcCoreFol.destr_app f in
    let fs_c = List.map (circuit_of_form env) fs in
    begin match f.f_node with
      | Fop (pth, _) ->
          trans_jops (EcPath.toqsymbol pth) fs_c
      | _ -> failwith "Cant apply to non op"
    end 
(*    let f = circuit_of_form env f in *)
  | Fquant (_, binds, f) -> 
      (* maybe add bindings to some env here? *)
      circuit_of_form env f (* FIXME *) 
  | Fproj (f, i) ->
      begin match f.f_node with
      | Ftuple tp ->
        circuit_of_form env (tp |> List.drop (i-1) |> List.hd)
      | _ -> circuit_of_form env f 
      (* FIXME^: for testing, to allow easycrypt to ignore flags on Jasmin operators *) 
      end
  | Fmatch _ -> failwith "fmatch"
  | Flet _ -> failwith "flet"
  | Fpvar _ -> failwith "fpvar"
  | _ -> failwith "Not yet implemented"
    
(* V might not be necessary V *)
and int_of_form (env: env) (f: EcAst.form) : int =
  let trans_jops (pth: qsymbol) : int list -> int =
    match pth with
    | (["Top"; "JWord"; "W16"], "of_int") -> 
        (fun rs -> assert (List.length rs == 1); 
        (List.hd rs) land ((1 lsl 16) - 1))
    | (["Top"; "JWord"; "W8"], "of_int") -> 
        (fun rs -> assert (List.length rs == 1); 
        (List.hd rs) land ((1 lsl 8) - 1))
    | (["Top"; "JWord"; "W16"], "*") -> 
        (fun rs -> assert (List.length rs == 2); 
        let a = List.hd rs in
        let b = rs |> List.tl |> List.hd in
        (a * b) land ((1 lsl 16) - 1))
    | (["Top"; "JWord"; "W16"], "+") -> 
        (fun rs -> assert (List.length rs == 2); 
        let a = List.hd rs in
        let b = rs |> List.tl |> List.hd in
        (a + b) land ((1 lsl 16) - 1))
    | (["Top"; "JWord"; "W16"], "`<<`") ->
        (fun rs -> assert (List.length rs == 2); 
        let a = List.hd rs in
        let b = rs |> List.tl |> List.hd in
        (a lsl (b mod 16)) land ((1 lsl 16) - 1))
        
    | _ -> List.iter (Format.eprintf "%s ") (fst pth);
        Format.eprintf "%s@." (snd pth);
        failwith "Operator not implemented yet?"
  in

  match f.f_node with
  | Fint z -> EcAst.BI.to_int z
  | Fapp _ as f_ -> 
    let (f, fs) = EcCoreFol.destr_app f in
    let fs_c = List.map (int_of_form env) fs in
    begin match f.f_node with
      | Fop (pth, _) ->
          trans_jops (EcPath.toqsymbol pth) fs_c
      | _ -> failwith "Cant apply to non op"
    end 

  | _ -> failwith "Form cannot be converted to int"

(* -------------------------------------------------------------------- *)
let bdep (env : env) (p : pgamepath) (f: psymbol) (n : int) (m : int) (vs : string list) : unit =
  let proc = EcTyping.trans_gamepath env p in
  let proc = EcEnv.Fun.by_xpath proc env in
  let pdef = match proc.f_def with FBdef def -> def | _ -> assert false in
  let f = EcEnv.Op.lookup ([], f.pl_desc) env |> snd in
  let f = match f.op_kind with
  | OB_oper (Some (OP_Plain (f, _))) -> f
  | _ -> failwith "Invalid operator type" in
  let fc = circuit_of_form env f in
  let () = Format.eprintf "len %d @." (List.length fc) in
  let () = inputs_of_reg fc |> Set.to_list |> List.iter (fun x -> Format.eprintf "%d %d@." (fst x) (snd x)) in
  print_deps_alt ~name:"test_out" fc;
  Format.eprintf "@. YAAAAAA @."
 
  (* Working with:
   op compress_alt (d: int, c: W16.t) : W16.t = (((c * ((W16.of_int 1) `<<` (W8.of_int d)) + (W16.of_int qh)) * (W16.of_int two_eight)) `>>` (W8.of_int 28)) `&` ((W16.of_int 1) `<<` (W8.of_int d)). 
  *)

(*

  let trans_int (p : path) : width =
    match EcPath.toqsymbol p with
    | (["Top"; "JWord"; "W256"], "of_int") -> 256
    | (["Top"; "JWord"; "W128"], "of_int") -> 128
    | (["Top"; "JWord"; "W64" ], "of_int") ->  64
    | (["Top"; "JWord"; "W32" ], "of_int") ->  32
    | (["Top"; "JWord"; "W16" ], "of_int") ->  16
    | (["Top"; "JWord"; "W8"  ], "of_int") ->   8
    | _ -> raise BDepError in

  let trans_wtype (ty : ty) : width =
    match (EcEnv.Ty.hnorm ty env).ty_node with
    | Tconstr (p, []) -> begin
        match EcPath.toqsymbol p with
        | (["Top"; "JWord"; "W256"], "t") -> 256
        | (["Top"; "JWord"; "W128"], "t") -> 128
        | (["Top"; "JWord"; "W64" ], "t") ->  64
        | (["Top"; "JWord"; "W32" ], "t") ->  32
        | (["Top"; "JWord"; "W16" ], "t") ->  16
        | (["Top"; "JWord"; "W8"  ], "t") ->   8
        | _ -> raise BDepError
      end

    | _ ->
       raise BDepError in

  let trans_arg (e : expr) : barg =
    match e.e_node with
    | Evar (PVloc y) ->
       Var (y, trans_wtype e.e_ty)

    | Eapp ({ e_node = Eop (p, []) }, [{ e_node = Eint i }]) ->
      Const (trans_int p, i)

    | _ ->
       let ppe = EcPrinting.PPEnv.ofenv env in
       Format.eprintf "%a@." (EcPrinting.pp_expr ppe) e;
       raise BDepError

  in

  let rec trans_ret (e : expr) : barg list =
    match e.e_node with
    | Evar (PVloc y) ->
        [Var (y, trans_wtype e.e_ty)]
    | Etuple es ->
        List.fold_left (fun acc x -> List.append (trans_ret x) acc) [] es
    | _ -> failwith "Not valid return type"

  in

  let trans_instr (i : instr) : bstmt =
    match i.i_node with
    | Sasgn (LvVar (PVloc x, xty), e) ->
       let rhs =
         match e.e_node with
         | Evar (PVloc y) ->
            Copy (y, trans_wtype e.e_ty)

         | Eapp ({ e_node = Eop (p, []) }, [{ e_node = Eint i }]) ->
            Const (trans_int p, i)

         | Eapp ({ e_node = Eop (p, []) }, args) ->
            Op (decode_op p, List.map trans_arg args)

         | _ ->
            raise BDepError

       in ((x, trans_wtype xty), rhs)

    | _ -> raise BDepError in

  let trans_arg_ (x : ovariable) =
   (oget ~exn:BDepError x.ov_name, trans_wtype x.ov_type) in

  let trans_local (x : variable) =
    (x.v_name, trans_wtype x.v_type) in

  let arguments = List.map trans_arg_ proc.f_sig.fs_anames in
  let ret_vars = Option.map trans_ret pdef.f_ret |> Option.map List.rev in
  let _locals = List.map trans_local pdef.f_locals in

  let body : bprgm = List.map trans_instr pdef.f_body.s_node in

  if not (List.is_unique (List.fst body)) then
    raise BDepError;

  let cenv = List.fold_left 
    (fun env (s,w) -> 
      let (env, idn) = CircEnv.push env s in
      CircEnv.bind  env idn (C.reg ~size:w ~name:(Ident.id idn)))
    CircEnv.empty arguments in
  let (cenv, circs) = circuit_from_bprgm cenv body in

  (*
   * TODO
   *  1: generator the circuit C from the program `body`
   *  2: compute the dependencies and infer sub-circuits C1...Cn
   *  3: check equivalence between the different boolean functions C1...Cn
   *  4: generate a circuit Pr encoding the pre-condition (partial)
   *  5: generate a circuit Po encoding the post-condition
   *  6: check that (Pri /\ Ci) => Poi by computation
   *)

  Format.eprintf "%a@." pp_bprgm body;

  (*
  print_deps_ric cenv "rp_0_0";
  print_deps_ric cenv "rp_1_0";
  print_deps_ric cenv "rp_2_0";
  print_deps_ric cenv "rp_3_0";*)

    (*
  let process (r : symbol) : unit = 
    let rs = Option.get (CircEnv.get_s cenv r) in
    let rs = circ_dep_split rs in
    let () = assert (List.for_all (circ_equiv (List.hd rs)) (List.tl rs)) in 
    List.iteri (fun i r_ -> print_deps ~name:(r ^ (string_of_int (i*(List.length r_)))) cenv r_) rs

  in match ret_vars with
  | Some vs ->
      List.iter
        process
        (List.map (fun x -> match x with | Var (v,_) -> v | _ -> failwith "Wrong") vs)
  | _ -> ()
    *)

  (*
  match ret_vars with
  | Some ((Var (v, _))::_) ->
    let rs = Option.get (CircEnv.get_s cenv v) in
    let rs = circ_dep_split rs |> List.hd in
    let inputs = inputs_of_reg rs in
    assert (bruteforce_equiv rs comp_circ 65536);
    Format.eprintf "Success@.";
    exit 0;
    bruteforce rs (Set.to_list inputs)
  | _ -> ()
*)

  let comp_circ = C.func_from_spec "COMPRESS" [C.reg ~size:16 ~name:0] in
  begin 
    let circ = List.map (fun v -> Option.get (CircEnv.get_s cenv v)) vs |> List.flatten in
    let () = assert ((List.length circ) mod m == 0) in
    let rec part (l : 'a list) (n : int) : 'a list list = (* assumes above assertion for correctness *)
      match l with
      | [] -> []
      | v -> (List.take n l)::(part (List.drop n l) n) in
    let circs = part circ m in
    (* DEBUG PRINT DEPS FOR PARTITIONED CIRCUITS: *)
    let () = 
    List.iteri (fun i c ->
      Format.eprintf "@.%d: " i;
      print_deps ~name:"TEST_" cenv c) circs
    in
    
    let () = assert (List.for_all (fun c ->
      let d = C.deps c in
      List.for_all (fun (_, deps) -> 
        List.for_all (fun (_, l) ->
          List.for_all (fun (a,b) ->
          b - a + 1 == n) l)
        (C.VarRange.contents deps)
      ) d) 
    circs) in
    let () = assert (List.for_all (circ_equiv (List.hd circs)) (List.tl circs)) in
    Format.eprintf "Success@."
  end 



  (*

    Take {rp_0, rp_1, rp_2, rp_3} e.g, flatten it as one bit array
    partition into array of m-bit words 
    these can be computed each from m-bit input words
    by operator f

    Args to bdep: {rp_0, ..., rp_3} as a list
                  n -> input words size
                  m -> output word size
                  f : `W n => `W m -> operator

    Args -> Semi done -> Need to check type still

  1) Circuit from procedure -> done
  2) Flatten array of the variables we want -> Done
  3) Join by each m bits -> Done
  4) Check that each block depends on (exactly) n bits -> Done
  5) Check that circuits are equivalent for each pair of blocks -> Done
  6) Generate circuit for operator
    -> 
  7) Check it is equivalent to first block -> Done*

  *)

*)
