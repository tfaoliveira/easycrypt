(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open EcIdent
open EcPath
open EcUid

module BI = EcBigInt

type memory = EcIdent.t

type 'a equality = 'a -> 'a -> bool
type 'a hash = 'a -> int
type 'a fv   = 'a -> int EcIdent.Mid.t

(* -------------------------------------------------------------------- *)
type quantum = [`Quantum | `Classical]

let pp_quantum = function
  | `Classical -> ""
  | `Quantum -> "quantum "

(* -------------------------------------------------------------------- *)
type quantum_op =
  | Qinit
  | Qunitary

let qo_equal (o1:quantum_op) (o2:quantum_op) = o1 == o2
let qo_hash (o1:quantum_op) = Hashtbl.hash o1
let qo_fv (_:quantum_op) : int Mid.t = Mid.empty

(* -------------------------------------------------------------------- *)
type pvar_kind =
  | PVKglob
  | PVKloc of quantum

(* -------------------------------------------------------------------- *)
type equantif  = [ `ELambda | `EForall | `EExists ]

type quantif =
  | Lforall
  | Lexists
  | Llambda

(* -------------------------------------------------------------------- *)
type hoarecmp = FHle | FHeq | FHge

(* -------------------------------------------------------------------- *)
type global = quantum * EcPath.xpath

module Oglobal = struct
  type t = global
  let compare (_, x1) (_, x2) = x_compare x1 x2
end

module Mglob = EcMaps.Map.Make(Oglobal)
module Sglob = EcMaps.Set.MakeOfMap(Mglob)

(* -------------------------------------------------------------------- *)
type ty = {
  ty_node : ty_node;
  ty_fv   : int Mid.t; (* only ident appearing in path *)
  ty_tag  : int;
}

and ty_node =
  | Tglob   of functor_fun (* Globals use by f *)
  | Tunivar of EcUid.uid
  | Tvar    of EcIdent.t
  | Ttuple  of ty list
  | Tconstr of EcPath.path * ty list
  | Tfun    of ty * ty

and ovariable = {
  ov_quantum : quantum;
  ov_name : EcSymbols.symbol option;
  ov_type : ty;
}

and variable = {
  v_quantum : quantum;
  v_name : EcSymbols.symbol;   (* can be "_" *)
  v_type : ty;
}

and lpattern =
  | LSymbol of (EcIdent.t * ty)
  | LTuple  of (EcIdent.t * ty) list
  | LRecord of EcPath.path * (EcIdent.t option * ty) list

and expr = {
  e_node : expr_node;
  e_ty   : ty;
  e_fv   : int Mid.t;
  e_tag  : int;
}

and expr_node =
  | Eint   of BI.zint                      (* int. literal          *)
  | Elocal of EcIdent.t                    (* let-variables         *)
  | Evar   of prog_var                     (* module variable       *)
  | Eop    of EcPath.path * ty list        (* op apply to type args *)
  | Eapp   of expr * expr list             (* op. application       *)
  | Equant of equantif * ebindings * expr  (* fun/forall/exists     *)
  | Elet   of lpattern * expr * expr       (* let binding           *)
  | Etuple of expr list                    (* tuple constructor     *)
  | Eif    of expr * expr * expr           (* _ ? _ : _             *)
  | Ematch of expr * expr list * ty        (* match _ with _        *)
  | Eproj  of expr * int                   (* projection of a tuple *)

and ebinding  = EcIdent.t * ty
and ebindings = ebinding list

(* -------------------------------------------------------------------- *)
and prog_var_ty = prog_var * ty

and prog_var =
  | PVglob of EcPath.xpath
  | PVloc of (quantum * EcSymbols.symbol)

(* -------------------------------------------------------------------- *)
and quantum_ref =
  | QRvar   of prog_var_ty
  | QRtuple of quantum_ref list
  | QRproj  of quantum_ref * int (* proj start at 0 *)

(* -------------------------------------------------------------------- *)
and lvalue =
  | LvVar   of prog_var_ty
  | LvTuple of prog_var_ty list

(* -------------------------------------------------------------------- *)
and instr = {
  i_node : instr_node;
  i_fv : int Mid.t;
  i_tag  : int;
}

and instr_node =
  | Squantum  of quantum_ref * quantum_op * expr
  | Smeasure  of lvalue * quantum_ref * expr
     (* x <- measure q with f *)
  | Sasgn     of lvalue * expr
  | Srnd      of lvalue * expr
  | Scall     of lvalue option * EcPath.xpath * expr list * quantum_ref
     (* quantum_arg can be empty, only local *)
  | Sif       of expr * stmt * stmt
  | Swhile    of expr * stmt
  | Smatch    of expr * ((EcIdent.t * ty) list * stmt) list
  | Sassert   of expr
  | Sabstract of EcIdent.t

and stmt = {
  s_node : instr list;
  s_fv   : int Mid.t;
  s_tag  : int;
}

(* -------------------------------------------------------------------- *)
and oracle_info = {
  oi_calls : xpath list;
}

and functor_params = (EcIdent.t * module_type) list

and functor_fun = {
  ff_params : functor_params;
  ff_xp     : xpath;                (* The xpath is fully applied *)
}

and mem_restr =
  | Empty
  | Quantum                   (* All quantum global references *)
  | Classical                 (* All classical global variables *)
  | Var     of global         (* The global variable or quantum ref *)
  | GlobFun of functor_fun    (* Global of a function *)
  | Union   of mem_restr * mem_restr
  | Inter   of mem_restr * mem_restr
  | Diff    of mem_restr * mem_restr

and mod_restr = {
  mr_mem    : mem_restr;
  mr_oinfos : oracle_info Msym.t;
}

and module_type = {
  mt_params : functor_params;
  mt_name   : EcPath.path;
  mt_args   : EcPath.mpath list;
  mt_restr  : mod_restr;
}

(* -------------------------------------------------------------------- *)
and proj_arg = {
  arg_quantum : quantum;    (* classical/quantum *)
  arg_ty      : ty;         (* type of the procedure argument "arg" *)
  arg_pos     : int;        (* projection *)
}

and local_memtype_ = {
  lmt_name : symbol option;      (* provides access to the full local memory *)
  lmt_decl : ovariable list;
  lmt_proj : (int * ty) Msym.t;  (* where to find the symbol in mt_decl and its type *)
  lmt_ty   : ty;                 (* ttuple (List.map v_type mt_decl) *)
  lmt_n    : int;                (* List.length mt_decl *)
}

and local_memtype = {
  classical_lmt : local_memtype_;
  quantum_lmt   : local_memtype_;
}

and memtype =
  | Lmt_concrete of local_memtype option

and memenv = memory * memtype

(* -------------------------------------------------------------------- *)
and gty =
  | GTty    of ty
  | GTmodty of module_type
  | GTmem   of memtype

and binding  = (EcIdent.t * gty)
and bindings = binding list

and form = {
  f_node : f_node;
  f_ty   : ty;
  f_fv   : int Mid.t; (* local, memory, module ident *)
  f_tag  : int;
}

and f_node =
  | Fquant  of quantif * bindings * form
  | Fif     of form * form * form
  | Fmatch  of form * form list * ty
  | Flet    of lpattern * form * form
  | Fint    of BI.zint
  | Flocal  of EcIdent.t
  | Fpvar   of prog_var * memory
  | Fglob   of functor_fun * memory
  | Fop     of EcPath.path * ty list
  | Fapp    of form * form list
  | Ftuple  of form list
  | Fproj   of form * int

  | FhoareF of sHoareF (* $hr / $hr *)
  | FhoareS of sHoareS

  | FbdHoareF of bdHoareF (* $hr / $hr *)
  | FbdHoareS of bdHoareS

  | FeHoareF of eHoareF (* $hr / $hr *)
  | FeHoareS of eHoareS

  | FequivF of qequivF (* $left,$right / $left,$right *)
  | FequivS of qequivS

  | FeagerF of eagerF

  | Fpr of pr (* hr *)

and eagerF = {
  eg_pr : form;
  eg_sl : stmt;  (* No local program variables *)
  eg_fl : EcPath.xpath;
  eg_fr : EcPath.xpath;
  eg_sr : stmt;  (* No local program variables *)
  eg_po : form
}

(* quantum_equality:
   qeg = true : equality of all global quantum variable;
   type of qel = type of qer
   qel and qer should be valid;
   qeg = true implies qel and qer are only locals
*)
and quantum_equality = {
   qeg : bool;
   qel : quantum_ref;
   qer : quantum_ref;
}

and equiv_cond = {
  ec_f : form;
  ec_e : quantum_equality;
}

and qequivF = {
  ef_pr : equiv_cond;
  ef_fl : EcPath.xpath;
  ef_fr : EcPath.xpath;
  ef_po : equiv_cond;
}

and qequivS = {
  es_ml  : memenv;
  es_mr  : memenv;
  es_pr  : equiv_cond;
  es_sl  : stmt;
  es_sr  : stmt;
  es_po  : equiv_cond; }

and sHoareF = {
  hf_pr : form;
  hf_f  : EcPath.xpath;
  hf_po : form;
}

and sHoareS = {
  hs_m  : memenv;
  hs_pr : form;
  hs_s  : stmt;
  hs_po : form; }


and eHoareF = {
  ehf_pr  : form;
  ehf_f   : EcPath.xpath;
  ehf_po  : form;
}

and eHoareS = {
  ehs_m   : memenv;
  ehs_pr  : form;
  ehs_s   : stmt;
  ehs_po  : form;
}

and bdHoareF = {
  bhf_pr  : form;
  bhf_f   : EcPath.xpath;
  bhf_po  : form;
  bhf_cmp : hoarecmp;
  bhf_bd  : form;
}

and bdHoareS = {
  bhs_m   : memenv;
  bhs_pr  : form;
  bhs_s   : stmt;
  bhs_po  : form;
  bhs_cmp : hoarecmp;
  bhs_bd  : form;
}

and pr = {
  pr_mem   : memory;
  pr_fun   : EcPath.xpath;
  pr_args  : form;
  pr_event : form;
}

(* ----------------------------------------------------------------- *)
(* Equality, hash, and fv                                            *)
(* ----------------------------------------------------------------- *)
let ty_equal : ty -> ty -> bool = (==)
let ty_hash ty = ty.ty_tag
let ty_fv ty = ty.ty_fv

(* -------------------------------------------------------------------- *)
let v_equal vd1 vd2 =
  vd1.v_name = vd2.v_name &&
  ty_equal vd1.v_type vd2.v_type

let v_hash v =
  Why3.Hashcons.combine
    (Hashtbl.hash v.v_name)
    (ty_hash v.v_type)

(* -------------------------------------------------------------------- *)
let pv_equal v1 v2 = match v1, v2 with
  | PVglob x1, PVglob x2 ->
    EcPath.x_equal x1 x2
  | PVloc(q1,i1), PVloc(q2,i2) -> q1 = q2 && EcSymbols.sym_equal i1 i2
  | PVloc _, PVglob _ | PVglob _, PVloc _ -> false

let pv_kind = function
  | PVglob _ -> PVKglob
  | PVloc (q,_) -> PVKloc q

let pv_hash v =
  let h = match v with
    | PVglob x -> EcPath.x_hash x
    | PVloc (_,i) -> Hashtbl.hash i in

  Why3.Hashcons.combine
    h (if pv_kind v = PVKglob then 1 else 0)

let pv_fv = function
  | PVglob x -> EcPath.x_fv Mid.empty x
  | PVloc _ -> Mid.empty

(* -------------------------------------------------------------------- *)
let pv_loc id = PVloc id
let pv_cloc id = PVloc (`Classical, id)
let pv_qloc id = PVloc (`Quantum, id)
let pv_var  v = pv_loc (v.v_quantum , v.v_name)
let pv_ovar v = pv_loc (v.ov_quantum, oget v.ov_name)

(* -------------------------------------------------------------------- *)
let idty_equal (x1,t1) (x2,t2) =
  EcIdent.id_equal x1 x2 && ty_equal t1 t2

let lp_equal p1 p2 =
  match p1, p2 with
  | LSymbol xt1, LSymbol xt2 -> idty_equal xt1 xt2
  | LTuple lx1, LTuple lx2 -> List.all2 idty_equal lx1 lx2
  | _ -> false

let idty_hash (x,t) = Why3.Hashcons.combine (EcIdent.id_hash x) (ty_hash t)

let lp_hash = function
  | LSymbol  x -> idty_hash x
  | LTuple  lx -> Why3.Hashcons.combine_list idty_hash 0 lx

  | LRecord (p, lx) ->
      let for1 (x, ty) =
        Why3.Hashcons.combine (ty_hash ty)
          (Why3.Hashcons.combine_option EcIdent.id_hash x)
      in
        Why3.Hashcons.combine_list for1 (p_hash p) lx

let lp_fv = function
  | LSymbol (id, _) ->
      Sid.singleton id

  | LTuple ids ->
      List.fold_left (fun s (id, _) -> Sid.add id s) Sid.empty ids

  | LRecord (_, ids) ->
      List.fold_left
        (fun s (id, _) -> ofold Sid.add s id)
        Sid.empty ids

(* -------------------------------------------------------------------- *)
let e_equal   = ((==) : expr -> expr -> bool)
let e_hash    = fun e -> e.e_tag
let e_fv e    = e.e_fv

(* -------------------------------------------------------------------- *)
let eqt_equal : equantif -> equantif -> bool = (==)
let eqt_hash  : equantif -> int = Hashtbl.hash

(* -------------------------------------------------------------------- *)
let pvt_equal (pv1, ty1) (pv2, ty2) =
  pv_equal pv1 pv2 && ty_equal ty1 ty2

let pvt_fv (pv, _) =
  (* FIXME QUANTUM: why type are not inspected *)
  pv_fv pv

let pvts_fv pvs =
  (* FIXME QUANTUM: why type are not inspected *)
  let add s xt = EcIdent.fv_union s (pvt_fv xt) in
  List.fold_left add Mid.empty pvs

(* -------------------------------------------------------------------- *)
let lv_equal lv1 lv2 =
  match lv1, lv2 with
  | LvVar pv1, LvVar pv2 -> pvt_equal pv1 pv2

  | LvTuple tu1, LvTuple tu2 ->
      List.all2 pvt_equal tu1 tu2

  | _, _ -> false

let lv_fv = function
  | LvVar x -> pvt_fv x
  | LvTuple pvs -> pvts_fv pvs

let lv_hash = function
  | LvVar (pv, ty) ->
      Why3.Hashcons.combine (pv_hash pv) (ty_hash ty)

  | LvTuple pvs ->
      Why3.Hashcons.combine_list
        (fun (pv, ty) ->
          Why3.Hashcons.combine (pv_hash pv) (ty_hash ty)) 0 pvs

(* -------------------------------------------------------------------- *)
let quantum_unit =
  QRtuple []

let is_quantum_unit (qr : quantum_ref) =
  qr = quantum_unit

let rec qr_equal (qr1 : quantum_ref) (qr2 : quantum_ref) =
  match qr1, qr2 with
  | QRvar (x1, ty1), QRvar (x2, ty2) -> pv_equal x1 x2 && ty_equal ty1 ty2
  | QRtuple t1, QRtuple t2 -> List.all2 qr_equal t1 t2
  | QRproj (qr1, i1), QRproj (qr2, i2) -> i1 = i2 && qr_equal qr1 qr2
  | _, _ -> false

let rec qr_hash (qr : quantum_ref) : int =
  match qr with
  | QRvar (x, ty)  -> Why3.Hashcons.combine (pv_hash x) (ty_hash ty)
  | QRtuple t      -> Why3.Hashcons.combine_list qr_hash 0 t
  | QRproj (qr, i) -> Why3.Hashcons.combine (qr_hash qr) i

let rec qr_fv = function
  | QRvar x -> pvt_fv x
  | QRtuple t ->
      let add s qr = EcIdent.fv_union s (qr_fv qr) in
      List.fold_left add Mid.empty t
  | QRproj (qr, _) -> qr_fv qr

let qrvar pvt = QRvar pvt

let qrtuple t =
  match t with
  | [qr] -> qr
  | _ -> QRtuple t

let qrproj (qr, i) =
  match qr with
  | QRtuple t ->
    (try List.nth t i
     with Invalid_argument _ ->
       Printexc.print_raw_backtrace Stdlib.stderr (Printexc.get_callstack 1000);
       Format.eprintf "i = %i; size = %i@." i (List.length t);
       assert false);
  | _ -> QRproj(qr, i)

let qr_pvloc v =
  assert (v.v_quantum = `Quantum);
  qrvar (pv_qloc v.v_name, v.v_type)

let qr_pvlocs vs =
  qrtuple (List.map qr_pvloc vs)

let rec qr_iter f = function
  | QRvar x -> f x
  | QRtuple t -> List.iter (qr_iter f) t
  | QRproj(q,_) -> qr_iter f q

let rec qr_map f = function
  | QRvar x -> qrvar (f x)
  | QRtuple t -> qrtuple (List.Smart.map (qr_map f) t)
  | QRproj (q, i) -> qrproj (qr_map f q, i)

let rec qr_fold f a = function
  | QRvar x -> f a x
  | QRtuple t -> List.fold_left (qr_fold f) a t
  | QRproj(q, _) -> qr_fold f a q

let rec qr_all f qr =
  match qr with
  | QRvar x -> f x
  | QRtuple t -> List.for_all (qr_all f) t
  | QRproj (q, _) -> qr_all f q

let rec qr_all2 f qr1 qr2 =
  match qr1, qr2 with
  | QRvar x1, QRvar x2 -> f x1 x2
  | QRtuple t1, QRtuple t2 -> List.all2 (qr_all2 f) t1 t2
  | QRproj (q1, i1), QRproj (q2,i2) -> i1 = i2 && qr_all2 f q1 q2
  | _, _ -> false

(* -------------------------------------------------------------------- *)
let i_equal   = ((==) : instr -> instr -> bool)
let i_hash    = fun i -> i.i_tag
let i_fv i    = i.i_fv

let s_equal   = ((==) : stmt -> stmt -> bool)
let s_hash    = fun s -> s.s_tag
let s_fv      = fun s -> s.s_fv


(*-------------------------------------------------------------------- *)
let qt_equal : quantif -> quantif -> bool = (==)
let qt_hash  : quantif -> int = Hashtbl.hash

(*-------------------------------------------------------------------- *)
let f_equal : form -> form -> bool = (==)
let f_hash f = f.f_tag
let f_fv f = f.f_fv

(* -------------------------------------------------------------------- *)
let oi_equal oi1 oi2 =
  List.all2 EcPath.x_equal oi1.oi_calls oi2.oi_calls

let oi_hash oi =
  Why3.Hashcons.combine_list EcPath.x_hash 0
    (List.sort EcPath.x_compare oi.oi_calls)

(* -------------------------------------------------------------------- *)
let hcmp_hash : hoarecmp -> int = Hashtbl.hash

(* -------------------------------------------------------------------- *)

let ov_quantum { ov_quantum = x } = x
let ov_name { ov_name = x } = x
let ov_type { ov_type = x } = x

let ov_hash v =
  Why3.Hashcons.combine
    (Hashtbl.hash v.ov_name)
    (ty_hash v.ov_type)

let ov_equal vd1 vd2 =
  vd1.ov_quantum = vd2.ov_quantum &&
  EcUtils.opt_equal (=) vd1.ov_name vd2.ov_name &&
  ty_equal vd1.ov_type vd2.ov_type

(* -------------------------------------------------------------------- *)
let v_quantum { v_quantum = x } = x
let v_name { v_name = x } = x
let v_type { v_type = x } = x

let v_hash v =
  Why3.Hashcons.combine
    (Hashtbl.hash v.v_name)
    (ty_hash v.v_type)

let v_equal vd1 vd2 =
  vd1.v_quantum = vd2.v_quantum &&
  vd1.v_name = vd2.v_name &&
  ty_equal vd1.v_type vd2.v_type

let ovar_of_var { v_quantum = q; v_name = n; v_type = t } =
  { ov_quantum = q; ov_name = Some n; ov_type = t }

(* -------------------------------------------------------------------- *)

(* Check for "physical" equality *)
let rec ff_equal ff1 ff2 =
  ff1 == ff2 ||
  x_equal ff1.ff_xp ff2.ff_xp &&
  mod_params_equal ff1.ff_params ff2.ff_params

and mod_params_equal mp1 mp2 =
  mp1 == mp2 ||
  List.equal (fun (x1,mt1) (x2,mt2) ->
     id_equal x1 x2 &&
     mty_equal mt1 mt2) mp1 mp2

and mty_equal mt1 mt2 =
  mt1 == mt2 ||
  p_equal mt1.mt_name mt2.mt_name &&
  List.equal m_equal mt1.mt_args mt2.mt_args &&
  mod_params_equal mt1.mt_params mt2.mt_params &&
  mr_equal mt1.mt_restr mt2.mt_restr

and mr_equal mr1 mr2 =
  mr1 == mr2 ||
  Msym.equal oi_equal mr1.mr_oinfos mr2.mr_oinfos &&
  mer_equal mr1.mr_mem mr2.mr_mem

and g_equal (q1, x1) (q2, x2) =
   q1 = q2 && x_equal x1 x2

and mer_equal mer1 mer2 =
  mer1 == mer2 ||
  match mer1, mer2 with
  | Empty, Empty | Quantum, Quantum | Classical, Classical -> true
  | Var v1, Var v2 -> g_equal v1 v2
  | GlobFun ff1, GlobFun ff2 -> ff_equal ff1 ff2
  | Union(s11, s12), Union(s21, s22)
  | Inter(s11, s12), Inter(s21, s22)
  | Diff (s11, s12), Diff (s21, s22) -> mer_equal s11 s21 && mer_equal s12 s22
  | _, _ -> false


let rec ff_fv ff =
  mod_params_fv ff.ff_params (x_fv Mid.empty ff.ff_xp)

and mod_params_fv mp fv =
  List.fold_right (fun (x,mt) fv ->
     fv_union (Mid.remove x fv) (mty_fv mt)) mp fv

and mty_fv mty =
  (* FIXME in mem_restr can depend on params ? *)
  let fv = mr_fv mty.mt_restr in
  let fv = List.fold_left m_fv fv mty.mt_args in
  mod_params_fv mty.mt_params fv

and mr_fv mr =
  fv_union (mer_fv mr.mr_mem) (oinfos_fv mr.mr_oinfos)

and oinfos_fv oi =
  EcSymbols.Msym.fold (fun _ oi fv ->
      List.fold_left EcPath.x_fv fv oi.oi_calls
    ) oi Mid.empty

and mer_fv mer =
  match mer with
  | Empty | Quantum | Classical -> Mid.empty
  | Var (_, x) -> x_fv Mid.empty x
  | GlobFun ff -> ff_fv ff
  | Union(s1, s2)
  | Inter(s1, s2)
  | Diff (s1, s2) -> fv_union (mer_fv s1)( mer_fv s2)

let mod_params_hash params =
  Why3.Hashcons.combine_list
     (fun (x, _) -> EcIdent.id_hash x)
     0 params

let mty_hash mty =
  Why3.Hashcons.combine2
    (EcPath.p_hash mty.mt_name)
    (mod_params_hash mty.mt_params)
    (Why3.Hashcons.combine_list EcPath.m_hash 0 mty.mt_args)

let ff_hash ff =
  Why3.Hashcons.combine
     (EcPath.x_hash ff.ff_xp)
     (mod_params_hash ff.ff_params)

(* -------------------------------------------------------------------- *)

let lmem_hash_ (lmem : local_memtype_) : int =
  let mt_name_hash = Why3.Hashcons.combine_option Hashtbl.hash lmem.lmt_name in
  let mt_decl_hash = Why3.Hashcons.combine_list ov_hash 0 lmem.lmt_decl in

  let mt_proj_hash =
    let el_hash (s, (i, ty)) =
      Why3.Hashcons.combine2 (Hashtbl.hash s) i (ty_hash ty) in
    Why3.Hashcons.combine_list el_hash 0 (Msym.bindings lmem.lmt_proj) in

  Why3.Hashcons.combine_list
    (fun i -> i)
    (ty_hash lmem.lmt_ty)
    [lmem.lmt_n; mt_name_hash; mt_decl_hash; mt_proj_hash]


let lmt_equal_
    (ty_equal : ty -> ty -> bool)
    (lmt1     : local_memtype_)
    (lmt2     : local_memtype_)
  =
  match lmt1.lmt_name, lmt2.lmt_name with
  | None, None ->
      Msym.equal (fun (_, ty1) (_, ty2) ->
        ty_equal ty1 ty2
      ) lmt1.lmt_proj lmt2.lmt_proj

  | Some name1, Some name2 when name1 = name2->
      List.all2 ov_equal lmt1.lmt_decl lmt2.lmt_decl

  | _, _ ->
     false

let lmt_fv_ (lmt : local_memtype_) (fv : int Mid.t) =
  List.fold_left (fun fv v ->
    EcIdent.fv_union fv v.ov_type.ty_fv
  ) fv lmt.lmt_decl

let lmt_iter_ty_ (f : ty -> unit) (lmt : local_memtype_) =
  List.iter (fun v -> f v.ov_type) lmt.lmt_decl

(* -------------------------------------------------------------------- *)
let lmt_hash (lmem : local_memtype) =
  Why3.Hashcons.combine
    (lmem_hash_ lmem.classical_lmt)
    (lmem_hash_ lmem.quantum_lmt)

let lmt_fv (lmem : local_memtype) =
  EcIdent.Mid.empty
  |> lmt_fv_ lmem.classical_lmt
  |> lmt_fv_ lmem.quantum_lmt

let lmt_equal
    (ty_equal : ty -> ty -> bool)
    (mt1      : local_memtype)
    (mt2      : local_memtype)
  =
     lmt_equal_ ty_equal mt1.classical_lmt mt2.classical_lmt
  && lmt_equal_ ty_equal mt1.quantum_lmt mt2.quantum_lmt

let lmt_iter_ty (f : ty -> unit) (lmem : local_memtype) =
  lmt_iter_ty_ f lmem.classical_lmt;
  lmt_iter_ty_ f lmem.quantum_lmt

(* -------------------------------------------------------------------- *)

let mt_fv (mt : memtype) =
  match mt with
  | Lmt_concrete None -> EcIdent.Mid.empty
  | Lmt_concrete (Some lmem) -> lmt_fv lmem

let mt_equal_gen ty_equal (Lmt_concrete mt1) (Lmt_concrete mt2) =
  oeq (lmt_equal ty_equal) mt1 mt2

let mt_equal = mt_equal_gen ty_equal

let mt_iter_ty (f : ty -> unit) (mt : memtype) =
  match mt with
  | Lmt_concrete lmem ->
     oiter (lmt_iter_ty f) lmem

(* -------------------------------------------------------------------- *)
let me_hash (mem, Lmt_concrete mt) =
  Why3.Hashcons.combine
    (EcIdent.id_hash mem)
    (Why3.Hashcons.combine_option lmt_hash mt)

let mem_equal (m1 : memory) (m2 : memory) =
  EcIdent.id_equal m1 m2

let me_equal_gen
    (ty_equal  : ty -> ty -> bool)
    ((m1, mt1) : memenv)
    ((m2, mt2) : memenv)
  =
    mem_equal m1 m2 && mt_equal_gen ty_equal mt1 mt2

let me_equal : memenv -> memenv -> bool =
  me_equal_gen ty_equal

(* -------------------------------------------------------------------- *)
let gty_equal ty1 ty2 =
  match ty1, ty2 with
  | GTty ty1, GTty ty2 ->
      ty_equal ty1 ty2

  | GTmodty p1, GTmodty p2  ->
    mty_equal p1 p2

  | GTmem mt1, GTmem mt2 ->
      mt_equal mt1 mt2

  | _ , _ -> false

let gty_hash = function
  | GTty ty -> ty_hash ty
  | GTmodty p  ->  mty_hash p
  | GTmem _ -> 1

(* -------------------------------------------------------------------- *)
let gty_fv = function
  | GTty ty -> ty.ty_fv
  | GTmodty mty -> mr_fv mty.mt_restr
  | GTmem mt -> mt_fv mt

(*-------------------------------------------------------------------- *)

let b_equal (b1 : bindings) (b2 : bindings) =
  let b1_equal (x1, ty1) (x2, ty2) =
    EcIdent.id_equal x1 x2 && gty_equal ty1 ty2
  in
    List.all2 b1_equal b1 b2

let b_hash (bs : bindings) =
  let b1_hash (x, ty) =
    Why3.Hashcons.combine (EcIdent.tag x) (gty_hash ty)
  in
    Why3.Hashcons.combine_list b1_hash 0 bs

(* -------------------------------------------------------------------- *)
let i_equal   = ((==) : instr -> instr -> bool)
let i_hash    = fun i -> i.i_tag
let i_fv i    = i.i_fv

let s_equal   = ((==) : stmt -> stmt -> bool)
let s_hash    = fun s -> s.s_tag
let s_fv      = fun s -> s.s_fv

(* -------------------------------------------------------------------- *)
let qe_equal qe1 qe2 =
     qe1.qeg = qe2.qeg
  && qr_equal qe1.qel qe2.qel
  && qr_equal qe1.qer qe2.qer

let qe_hash qe =
  Why3.Hashcons.combine2 (Hashtbl.hash qe.qeg) (qr_hash qe.qel) (qr_hash qe.qer)

let qe_fv qe =
  fv_union (qr_fv qe.qel) (qr_fv qe.qer)

let qe_empty = {
  qeg = false;
  qel = quantum_unit;
  qer = quantum_unit;
}

let is_qe_empty qe =
  not qe.qeg && is_quantum_unit qe.qel && is_quantum_unit qe.qer

let qe_iter f qe =
  qr_iter f qe.qel; qr_iter f qe.qer

let qe_map f qe =
  { qeg = qe.qeg; qel = qr_map f qe.qel; qer = qr_map f qe.qer }

let qe_all f qe =
   qr_all f qe.qel &&  qr_all f qe.qer

let qe_all2 f qe1 qe2 =
  qe1.qeg = qe2.qeg && qr_all2 f qe1.qel qe2.qel && qr_all2 f qe1.qer qe2.qer

(*-------------------------------------------------------------------- *)
let hf_equal hf1 hf2 =
     f_equal hf1.hf_pr hf2.hf_pr
  && f_equal hf1.hf_po hf2.hf_po
  && EcPath.x_equal hf1.hf_f hf2.hf_f

let hs_equal hs1 hs2 =
     f_equal hs1.hs_pr hs2.hs_pr
  && f_equal hs1.hs_po hs2.hs_po
  && s_equal hs1.hs_s hs2.hs_s
  && me_equal hs1.hs_m hs2.hs_m


let ehf_equal hf1 hf2 =
     f_equal hf1.ehf_pr  hf2.ehf_pr
  && f_equal hf1.ehf_po  hf2.ehf_po
  && EcPath.x_equal hf1.ehf_f hf2.ehf_f

let ehs_equal hs1 hs2 =
     f_equal hs1.ehs_pr  hs2.ehs_pr
  && f_equal hs1.ehs_po  hs2.ehs_po
  && s_equal hs1.ehs_s hs2.ehs_s
  && me_equal hs1.ehs_m hs2.ehs_m

let bhf_equal bhf1 bhf2 =
     f_equal bhf1.bhf_pr bhf2.bhf_pr
  && f_equal bhf1.bhf_po bhf2.bhf_po
  && EcPath.x_equal bhf1.bhf_f bhf2.bhf_f
  && bhf1.bhf_cmp = bhf2.bhf_cmp
  && f_equal bhf1.bhf_bd bhf2.bhf_bd

let bhs_equal bhs1 bhs2 =
     f_equal bhs1.bhs_pr bhs2.bhs_pr
  && f_equal bhs1.bhs_po bhs2.bhs_po
  && s_equal bhs1.bhs_s bhs2.bhs_s
  && me_equal bhs1.bhs_m bhs2.bhs_m
  && bhs1.bhs_cmp = bhs2.bhs_cmp
  && f_equal bhs1.bhs_bd bhs2.bhs_bd

let ec_equal ec1 ec2 =
     f_equal ec1.ec_f ec2.ec_f
  && qe_equal ec1.ec_e ec2.ec_e

let eqf_equal ef1 ef2 =
     ec_equal ef1.ef_pr ef2.ef_pr
  && ec_equal ef1.ef_po ef2.ef_po
  && EcPath.x_equal ef1.ef_fl ef2.ef_fl
  && EcPath.x_equal ef1.ef_fr ef2.ef_fr

let eqs_equal es1 es2 =
     ec_equal es1.es_pr es2.es_pr
  && ec_equal es1.es_po es2.es_po
  && s_equal es1.es_sl es2.es_sl
  && s_equal es1.es_sr es2.es_sr
  && me_equal es1.es_ml es2.es_ml
  && me_equal es1.es_mr es2.es_mr

let egf_equal eg1 eg2 =
     f_equal eg1.eg_pr eg2.eg_pr
  && f_equal eg1.eg_po eg2.eg_po
  && s_equal eg1.eg_sl eg2.eg_sl
  && EcPath.x_equal eg1.eg_fl eg2.eg_fl
  && EcPath.x_equal eg1.eg_fr eg2.eg_fr
  && s_equal eg1.eg_sr eg2.eg_sr

let pr_equal pr1 pr2 =
     EcIdent.id_equal pr1.pr_mem pr2.pr_mem
  && EcPath.x_equal   pr1.pr_fun pr2.pr_fun
  && f_equal          pr1.pr_event pr2.pr_event
  && f_equal          pr1.pr_args pr2.pr_args

(* -------------------------------------------------------------------- *)
let hf_hash hf =
  Why3.Hashcons.combine2
    (f_hash hf.hf_pr) (f_hash hf.hf_po) (EcPath.x_hash hf.hf_f)

let hs_hash hs =
  Why3.Hashcons.combine3
    (f_hash hs.hs_pr) (f_hash hs.hs_po)
    (s_hash hs.hs_s)
    (me_hash hs.hs_m)

let ec_hash ec =
  Why3.Hashcons.combine (f_hash ec.ec_f) (qe_hash ec.ec_e)

let ef_hash (ef : qequivF) =
  Why3.Hashcons.combine3
    (ec_hash ef.ef_pr) (ec_hash ef.ef_po)
    (EcPath.x_hash ef.ef_fl) (EcPath.x_hash ef.ef_fr)

let es_hash (es : qequivS) =
  Why3.Hashcons.combine3
    (ec_hash es.es_pr) (ec_hash es.es_po)
    (s_hash es.es_sl)
    (Why3.Hashcons.combine2
       (me_hash es.es_mr)
       (me_hash es.es_ml)
       (s_hash es.es_sr))

let ehf_hash hf =
  Why3.Hashcons.combine2
    (f_hash hf.ehf_pr) (f_hash hf.ehf_po)
    (EcPath.x_hash hf.ehf_f)

let ehs_hash hs =
  Why3.Hashcons.combine3
    (f_hash hs.ehs_pr) (f_hash hs.ehs_po)
    (s_hash hs.ehs_s)
    (me_hash hs.ehs_m)

let bhf_hash bhf =
  Why3.Hashcons.combine_list f_hash
    (Why3.Hashcons.combine (hcmp_hash bhf.bhf_cmp) (EcPath.x_hash bhf.bhf_f))
    [bhf.bhf_pr;bhf.bhf_po;bhf.bhf_bd]

let bhs_hash bhs =
  Why3.Hashcons.combine_list f_hash
    (Why3.Hashcons.combine2
       (hcmp_hash bhs.bhs_cmp)
       (s_hash bhs.bhs_s)
       (me_hash bhs.bhs_m))
    [bhs.bhs_pr;bhs.bhs_po;bhs.bhs_bd]

let ef_hash ef =
  Why3.Hashcons.combine3
    (ec_hash ef.ef_pr) (ec_hash ef.ef_po)
    (EcPath.x_hash ef.ef_fl) (EcPath.x_hash ef.ef_fr)

let es_hash es =
  Why3.Hashcons.combine3
    (ec_hash es.es_pr) (ec_hash es.es_po)
    (s_hash es.es_sl)
    (Why3.Hashcons.combine2
       (me_hash es.es_mr)
       (me_hash es.es_ml)
       (s_hash es.es_sr))

let eg_hash eg =
  Why3.Hashcons.combine3
    (f_hash eg.eg_pr) (f_hash eg.eg_po)
    (Why3.Hashcons.combine (s_hash eg.eg_sl) (EcPath.x_hash eg.eg_fl))
    (Why3.Hashcons.combine (s_hash eg.eg_sr) (EcPath.x_hash eg.eg_fr))

let pr_hash pr =
  Why3.Hashcons.combine3
    (EcIdent.id_hash pr.pr_mem)
    (EcPath.x_hash   pr.pr_fun)
    (f_hash          pr.pr_args)
    (f_hash          pr.pr_event)

(* ----------------------------------------------------------------- *)
let ec_fv ec =
  fv_union ec.ec_f.f_fv (qe_fv ec.ec_e)

(* ----------------------------------------------------------------- *)
(* Hashconsing                                                       *)
(* ----------------------------------------------------------------- *)

module Hsty = Why3.Hashcons.Make (struct
  type t = ty

  let equal ty1 ty2 =
    match ty1.ty_node, ty2.ty_node with
    | Tglob ff1, Tglob ff2 ->
        ff_equal ff1 ff2

    | Tunivar u1, Tunivar u2 ->
        uid_equal u1 u2

    | Tvar v1, Tvar v2 ->
        id_equal v1 v2

    | Ttuple lt1, Ttuple lt2 ->
        List.all2 ty_equal lt1 lt2

    | Tconstr (p1, lt1), Tconstr (p2, lt2) ->
        EcPath.p_equal p1 p2 && List.all2 ty_equal lt1 lt2

    | Tfun (d1, c1), Tfun (d2, c2)->
        ty_equal d1 d2 && ty_equal c1 c2

    | _, _ -> false

  let hash ty =
    match ty.ty_node with
    | Tglob ff         -> ff_hash ff
    | Tunivar u        -> u
    | Tvar    id       -> EcIdent.tag id
    | Ttuple  tl       -> Why3.Hashcons.combine_list ty_hash 0 tl
    | Tconstr (p, tl)  -> Why3.Hashcons.combine_list ty_hash p.p_tag tl
    | Tfun    (t1, t2) -> Why3.Hashcons.combine (ty_hash t1) (ty_hash t2)

  let fv ty =
    let union ex =
      List.fold_left (fun s a -> fv_union s (ex a)) Mid.empty in

    match ty with
    | Tglob ff         -> ff_fv ff
    | Tunivar _        -> Mid.empty
    | Tvar    _        -> Mid.empty (* FIXME: section *)
    | Ttuple  tys      -> union (fun a -> a.ty_fv) tys
    | Tconstr (_, tys) -> union (fun a -> a.ty_fv) tys
    | Tfun    (t1, t2) -> union (fun a -> a.ty_fv) [t1; t2]

  let tag n ty = { ty with ty_tag = n; ty_fv = fv ty.ty_node; }
end)

let mk_ty node =
  Hsty.hashcons { ty_node = node; ty_tag = -1; ty_fv = Mid.empty }

(* ----------------------------------------------------------------- *)

module Hexpr = Why3.Hashcons.Make (struct
  type t = expr

  let b_equal b1 b2 =
    let b1_equal (x1, ty1) (x2, ty2) =
      EcIdent.id_equal x1 x2 && ty_equal ty1 ty2 in
    List.all2 b1_equal b1 b2

  let equal_node e1 e2 =
    match e1, e2 with
    | Eint   i1, Eint   i2 -> BI.equal i1 i2
    | Elocal x1, Elocal x2 -> EcIdent.id_equal x1 x2
    | Evar   x1, Evar   x2 -> pv_equal x1 x2

    | Eop (p1, tys1), Eop (p2, tys2) ->
           (EcPath.p_equal p1 p2)
        && (List.all2 ty_equal tys1 tys2)

    | Eapp (e1, es1), Eapp (e2, es2) ->
           (e_equal e1 e2)
        && (List.all2 e_equal es1 es2)

    | Elet (lp1, e1, f1), Elet (lp2, e2, f2) ->
        (lp_equal lp1 lp2) && (e_equal e1 e2) && (e_equal f1 f2)

    | Etuple es1, Etuple es2 ->
        List.all2 e_equal es1 es2

    | Eif (c1, e1, f1), Eif (c2, e2, f2) ->
        (e_equal c1 c2) && (e_equal e1 e2) && (e_equal f1 f2)

    | Ematch (e1, es1, ty1), Ematch (e2, es2, ty2) ->
           List.all2 e_equal (e1 :: es1) (e2 :: es2)
        && ty_equal ty1 ty2

    | Equant (q1, b1, e1), Equant (q2, b2, e2) ->
        eqt_equal q1 q2 && e_equal e1 e2 && b_equal b1 b2

    | Eproj(e1, i1), Eproj(e2, i2) ->
        i1 = i2 && e_equal e1 e2

    | _, _ -> false

  let equal e1 e2 =
    equal_node e1.e_node e2.e_node &&
    ty_equal e1.e_ty e2.e_ty

  let b_hash bs =
    let b1_hash (x, ty) =
      Why3.Hashcons.combine (EcIdent.tag x) (ty_hash ty)
    in
    Why3.Hashcons.combine_list b1_hash 0 bs

  let hash e =
    match e.e_node with
    | Eint   i -> BI.hash i
    | Elocal x -> Hashtbl.hash x
    | Evar   x -> pv_hash x

    | Eop (p, tys) ->
        Why3.Hashcons.combine_list ty_hash
          (EcPath.p_hash p) tys

    | Eapp (e, es) ->
        Why3.Hashcons.combine_list e_hash (e_hash e) es

    | Elet (p, e1, e2) ->
        Why3.Hashcons.combine2
          (lp_hash p) (e_hash e1) (e_hash e2)

    | Etuple es ->
        Why3.Hashcons.combine_list e_hash 0 es

    | Eif (c, e1, e2) ->
        Why3.Hashcons.combine2
          (e_hash c) (e_hash e1) (e_hash e2)

    | Ematch (e, es, ty) ->
        Why3.Hashcons.combine_list e_hash
          (Why3.Hashcons.combine (e_hash e) (ty_hash ty))
          es

    | Equant (q, b, e) ->
        Why3.Hashcons.combine2 (eqt_hash q) (e_hash e) (b_hash b)

    | Eproj (e, i) ->
        Why3.Hashcons.combine (e_hash e) i

  let fv_node e =
    let union ex =
      List.fold_left (fun s e -> fv_union s (ex e)) Mid.empty
    in

    match e with
    | Eint _            -> Mid.empty
    | Eop (_, tys)      -> union (fun a -> a.ty_fv) tys
    | Evar v            -> pv_fv v
    | Elocal id         -> fv_singleton id
    | Eapp (e, es)      -> union e_fv (e :: es)
    | Elet (lp, e1, e2) -> fv_union (e_fv e1) (fv_diff (e_fv e2) (lp_fv lp))
    | Etuple es         -> union e_fv es
    | Eif (e1, e2, e3)  -> union e_fv [e1; e2; e3]
    | Ematch (e, es, _) -> union e_fv (e :: es)
    | Equant (_, b, e)  -> List.fold_left (fun s (id, _) -> Mid.remove id s) (e_fv e) b
    | Eproj (e, _)      -> e_fv e

  let tag n e =
    let fv = fv_union (fv_node e.e_node) e.e_ty.ty_fv in
      { e with e_tag = n; e_fv = fv; }
end)

(* -------------------------------------------------------------------- *)
let mk_expr e ty =
  Hexpr.hashcons { e_node = e; e_tag = -1; e_fv = Mid.empty; e_ty = ty }

(* -------------------------------------------------------------------- *)
let mhr    = EcIdent.create "&hr"
let mleft  = EcIdent.create "&1"
let mright = EcIdent.create "&2"

module Hsform = Why3.Hashcons.Make (struct
  type t = form

  let equal_node f1 f2 =
    match f1, f2 with
    | Fquant(q1,b1,f1), Fquant(q2,b2,f2) ->
        qt_equal q1 q2 && b_equal b1 b2 && f_equal f1 f2

    | Fif(b1,t1,f1), Fif(b2,t2,f2) ->
        f_equal b1 b2 && f_equal t1 t2 && f_equal f1 f2

    | Fmatch(b1,es1,ty1), Fmatch(b2,es2,ty2) ->
           List.all2 f_equal (b1::es1) (b2::es2)
        && ty_equal ty1 ty2

    | Flet(lp1,e1,f1), Flet(lp2,e2,f2) ->
        lp_equal lp1 lp2 && f_equal e1 e2 && f_equal f1 f2

    | Fint i1, Fint i2 ->
        BI.equal i1 i2

    | Flocal id1, Flocal id2 ->
        EcIdent.id_equal id1 id2

    | Fpvar(pv1,s1), Fpvar(pv2,s2) ->
        EcIdent.id_equal s1 s2 && pv_equal pv1 pv2

    | Fglob(ff1,m1), Fglob(ff2,m2) ->
      ff_equal ff1 ff2 && EcIdent.id_equal m1 m2

    | Fop(p1,lty1), Fop(p2,lty2) ->
        EcPath.p_equal p1 p2 && List.all2 ty_equal lty1 lty2

    | Fapp(f1,args1), Fapp(f2,args2) ->
        f_equal f1 f2 && List.all2 f_equal args1 args2

    | Ftuple args1, Ftuple args2 ->
        List.all2 f_equal args1 args2

    | Fproj(f1,i1), Fproj(f2,i2) ->
      i1 = i2 && f_equal f1 f2

    | FhoareF  hf1 , FhoareF  hf2  -> hf_equal hf1 hf2
    | FhoareS  hs1 , FhoareS  hs2  -> hs_equal hs1 hs2
    | FeHoareF  hf1 , FeHoareF  hf2  -> ehf_equal hf1 hf2
    | FeHoareS  hs1 , FeHoareS  hs2  -> ehs_equal hs1 hs2
    | FbdHoareF   bhf1, FbdHoareF   bhf2 -> bhf_equal bhf1 bhf2
    | FbdHoareS   bhs1, FbdHoareS   bhs2 -> bhs_equal bhs1 bhs2
    | FequivF     eqf1, FequivF     eqf2 -> eqf_equal eqf1 eqf2
    | FequivS     eqs1, FequivS     eqs2 -> eqs_equal eqs1 eqs2
    | FeagerF     eg1 , FeagerF     eg2  -> egf_equal eg1 eg2
    | Fpr         pr1 , Fpr         pr2  -> pr_equal pr1 pr2

    | _, _ -> false

  let equal f1 f2 =
       ty_equal f1.f_ty f2.f_ty
    && equal_node f1.f_node f2.f_node

  let hash f =
    match f.f_node with
    | Fquant(q, b, f) ->
        Why3.Hashcons.combine2 (f_hash f) (b_hash b) (qt_hash q)

    | Fif(b, t, f) ->
        Why3.Hashcons.combine2 (f_hash b) (f_hash t) (f_hash f)

    | Fmatch (f, fs, ty) ->
        Why3.Hashcons.combine_list f_hash
          (Why3.Hashcons.combine (f_hash f) (ty_hash ty))
          fs

    | Flet(lp, e, f) ->
        Why3.Hashcons.combine2 (lp_hash lp) (f_hash e) (f_hash f)

    | Fint i -> Hashtbl.hash i

    | Flocal id -> EcIdent.tag id

    | Fpvar(pv, m) ->
        Why3.Hashcons.combine (pv_hash pv) (EcIdent.id_hash m)

    | Fglob(ff, m) ->
        Why3.Hashcons.combine (ff_hash ff) (EcIdent.id_hash m)

    | Fop(p, lty) ->
        Why3.Hashcons.combine_list ty_hash (EcPath.p_hash p) lty

    | Fapp(f, args) ->
        Why3.Hashcons.combine_list f_hash (f_hash f) args

    | Ftuple args ->
        Why3.Hashcons.combine_list f_hash 0 args
    | Fproj(f,i) ->
        Why3.Hashcons.combine (f_hash f) i

    | FhoareF     hf   -> hf_hash hf
    | FhoareS     hs   -> hs_hash hs
    | FeHoareF    hf   -> ehf_hash hf
    | FeHoareS    hs   -> ehs_hash hs
    | FbdHoareF   bhf  -> bhf_hash bhf
    | FbdHoareS   bhs  -> bhs_hash bhs
    | FequivF     ef   -> ef_hash ef
    | FequivS     es   -> es_hash es
    | FeagerF     eg   -> eg_hash eg
    | Fpr         pr   -> pr_hash pr

  let fv_mlr = Sid.add mleft (Sid.singleton mright)

  let fv_node f =
    let union ex nodes =
      List.fold_left (fun s a -> fv_union s (ex a)) Mid.empty nodes
    in

    match f with
    | Fint _              -> Mid.empty
    | Fop (_, tys)        -> union (fun a -> a.ty_fv) tys
    | Fpvar (PVglob pv,m) -> EcPath.x_fv (fv_add m Mid.empty) pv
    | Fpvar (PVloc _,m)   -> fv_add m Mid.empty
    | Fglob (ff,m)        -> fv_add m (ff_fv ff)
    | Flocal id           -> fv_singleton id
    | Fapp (f, args)      -> union f_fv (f :: args)
    | Ftuple args         -> union f_fv args
    | Fproj(e, _)         -> f_fv e
    | Fif (f1, f2, f3)    -> union f_fv [f1; f2; f3]
    | Fmatch (b, fs, ty)  -> fv_union ty.ty_fv (union f_fv (b :: fs))

    | Fquant(_, b, f) ->
      let do1 (id, ty) fv = fv_union (gty_fv ty) (Mid.remove id fv) in
      List.fold_right do1 b (f_fv f)

    | Flet(lp, f1, f2) ->
      let fv2 = fv_diff (f_fv f2) (lp_fv lp) in
      fv_union (f_fv f1) fv2

    | FhoareF hf ->
      let fv = fv_union (f_fv hf.hf_pr) (f_fv hf.hf_po) in
      EcPath.x_fv (Mid.remove mhr fv) hf.hf_f

    | FhoareS hs ->
      let fv = fv_union (f_fv hs.hs_pr) (f_fv hs.hs_po) in
      fv_union (s_fv hs.hs_s) (Mid.remove (fst hs.hs_m) fv)

    | FeHoareF hf ->
      let fv = fv_union (f_fv hf.ehf_pr) (f_fv hf.ehf_po) in
      EcPath.x_fv (Mid.remove mhr fv) hf.ehf_f

    | FeHoareS hs ->
      let fv = fv_union (f_fv hs.ehs_pr) (f_fv hs.ehs_po) in
      fv_union (s_fv hs.ehs_s) (Mid.remove (fst hs.ehs_m) fv)

    | FbdHoareF bhf ->
      let fv =
        fv_union (f_fv bhf.bhf_pr)
          (fv_union (f_fv bhf.bhf_po) (f_fv bhf.bhf_bd)) in
      EcPath.x_fv (Mid.remove mhr fv) bhf.bhf_f

    | FbdHoareS bhs ->
      let fv =
        fv_union (f_fv bhs.bhs_pr)
          (fv_union (f_fv bhs.bhs_po) (f_fv bhs.bhs_bd)) in
      fv_union (s_fv bhs.bhs_s) (Mid.remove (fst bhs.bhs_m) fv)

    | FequivF ef ->
        let fv = fv_union (ec_fv ef.ef_pr) (ec_fv ef.ef_po) in
        let fv = fv_diff fv fv_mlr in
        EcPath.x_fv (EcPath.x_fv fv ef.ef_fl) ef.ef_fr

    | FequivS es ->
        let fv = fv_union (ec_fv es.es_pr) (ec_fv es.es_po) in
        let ml, mr = fst es.es_ml, fst es.es_mr in
        let fv = fv_diff fv (Sid.add ml (Sid.singleton mr)) in
        fv_union fv
          (fv_union (s_fv es.es_sl) (s_fv es.es_sr))

    | FeagerF eg ->
        let fv = fv_union (f_fv eg.eg_pr) (f_fv eg.eg_po) in
        let fv = fv_diff fv fv_mlr in
        let fv = EcPath.x_fv (EcPath.x_fv fv eg.eg_fl) eg.eg_fr in
        fv_union fv
          (fv_union (s_fv eg.eg_sl) (s_fv eg.eg_sr))

    | Fpr pr ->
        let fve = Mid.remove mhr (f_fv pr.pr_event) in
        let fv  = EcPath.x_fv fve pr.pr_fun in
        fv_union (f_fv pr.pr_args) (fv_add pr.pr_mem fv)

  let tag n f =
    let fv = fv_union (fv_node f.f_node) f.f_ty.ty_fv in
      { f with f_tag = n; f_fv = fv; }
end)

let mk_form node ty =
  let aout =
    Hsform.hashcons
      { f_node = node;
        f_ty   = ty;
        f_fv   = Mid.empty;
        f_tag  = -1; }
  in assert (ty_equal ty aout.f_ty); aout

(* -------------------------------------------------------------------- *)
module Hinstr = Why3.Hashcons.Make (struct
  type t = instr

  let equal_node i1 i2 =
    match i1, i2 with
    | Squantum (qr1, o1, e1), Squantum (qr2, o2, e2) ->
        (qr_equal qr1 qr2) && (qo_equal o1 o2) && (e_equal e1 e2)

    | Smeasure(lv1, qr1, e1), Smeasure(lv2, qr2, e2) ->
        (lv_equal lv1 lv2) && (qr_equal qr1 qr2) && (e_equal e1 e2)

    | Sasgn (lv1, e1), Sasgn (lv2, e2) ->
        (lv_equal lv1 lv2) && (e_equal e1 e2)

    | Srnd (lv1, e1), Srnd (lv2, e2) ->
        (lv_equal lv1 lv2) && (e_equal e1 e2)

    | Scall (lv1, f1, es1, q1), Scall (lv2, f2, es2, q2) ->
           (EcUtils.opt_equal lv_equal lv1 lv2)
        && (EcPath.x_equal f1 f2)
        && (List.all2 e_equal es1 es2)
        && (qr_equal q1 q2)

    | Sif (c1, s1, r1), Sif (c2, s2, r2) ->
           (e_equal c1 c2)
        && (s_equal s1 s2)
        && (s_equal r1 r2)

    | Swhile (c1, s1), Swhile (c2, s2) ->
           (e_equal c1 c2)
        && (s_equal s1 s2)

    | Smatch (e1, b1), Smatch (e2, b2) when List.length b1 = List.length b2 ->
        let forb (bs1, s1) (bs2, s2) =
          let forbs (x1, ty1) (x2, ty2) =
               EcIdent.id_equal x1  x2
            && ty_equal ty1 ty2
          in List.all2 forbs bs1 bs2 && s_equal s1 s2
        in e_equal e1 e2 && List.all2 forb b1 b2

    | Sassert e1, Sassert e2 ->
        (e_equal e1 e2)

    | Sabstract id1, Sabstract id2 -> EcIdent.id_equal id1 id2

    | _, _ -> false

  let equal i1 i2 = equal_node i1.i_node i2.i_node

  let hash p =
    match p.i_node with
    | Squantum(q, o, e) ->
        Why3.Hashcons.combine2 (qr_hash q) (qo_hash o) (e_hash e)

    | Smeasure(lv, q, e) ->
        Why3.Hashcons.combine2 (Hashtbl.hash lv) (qr_hash q) (e_hash e)

    | Sasgn (lv, e) ->
        Why3.Hashcons.combine
          (lv_hash lv) (e_hash e)

    | Srnd (lv, e) ->
        Why3.Hashcons.combine
          (lv_hash lv) (e_hash e)

    | Scall (lv, f, arg, qarg) ->
        Why3.Hashcons.combine_list e_hash
          (Why3.Hashcons.combine2
             (Hashtbl.hash lv) (EcPath.x_hash f) (qr_hash qarg))
          arg

    | Sif (c, s1, s2) ->
        Why3.Hashcons.combine2
          (e_hash c) (s_hash s1) (s_hash s2)

    | Swhile (c, s) ->
        Why3.Hashcons.combine (e_hash c) (s_hash s)

    | Smatch (e, b) ->
        let forb (bds, s) =
          let forbs (x, ty) =
            Why3.Hashcons.combine (EcIdent.id_hash x) (ty_hash ty)
          in Why3.Hashcons.combine_list forbs (s_hash s) bds
        in Why3.Hashcons.combine_list forb (e_hash e) b

    | Sassert e -> e_hash e

    | Sabstract id -> EcIdent.id_hash id

  let i_fv = function
    | Squantum(qr, qo, e) ->
        EcIdent.fv_unions [qr_fv qr; qo_fv qo; e_fv e]

    | Smeasure(lv, qr, e) ->
        EcIdent.fv_unions [lv_fv lv; qr_fv qr; e_fv e]

    | Sasgn (lv, e) ->
        EcIdent.fv_union (lv_fv lv) (e_fv e)

    | Srnd (lv, e) ->
        EcIdent.fv_union (lv_fv lv) (e_fv e)

    | Scall (olv, f, args, qarg) ->
        let ffv = EcPath.x_fv Mid.empty f in
        let ofv = olv |> omap lv_fv |> odfl Mid.empty in
        let qfv = qr_fv qarg in
        List.fold_left
          (fun s a -> EcIdent.fv_union s (e_fv a))
          (EcIdent.fv_unions [ffv; ofv; qfv]) args

    | Sif (e, s1, s2) ->
        List.fold_left EcIdent.fv_union Mid.empty
          [e_fv e; s_fv s1; s_fv s2]

    | Swhile (e, s)  ->
        EcIdent.fv_union (e_fv e) (s_fv s)

    | Smatch (e, b) ->
        let forb (bs, s) =
          let bs = Sid.of_list (List.map fst bs) in
          EcIdent.fv_diff (s_fv s) bs

        in List.fold_left
             (fun s b -> EcIdent.fv_union s (forb b))
             (e_fv e) b

    | Sassert e    ->
        e_fv e

    | Sabstract id ->
        EcIdent.fv_singleton id

  let tag n p = { p with i_tag = n; i_fv = i_fv p.i_node }
end)

let mk_instr i = Hinstr.hashcons
  { i_node = i; i_tag = -1; i_fv = Mid.empty }

(* -------------------------------------------------------------------- *)
module Hstmt = Why3.Hashcons.Make (struct
  type t = stmt

  let equal_node s1 s2 =
    List.all2 i_equal s1 s2

  let equal s1 s2 = equal_node s1.s_node s2.s_node

  let hash p =
    Why3.Hashcons.combine_list i_hash 0 p.s_node

  let tag n p =
    let fv =
      List.fold_left
        (fun s i -> EcIdent.fv_union s (i_fv i))
        Mid.empty p.s_node
    in { p with s_tag = n; s_fv = fv; }
end)

let stmt s = Hstmt.hashcons
  { s_node = s; s_tag = -1; s_fv = Mid.empty}
