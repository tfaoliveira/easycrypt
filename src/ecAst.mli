(* -------------------------------------------------------------------- *)
open EcSymbols
open EcIdent
open EcPath

module BI = EcBigInt

type memory = EcIdent.t

(* -------------------------------------------------------------------- *)
type quantum = [`Quantum | `Classical]

val pp_quantum : quantum -> string

(* -------------------------------------------------------------------- *)
type quantum_op =
  | Qinit
  | Qunitary

val qo_equal : quantum_op -> quantum_op -> bool
val qo_hash : quantum_op -> int
val qo_fv : quantum_op -> int Mid.t

(* -------------------------------------------------------------------- *)
type pvar_kind =
  | PVKglob
  | PVKloc of quantum

type equantif  = [ `ELambda | `EForall | `EExists ]

type quantif =
  | Lforall
  | Lexists
  | Llambda

(* -------------------------------------------------------------------- *)
type hoarecmp = FHle | FHeq | FHge

(* -------------------------------------------------------------------- *)
type global = quantum * EcPath.xpath
module Mglob : EcMaps.Map.S with type key = global

module Sglob : EcMaps.Set.S with type M.key = global

(* -------------------------------------------------------------------- *)
type ty = private {
  ty_node : ty_node;
  ty_fv   : int Mid.t; (* only ident appearing in path *)
  ty_tag  : int;
}

and ty_node =
  | Tglob   of EcIdent.t (* The tuple of global variable of the module *)
  | Tunivar of EcUid.uid
  | Tvar    of EcIdent.t
  | Ttuple  of ty list
  | Tconstr of EcPath.path * ty list
  | Tfun    of ty * ty

(* -------------------------------------------------------------------- *)
and ovariable = {
  ov_quantum : quantum;
  ov_name    : EcSymbols.symbol option;
  ov_type    : ty;
}

and variable = {
  v_quantum : quantum;
  v_name    : EcSymbols.symbol;   (* can be "_" *)
  v_type    : ty;
}

and lpattern =
  | LSymbol of (EcIdent.t * ty)
  | LTuple  of (EcIdent.t * ty) list
  | LRecord of EcPath.path * (EcIdent.t option * ty) list

and expr = private {
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
and instr = private {
  i_node : instr_node;
  i_fv : int Mid.t;
  i_tag  : int;
}

and instr_node =
  | Squantum  of quantum_ref * quantum_op * expr
  | Smeasure  of lvalue * quantum_ref * expr
  | Sasgn     of lvalue * expr
  | Srnd      of lvalue * expr
  | Scall     of lvalue option * EcPath.xpath * expr list * quantum_ref
  | Sif       of expr * stmt * stmt
  | Swhile    of expr * stmt
  | Smatch    of expr * ((EcIdent.t * ty) list * stmt) list
  | Sassert   of expr
  | Sabstract of EcIdent.t

and stmt = private {
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
  | GlobFun of functor_fun   (* Global of a function *)
  | Union   of mem_restr * mem_restr
  | Inter   of mem_restr * mem_restr
  | Diff    of mem_restr * mem_restr

and mod_restr = {
  mr_mem    : mem_restr;
  mr_oinfos : oracle_info Msym.t;
}

(* FIXME this is not clear, does the mem_restr can depend on params.
   I think not *)
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

and form = private {
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
  | Fglob   of EcIdent.t * memory
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

type 'a equality = 'a -> 'a -> bool
type 'a hash = 'a -> int
type 'a fv   = 'a -> int EcIdent.Mid.t

val ty_equal : ty equality
val ty_hash  : ty hash
val ty_fv    : ty fv

(* -------------------------------------------------------------------- *)
val ov_quantum : ovariable -> quantum
val ov_name    : ovariable -> symbol option
val ov_type    : ovariable -> ty
val ov_equal   : ovariable equality
val ov_hash    : ovariable hash

(* -------------------------------------------------------------------- *)
val v_quantum : variable -> quantum
val v_name    : variable -> symbol
val v_type    : variable -> ty
val v_equal   : variable equality
val v_hash    : variable hash

(* -------------------------------------------------------------------- *)
val ovar_of_var: variable -> ovariable

(* -------------------------------------------------------------------- *)
val pv_equal : prog_var equality
val pv_hash  : prog_var hash
val pv_fv    : prog_var fv

val pv_kind : prog_var -> pvar_kind

(* -------------------------------------------------------------------- *)
val pv_loc  : quantum * string -> prog_var
val pv_cloc : string -> prog_var
val pv_qloc : string -> prog_var
val pv_var  : variable -> prog_var
val pv_ovar : ovariable -> prog_var

(* -------------------------------------------------------------------- *)
val idty_equal : (EcIdent.t * ty) equality
val idty_hash  : (EcIdent.t * ty) hash

val lp_equal : lpattern equality
val lp_hash  : lpattern hash
val lp_fv    : lpattern -> EcIdent.Sid.t

(* -------------------------------------------------------------------- *)
val e_equal : expr equality
val e_hash  : expr hash
val e_fv    : expr fv

(* -------------------------------------------------------------------- *)
val eqt_equal : equantif equality
val eqt_hash  : equantif hash

(* -------------------------------------------------------------------- *)
val lv_equal : lvalue equality
val lv_fv    : lvalue fv
val lv_hash  : lvalue hash

(* -------------------------------------------------------------------- *)
val i_equal : instr equality
val i_hash  : instr hash
val i_fv    : instr fv

val s_equal : stmt equality
val s_hash  : stmt hash
val s_fv    : stmt fv

(*-------------------------------------------------------------------- *)
val qt_equal : quantif equality
val qt_hash  : quantif hash

(*-------------------------------------------------------------------- *)
val f_equal : form equality
val f_hash  : form hash
val f_fv    : form fv

(* -------------------------------------------------------------------- *)
val oi_equal : oracle_info equality
val oi_hash  : oracle_info hash

(* -------------------------------------------------------------------- *)
val hcmp_hash : hoarecmp hash

(* -------------------------------------------------------------------- *)
val ov_equal : ovariable equality
val ov_hash  : ovariable hash

val v_equal : variable equality
val v_hash : variable hash

(* -------------------------------------------------------------------- *)
val g_equal : global equality

(* -------------------------------------------------------------------- *)

val mr_equal : mod_restr equality
val mr_fv    : mod_restr fv

val mty_equal : module_type equality
val mty_hash  : module_type hash
val mty_fv    : module_type fv

(* -------------------------------------------------------------------- *)
val lmt_equal : ty equality -> local_memtype equality
val lmt_hash : local_memtype hash

val mt_equal_gen : ty equality -> memtype equality
val mt_equal : memtype equality
val mt_fv : memtype fv

val mt_iter_ty : (ty -> unit) -> memtype -> unit

val mem_equal : memory equality

val me_equal_gen : ty equality -> memenv equality
val me_equal : memenv equality
val me_hash : memenv hash

(*-------------------------------------------------------------------- *)
val gty_equal : gty equality
val gty_hash  : gty hash
val gty_fv    : gty fv

(*-------------------------------------------------------------------- *)

val b_equal : bindings equality
val b_hash : bindings hash

(* -------------------------------------------------------------------- *)
val i_equal   : instr equality
val i_hash    : instr hash
val i_fv      : instr fv

val s_equal   : stmt equality
val s_hash    : stmt hash
val s_fv      : stmt fv

(* -------------------------------------------------------------------- *)
val qe_equal : quantum_equality -> quantum_equality -> bool
val qe_hash  : quantum_equality -> int
val qe_fv    : quantum_equality -> int Mid.t

val qe_empty : quantum_equality
val is_qe_empty : quantum_equality -> bool

val qe_iter : (prog_var_ty -> unit) -> quantum_equality -> unit
val qe_map  : (prog_var_ty -> prog_var_ty) -> quantum_equality -> quantum_equality
val qe_all  : (prog_var_ty -> bool) -> quantum_equality -> bool
val qe_all2 : (prog_var_ty -> prog_var_ty -> bool) -> quantum_equality -> quantum_equality -> bool

(* -------------------------------------------------------------------- *)
val quantum_unit : quantum_ref
val is_quantum_unit : quantum_ref -> bool

val qr_equal : quantum_ref -> quantum_ref -> bool
val qr_hash  : quantum_ref -> int
val qr_fv    : quantum_ref -> int Mid.t

val qr_pvloc : variable -> quantum_ref
val qr_pvlocs : variable list -> quantum_ref

val qr_iter : (prog_var_ty -> unit) -> quantum_ref -> unit
val qr_map  : (prog_var_ty -> prog_var_ty) -> quantum_ref -> quantum_ref
val qr_fold : ('a -> prog_var_ty -> 'a) -> 'a -> quantum_ref -> 'a
val qr_all  : (prog_var_ty -> bool) -> quantum_ref -> bool
val qr_all2 : (prog_var_ty -> prog_var_ty -> bool) -> quantum_ref -> quantum_ref -> bool

val qrvar   : prog_var_ty -> quantum_ref
val qrtuple : quantum_ref list -> quantum_ref
val qrproj  : quantum_ref * int -> quantum_ref

(*-------------------------------------------------------------------- *)
val hf_equal  : sHoareF equality
val hf_hash   : sHoareF hash

val hs_equal  : sHoareS equality
val hs_hash   : sHoareS hash

val ehf_equal : eHoareF equality
val ehf_hash  : eHoareF hash

val ehs_equal : eHoareS equality
val ehs_hash  : eHoareS hash

val bhf_equal : bdHoareF equality
val bhf_hash  : bdHoareF hash

val bhs_equal : bdHoareS equality
val bhs_hash  : bdHoareS hash

val eqf_equal : qequivF equality
val ef_hash   : qequivF hash

val eqs_equal : qequivS equality
val es_hash   : qequivS hash

val egf_equal : eagerF equality
val eg_hash   : eagerF hash

val pr_equal  : pr equality
val pr_hash   : pr hash

(* ----------------------------------------------------------------- *)
(* Predefined memories                                               *)
(* ----------------------------------------------------------------- *)

val mhr    : memory
val mleft  : memory
val mright : memory

(* ----------------------------------------------------------------- *)
(* Hashconsing                                                       *)
(* ----------------------------------------------------------------- *)

val mk_ty : ty_node -> ty
val mk_expr : expr_node -> ty -> expr
val mk_form : f_node -> ty -> form
val mk_instr : instr_node -> instr
val stmt : instr list -> stmt
