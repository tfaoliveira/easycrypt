(* -------------------------------------------------------------------- *)
open EcSymbols
open EcIdent
open EcPath

module BI = EcBigInt

type memory = EcIdent.t

(* -------------------------------------------------------------------- *)
type pvar_kind =
  | PVKglob
  | PVKloc

type prog_var =
  | PVglob of EcPath.xpath
  | PVloc of EcSymbols.symbol

type equantif  = [ `ELambda | `EForall | `EExists ]

type quantif =
  | Lforall
  | Lexists
  | Llambda

(* -------------------------------------------------------------------- *)
type hoarecmp = FHle | FHeq | FHge

(* -------------------------------------------------------------------- *)
type ty = private {
  ty_node : ty_node;
  ty_fv   : int Mid.t; (* only ident appearing in path *)
  ty_tag  : int;
}

and ty_node =
  | Tmem    of memtype
  | Tunivar of EcUid.uid
  | Tvar    of EcIdent.t
  | Ttuple  of ty list
  | Tconstr of EcPath.path * ty list
  | Tfun    of ty * ty

(* -------------------------------------------------------------------- *)
(* lmt_symb :
   A map associating to a symbol is type
   furthermore for function argument we also associate the projection
   with respect to arg
   proc f (x1:t1, _: t2)
   lmt_symb[x1] -> (arg, t1*t2, Some 0), t1
   Particular case when the procedure has only one argument:
   proc f (x1:t1)
   lmt_symb[x1] -> (arg, t1, None), t1

   lmt_proj :
   It is the inverse map of lmt_symb, it is used for printing

   We can look in EcMemory for a better understanding
*)

and proj_tbl =
  | Ptbl_direct of EcSymbols.symbol
  | Ptbl_proj   of EcSymbols.symbol EcMaps.Mint.t

and local_memtype = private {
  lmt_symb : ((EcSymbols.symbol * ty * int option) option * ty) Msym.t;
  lmt_proj : proj_tbl Msym.t;
  lmt_fv   : int EcIdent.Mid.t;
  lmt_tag  : int;
}

(* The type of memory restricted to a gvar_set *)
(* [lmt = None] is for an axiom schema, and is instantiated to a concrete
   memory type when the axiom schema is.  *)
and memtype = private {
  mt_lmt : local_memtype option;
  mt_gvs : gvar_set;
  mt_fv  : int Mid.t;
  mt_tag : int;
}

and memenv = memory * memtype

(* -------------------------------------------------------------------- *)
and functor_fun = private {
  ff_params : (EcIdent.t * module_type) list;
  ff_xp     : xpath;  (* The xpath is fully applied *)
  ff_fv     : int Mid.t;
  ff_tag    : int;
}

and gvar_set_node =
  | Empty                              (* The empty memory                           *)
  | All                                (* The memory of All global                   *)
  | Set       of Sx.t                  (* The memory restricted to the variable in s *)
  | GlobFun   of functor_fun           (* The global memory used by the function     *)
  | Union     of gvar_set * gvar_set   (* Union                                      *)
  | Diff      of gvar_set * gvar_set   (* Difference                                 *)
  | Inter     of gvar_set * gvar_set   (* Intersection                               *)

and gvar_set = private {
  gvs_node : gvar_set_node;
  gvs_tag  : int;
  gvs_fv   : int EcIdent.Mid.t;
}

and var_set = private {
  lvs : Ssym.t;
  gvs : gvar_set;
  vs_tag : int;
}

(* -------------------------------------------------------------------- *)
and ovariable = {
  ov_name : EcSymbols.symbol option;
  ov_type : ty;
}

and variable = {
  v_name : EcSymbols.symbol;   (* can be "_" *)
  v_type : ty;
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

and lvalue =
  | LvVar   of (prog_var * ty)
  | LvTuple of (prog_var * ty) list

(* -------------------------------------------------------------------- *)
and instr = private {
  i_node : instr_node;
  i_fv : int Mid.t;
  i_tag  : int;
}

and instr_node =
  | Sasgn     of lvalue * expr
  | Srnd      of lvalue * expr
  | Scall     of lvalue option * EcPath.xpath * expr list
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

and oracle_info = private {
  oi_calls : xpath list;
  oi_costs : (form * form Mx.t) option;
  oi_fv    : int Mid.t;
  oi_tag   : int;
}

and module_type = private {
  mt_restr  : gvar_set;  (* The set of allowed global variables *)
  (* params are unbound in restr *)
  mt_params : (EcIdent.t * module_type) list;
  mt_name   : EcPath.path;
  mt_args   : EcPath.mpath list;
  mt_oi     : oracle_info Msym.t;
  mty_fv    : int Mid.t;
  mty_tag   : int;
}

(* -------------------------------------------------------------------- *)
and gty =
  | GTty    of ty
  | GTmodty of module_type

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

  | Fpvar   of prog_var * form        (* x{m} *)
  | Fmrestr of form * memtype         (* (m|X) *)
  | Fupdvar of form * prog_var * form (* m[x<-v] *)
  | Fupdmem of form * var_set * form  (* m[X<- m'] *)

  | Fop     of EcPath.path * ty list
  | Fapp    of form * form list
  | Ftuple  of form list
  | Fproj   of form * int

  | FhoareF of sHoareF (* $hr / $hr *)
  | FhoareS of sHoareS

  | FcHoareF of cHoareF (* $hr / $hr *)
  | FcHoareS of cHoareS

  | FbdHoareF of bdHoareF (* $hr / $hr *)
  | FbdHoareS of bdHoareS

  | FeHoareF of eHoareF (* $hr / $hr *)
  | FeHoareS of eHoareS

  | FequivF of equivF (* $left,$right / $left,$right *)
  | FequivS of equivS

  | FeagerF of eagerF

  | Fcoe of coe

  | Fpr of pr (* hr *)

and eagerF = {
  eg_pr : form;
  eg_sl : stmt;  (* No local program variables *)
  eg_fl : EcPath.xpath;
  eg_fr : EcPath.xpath;
  eg_sr : stmt;  (* No local program variables *)
  eg_po : form
}

and equivF = {
  ef_pr : form;
  ef_fl : EcPath.xpath;
  ef_fr : EcPath.xpath;
  ef_po : form;
}

and equivS = {
  es_ml  : memenv;
  es_mr  : memenv;
  es_pr  : form;
  es_sl  : stmt;
  es_sr  : stmt;
  es_po  : form; }

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

and cHoareF = {
  chf_pr : form;
  chf_f  : EcPath.xpath;
  chf_po : form;
  chf_co : cost;
}

and cHoareS = {
  chs_m  : memenv;
  chs_pr : form;
  chs_s  : stmt;
  chs_po : form;
  chs_co : cost; }

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
  pr_mem   : form;
  pr_fun   : EcPath.xpath;
  pr_args  : form;
  pr_event : form;
}

and coe = {
  coe_pre : form;
  coe_mem : memenv;
  coe_e   : expr;
}

(* Invariant: keys of c_calls are functions of local modules,
   with no arguments. *)
and cost = {
  c_self  : form;    (* of type xint *)
  c_calls : call_bound EcPath.Mx.t;
}

(* Call with cost at most [cb_cost], called at mist [cb_called].
   [cb_cost] is here to properly handle substsitution when instantiating an
   abstract module by a concrete one. *)
and call_bound = {
  cb_cost  : form;   (* of type xint *)
  cb_called : form;  (* of type int  *)
}

type 'a equality = 'a -> 'a -> bool
type 'a hash = 'a -> int
type 'a fv   = 'a -> int EcIdent.Mid.t

val ty_equal : ty equality
val ty_hash  : ty hash
val ty_fv    : ty fv

(* -------------------------------------------------------------------- *)
val v_equal : variable equality
val v_hash  : variable hash

(* -------------------------------------------------------------------- *)
val pv_equal : prog_var equality
val pv_hash  : prog_var hash
val pv_fv    : prog_var fv

val pv_kind : prog_var -> pvar_kind
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
val oi_fv    : oracle_info fv

(* -------------------------------------------------------------------- *)
val hcmp_hash : hoarecmp hash

(* -------------------------------------------------------------------- *)
val ov_equal : ovariable equality
val ov_hash  : ovariable hash

val v_equal : variable equality
val v_hash : variable hash

(* ----------------------------------------------------------------- *)
val mty_equal : module_type equality
val mty_hash  : module_type hash
val mty_fv    : module_type fv

(* ----------------------------------------------------------------- *)
val ff_equal : functor_fun equality
val ff_hash  : functor_fun hash
val ff_fv    : functor_fun fv

(*-------------------------------------------------------------------- *)
val gvs_equal : gvar_set equality
val gvs_hash  : gvar_set hash
val gvs_fv    : gvar_set fv

(*-------------------------------------------------------------------- *)
val vs_equal : var_set equality
val vs_hash  : var_set hash
val vs_fv    : var_set fv

(* -------------------------------------------------------------------- *)
val lmt_equal : local_memtype equality
val lmt_hash  : local_memtype hash
val lmt_fv    : local_memtype fv

(* -------------------------------------------------------------------- *)
val mt_equal : memtype equality
val mt_hash  : memtype hash
val mt_fv    : memtype fv

val is_schema : memtype -> bool

val mem_equal : memory equality

val me_equal : memenv equality
val me_hash  : memenv hash

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

(*-------------------------------------------------------------------- *)
val call_bound_equal : call_bound equality
val call_bound_hash  : call_bound hash

val cost_equal : cost equality
val cost_hash  : cost hash

val hf_equal  : sHoareF equality
val hf_hash   : sHoareF hash

val hs_equal  : sHoareS equality
val hs_hash   : sHoareS hash

val ehf_equal : eHoareF equality
val ehf_hash  : eHoareF hash

val ehs_equal : eHoareS equality
val ehs_hash  : eHoareS hash

val chf_equal : cHoareF equality
val chf_hash  : cHoareF hash

val chs_equal : cHoareS equality
val chs_hash  : cHoareS hash

val bhf_equal : bdHoareF equality
val bhf_hash  : bdHoareF hash

val bhs_equal : bdHoareS equality
val bhs_hash  : bdHoareS hash

val eqf_equal : equivF equality
val ef_hash   : equivF hash

val eqs_equal : equivS equality
val es_hash   : equivS hash

val egf_equal : eagerF equality
val eg_hash   : eagerF hash

val coe_equal : coe equality
val coe_hash  : coe hash

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

val mk_lmt :
  ((EcSymbols.symbol * ty * int option) option * ty) Msym.t ->
  proj_tbl Msym.t ->
  local_memtype

val mk_mt : local_memtype option -> gvar_set -> memtype

val mk_oi : xpath list -> (form * form Mx.t) option -> oracle_info

val mk_mty :
  gvar_set ->
  (EcIdent.t * module_type) list ->
  EcPath.path ->
  EcPath.mpath list ->
  oracle_info Msym.t ->
  module_type

val mk_ff : (memory * module_type) list -> xpath -> functor_fun

val mk_gvs: gvar_set_node -> gvar_set
val mk_vs : Ssym.t -> gvar_set -> var_set

val mk_expr : expr_node -> ty -> expr
val mk_form : f_node -> ty -> form
val mk_instr : instr_node -> instr
val stmt : instr list -> stmt
