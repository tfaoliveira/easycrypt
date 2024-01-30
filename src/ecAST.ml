open EcUtils
open EcSymbols
open EcIdent
open EcPath
open EcUid

module BI = EcBigInt

(* -------------------------------------------------------------------- *)

type locality  = [`Local | `Declare | `Global]
type is_local  = [`Local | `Global]

(* -------------------------------------------------------------------- *)
type pvar_kind =
  | PVKglob
  | PVKloc

type prog_var =
  | PVglob of EcPath.xpath
  | PVloc of EcSymbols.symbol

(* -------------------------------------------------------------------- *)
type uses = {
  us_calls  : Sx.t;
  us_reads  : Sx.t;
  us_writes : Sx.t;
}

(* -------------------------------------------------------------------- *)
type quantif =
  | Lforall
  | Lexists
  | Llambda

type equantif  = [ `ELambda | `EForall | `EExists ]

(* -------------------------------------------------------------------- *)
type hoarecmp = FHle | FHeq | FHge

(* -------------------------------------------------------------------- *)
type memory = EcIdent.t

(* -------------------------------------------------------------------- *)
type functor_fun = {
  ff_params : (EcIdent.t * module_type) list;
  ff_xp : xpath;  (* The xpath is fully applied *)
}

and gvar_set_node =
  | Empty                              (* The empty memory                           *)
  | All                                (* The memory of All global                   *)
  | Set       of Sx.t                  (* The memory restricted to the variable in s *)
  | GlobFun   of functor_fun           (* The global memory used by the function     *)
  | Union     of gvar_set * gvar_set   (* Union                                      *)
  | Diff      of gvar_set * gvar_set   (* Difference                                 *)
  | Inter     of gvar_set * gvar_set   (* Intersection                               *)

and gvar_set =
  { gvs_node : gvar_set_node;
    gvs_tag  : int;
    gvs_fv   : int EcIdent.Mid.t;
  }

and var_set = {
  lvs : Ssym.t;
  gvs : gvar_set;
}

and ty = {
  ty_node : ty_node;
  ty_fv   : int EcIdent.Mid.t; (* only ident appearing in path *)
  ty_tag  : int;
}

and ty_node =
  | Tmem    of memtype
  | Tunivar of EcUid.uid
  | Tvar    of EcIdent.t
  | Ttuple  of ty list
  | Tconstr of EcPath.path * ty list
  | Tfun    of ty * ty

and local_memtype =
  { lmt_symb : ((EcSymbols.symbol * ty * int) option * ty) Msym.t;
    lmt_proj : EcSymbols.symbol EcMaps.Mint.t Msym.t;
    lmt_fv   : int EcIdent.Mid.t;
    lmt_tag  : int;
  }

(* The type of memory restricted to a gvar_set *)
(* [lmt = None] is for an axiom schema, and is instantiated to a concrete
   memory type when the axiom schema is.  *)
and memtype = {
  lmt : local_memtype option;
  gvs : gvar_set;
  mt_fv : int EcIdent.Mid.t;
  mt_tag : int;
}

and memenv = memory * memtype

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

and lvalue =
  | LvVar   of (prog_var * ty)
  | LvTuple of (prog_var * ty) list

and instr = {
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

and stmt = {
  s_node : instr list;
  s_fv   : int Mid.t;
  s_tag  : int;
}

and oracle_info = {
  oi_calls : xpath list;
  oi_costs : (form * form Mx.t) option;
}

and mod_restr = {
  mr_mem    : gvar_set;  (* The set of allowed global variables *)
  mr_oinfos : oracle_info Msym.t;
}

and module_type = {
  mt_params : (EcIdent.t * module_type) list;
  mt_name   : EcPath.path;
  mt_args   : EcPath.mpath list;
  mt_restr  : mod_restr;
}

(* ----------------------------------------------------------------- *)
and gty =
  | GTty    of ty
  | GTmodty of module_type

and binding  = (EcIdent.t * gty)
and bindings = binding list

and form = {
  f_node : f_node;
  f_ty   : ty;
  f_fv   : int EcIdent.Mid.t; (* local, memory, module ident *)
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
  pr_mem   : form; (* a memory *)
  pr_fun   : EcPath.xpath;
  pr_args  : form;
  pr_event : form;
}

and coe = {
  coe_pre : form;
  coe_mem : EcMemory.memenv;
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



(* This can be moved to ecCoreModules *)

(* -------------------------------------------------------------------- *)
(* Simple module signature, without restrictions. *)

type funsig = {
  fs_name   : symbol;
  fs_arg    : ty;
  fs_anames : ovariable list;
  fs_ret    : ty;
}

type module_sig_body_item = Tys_function of funsig

and module_sig_body = module_sig_body_item list

and module_sig = {
  mis_params : (EcIdent.t * module_type) list;
  mis_body   : module_sig_body;
  mis_restr  : mod_restr;
}

type top_module_sig = {
  tms_sig  : module_sig;
  tms_loca : is_local;
}

and module_smpl_sig = {
  miss_params : (EcIdent.t * module_type) list;
  miss_body   : module_sig_body;
}

and function_def = {
  f_locals : variable list;
  f_body   : stmt;
  f_ret    : expr option;
  f_uses   : uses;
}

and function_body =
  | FBdef   of function_def
  | FBalias of xpath
  | FBabs   of oracle_info


and function_ = {
  f_name   : symbol;
  f_sig    : funsig;
  f_def    : function_body;
}

and module_expr = {
  me_name     : symbol;
  me_body     : module_body;
  me_comps    : module_comps;
  me_sig_body : module_sig_body;
  me_params   : (EcIdent.t * module_type) list;
}

(* Invariant:
   In an abstract module [ME_Decl mt], [mt] must not be a functor, i.e. it must
   be fully applied. Therefore, we must have:
   [List.length mp.mt_params = List.length mp.mt_args]  *)
and module_body =
  | ME_Alias       of int * EcPath.mpath
  | ME_Structure   of module_structure       (* Concrete modules. *)
  | ME_Decl        of module_type            (* Abstract modules. *)

and module_structure = {
  ms_body      : module_item list;
}

and module_item =
  | MI_Module   of module_expr
  | MI_Variable of variable
  | MI_Function of function_

and module_comps = module_comps_item list

and module_comps_item = module_item
