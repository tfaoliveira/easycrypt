(* -------------------------------------------------------------------- *)
open EcSymbols
open EcBigInt
open EcPath
open EcMaps
open EcIdent
open EcTypes
open EcCoreModules
open EcMemory

(* -------------------------------------------------------------------- *)
type cp = EcIdent.t * symbol

val cp_hash : cp -> int
val cp_equal : cp -> cp -> bool

module Mcp : EcMaps.Map.S with type key = cp

(* -------------------------------------------------------------------- *)
val mhr    : memory
val mleft  : memory
val mright : memory

(* -------------------------------------------------------------------- *)
type quantif =
  | Lforall
  | Lexists
  | Llambda

type hoarecmp = FHle | FHeq | FHge

(* projection of a cost record or module cost record *)
type cost_proj =
  | Intr  of symbol               (* procedure *)
  | Param of {
      proc    : symbol;           (* procedure *)
      param_m : symbol;           (* parameter module *)
      param_p : symbol;           (* parameter procedure *)
    }

val cost_proj_equal : cost_proj -> cost_proj -> bool

(** module info *)
type mod_info =
  | Std                (* standard module *)
  | Wrap
  (* external wrapped module: execution cost belongs to the implicit
     agent associated to the module *)

(* TODO: cost: since abstract modules can be used as agent names,
   substitution need to be updated accordingly *)

(* TODO: cost: epoch need to be done correctly *)

(* -------------------------------------------------------------------- *)
type gty =
  | GTty    of EcTypes.ty
  | GTmodty of mod_info * module_type
  | GTmem   of EcMemory.memtype

and binding  = (EcIdent.t * gty)
and bindings = binding list

and form = private {
  f_node : f_node;
  f_ty   : ty;
  f_fv   : int Mid.t;
  f_tag  : int;
}

and f_node =
  | Fquant  of quantif * bindings * form
  | Fif     of form * form * form
  | Fmatch  of form * form list * ty
  | Flet    of lpattern * form * form
  | Fint    of zint
  | Flocal  of EcIdent.t
  | Fpvar   of EcTypes.prog_var * memory
  | Fglob   of mpath * memory
  | Fop     of path * ty list
  | Fapp    of form * form list
  | Ftuple  of form list
  | Fproj   of form * int

  | Fcost      of cost
  | Fmodcost   of mod_cost
  | Fcost_proj of form * cost_proj
  (* [Fmodcost_proj mod_cost p] projects [mod_cost] over
     procedure [proc] and [p]. *)

  | FhoareF of sHoareF (* $hr / $hr *)
  | FhoareS of sHoareS

  | FcHoareF of cHoareF (* $hr / $hr *)
  | FcHoareS of cHoareS

  | FbdHoareF of bdHoareF (* $hr / $hr *)
  | FbdHoareS of bdHoareS (* $hr  / $hr   *)

  | FequivF of equivF (* $left,$right / $left,$right *)
  | FequivS of equivS (* $left,$right / $left,$right *)

  | FeagerF of eagerF

  | Fcoe of coe

  | Fpr of pr (* hr *)

and eagerF = {
  eg_pr : form;
  eg_sl : stmt;  (* No local program variables *)
  eg_fl : xpath;
  eg_fr : xpath;
  eg_sr : stmt;  (* No local program variables *)
  eg_po : form
}

and equivF = {
  ef_pr : form;
  ef_fl : xpath;
  ef_fr : xpath;
  ef_po : form;
}

and equivS = {
  es_ml : EcMemory.memenv;
  es_mr : EcMemory.memenv;
  es_pr : form;
  es_sl : stmt;
  es_sr : stmt;
  es_po : form;
}

and sHoareF = {
  hf_pr : form;
  hf_f  : EcPath.xpath;
  hf_po : form;
}

and sHoareS = {
  hs_m  : EcMemory.memenv;
  hs_pr : form;
  hs_s  : stmt;
  hs_po : form;
}

and cHoareF = {
  chf_pr : form;
  chf_f  : EcPath.xpath;
  chf_po : form;
  chf_co : form; (* type `cost` *)
}

and cHoareS = {
  chs_m  : EcMemory.memenv;
  chs_pr : form;
  chs_s  : stmt;
  chs_po : form;
  chs_co : form; (* type `cost` *)
}

and bdHoareF = {
  bhf_pr  : form;
  bhf_f   : xpath;
  bhf_po  : form;
  bhf_cmp : hoarecmp;
  bhf_bd  : form;
}

and bdHoareS = {
  bhs_m   : EcMemory.memenv;
  bhs_pr  : form;
  bhs_s   : stmt;
  bhs_po  : form;
  bhs_cmp : hoarecmp;
  bhs_bd  : form;
}

and coe = {
  coe_pre : form;
  coe_mem : EcMemory.memenv;
  coe_e   : expr;
}

and pr = {
  pr_mem   : memory;
  pr_fun   : xpath;
  pr_args  : form;
  pr_event : form;
}

(* A cost record, used in both CHoares and in procedure cost restrictions.
   Keys of [c_calls] are agent names.
   Missing entries in [c_calls] are:
   - any number of times in if [full] is [false]
   - zero times if [full] is [true] *)
and crecord = private {
  c_self  : form;              (* type [txint] for [cost],
                                  type [tcost] for [proc_cost] *)
  c_calls : form Mcp.t;        (* type [xint] *)
  c_full  : bool;
}

and cost = crecord

(* A module procedure `F.f` cost, where `F` can be an non-applied functor.
   The cost is split between:
   - intrinsic cost [c_self], of type [tcost]
   - the number of calls [c_calls] to the parameters of `F` *)
and proc_cost = crecord

(* A module `F` cost, where `F` can be an non-applied functor.
   All declared procedures of `F` must appear. *)
and mod_cost = proc_cost EcSymbols.Msym.t

and module_type = form p_module_type

and module_sig = form p_module_sig

type mod_restr = form p_mod_restr

(* -------------------------------------------------------------------- *)
val gtty    : EcTypes.ty -> gty
val gtmodty : mod_info -> module_type -> gty
val gtmem   : EcMemory.memtype -> gty

(* -------------------------------------------------------------------- *)
val gty_equal : gty -> gty -> bool
val gty_fv    : gty -> int Mid.t

(* -------------------------------------------------------------------- *)
val mty_equal : module_type -> module_type -> bool
val mty_hash  : module_type -> int

val mr_equal : mod_restr -> mod_restr -> bool
val mr_hash  : mod_restr -> int

(* -------------------------------------------------------------------- *)
val f_equal   : form -> form -> bool
val f_compare : form -> form -> int
val f_hash    : form -> int
val f_fv      : form -> int Mid.t
val f_ty      : form -> EcTypes.ty
val f_ops     : form -> Sp.t

module Mf : Map.S with type key = form
module Sf : Set.S with module M = Map.MakeBase(Mf)
module Hf : EHashtbl.S with type key = form

(* -------------------------------------------------------------------- *)
val mk_form : f_node -> EcTypes.ty -> form
val f_node  : form -> f_node

(* -------------------------------------------------------------------- *)
(* not recursive *)
val f_map  : (EcTypes.ty -> EcTypes.ty) -> (form -> form) -> form -> form
val f_iter : (form -> unit) -> form -> unit

(* -------------------------------------------------------------------- *)
(* not recursive *)
val cost_iter : (form -> unit)     -> cost       -> unit
val cost_map  : (form -> form)     -> cost       -> cost
val cost_fold : (form -> 'a -> 'a) -> cost -> 'a -> 'a

val proc_cost_iter : (form -> unit)     -> proc_cost       -> unit
val proc_cost_map  : (form -> form)     -> proc_cost       -> proc_cost
val proc_cost_fold : (form -> 'a -> 'a) -> proc_cost -> 'a -> 'a

(* -------------------------------------------------------------------- *)
val gty_as_ty  : gty -> EcTypes.ty
val gty_as_mem : gty -> EcMemory.memtype
val gty_as_mod : gty -> mod_info * module_type

(* soft-constructors - common leaves *)
val f_local : EcIdent.t -> EcTypes.ty -> form
val f_pvar  : EcTypes.prog_var -> EcTypes.ty -> memory -> form
val f_pvarg : EcTypes.ty -> memory -> form
val f_pvloc : variable -> memory -> form
val f_glob  : mpath -> memory -> form

(* soft-constructors - common formulas constructors *)
val f_op     : path -> EcTypes.ty list -> EcTypes.ty -> form
val f_app    : form -> form list -> EcTypes.ty -> form
val f_tuple  : form list -> form
val f_proj   : form -> int -> EcTypes.ty -> form
val f_if     : form -> form -> form -> form
val f_match  : form -> form list -> EcTypes.ty -> form
val f_let    : EcTypes.lpattern -> form -> form -> form
val f_let1   : EcIdent.t -> form -> form -> form
val f_quant  : quantif -> bindings -> form -> form
val f_exists : bindings -> form -> form
val f_forall : bindings -> form -> form
val f_lambda : bindings -> form -> form

val f_forall_mems : (EcIdent.t * memtype) list -> form -> form

(* soft-constructors - cost hoare *)
val cost_r   : form -> form Mcp.t -> bool -> cost
val f_cost_r : cost -> form

val proc_cost_r : form -> form Mcp.t -> bool -> proc_cost

val f_mod_cost_r : mod_cost -> form

val f_cost_proj_r : form -> cost_proj -> form

(* soft-constructors - hoare *)
val f_hoareF_r : sHoareF -> form
val f_hoareS_r : sHoareS -> form

val f_hoareF : form -> xpath -> form -> form
val f_hoareS : memenv -> form -> stmt -> form -> form

val f_cHoareF_r : cHoareF -> form
val f_cHoareS_r : cHoareS -> form

val f_cHoareF : form -> xpath -> form -> form -> form
val f_cHoareS : memenv -> form -> stmt -> form -> form -> form

(* soft-constructors - bd hoare *)
val hoarecmp_opp : hoarecmp -> hoarecmp

val f_bdHoareF_r : bdHoareF -> form
val f_bdHoareS_r : bdHoareS -> form

val f_bdHoareF : form -> xpath -> form -> hoarecmp -> form -> form
val f_bdHoareS : memenv -> form -> stmt -> form -> hoarecmp -> form -> form

(* soft-constructors - equiv *)
val f_equivS : memenv -> memenv -> form -> stmt -> stmt -> form -> form
val f_equivF : form -> xpath -> xpath -> form -> form

val f_equivS_r : equivS -> form
val f_equivF_r : equivF -> form

(* soft-constructors - eager *)
val f_eagerF_r : eagerF -> form
val f_eagerF   : form -> stmt -> xpath -> xpath -> stmt -> form -> form

(* soft-constructors - Coe *)
val f_coe_r : coe -> form
val f_coe   : form -> memenv -> expr -> form

(* soft-constructors - Pr *)
val f_pr_r : pr -> form
val f_pr   : memory -> xpath -> form -> form -> form

(* soft-constructors - unit *)
val f_tt : form

(* soft-constructors - bool *)
val f_bool  : bool -> form
val f_true  : form
val f_false : form

(* soft-constructors - boolean operators *)
val fop_not  : form
val fop_and  : form
val fop_anda : form
val fop_or   : form
val fop_ora  : form
val fop_imp  : form
val fop_iff  : form
val fop_eq   : EcTypes.ty -> form

val f_not   : form -> form
val f_and   : form -> form -> form
val f_ands  : form list -> form
val f_anda  : form -> form -> form
val f_andas : form list -> form
val f_or    : form -> form -> form
val f_ors   : form list -> form
val f_ora   : form -> form -> form
val f_oras  : form list -> form
val f_imp   : form -> form -> form
val f_imps  : form list -> form -> form
val f_iff   : form -> form -> form

val f_eq  : form -> form -> form
val f_eqs : form list -> form list -> form

(* soft-constructors - integers *)
val fop_int_opp : form
val fop_int_add : form
val fop_int_pow : form

val f_i0  : form
val f_i1  : form
val f_im1 : form

val f_int       : zint -> form
val f_int_add   : form -> form -> form
val f_int_sub   : form -> form -> form
val f_int_opp   : form -> form
val f_int_mul   : form -> form -> form
val f_int_pow   : form -> form -> form
val f_int_edivz : form -> form -> form
val f_int_max   : form -> form -> form

(* -------------------------------------------------------------------- *)
val fop_cost_opp    : form
val fop_cost_add    : form
val fop_cost_scale  : form
val fop_cost_xscale : form
val fop_cost_le     : form
val fop_cost_lt     : form

val f_cost_zero    : form
val f_cost_inf     : form
val f_cost_inf0    : form
val f_cost_opp     : form -> form
val f_cost_add     : form -> form -> form
val f_cost_scale   : form -> form -> form
val f_cost_xscale  : form -> form -> form
val f_cost_le      : form -> form -> form
val f_cost_lt      : form -> form -> form
val f_cost_subcond : form -> form -> form
val f_cost_is_int  : form -> form

(* -------------------------------------------------------------------- *)
val f_bigcost : form -> form -> form -> form
val f_bigx    : form -> form -> form -> form
val f_big     : form -> form -> form -> form

val f_bigicost : form -> form -> form -> form
val f_bigix    : form -> form -> form -> form
val f_bigi     : form -> form -> form -> form

(* -------------------------------------------------------------------- *)
val f_is_inf : form -> form
val f_is_int : form -> form

val f_op_xopp  : form
val f_op_xadd  : form
val f_op_xmul  : form
val f_op_xmuli : form
val f_op_xle   : form
val f_op_xlt   : form

val f_Inf   : form
val f_N     : form -> form
val f_xopp  : form -> form
val f_xadd  : form -> form -> form
val f_xmul  : form -> form -> form
val f_xmuli : form -> form -> form
val f_xle   : form -> form -> form
val f_xlt   : form -> form -> form
val f_xmax  : form -> form -> form
val f_xoget : form -> form

val f_x0 : form
val f_x1 : form

(* -------------------------------------------------------------------- *)
val oget_c_bnd : form option -> bool -> form
val cost_add   : cost -> cost -> cost

(* -------------------------------------------------------------------- *)
val proc_cost_top : proc_cost

val mod_cost_top   : Ssym.t -> mod_cost
val mod_cost_top_r : Ssym.t -> form

(* -------------------------------------------------------------------- *)
(* Smart constructor for module types *)
val mk_mt_r :
  mt_params  : ((EcIdent.t * module_type) list) ->
  mt_name    : EcPath.path ->
  mt_args    : EcPath.mpath list ->
  mt_restr   : mod_restr ->
  module_type

(* Smart constructor for module signatures *)
val mk_msig_r :
  mis_params : (EcIdent.t * module_type) list ->
  mis_body   : module_sig_body ->
  mis_restr  : mod_restr ->
  module_sig

(* -------------------------------------------------------------------- *)
exception DestrError of string

val destr_error : string -> 'a

(* -------------------------------------------------------------------- *)
val destr_app1 : name:string -> (path -> bool) -> form -> form
val destr_app2 : name:string -> (path -> bool) -> form -> form * form

val destr_app1_eq : name:string -> path -> form -> form
val destr_app2_eq : name:string -> path -> form -> form * form

val destr_op        : form -> EcPath.path * ty list
val destr_local     : form -> EcIdent.t
val destr_pvar      : form -> prog_var * memory
val destr_proj      : form -> form * int
val destr_tuple     : form -> form list
val destr_app       : form -> form * form list
val destr_op_app    : form -> (EcPath.path * ty list) * form list
val destr_not       : form -> form
val destr_nots      : form -> bool * form
val destr_and       : form -> form * form
val destr_and3      : form -> form * form * form
val destr_and_r     : form -> [`Sym | `Asym] * (form * form)
val destr_or        : form -> form * form
val destr_or_r      : form -> [`Sym | `Asym] * (form * form)
val destr_imp       : form -> form * form
val destr_iff       : form -> form * form
val destr_eq        : form -> form * form
val destr_eq_or_iff : form -> form * form
val destr_let       : form -> lpattern * form * form
val destr_let1      : form -> EcIdent.t * ty * form * form
val destr_forall1   : form -> EcIdent.t * gty * form
val destr_forall    : form -> bindings * form
val decompose_forall: form -> bindings * form
val decompose_lambda: form -> bindings * form
val destr_lambda    : form -> bindings * form

val destr_exists1   : form -> EcIdent.t * gty * form
val destr_exists    : form -> bindings * form
val destr_equivF    : form -> equivF
val destr_equivS    : form -> equivS
val destr_eagerF    : form -> eagerF
val destr_hoareF    : form -> sHoareF
val destr_hoareS    : form -> sHoareS
val destr_cHoareF   : form -> cHoareF
val destr_cHoareS   : form -> cHoareS
val destr_bdHoareF  : form -> bdHoareF
val destr_bdHoareS  : form -> bdHoareS
val destr_coe       : form -> coe
val destr_cost      : form -> cost
val destr_modcost   : form -> mod_cost
val destr_pr        : form -> pr
val destr_programS  : [`Left | `Right] option -> form -> memenv * stmt
val destr_int       : form -> zint

val destr_glob      : form -> EcPath.mpath     * memory
val destr_pvar      : form -> EcTypes.prog_var * memory

val destr_xint : form -> [`Int of form | `Inf | `Unknown]

(* -------------------------------------------------------------------- *)
val is_true      : form -> bool
val is_false     : form -> bool
val is_inf       : form -> bool
val is_tuple     : form -> bool
val is_not       : form -> bool
val is_and       : form -> bool
val is_or        : form -> bool
val is_imp       : form -> bool
val is_iff       : form -> bool
val is_forall    : form -> bool
val is_exists    : form -> bool
val is_lambda    : form -> bool
val is_let       : form -> bool
val is_eq        : form -> bool
val is_op        : form -> bool
val is_local     : form -> bool
val is_pvar      : form -> bool
val is_proj      : form -> bool
val is_equivF    : form -> bool
val is_equivS    : form -> bool
val is_eagerF    : form -> bool
val is_hoareF    : form -> bool
val is_hoareS    : form -> bool
val is_cHoareF   : form -> bool
val is_cHoareS   : form -> bool
val is_bdHoareF  : form -> bool
val is_bdHoareS  : form -> bool
val is_coe       : form -> bool
val is_cost      : form -> bool
val is_modcost   : form -> bool
val is_pr        : form -> bool
val is_eq_or_iff : form -> bool

(* -------------------------------------------------------------------- *)
val split_fun  : form -> bindings * form
val split_args : form -> form * form list

(* -------------------------------------------------------------------- *)
val form_of_expr : EcMemory.memory -> EcTypes.expr -> form

(* -------------------------------------------------------------------- *)
exception CannotTranslate

val expr_of_form : EcMemory.memory -> form -> EcTypes.expr

(* -------------------------------------------------------------------- *)
(* A predicate on memory: λ mem. -> pred *)
type mem_pr = EcMemory.memory * form


(* -------------------------------------------------------------------- *)
type f_subst = private {
  fs_freshen  : bool; (* true means freshen locals *)
  fs_loc      : form Mid.t;
  fs_mem      : EcIdent.t Mid.t; (* memories *)
  fs_sty      : ty_subst;
  fs_ty       : ty -> ty;
  fs_opdef    : (EcIdent.t list * expr) Mp.t;
  fs_pddef    : (EcIdent.t list * form) Mp.t;
  fs_modtydef : EcPath.path Mp.t;
  fs_esloc    : expr Mid.t;
  fs_memtype  : EcMemory.memtype option; (* Only substituted in Fcoe *)
  fs_mempred  : mem_pr Mid.t;
  (* For predicates over memories, only substituted in Fcoe *)
}

(* -------------------------------------------------------------------- *)
module Fsubst : sig
  val f_subst_id  : f_subst
  val is_subst_id : f_subst -> bool

  val f_subst_init :
       ?freshen:bool
    -> ?sty:ty_subst
    -> ?opdef:(EcIdent.t list * expr) Mp.t
    -> ?prdef:(EcIdent.t list * form) Mp.t
    -> ?modtydef:path Mp.t
    -> ?esloc:expr Mid.t
    -> ?mt:EcMemory.memtype
    -> ?mempred:(mem_pr Mid.t)
    -> unit -> f_subst

  val f_bind_local   : f_subst -> EcIdent.t -> form -> f_subst
  val f_bind_mem     : f_subst -> EcIdent.t -> EcIdent.t -> f_subst
  val f_bind_agent   : f_subst -> EcIdent.t -> EcIdent.t -> f_subst
  val f_bind_rename  : f_subst -> EcIdent.t -> EcIdent.t -> ty -> f_subst

  val f_bind_mod : f_subst -> EcIdent.t -> mpath -> f_subst

  val f_subst   : ?tx:(form -> form -> form) -> f_subst -> form -> form

  val f_subst_local : EcIdent.t -> form -> form -> form
  val f_subst_mem   : EcIdent.t -> EcIdent.t -> form -> form
  val f_subst_agent : EcIdent.t -> EcIdent.t -> form -> form
  val f_subst_mod   : EcIdent.t -> mpath -> form -> form

  val uni_subst : (EcUid.uid -> ty option) -> f_subst
  val uni : (EcUid.uid -> ty option) -> form -> form
  val subst_tvar :
    ?es_loc:(EcTypes.expr EcIdent.Mid.t) ->
    EcTypes.ty EcIdent.Mid.t ->
    form -> form

  (* susbtitute agent names in a formula *)
  val subst_agents : EcIdent.t EcIdent.Mid.t -> form -> form

  val add_binding  : f_subst -> binding  -> f_subst * binding
  val add_bindings : f_subst -> bindings -> f_subst * bindings

  val subst_lpattern : f_subst -> lpattern -> f_subst * lpattern
  val subst_xpath    : f_subst -> xpath -> xpath
  val subst_stmt     : f_subst -> stmt  -> stmt
  val subst_e        : f_subst -> expr  -> expr
  val subst_me       : f_subst -> EcMemory.memenv -> EcMemory.memenv
  val subst_m        : f_subst -> EcIdent.t -> EcIdent.t
  val subst_cp       : f_subst -> cp    -> cp
  val subst_ty       : f_subst -> ty -> ty
  val subst_mty      : f_subst -> module_type -> module_type
  val subst_param    : f_subst -> oi_param -> oi_param
  val subst_params   : f_subst -> oi_params -> oi_params
  (* val subst_oi       : f_subst -> c_bnd PreOI.t -> c_bnd PreOI.t *)
  val subst_gty      : f_subst -> gty -> gty
end

(* -------------------------------------------------------------------- *)
val can_subst : form -> bool

(* -------------------------------------------------------------------- *)
type core_op = [
  | `True
  | `False
  | `Not
  | `And of [`Asym | `Sym]
  | `Or  of [`Asym | `Sym]
  | `Imp
  | `Iff
  | `Eq
]

val core_op_kind : path -> core_op option

(* -------------------------------------------------------------------- *)
val string_of_quant : quantif -> string
val string_of_hcmp  : hoarecmp -> string

val pp_cost_proj : Format.formatter -> cost_proj -> unit
val pp_mod_info  : Format.formatter -> mod_info  -> unit

(* -------------------------------------------------------------------- *)
val dump_form      : Format.formatter -> form        -> unit
val dump_modty     : Format.formatter -> module_type -> unit
val dump_modcost   : Format.formatter -> mod_cost    -> unit
val dump_proc_cost : Format.formatter -> proc_cost   -> unit

val dump_form_long      : Format.formatter -> form        -> unit
val dump_modty_long     : Format.formatter -> module_type -> unit
val dump_modcost_long   : Format.formatter -> mod_cost    -> unit
val dump_proc_cost_long : Format.formatter -> proc_cost   -> unit
