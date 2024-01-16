(* -------------------------------------------------------------------- *)
open EcUid
open EcPath
open EcSymbols
open EcMaps
open EcTypes
open EcDecl

(* -------------------------------------------------------------------- *)
exception UnificationFailure of [`TyUni of ty * ty | `TcCtt of ty * typeclass]
exception UninstanciateUni

type unienv

type tvar_inst =
| TVIunamed of ty list
| TVInamed  of (EcSymbols.symbol * ty) list

type tvi = tvar_inst option
type uidmap = uid -> ty option

module UniEnv : sig
  val create     : (EcIdent.t * typeclass list) list option -> unienv
  val copy       : unienv -> unienv                 (* constant time *)
  val restore    : dst:unienv -> src:unienv -> unit (* constant time *)
  val fresh      : ?tcs:typeclass list -> ?ty:ty -> unienv -> ty
  val getnamed   : unienv -> symbol -> EcIdent.t
  val repr       : unienv -> ty -> ty
  val opentvi    : unienv -> ty_params -> tvi -> ty EcIdent.Mid.t
  val openty     : unienv -> ty_params -> tvi -> ty -> ty * (ty * typeclass list) list
  val opentys    : unienv -> ty_params -> tvi -> ty list -> ty list * (ty * typeclass list) list
  val closed     : unienv -> bool
  val close      : unienv -> ty Muid.t
  val assubst    : unienv -> ty Muid.t
  val tparams    : unienv -> ty_params
end

val unify : EcEnv.env -> unienv -> ty -> ty -> unit

val hastc : EcEnv.env -> unienv -> ty -> typeclass -> ((path * ty list) Mstr.t) option option

val tfun_expected : unienv -> EcTypes.ty list -> EcTypes.ty

type sbody = ((EcIdent.t * ty) list * expr) Lazy.t

val select_op :
     ?hidden:bool
  -> ?filter:(EcPath.path -> operator -> bool)
  -> tvi
  -> EcEnv.env
  -> qsymbol
  -> unienv
  -> dom
  -> ((EcPath.path * ty list) * ty * unienv * sbody option) list
