(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcAst
open EcFol
open EcCoreGoal

(* -------------------------------------------------------------------- *)
(* FIXME: add t_low* to all these tactics                               *)

type conseq_tac = form -> form -> FApi.backward
type qconseq_tac =
  form -> ?qepr:quantum_equality ->
  form -> ?qepo:quantum_equality ->
  FApi.backward

type qconseq_core_tac = equiv_cond -> equiv_cond -> FApi.backward

(* -------------------------------------------------------------------- *)
val t_equivS_conseq_core  : ?witheq:bool -> qconseq_core_tac

val t_equivF_conseq       : qconseq_tac
val t_equivS_conseq       : qconseq_tac
val t_eagerF_conseq       : conseq_tac
val t_hoareF_conseq       : conseq_tac
val t_hoareS_conseq       : conseq_tac
val t_cHoareF_conseq      : conseq_tac
val t_cHoareS_conseq      : conseq_tac
val t_bdHoareF_conseq     : conseq_tac
val t_bdHoareS_conseq     : conseq_tac

val t_cHoareF_conseq_c    : cost -> FApi.backward
val t_cHoareS_conseq_c    : cost -> FApi.backward
val t_cHoareF_conseq_full : form -> form -> cost -> FApi.backward
val t_cHoareS_conseq_full : form -> form -> cost -> FApi.backward
val t_ehoareF_conseq      : conseq_tac
val t_ehoareS_conseq      : conseq_tac
val t_bdHoareS_conseq_bd  : hoarecmp -> form -> FApi.backward
val t_bdHoareF_conseq_bd  : hoarecmp -> form -> FApi.backward

(* -------------------------------------------------------------------- *)
val t_equivF_conseq_nm    : qconseq_tac
val t_equivS_conseq_nm    : qconseq_tac
val t_hoareF_conseq_nm    : conseq_tac
val t_hoareS_conseq_nm    : conseq_tac
val t_cHoareF_conseq_nm   : conseq_tac
val t_cHoareS_conseq_nm   : conseq_tac
val t_bdHoareF_conseq_nm  : conseq_tac
val t_bdHoareS_conseq_nm  : conseq_tac

(* -------------------------------------------------------------------- *)
val t_ehoareS_concave : form -> conseq_tac
val t_ehoareF_concave : form -> conseq_tac
val t_concave_incr : FApi.backward

(* -------------------------------------------------------------------- *)
val t_equivS_conseq_bd : side -> EcFol.form -> EcFol.form ->FApi.backward

(* -------------------------------------------------------------------- *)
val t_conseq : conseq_tac


(* -------------------------------------------------------------------- *)
val process_conseq   : bool -> conseq_ppterm option tuple3 -> FApi.backward
val process_bd_equiv : side -> pformula pair -> FApi.backward

(* -------------------------------------------------------------------- *)
val process_conseq_opt :
  pcqoptions -> conseq_ppterm option tuple3 -> FApi.backward

(* -------------------------------------------------------------------- *)
val t_conseqauto : ?delta:bool -> ?tsolve:FApi.backward -> FApi.backward

val process_concave : pformula option tuple2 gppterm * pformula -> FApi.backward
