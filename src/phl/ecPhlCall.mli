(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcParsetree
open EcFol
open EcCoreGoal.FApi

(* -------------------------------------------------------------------- *)
(* As [EcCHoare.cost_sub], but raises error messages if the equation
   cannot be solved. *)
val tc1_cost_sub : EcCoreGoal.tcenv1 -> cost -> cost -> form * cost

(* -------------------------------------------------------------------- *)
val wp2_call :
     EcEnv.env -> form -> form
  -> EcModules.lvalue option * EcPath.xpath * EcTypes.expr list
  -> EcPV.PV.t
  -> EcModules.lvalue option * EcPath.xpath * EcTypes.expr list
  -> EcPV.PV.t
  -> EcMemory.memory -> EcMemory.memory -> form
  -> EcEnv.LDecl.hyps -> form

val t_hoare_call   : form -> form -> backward
val t_bdhoare_call : form -> form -> form option -> backward
val t_equiv_call   : form -> form -> backward
val t_equiv_call1  : side -> form -> form -> backward
val t_call         : oside -> form -> backward

(* -------------------------------------------------------------------- *)
val process_call : oside -> call_info gppterm -> backward
