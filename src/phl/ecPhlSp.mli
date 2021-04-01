(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal.FApi
open EcEnv
open EcFol
open EcModules

(* -------------------------------------------------------------------- *)
val sp_stmt_free : env -> form -> stmt -> bool

(* -------------------------------------------------------------------- *)
val t_sp : (codepos1 doption) option -> backward
