(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcPath
open EcFol
open EcTyping

(* -------------------------------------------------------------------- *)

type pattern = (ptnmap * EcUnify.unienv) * form

type search = [
  | `ByName    of string
  | `ByPath    of Sp.t
  | `ByPattern of pattern
  | `ByOr      of search list
]

type context = EcPath.path

val search : EcEnv.env -> context list -> search list -> (path * EcDecl.axiom) list
val sort : Sp.t -> (path * EcDecl.axiom) list -> (path * EcDecl.axiom) list
