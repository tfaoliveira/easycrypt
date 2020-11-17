(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
type unit.

op tt : unit.

(* -------------------------------------------------------------------- *)
type bool.

op false : bool.
op true  : bool.

op [!]  : bool -> bool.
op (||) : bool -> bool -> bool.
op (\/) : bool -> bool -> bool.
op (&&) : bool -> bool -> bool.
op (/\) : bool -> bool -> bool.
op (=>) : bool -> bool -> bool.
op (<=>): bool -> bool -> bool.

(* -------------------------------------------------------------------- *)
op (=) ['a]: 'a -> 'a -> bool.

(* -------------------------------------------------------------------- *)
type int.

(* -------------------------------------------------------------------- *)
type real.

(* -------------------------------------------------------------------- *)
type 'a distr.

op mu: 'a distr -> ('a -> bool) -> real.

(* -------------------------------------------------------------------- *)
type mem.
type name.

op mget ['a] : mem -> name -> 'a.
op mset ['a] : mem -> name -> 'a -> mem.

axiom mget_mset_eq ['a] (m : mem) (v : 'a) (x y : name) :
  x = y => mget<:'a> (mset<:'a> m x v) y = v.

axiom mget_mset_neq ['a 'b] (m : mem) (v : 'a) (x y : name) :
  x <> y => mget<:'b> (mset m x v) y = mget m y.

hint simplify mget_mset_eq, mget_mset_neq.

(*
abbrev "_.[_]" ['a] = mget<:'a>.
abbrev "_.[_<-_]" ['a] = mset<:'a>.
*)
