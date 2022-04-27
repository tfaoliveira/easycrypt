require import CoreXint Int.

(* -------------------------------------------------------------------- *)
op zero : cost.

(* FIXME: remove after generalized expressions *)
axiom zero_def : zero = `[: N 0].

hint simplify zero_def.

(* -------------------------------------------------------------------- *)
(* scalar mutliplication *)

op scale : int -> cost -> cost.
op xscale (x : xint) (c : cost) =
  with x = N x => scale x c
  with x = Inf => inf.

(* -------------------------------------------------------------------- *)
(* Point-wise lifting of some [xint] operators.
   Since these cost operators must be defined abstractly, we
   add axioms lifting the (proven) properties of [xint] operators. *)

op add : cost -> cost -> cost.
op opp : cost -> cost.

op lt : cost -> cost -> bool.
op le = fun x y => lt x y \/ x = y.

abbrev ([-]) = opp.
abbrev ( + ) = add.
abbrev ( - ) (x : cost) (y : cost) = add x (-y).
abbrev ( *  ) = scale.
abbrev ( ** ) = xscale.
abbrev ( <= ) = le.
abbrev ( <  ) = lt.

(* -------------------------------------------------------------------- *)
(* sufficient condition to do backward reasoning over costs. *)
op subcond = fun x y => (x - y) + y = x.

(* -------------------------------------------------------------------- *)
(* axioms for scalar multiplication *)

axiom scale0c (x : cost) : 0 * x = zero.
axiom scale1c (x : cost) : 1 * x = x.

hint simplify scale0c, scale1c.

(* lifting [CHoareTactic.xscale_distri] *)
(* not that this does not hold for negative scaling, taking [j = -i]. *)
axiom scale_distri (i j : int) (x : cost) : 
  0 <= i => 0 <= j => (i + j) * x = i * x + j * x.

(* lifting [CHoareTactic.xscale_distrc] *)
axiom scale_distrc (i : int) (x y : cost) : 
  i * (x + y) = i * x + i * y.

axiom scale_comp (i j : int) (x : cost) : 
  i * (j * x) = (i * j) * x.

(* -------------------------------------------------------------------- *)
(* axioms for addition *)
(* lifted from lemmas in [CHoareTactic] *)

axiom add0c (x : cost) : zero + x = x.
axiom addc0 (x : cost) : x + zero = x.

axiom addinfc (x : cost) : inf + x = inf. 
axiom addcinf (x : cost) : x + inf = inf.

hint simplify add0c, addc0, addinfc, addinfc.

axiom addcA : associative add.

axiom addcC : commutative add.

(* -------------------------------------------------------------------- *)
(* ordering axioms *)
(* lifted from lemmas in [CHoareTactic] *)

axiom lecx : reflexive (<=).

lemma lecx_rw (x y : cost) : x = y => x <= y.
proof. by move=> ->; apply lecx. qed.

hint simplify lecx_rw.

axiom lec_anti (x y : cost) : x <= y <= x => x = y.

axiom lec_trans : transitive (<=).

axiom lec_inf (x : cost) : x <= inf.
hint simplify lec_inf.

lemma lec_inf0 (x : cost) : x <= `[: .., ..].
proof. rewrite -inf_def; exact lec_inf. qed.
hint exact : lec_inf0.

axiom lec_add2r (x1 x2 y : cost) :
  x1 <= x2 => x1 + y <= x2 + y.

lemma lec_add2l (x1 x2 y : cost) :
  x1 <= x2 => y + x1 <= y + x2.
proof. by rewrite !(@addcC y) &(lec_add2r). qed.

(* -------------------------------------------------------------------- *)
(* lifted from lemmas in [CHoareTactic] *)

(* This axiom can be used to prove the side-conditions of our rules 
   for seq, wp ... *)
axiom subrcle (x y : cost) : y <= x => subcond x y.

axiom lec_add_posr (x y : cost) :
  zero <= x => y <= y + x.

lemma lec_add_posl (x y : cost) :
  zero <= x => y <= x + y.
proof. rewrite (addcC x); exact lec_add_posr. qed.
