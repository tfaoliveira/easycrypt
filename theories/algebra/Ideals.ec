(* -------------------------------------------------------------------- *)
require import AllCore Ring.
require (*--*) Quotient.

pragma +implicits.

(* ==================================================================== *)
abstract theory Ideals.
(* -------------------------------------------------------------------- *)
type t.

clone import Ring.IDomain as Ring with type t <- t.

(* -------------------------------------------------------------------- *)
op ideal (p : t -> bool) =
     (p zeror /\ (forall x y, p x => p y => p (x - y)))
  /\ (forall a x, p x => p (a * x)).

(* -------------------------------------------------------------------- *)
lemma ideal0 (p : t -> bool) : ideal p => p zeror.
proof. by case=> [[]]. qed.

lemma idealN (p : t -> bool) x : ideal p => p x => p (-x).
proof.
by move=> ^ip [[_ +] _] px - /(_ _ _ (ideal0 p ip) px); rewrite sub0r.
qed.

lemma idealD (p : t -> bool) x y : ideal p => p x => p y => p (x + y).
proof.
move=> ip px py; have pNy := idealN p y ip py.
by case: ip => [[_ +] _] - /(_ _ _ px pNy); rewrite opprK.
qed.

lemma ideapM (p : t -> bool) a x : ideal p => p x => p (a * x).
proof. by case=> _; apply. qed.

(* -------------------------------------------------------------------- *)
op idealp (g : t) = fun x => exists a, x = a * g.

lemma ideal_idealp g : ideal (idealp g).
proof. split; first split.
+ by exists zeror; rewrite mul0r.
+ by move=> x y [ax ->] [ay ->]; rewrite -mulrBl; exists (ax - ay).
+ by move=> a x [ax ->]; rewrite mulrA; exists (a * ax).
qed.
end Ideals.

(* ==================================================================== *)
abstract theory RingQuotient.
clone Ideals as ID.

import ID.Ring.

op I : { ID.t -> bool | ID.ideal I } as idI.

hint exact : idI.

op eqv (x y : ID.t) = I (x - y).

lemma eqv_refl : reflexive eqv.
proof. by move=> x @/eqv; rewrite subrr &(ID.ideal0) &(idI). qed.

lemma eqv_sym : symmetric eqv.
proof.
have sym: forall (x y : ID.t), I (x - y) => I (y - x).
+ by move=> x y /(ID.idealN _ _ idI); rewrite opprB.
by move=> x y @/eqv; apply/eq_iff; split=> /sym.
qed.

lemma eqv_trans : transitive eqv.
proof.
move=> y x z @/eqv pxz pzy; have := ID.idealD _ _ _ idI pxz pzy.
by rewrite addrA -(@addrA _ _ y) addNr addr0.
qed.

type t.

clone Quotient.Equiv with
  type T  <- ID.t, op eqv <- eqv
  proof *.

realize eqv_refl  by apply: eqv_refl.
realize eqv_sym   by move=> x y; rewrite eqv_sym.
realize eqv_trans by apply: eqv_trans.
end RingQuotient.
