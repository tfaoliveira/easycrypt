(* -------------------------------------------------------------------- *)
require import AllCore Real StdOrder EReal RealLub.
        import RField RealOrder.

op ub (E:ereal -> bool) (x:ereal) = 
  forall y, E y => y <= x.

op is_lub (E:ereal -> bool) x =
  ub E x /\ forall y, ub E y => x <= y.

op lub (E:ereal -> bool) =
  choiceb (is_lub E) #-oo.

(* -------------------------------------------------------------------- *)
(* Basic lemmas                                                         *)

lemma ub_empty : ub pred0 = predT.
proof. done. qed.

lemma ub_top E : ub E #+oo.
(* TODO : why done does not work *)
proof. by rewrite /ub. qed.

hint simplify ub_top.

lemma is_lub_uniq E x y : 
  is_lub E x => is_lub E y => x = y.
proof.
wlog : x y / x <= y.
+ move=> h; case : (x <= y) => [/h // | + *].
  by rewrite -lteNge => /lteW /h ->.
by move=> hxy [h1 _] [_ /(_ _ h1)];rewrite eqe_le.
qed.

lemma nonempty_is_lub E : exists x, is_lub E x.
proof.
case: (E #+oo) => [Eoo | NEoo].
- by exists #+oo; split => //; move=> y /(_ #+oo Eoo).
pose F (x : real) := E x%e; case: (nonempty F); last first.
- move=> zF; exists #-oo; split => //.
  by case=> //= y; apply: contra zF => Ey; exists y.
move=> nzF; case: (has_ub F); last first.
- by move=> NubF; exists #+oo; split=> //#.
move=> ubF; exists (lub F)%e; split.
- by case=> //= y Ey; apply: lub_upper_bound.
case=> //=; last first.
- by move=> z ubEz; apply: lub_le_ub => // y /ubEz.
by case: nzF => x Fx; apply/negP => /(_ x%e Fx).
qed.

lemma lub_empty : lub pred0 = #-oo.
proof. by apply choiceb_uniq; 1: by apply is_lub_uniq. qed.

(* TODO : nonempty should be defined over any type *)
lemma nonempty_ub E : exists x, ub E x. (* nonempty (ub E) *)
proof. by exists #+oo; apply ub_top. qed.

lemma ub_lub E : ub E (lub E).
proof. 
by case: (choicebP (is_lub E) #-oo (nonempty_is_lub E)).
qed.

