(* -------------------------------------------------------------------- *)
require import AllCore Real StdOrder EReal.
        import RField RealOrder.

op ub (E:ereal -> bool) (x:ereal) = 
  forall y, E y => y <= x.

lemma ub_empty : ub pred0 = predT.
proof. done. qed.

op is_lub (E:ereal -> bool) x =
  ub E x /\ forall y, ub E y => x <= y.

(* TODO Move to EReal. *)
lemma eqe_le (x y : ereal): x = y <=> x <= y <= x.
proof.
  split=> [-> // | ].
admitted.

lemma lee_bot x : #-oo <= x.
proof. by case x. qed.
hint simplify lee_bot.

lemma lee_top x : x <= #+oo.
proof. by case x. qed.
hint simplify lee_top.
 
lemma is_lub_uniq E x y : 
  is_lub E x => is_lub E y => x = y.
proof.
wlog : x y / x <= y.
+ move=> h; case : (x <= y) => [/h // | + *].
  by rewrite -lteNge => /lteW /h ->.
by move=> hxy [h1 _] [_ /(_ _ h1)];rewrite eqe_le.
qed.

lemma nonempty_is_lub E : exists x, is_lub E x.
rewrite /is_lub.
admitted.

op lub (E:ereal -> bool) =
  choiceb (is_lub E) #-oo.

(* TODO : move this *)
lemma choiceb_uniq x (P: 'a -> bool) dfl :
  (forall z1 z2, P z1 => P z2 => z1 = z2) =>
  P x => 
  choiceb P dfl = x.
proof.
by move=> hu hx; have /hu /(_ _ hx) // := choicebP P dfl _; exists x.
qed.

lemma lub_empty : lub pred0 = #-oo.
proof. by apply choiceb_uniq; 1: by apply is_lub_uniq. qed.

lemma ub_top E : ub E #+oo.
(* TODO : why done does not work *)
proof. by rewrite /ub. qed.

(* TODO : nonempty should be defined over any type *)
lemma nonempty_ub E : exists x, ub E x. (* nonempty (ub E) *)
proof. exists #+oo; apply ub_top. qed.

(*
lemma ub_lub E : ub E (lub E).
proof. 
search choiceb.

 have := choicebP (is_lub E).
  no
forall x, ub E x => lub E <= x.

*)


  
