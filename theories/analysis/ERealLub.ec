(* -------------------------------------------------------------------- *)
require import AllCore Real StdOrder EReal RealLub.
        import RField RealOrder.

op ub (E:ereal -> bool) (x:ereal) = 
  forall y, E y => y <= x.

op is_lub (E:ereal -> bool) x =
  ub E x /\ forall y, ub E y => x <= y.

op lub (E:ereal -> bool) =
  choiceb (is_lub E) #-oo.

op etrunc (E : ereal -> 'a) (x : real) : 'a = 
  E x%e.

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
proof. by move=> [u1 le1] [u2 le2]; rewrite eqe_le le1 2:le2. qed.

lemma is_lubP E :
  is_lub E ( 
   if ! E #+oo then
     if nonempty (etrunc E) then 
       if has_ub (etrunc E) then (lub (etrunc E))%e
       else #+oo
     else #-oo     
   else #+oo).
proof.
case: (E #+oo) => [Eoo | NEoo] /=.
- by split => //; move=> y /(_ #+oo Eoo).
pose F := etrunc E; case: (nonempty F); last first.
- move=> zF; split => //.
  by case=> //= y; apply: contra zF => Ey; exists y.
move=> nzF; case: (has_ub F); last first.
- by move=> NubF; split => //#.
move=> ubF; split.
- by case=> //= y Ey; apply: lub_upper_bound.
case=> //=; last first.
- by move=> z ubEz; apply: lub_le_ub => // y /ubEz.
by case: nzF => x Fx; apply/negP => /(_ x%e Fx).
qed.

lemma lubE E : 
  lub E = 
   if ! E #+oo then
     if nonempty (etrunc E) then 
       if has_ub (etrunc E) then (lub (etrunc E))%e
       else #+oo
     else #-oo     
   else #+oo.
proof.
apply choiceb_uniq; 1: by apply is_lub_uniq.
apply is_lubP.
qed.

lemma lub_ind E (P: ereal -> bool) : 
  (!E #+oo => has_lub (etrunc E) => P (lub (etrunc E))%e) =>
  (!E #+oo => nonempty (etrunc E) => !has_ub (etrunc E) => P #+oo) => 
  (!E #+oo => !nonempty (etrunc E) => P #-oo) => 
  (E #+oo => P #+oo) =>
  P (lub E).
proof.
move=> h1 h2 h3 h4; rewrite lubE.
case: (E #+oo) => //= hE.
case: (nonempty (etrunc E)) => hne; 2: by apply h3.  
by case: (has_ub (etrunc E)) => hhas; [apply h1|apply h2].
qed.

lemma nonempty_is_lub E : exists x, is_lub E x.
proof. exists (lub E); rewrite lubE is_lubP. qed.

lemma lub_empty : lub pred0 = #-oo.
proof. by apply choiceb_uniq; 1: by apply is_lub_uniq. qed.

(* TODO : nonempty should be defined over any type *)
lemma nonempty_ub E : exists x, ub E x. (* nonempty (ub E) *)
proof. by exists #+oo; apply ub_top. qed.

lemma ub_lub E : ub E (lub E).
proof. 
by case: (choicebP (is_lub E) #-oo (nonempty_is_lub E)).
qed.


