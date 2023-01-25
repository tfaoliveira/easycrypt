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

(* Move this *)
op is_real (x: ereal) = exists z:real, x = z%e.

lemma is_real_notinf x : is_real x => x <> #+oo /\ x <> #-oo.
proof. by move=> [? ->]. qed.

print is_empty.

lemma is_lubP E :
  is_lub E ( 
   if ! E #+oo then
     let F = fun (x:real) => E x%e in
     if nonempty F then 
       if has_ub F then (lub F)%e
       else #+oo
     else #-oo     
   else #+oo).
proof.
case: (E #+oo) => [Eoo | NEoo] /=.
- by split => //; move=> y /(_ #+oo Eoo).
pose F (x : real) := E x%e; case: (nonempty F); last first.
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

lemma is_lub_uniq E x y : 
  is_lub E x => is_lub E y => x = y.
proof. by move=> [u1 le1] [u2 le2]; rewrite eqe_le le1 2:le2. qed.

lemma lubE E : 
  lub E = 
   if ! E #+oo then
     let F = fun (x:real) => E x%e in
     if nonempty F then 
       if has_ub F then (lub F)%e
       else #+oo
     else #-oo     
   else #+oo.
proof.
apply choiceb_uniq; 1: by apply is_lub_uniq.
apply is_lubP.
qed.

lemma lub_ind E (P: ereal -> bool) : 
  let F = fun (x:real) => E x%e in
  (!E #+oo => has_lub F => P (lub F)%e) =>
  (!E #+oo => nonempty F => !has_ub F => P #+oo) => 
  (!E #+oo => !nonempty F => P #-oo) => 
  (E #+oo => P #+oo) =>
  P (lub E).
proof.
move=> F h1 h2 h3 h4; rewrite lubE.
case: (E #+oo) => //= hE; rewrite -/F.
case: (nonempty F) => hne; 2: by apply h3.  
by case: (has_ub F) => hhas; [apply h1|apply h2].
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


