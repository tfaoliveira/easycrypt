require import AllCore Distr RealExp RealSeries Ring StdRing StdOrder DList.
require import StdBigop.
import RField RealOrder RealLub Bigreal List.

abbrev expr = RealExp.exp.

abbrev minus (E:real -> 'a) = (E \o fun x  => 0%r - x).

op glb (E : real -> bool) = - lub (minus E).

op lb (E : real -> bool) (z : real) =
  forall y, E y => y >= z.

op has_lb  (E : real -> bool) = nonempty (lb E).
op has_glb (E : real -> bool) = nonempty E /\ has_lb E.

lemma has_lb_ub E : has_lb E <=> has_ub (minus E).
proof.
rewrite /has_lb /has_ub.
split;rewrite /lb /ub /(\o).
+ rewrite /nonempty=> [[]] x lbx. 
+ exists (-x).
+ move=> y //=.
+ rewrite ler_oppr.
+ smt().
move=>//=.
rewrite /nonempty=> [[]] x ubx.
exists (-x).
move => //=.
smt().
qed.

lemma nonempty_minus E : nonempty (minus E) = nonempty E.
proof.
smt().
qed.

lemma has_glb_lub E : has_glb E <=> has_lub (minus E).
proof.
by rewrite /has_glb /has_lub has_lb_ub nonempty_minus.
qed.

lemma glb_upper_bound (E : real -> bool) : has_glb E =>
  forall x, E x => x >= glb E.
proof.
rewrite has_glb_lub=> lub_minusE x Ex.
by rewrite /glb ler_oppl;apply lub_upper_bound.
qed.

lemma glb_adherent (E : real -> bool): has_glb E =>
  forall eps, 0%r < eps => exists e, E e /\ glb E + eps > e.
proof.
rewrite has_glb_lub => /lub_adherent eps_adherent eps /eps_adherent.
move=> [e]; rewrite /(\o); move=> [] E_me;rewrite /lub=> lub_me.
by exists (-e); split=> //=; rewrite ltr_oppl; smt().
qed.

op image (f : 'a  -> 'b) x = exists t, x = f t.

lemma image_image (f : real -> real) (g : real -> real) x :
    image g x => image (f \o g) (f x).
rewrite /image. smt().
qed.

lemma lub_min E : nonempty E => (exists m, forall x, E x => m >= x) => has_lub E.
move => nonempty_E [m] Hm.
rewrite /has_lub; split=> //=; rewrite /has_ub.
by exists m.
qed.

lemma glb_max E : nonempty E => (exists m, forall x, E x => m <= x) => has_glb E.
proof.
move => nonemptyE [m] Hm;rewrite /has_glb;split=> //=.
rewrite /has_lb.
by exists m.
qed.

lemma glb_expr (f: real -> real) : has_glb (image (expr \o f)).
rewrite /has_glb; split=>//=.
+ rewrite /nonempty.
+ exists (expr (f 0%r)). by rewrite /expr_b; exists 0%r.
rewrite/has_lb /nonempty.
exists 0%r.
rewrite /lb /expr_b=> y [] t ->.
by apply exp_ge0.
qed.

op inf P (f : real -> real) : real =  glb (fun x => ((image f x) && P x)).
op sup P (f : real -> real) : real =  lub (fun x => ((image f x) && P x)).
(*op sup P E : real = lub (fun x => E x && P x).*)

(*lemma inf_opp E P : inf P E = - sup (minus P) (minus E).
proof.
rewrite /inf /sup; smt().
qed.*)

lemma image_minus (f : real -> real) : image f =
    minus (image (fun x => - (f x))).
proof.
rewrite /image /minus /(\o) => //=;smt().
qed.

lemma inf_opp f P : inf P f = - sup (minus P) (fun x => - (f x)).
proof.
rewrite /inf /sup /glb /(\o) => //=.
by rewrite image_minus.
qed.

lemma incfun_inf f (g : real -> real) P : (forall x y, x >= y => f x >= f y) =>
    inf P (f \o g) = f (inf P g).
move => incf.
rewrite /inf.

admitted.

theory Chernoff.

op d : real distr.
(*abbrev phi t x = expr (t * x)%Real.*)
abbrev phi t = E d (fun x => expr (t * x)%Real).
axiom de : forall t, hasE d (fun x => expr (t * x)%Real).

(*lemma Chernoff1 (a : real) (t : real) : a >= 0%r => t >= 0%r =>
    mu d (fun x => x >= a) <= (expr ( -t * a)) * E d (phi t).
proof.
move=> ge0_a ge0_t; rewrite -expZ exp_mu; apply ler_exp_pos => /=.
apply hasEZ; first by apply de.
move=> x; rewrite b2r_ge0 /(\o) /=; case : (a <= x); last first.
+ move=> _; rewrite -expD; apply exp_ge0.
move=> le_ax; rewrite -expD -exp0 exp_mono.
smt().
qed.*)

lemma Chernoff1 (a : real) (t : real) : a >= 0%r => t >= 0%r =>
    mu d (fun x => x >= a) <= (expr ( -t * a)) * phi t.
proof.
move=> ge0_a ge0_t; rewrite -expZ exp_mu; apply ler_exp_pos => /=.
apply hasEZ; first by apply de.
move=> x; rewrite b2r_ge0 /(\o) /=; case : (a <= x); last first.
+ move=> _; rewrite -expD; apply exp_ge0.
move=> le_ax; rewrite -expD -exp0 exp_mono.
smt().
qed.
(*lemma Chernoff2 (a : real) (t : real) : a <= 0%r => t <= 0%r =>
    mu d (fun x => x <= a) <= (expr ( -t * a)) * E d (phi t).
proof.
move=> le0_a le0_t; rewrite -expZ exp_mu; apply ler_exp_pos => /=.
apply hasEZ; first by apply de.
move=> x; rewrite b2r_ge0 /(\o) /=; case : (x <= a); last first.
+ move=> _; rewrite -expD; apply exp_ge0.
move=> le_xa; rewrite -expD -exp0 exp_mono.
smt().
qed.*)

lemma Chernoff2 (a : real) (t : real) : a <= 0%r => t <= 0%r =>
    mu d (fun x => x <= a) <= (expr ( -t * a)) * phi t.
proof.
move=> le0_a le0_t; rewrite -expZ exp_mu; apply ler_exp_pos => /=.
apply hasEZ; first by apply de.
move=> x; rewrite b2r_ge0 /(\o) /=; case : (x <= a); last first.
+ move=> _; rewrite -expD; apply exp_ge0.
move=> le_xa; rewrite -expD -exp0 exp_mono.
smt().
qed.

op h (a : real) = sup (fun t => t >= 0%r) (fun t => t * a - ln (phi t)).

lemma Chernoff_inf1 (a : real) : a >= 0%r =>
    mu d (fun x => x <= a) <= expr (- h a).
proof.
move => ge0_a.
have: expr (- h a) = inf (fun t => t >= 0%r)
(fun t => expr (- (t * a - ln (phi t)))).

rewrite /h.
admitted.
end Chernoff.

theory Additive_Chernoff.

op clamp (r:real) = minr 1%r (maxr 0%r r).

op mBernoulli p = fun x => (b2r (x = 0%r)) * (clamp p) +
                          (b2r (x = 1%r)) * (1%r - (clamp p)).

op Bernoulli p = Distr.mk (mBernoulli p).
(* prouver que son esperance est p, ...*)

op n : int.
op p : real.

axiom gt0_n : 0 < n.
axiom rg01_p : 0%r <= p <= 1%r.

op X = dlist (Bernoulli p) n.

op e : real.
axiom gt0_e : e > 0%r.

lemma AddChernoff1 : mu X (fun vs => BRA.big predT idfun vs >=
                      n%r * (p + e)) <= expr (-2%r * (e^2) * n%r).
proof.
admitted.

end Additive_Chernoff.
