require import AllCore Distr RealExp RealSeries Ring StdRing StdOrder.
import RField RealOrder.
  
op d : real distr.
abbrev expr = RealExp.exp.
abbrev phi t x = expr (t * x)%Real.
axiom de : forall t, hasE d (phi t).

lemma Chernoff1 (a : real) (t : real) : a >= 0%r => t >= 0%r =>
    mu d (fun x => x >= a) <= (expr ( -t * a)) * E d (phi t).
proof.
move=> ge0_a ge0_t; rewrite -expZ exp_mu; apply ler_exp_pos => /=.
apply hasEZ; first by apply de.
move=> x; rewrite b2r_ge0 /(\o) /=; case : (a <= x); last first.
+ move=> _; rewrite -expD; apply exp_ge0.
move=> le_ax; rewrite -expD -exp0 exp_mono.
smt().
qed.


lemma Chernoff2 (a : real) (t : real) : a <= 0%r => t <= 0%r =>
    mu d (fun x => x <= a) <= (expr ( -t * a)) * E d (phi t).
proof.
move=> le0_a le0_t; rewrite -expZ exp_mu; apply ler_exp_pos => /=.
apply hasEZ; first by apply de.
move=> x; rewrite b2r_ge0 /(\o) /=; case : (x <= a); last first.
+ move=> _; rewrite -expD; apply exp_ge0.
move=> le_xa; rewrite -expD -exp0 exp_mono.
smt().
qed.
