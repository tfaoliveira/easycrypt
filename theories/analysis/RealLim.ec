(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import AllCore Real StdRing StdOrder RealLub RealExp.
(*---*) import RField RealOrder.

pragma +implicits.
pragma -oldip.

(* -------------------------------------------------------------------- *)
type 'a set = 'a -> bool.

abbrev (\union) ['a] (p1 p2 : 'a -> bool) = predU p1 p2.
abbrev (\inter) ['a] (p1 p2 : 'a -> bool) = predI p1 p2.

abbrev (+) (f1 f2 : real -> real) =
  fun x => f1 x + f2 x.

inductive filter (E : real set set) =
| Filter of
     (E predT) & (!E pred0)
  & (forall p1 p2, E p1 => p1 <= p2 => E p2)
  & (forall p1 p2, E p1 => E p2 => E (p1 \inter p2)).

op image (f : real -> real) (E : real set) =
  fun y => exists x, E x /\ f x = y.

op preimage (f : real -> real) (E : real set) =
  fun x => E (f x).

op fimage (f : real -> real) (E : real set set) =
  fun p => E (preimage f p).

op isnbh (a : real) (p : real set) =
  exists e, 0%r < e /\ forall x, `|a - x| < e => p x.

pred fcvg (a : real) (p : real set set) =
  filter p /\ p <= isnbh a.

pred flim (l : real) (f : real -> real) (p : real set set) =
  fcvg l (fimage f p).

pred nlim (l : real) (f : real -> real) (x : real) =
  flim l f (isnbh x).

(* -------------------------------------------------------------------- *)
lemma filter_isnbh a : filter (isnbh a).
proof. split.
- by exists 1%r.
- by apply/negP; case=> e [gt0_e /(_ a)].
- move=> p1 p2 [e] [gt0_e nbh_p1] le_p1p2.
  by exists e; split=> // x /nbh_p1; apply: le_p1p2.
- move=> p1 p2 [e1 [gt0_e1 nbh_p1]] [e2 [gt0_e2 nbh_p2]].
  by exists (minr e1 e2) => /#.
qed.

(* -------------------------------------------------------------------- *)
lemma filter_fimage f p : filter p => filter (fimage f p).
proof.
case=> p1 Np0 le_p pI; split=> //.
- move=> q1 q2 f_p_q1 le_q1q2; apply: (le_p (fun x => q1 (f x))) => //.
  by move=> x; apply: le_q1q2.
- by move=> q1 q2 f_p_q1 f_p_q2; apply: pI.
qed.

(* -------------------------------------------------------------------- *)
lemma limP l f x : nlim l f x =>
  forall e, 0%r < e => exists a, forall y, `|x - y| < a => `|f x - f y| < l.
proof.
move=> lim_fx e gt0_e.
admitted.

(* -------------------------------------------------------------------- *)
lemma limD l1 l2 f1 f2 x : nlim l1 f1 x => nlim l2 f2 x =>
  nlim (l1 + l2) (f1 + f2) x.
proof.
move=> lim_f1 lim_f2; split; 1: by apply/filter_fimage/filter_isnbh.
move=> p; case: lim_f1 => _ le1; case: lim_f2 => _ le2.
rewrite /fimage /preimage.
admitted.

(* -------------------------------------------------------------------- *)
op nbh (a : real) (b : bool * bool) =
  fun x => a - b2r b.`1 <= x <= a + b2r b.`2.

lemma nbh_pt (a : real) (b : bool * bool) : nbh a b a.
proof. by smt(). qed.

op limto_g b (f : real -> real) x0 l =
  forall e, 0%r < e => exists a, 0%r < a /\
    forall x, (nbh x0 b) x => `|x - x0| < a => `|f x - l| < e.

abbrev limto_up = limto_g (false,  true).
abbrev limto_dw = limto_g ( true, false).
abbrev limto    = limto_g ( true,  true).

op haslim_g b (f : real -> real) x0 =
  exists l, limto_g b f x0 l.

abbrev haslim_up = haslim_g (false,  true).
abbrev haslim_dw = haslim_g ( true, false).
abbrev haslim    = haslim_g ( true,  true).

abbrev [-printing] continuous_g b (f : real -> real) x0 =
  haslim_g b f x0.

(* -------------------------------------------------------------------- *)
op lim_g b (f : real -> real) x =
  choiceb (fun l => limto_g b f x l) 0%r.

abbrev lim = lim_g (true, true).

(* -------------------------------------------------------------------- *)
lemma limE b f x : haslim_g b f x => limto_g b f x (f x).
proof.
case=> l; case: (l = f x) => [->//|ne_l_fx].
move/(_ `|l - f x| _); first by rewrite normr_gt0 subr_eq0.
case=> a [gt0_a /(_ x _ _)]; rewrite 1?(nbh_pt, subrr) //.
by rewrite distrC ltrr.
qed.

(* -------------------------------------------------------------------- *)
lemma eq_haslim b (g f : real -> real) x :
  f == g => haslim_g b f x <=> haslim_g b g x.
proof. by move/fun_ext=> ->. qed.

(* -------------------------------------------------------------------- *)
abbrev invf (f : real -> real) = fun x => 1%r / f x.

lemma haslimD b (f g : real -> real) x :
  haslim_g b f x => haslim_g b g x => haslim_g b (f + g) x.
proof.
case=> [l1].


admitted.

lemma haslimZ b (f : real -> real) c x :
  haslim_g b (fun x => c * f x) x <=> haslim_g b f x.
proof. admitted.

lemma haslimV b (f : real -> real) x :
  lim f x <> 0%r => haslim_g b (invf f) x.
proof. admitted.

lemma haslimP f x : haslim f x <=> (haslim_up f x /\ haslim_dw f x).
proof. admitted.

(* -------------------------------------------------------------------- *)
lemma haslim_shift b (f : real -> real) x0 a :
      haslim_g b (fun x : real => f (x + a)) x0
  <=> haslim_g b f (x0 + a).
proof. admitted.
