(* -------------------------------------------------------------------- *)
require import AllCore Real StdOrder.
        import RealOrder.

(* -------------------------------------------------------------------- *)
op nonempty ['a] (E : 'a -> bool) =
  exists x, E x.

(* -------------------------------------------------------------------- *)
type xreal = [
  | Real of real
  | PInf
  | NInf
].

op xzero : xreal.

abbrev (%x) (x : real) = Real x.

theory OfInt.
abbrev (%x) (x : int) = Real x%r.
end OfInt.

export OfInt.

op (+) (x y : xreal) =
  with x = NInf   , y = NInf    => NInf
  with x = NInf   , y = Real _  => NInf
  with x = NInf   , y = PInf    => 0%x
  with x = Real x0, y = NInf    => NInf
  with x = Real x0, y = Real y0 => (Real.(+) x0 y0)%x
  with x = Real  _, y = PInf    => PInf
  with x = PInf   , y = NInf    => 0%x
  with x = PInf   , y = Real _  => PInf
  with x = PInf   , y = PInf    => PInf.

op ([-]) (x : xreal) =
  with x = NInf    => PInf
  with x = Real x0 => (Real.([-]) x0)%x
  with x = PInf    => NInf.

op ( * ) : xreal -> xreal -> xreal.

(*
op xinv (x : xreal) =
  with x = NInf    => 0%x
  with x = PInf    => 0%x
  with x = Real x0 => 
*)

abbrev (-) x y = x + -y.

axiom addxC : commutative (+).

(* -------------------------------------------------------------------- *)
op (<=) (x y : xreal) =
  with x = NInf   , y = NInf    => true
  with x = NInf   , y = Real _  => true
  with x = NInf   , y = PInf    => true
  with x = Real x0, y = NInf    => false
  with x = Real x0, y = Real y0 => Real.(<=) x0 y0
  with x = Real  _, y = PInf    => true
  with x = PInf   , y = NInf    => false
  with x = PInf   , y = Real _  => false
  with x = PInf   , y = PInf    => true.

op (<) (x y : xreal) =
  with x = NInf   , y = NInf    => false
  with x = NInf   , y = Real _  => true
  with x = NInf   , y = PInf    => true
  with x = Real x0, y = NInf    => false
  with x = Real x0, y = Real y0 => Real.(<) x0 y0
  with x = Real  _, y = PInf    => true
  with x = PInf   , y = NInf    => false
  with x = PInf   , y = Real _  => false
  with x = PInf   , y = PInf    => false.

axiom ltxNge (x y : xreal) : (x < y) = !(y <= x).
axiom ltxW (x y : xreal) : (x < y) => (x <= y).

(* -------------------------------------------------------------------- *)
op "`|_|" (x : xreal) =
  with x = PInf => PInf
  with x = NInf => NInf
  with x = Real x0 => (Real."`|_|" x0)%x.

(* -------------------------------------------------------------------- *)
(* xlub E returns -oo if E is empty                                     *)
op xlub : (xreal -> bool) -> xreal.

axiom xlub_ub (E : xreal -> bool) (x : xreal) :
  E x => (x <= xlub E).

axiom xlub_lub (E : xreal -> bool) (M : xreal) :
  (forall x, E x => x <= M) => xlub E <= M.

(* -------------------------------------------------------------------- *)
op nbh (l : xreal) (p : xreal -> bool) =
  with l = PInf =>
    exists x, x < PInf /\ p = (fun y => x < y)
  with l = NInf =>
    exists x, NInf < x /\ p = (fun y => y < x)
  with l = Real k =>
    exists e, Real 0%r < e /\ p = (fun y => l - e < y < l + e).

(* -------------------------------------------------------------------- *)
op cvgto (s : int -> xreal) (l : xreal) =
  forall (p : xreal -> bool), nbh l p =>
    exists (N : int), forall (n : int),
      N <= n => p (s n).

axiom cvgto_eq (s1 s2 : int -> xreal) l :
  (forall x, s1 x = s2 x) => cvgto s1 l => cvgto s2 l.

(* -------------------------------------------------------------------- *)
lemma cvgtoN (s : int -> xreal) (l : xreal) :
  cvgto s l => cvgto (fun x => - s x) (- l).
proof. admitted.

lemma cvgtoZ (c : xreal) (s : int -> xreal) (l : xreal) :
  cvgto s l => cvgto (fun x => c * s x) (c * l).
proof. admitted.

lemma cvgtoD (s1 s2 : int -> xreal) (l1 l2 : xreal) :
     (l1, l2) <> (PInf, NInf)
  => (l1, l2) <> (NInf, PInf)
  => cvgto s1 l1 => cvgto s2 l2 => cvgto (fun x => s1 x + s2 x) (l1 + l2).
proof.
wlog: l1 l2 s1 s2 / (l1 <= l2) => [wlog|].
- case: (l1 <= l2); first by apply: wlog.
  rewrite -ltxNge => /ltxW le h1 h2 cvg1 cvg2.
  have := wlog _ _ _ _ le _ _ cvg2 cvg1; 1,2: smt().
  by rewrite addxC &(cvgto_eq) /= => *; rewrite addxC.
case: l1 l2 => [l1| | ] [l2 | | ] //=.
- admit.
- move=> h1 h2 p /= [d [ltd ->>]]; pose e := 1%x.
  pose p y := (l1%x - e < y < l1%x + e); have:= h1 p _.
  - by exists e.
  case=> N @/p /= cvg1; have := h2 ((<) (d - (l1%x - e))) _.
  - by smt().
  by case=> N' cvg2; exists (max N N') => n gen /#.
- move=> h1 h2 p /= [d [ltd ->>]].
  have := h1 ((<) `|d|) _ => /=; first smt().
  have := h2 ((<) `|d|) _ => /=; first smt().
  by case=> [N1 ?] [N2 ?]; exists (max N1 N2) => /#.

- admit.

- move=> h1 h2 p /= [d [ltd ->>]].
  admit.
admitted.

(* -------------------------------------------------------------------- *)
op lim : (int -> xreal) -> xreal.

axiom limP (s : int -> xreal) (l : xreal) : cvgto s l => lim s = l.

(* -------------------------------------------------------------------- *)

