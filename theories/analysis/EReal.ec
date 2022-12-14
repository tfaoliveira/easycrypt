(* -------------------------------------------------------------------- *)
require import AllCore Real StdOrder.
        import RField RealOrder.
(* -------------------------------------------------------------------- *)
type ereal = [ PInf | NInf | Real of real ].

abbrev (%e) (x : real) = Real x.

theory IntNotations.
abbrev (%e) (x : int)  = x%r%e.
end IntNotations. export IntNotations.

abbrev #+oo = PInf.
abbrev #-oo = NInf.

(* -------------------------------------------------------------------- *)
type sign = [ Null | Pos | Neg ].

(* -------------------------------------------------------------------- *)
op select ['a] (s : sign) (z p n : 'a) =
  with s = Pos  => p
  with s = Neg  => n
  with s = Null => z.

(* -------------------------------------------------------------------- *)
op muls (x y :sign) = 
  with x = Null, y = Null => Null
  with x = Null, y = Pos  => Null
  with x = Null, y = Neg  => Null
  with x = Pos , y = Null => Null
  with x = Pos , y = Pos  => Pos
  with x = Pos , y = Neg  => Neg
  with x = Neg , y = Null => Null
  with x = Neg , y = Pos  => Neg
  with x = Neg , y = Neg  => Pos.

(* -------------------------------------------------------------------- *)
op rsign (x : real) : sign =
  if x = 0%r then Null else if x < 0%r then Neg else Pos.

(* -------------------------------------------------------------------- *)
op sign (x : ereal) : sign =
  with x = PInf   => Pos
  with x = NInf   => Neg
  with x = Real x => rsign x.

(* -------------------------------------------------------------------- *)
op is_real (x:ereal) = 
  with x = PInf   => false
  with x = NInf   => false
  with x = Real _ => true.

(* -------------------------------------------------------------------- *)
op (<=) (x y : ereal) =
  with x = PInf  , y = PInf   => true
  with x = PInf  , y = NInf   => false
  with x = PInf  , y = Real _ => false
  with x = Real _, y = PInf   => true
  with x = Real x, y = Real y => Real.(<=) x y
  with x = Real x, y = NInf   => false
  with x = NInf  , y = PInf   => true
  with x = NInf  , y = Real _ => true
  with x = NInf  , y = NInf   => true.

(* -------------------------------------------------------------------- *)
op (<) (x y : ereal) =
  with x = PInf  , y = PInf   => false
  with x = PInf  , y = NInf   => false
  with x = PInf  , y = Real _ => false
  with x = Real _, y = PInf   => true
  with x = Real x, y = Real y => Real.(<) x y
  with x = Real x, y = NInf   => false
  with x = NInf  , y = PInf   => true
  with x = NInf  , y = Real _ => true
  with x = NInf  , y = NInf   => false.

(* -------------------------------------------------------------------- *)
op esign (x : ereal) : sign =
  if x = 0%e then Null else if x < 0%e then Neg else Pos.

(* -------------------------------------------------------------------- *)
op "`|_|" (x : ereal) =
  with x = PInf => PInf
  with x = NInf => PInf
  with x = Real x0 => (Real."`|_|" x0)%e.

(* -------------------------------------------------------------------- *)
op [-] (x : ereal) =
  with x = PInf   => #-oo
  with x = NInf   => #+oo
  with x = Real x => (Real.([-])x)%e.

(* -------------------------------------------------------------------- *)
op (+) (x y : ereal) =
  with x = PInf  , y = PInf   => #+oo
  with x = PInf  , y = NInf   => #-oo
  with x = PInf  , y = Real _ => #+oo
  with x = NInf  , y = PInf   => #-oo
  with x = NInf  , y = NInf   => #-oo
  with x = NInf  , y = Real _ => #-oo
  with x = Real x, y = PInf   => #+oo
  with x = Real _, y = NInf   => #-oo
  with x = Real x, y = Real y => (Real.(+) x y)%e.

abbrev (-) (x y : ereal) = x + (-y).

(* -------------------------------------------------------------------- *)
op ( * ) (x y : ereal) =
  with x = PInf  , y = PInf   => #+oo
  with x = PInf  , y = NInf   => #-oo
  with x = NInf  , y = PInf   => #-oo
  with x = NInf  , y = NInf   => #+oo
  with x = Real x, y = Real y => (Real.( * ) x y)%e
  with x = Real x, y = PInf   => select (rsign x) 0%e #+oo #-oo
  with x = Real x, y = NInf   => select (rsign x) 0%e #-oo #+oo
  with x = PInf  , y = Real y => select (rsign y) 0%e #+oo #-oo
  with x = NInf  , y = Real y => select (rsign y) 0%e #-oo #+oo.

op inve (x: ereal) = 
  with x = PInf => 0%e
  with x = NInf => 0%e
  with x = Real x => if x = 0%r then #+oo else (inv x)%e.

abbrev ( / ) (x y : ereal) = x * (inve y).
 
(* -------------------------------------------------------------------- *)
(* Lemmas on basic operators                                            *)

lemma addeA: associative (+).
proof. by move=> [ | |x] [ | | y] [ | |z] //=; rewrite addrA. qed.

lemma addeC: commutative (+).
proof. by move=> [ | |x] [ | |y] //=; rewrite addrC. qed.

lemma add0e : left_id 0%e (+).
proof. by move=> []. qed.

lemma addNe x : is_real x => (-x) + x = 0%e.
proof. by case: x. qed.

lemma nosmt oppeK: involutive [-].
proof. by case. qed.

lemma onee_neq0 : 1%e <> 0%e. 
proof. done. qed.

lemma rsign_mul (x y : real) : rsign (x * y) = muls (rsign x) (rsign y).
proof. smt(). qed.

lemma mul0s s : muls Null s = Null.
proof. by case: s. qed.

lemma mulsC x y : muls x y = muls y x.
proof. by case x; case y. qed.

lemma mulePinf x : x * #+oo = select (esign x) 0%e #+oo #-oo.
proof. by case: x. qed.

lemma esign_Null x : esign x = Null <=> x = 0%e.
proof. smt(). qed.

lemma muleA : associative ( * ).
proof. 
move=> [ | |x] [ | |y] [ | |z] //=; rewrite ?rsign_mul;
  try ((by case: (rsign _)) 
    || (by case: (rsign _) => //=; case: (rsign _))
    || by case _: (rsign z) => //= heq; case: (rsign _) => //=; rewrite heq).
ring.
qed.

lemma muleC : commutative ( * ).
proof. move=> [ | |x] [ | |y] //=; ring. qed.

lemma mul1e x : 1%e * x = x.
proof. by case: x. qed.

lemma mule1 x : x * 1%e = x.
proof. by rewrite muleC mul1e. qed.

lemma mul0e x : 0%e * x = 0%e. 
proof. by case: x. qed.

lemma mule0 x : x * 0%e = 0%e.
proof. by rewrite muleC mul0e. qed.

lemma lteNge (x y : ereal) : (x < y) = !(y <= x).
proof. case x; case y => //= /#. qed.

lemma lteW (x y : ereal) : (x < y) => (x <= y).
proof. case x; case y => //= /#. qed.

lemma leeNinf_eq x : x <= #-oo => x = #-oo.
proof. by case x. qed.

lemma lte_opp2 x y : -x < -y <=> y < x.
proof. by case: x; case: y => //= ??;rewrite ltr_opp2. qed.

lemma lte_oppr x y : x < -y <=> y < -x.
proof. by rewrite -lte_opp2 oppeK. qed.

lemma lte_oppl x y : -x < y <=> -y < x.
proof. by rewrite -lte_opp2 oppeK. qed.

(* -------------------------------------------------------------------- *)
(* elub E returns -oo if E is empty                                     *)
op elub : (ereal -> bool) -> ereal.

axiom elub_ub (E : ereal -> bool) (x : ereal) :
  E x => (x <= elub E).

axiom elub_lub (E : ereal -> bool) (M : ereal) :
  (forall x, E x => x <= M) => elub E <= M.

lemma elub_empty (E: ereal -> bool) : elub (fun _ => false) = #-oo.
proof. by apply/leeNinf_eq/elub_lub. qed.

lemma elub_eq (p q: ereal -> bool) : p == q => elub p = elub q.
proof. by move=> /fun_ext ->. qed.

(* -------------------------------------------------------------------- *)
op nbh (l : ereal) (p : ereal -> bool) =
  with l = PInf =>
    exists x, 0%r < x /\ p = (fun y => x%e < y)
  with l = NInf =>
    exists x, x < 0%r /\ p = (fun y => y < x%e)
  with l = Real k =>
    exists (e:real), 0%r < e /\ p = (fun y => l - e%e < y < l + e%e).

(* -------------------------------------------------------------------- *)
op cvgto (s : int -> ereal) (l : ereal) =
  forall (p : ereal -> bool), nbh l p =>
    exists (N : int), forall (n : int),
      N <= n => p (s n).

lemma cvgto_eq (s1 s2 : int -> ereal) l :
  s1 == s2 => cvgto s1 l = cvgto s2 l.
proof. by move=> /fun_ext ->. qed.

(* -------------------------------------------------------------------- *)
lemma cvgtoN (s : int -> ereal) (l : ereal) :
  cvgto s l => cvgto (fun x => - s x) (- l).
proof.
move=> + p; case: l => /= [ | | l] hc [x [? ->]]. 
+ have := hc (fun y => (-x)%e < y) _; 1: by exists (-x) => /#.
  by move=> [N h]; exists N => n /h /= ?; apply lte_oppl.
+ have := hc (fun y => y < (-x)%e) _; 1: by exists (-x) => /#.
  by move=> [N h]; exists N => n /h /= ?; apply lte_oppr.
have := hc (fun y => l%e - x%e < y < l%e + x%e) _; 1: by exists x.
move=> [N h]; exists N => n /h /=; rewrite -lte_oppr -lte_oppl /= /#.
qed.

lemma cvgtoZ (c : ereal) (s : int -> ereal) (l : ereal) :
  cvgto s l => cvgto (fun x => c * s x) (c * l).
proof.
move=> + p; case: l => [ | | l] hc /=; case: c => /=.
(* nbh (+oo) p => cvgto (fun x => +oo * s x) +oo *)
+ move=> h;  have [N hN]:= hc p h; exists N => n /hN.
  by case: h => x [? ->]; case: (s n) => //= /#. 
+ move=> [x [? ->]].
  have := hc (fun y => 1%e < y) _; 1: by exists 1%r.
  by move=> [N hN]; exists N => n /hN /=; case: (s n) => //= /#.
+ move=> r; rewrite /rsign; case (r = 0%r) => [-> | ].
  + by move=> [e [he -> ]] /=; exists 0 => n; rewrite mul0e /= /#.
  move=> hr; case (r < 0%r) => hr' [x [hx ->]] /=.
  + have := hc (fun y => (x / r)%e < y) _; 1: by exists (x / r) => /= /#.
    move=> [N hN]; exists N => n /hN /=.
    case: (s n) => //=; 1: by rewrite /rsign hr /= hr'.
    by move=> r0; rewrite ltr_ndivr_mulr // mulrC.
  have := hc (fun y => (x / r)%e < y) _; 1: by exists (x / r) => /= /#.
  move=> [N hN]; exists N => n /hN /=.
  case: (s n) => //=; 1: by rewrite /rsign hr /= hr'.
  by move=> r0; rewrite ltr_pdivr_mulr // 1:/# mulrC.
+ move=> h;  have [N hN]:= hc p h; exists N => n /hN.
  by case: h => x [? ->]; case: (s n) => //= /#. 
+ move=> [x [? ->]].
  have := hc (fun y => y < (-1)%e) _; 1: by exists (-1)%r.
  by move=> [N hN]; exists N => n /hN /=; case: (s n) => //= /#.
+ move=> r; rewrite /rsign; case (r = 0%r) => [-> | ].
  + by move=> [e [he -> ]] /=; exists 0 => n; rewrite mul0e /= /#.
  move=> hr; case (r < 0%r) => hr' [x [hx ->]] /=.
  + have := hc (fun y => y < (x / r)%e) _; 1: by exists (x / r) => /= /#.
    move=> [N hN]; exists N => n /hN /=.
    case: (s n) => //=; 1: by rewrite /rsign hr /= hr'.
    by move=> r0; rewrite ltr_ndivl_mulr // mulrC.
  have := hc (fun y => y < (x / r)%e) _; 1: by exists (x / r) => /= /#.
  move=> [N hN]; exists N => n /hN /=.
  case: (s n) => //=; 1: by rewrite /rsign hr /= hr'.
  by move=> r0; rewrite ltr_pdivl_mulr // 1:/# mulrC.
admitted.
(*
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

*)
