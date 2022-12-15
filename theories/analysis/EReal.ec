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
op muls (x y : sign) = 
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
op opps (x : sign) = 
  with x = Null => Null
  with x = Pos  => Neg
  with x = Neg  => Pos.

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

lemma oppeK : involutive [-].
proof. by case. qed.

lemma onee_neq0 : 1%e <> 0%e. 
proof. done. qed.

lemma rsign_Null (x : real) : rsign x = Null <=> x = 0%r.
proof. smt(). qed.

lemma rsign_Pos (x : real) : rsign x = Pos <=> 0%r < x.
proof. smt(). qed.

lemma rsign_Neg (x : real) : rsign x = Neg <=> x < 0%r.
proof. smt(). qed.

lemma rsignN (x : real) : rsign (-x) = opps (rsign x).
proof. smt(). qed.

lemma rsignM (x y : real) : rsign (x * y) = muls (rsign x) (rsign y).
proof. smt(). qed.

op add_def (x y : ereal) = ((x <> #+oo \/ y <> #-oo) /\ (x <> #-oo \/ y <> #+oo)).

lemma add_defC l1 l2 : add_def l1 l2 = add_def l2 l1.
proof. smt(). qed.

lemma oppeD x y : add_def x y => - (x + y) = (-x) - y.
proof. case: x y => [ | |x] [ | |y] => //= _; apply opprD. qed.

lemma oppeB x y : add_def x (-y) => - (x - y) = y - x.
proof. by move=> /oppeD ->; rewrite addeC oppeK. qed.

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
move=> [ | |x] [ | |y] [ | |z] //=; rewrite ?rsignM;
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

lemma mulNe x y : (-x) * y = - x * y.
proof.
case: x y => [ | |x] [ | | y] => //=; rewrite ?rsignN;
try (by case : (rsign _)); ring.
qed.

lemma mulN1e x : (- 1%e) * x = -x.
proof. by rewrite mulNe mul1e. qed.

lemma muleNN x y : (-x) * -y = x * y.
proof. by rewrite mulNe muleC mulNe oppeK muleC. qed.

lemma muleN1 x : x * - 1%e = -x.
proof. by rewrite muleC mulN1e. qed.

lemma muleN x y : x * -y = - x * y.
proof. by rewrite muleC mulNe muleC. qed.

lemma mule_eq0 x y : x * y = 0%e <=> x = 0%e \/ y = 0%e.
proof. smt(). qed.

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

lemma lee_r_x x c: c%e <= x => (exists r, c <= r /\ x = r%e ) \/ x = #+oo.
proof. by case: x => // /#. qed.

lemma normeN x : `|-x| = `|x|.
proof. case: x => //; apply normrN. qed.

lemma normE x : `|x| = if 0%e <= x then x else -x.
proof. case: x => //= /#. qed.

lemma ltee x : ! x < x.
proof. by case x. qed.

lemma lte_pmul2r x : 0%r < x => forall (y z : ereal), y * x%e < z * x%e <=> y < z.
proof.
move=> hx [ | |y] [ | |z] => //=; rewrite ?ltee //;
move/rsign_Pos: (hx) => h; rewrite ?h //.
by apply ltr_pmul2r.
qed.

lemma lte_pmul2l x : 0%r < x => forall (y z : ereal), x%e * y < x%e * z <=> y < z.
proof. by move=> ???;rewrite !(muleC (x%e)) lte_pmul2r. qed.

lemma lte_add2r z x y : x + z%e < y + z%e <=> x < y.
proof. case: x y => [ | |x] [ | |y] //=; apply ltr_add2r. qed.

lemma lte_add2l z x y : z%e + x < z%e + y <=> x < y.
proof. by rewrite !(addeC z%e) lte_add2r. qed.

lemma lee_lt_trans y x z : x <= y => y < z => x < z.
proof. case: x y z => [ | |x] [ | |y] [ | |z] //=; apply ler_lt_trans. qed.

lemma nosmt lte_le_trans y x z : x < y => y <= z => x < z.
proof. case: x y z => [ | |x] [ | |y] [ | |z] //=; apply ltr_le_trans. qed.

lemma lte_trans y x z : x < y => y < z => x < z.
proof. case: x y z => [ | |x] [ | |y] [ | |z] //=; apply ltr_trans. qed.

lemma lee_add2lW x y z : y <= z => x + y <= x + z.
proof. case: x y z => [ | |x] [ | |y] [ | |z] //=; apply ler_add2l. qed.

lemma lee_add2rW x y z : y <= z => y + x <= z + x.
proof. rewrite !(addeC _ x); apply lee_add2lW. qed.

lemma lte_add x y z t : x < y => z < t => x + z < y + t.
proof. case: x y z t => [ | |x] [ | |y] [ | |z] [ | |t] //=; apply ltr_add. qed.

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

(* -------------------------------------------------------------------- *)
lemma cvgto_eq (s1 s2 : int -> ereal) l1 l2 :
  s1 == s2 => l1 = l2 => cvgto s1 l1 <=> cvgto s2 l2.
proof. by move=> /fun_ext -> ->. qed.

lemma cvgto_cst c : cvgto (fun _ => c) c.
proof.
move=> p; case: c => /=; 1,2: by move=> [? [? ->]].
move=> r [e [? ->]]; exists 0 => /#.
qed.

lemma cvgtoN (s : int -> ereal) (l : ereal) :
  cvgto s l <=> cvgto (fun x => - s x) (- l).
proof.
have : forall s l, cvgto s l => cvgto (fun x => - s x) (- l).
+ move=> {s l} s l + p; case: l => /= [ | | l] hc [x [? ->]]. 
  + have := hc (fun y => (-x)%e < y) _; 1: by exists (-x) => /#.
    by move=> [N h]; exists N => n /h /= ?; apply lte_oppl.
  + have := hc (fun y => y < (-x)%e) _; 1: by exists (-x) => /#.
    by move=> [N h]; exists N => n /h /= ?; apply lte_oppr.
  have := hc (fun y => l%e - x%e < y < l%e + x%e ) _; 1: by exists x.
  move=> [N h]; exists N => n /h /=.
  rewrite lte_oppr lte_oppl /= opprB opprD opprK (addrC l x) => />.
move=> h; split; 1: by apply h.
by move=> /h /=; apply cvgto_eq => [ ?| ]; rewrite oppeK.
qed.

lemma cvgtoZ (c : real) (s : int -> ereal) (l : ereal) :
  cvgto s l => cvgto (fun x => c%e * s x) (c%e * l).
proof.
wlog: s l / (0%e <= l).
+ move => h; case (0%e <= l); 1: by apply h.
  rewrite -lteNge => /lte_opp2 /= hlt; have := (h (fun x => - s x) (-l) _); 1: by apply lteW.
  by rewrite -cvgtoN => h1 /h1 h2; apply cvgtoN; apply: cvgto_eq h2 => [? /= | ]; rewrite muleN.
wlog: c s l/ (0%r <= c).
+ move=> h; case (0%r <= c); 1: by apply h.
  rewrite -ltrNge => /ltr_opp2 /= hlt; have := (h (-c) (fun x => s x) l _); 1: by apply ltrW.
  by move=> {h} h1 /h1 h2 /h2 /=; rewrite cvgtoN; apply cvgto_eq => [?/= | ]; rewrite (mulNe (c%e)) oppeK.
move=> hc /lee_r_x [[l'] | ] -> /=.
+ move=> h p [e [he ->]].
  case (c = 0%r) => [-> /=| hne].
  + by exists 0 => n _; rewrite mul0e /= /#.
  have [N hN]:= h (fun y => l'%e - (e/c)%e < y < l'%e + (e/c)%e) _.
  + exists (e/c) => /= /#.
  have h0c : 0%r < c by smt().
  by exists N => n /hN /= [] /(lte_pmul2l _ h0c) /= ?  /(lte_pmul2l _ h0c) /= /#.
case _: (rsign c) => /=; last by move=> /rsign_Neg /#.
+ move=> /rsign_Null -> _ p [e [he ->]] /=.
  exists 0 => n _; rewrite mul0e /= /#.
move=> /rsign_Pos h0c h _ [x [hx -> ]] /=.
have [N hN] := h (fun y => (x/c)%e < y) _; 1: by exists (x/c) => /= /#.
by exists N => n /hN /= /(lte_pmul2l _ h0c) /= /#.
qed.

lemma cvgtoD (s1 s2 : int -> ereal) (l1 l2 : ereal) :
  add_def l1 l2 => 
  cvgto s1 l1 => cvgto s2 l2 => cvgto (fun x => s1 x + s2 x) (l1 + l2).
proof.
wlog: l1 l2 s1 s2 / (l1 <= l2) => [wlog|].
- case: (l1 <= l2); first by apply: wlog.
  rewrite -lteNge => /lteW le ha h1 h2.
  have := wlog _ _ _ _ le _ h2 h1; 1: by rewrite add_defC.
  by apply cvgto_eq => [?|]; rewrite addeC.
rewrite /add_def; case: l1 l2 => [ | |l1] [ | |l2] //=.
+ move=> h1 h2 ? [x [hx ->]].
  have hx2: 0%r < x/2%r by smt().
  have hp2 : nbh #+oo (fun y => (x/2%r)%e < y) by exists (x/2%r) => /= /#.
  have [N1 hN1] := h1 _ hp2; have [N2 hN2] := h2 _ hp2.
  exists (max N1 N2) => /= n hn; smt (lte_add).
+ move=> h1 h2 ? [x [hx ->]].
  have hx2: x/2%r < 0%r by smt().
  have hp2 : nbh #-oo (fun y => y < (x/2%r)%e) by exists (x/2%r) => /= /#.
  have [N1 hN1] := h1 _ hp2; have [N2 hN2] := h2 _ hp2.
  exists (max N1 N2) => /= n hn; smt (lte_add).
+ move=> h1 h2 ? [x [hx ->]].
  have [N2 hN2]:= h2 (fun y => l2%e - 1%e < y < l2%e + 1%e) _; 1: by exists (1%r).
  case (0%r <= l2 + 1%r) => hl21.
  + have [N1 hN1]:= h1 (fun y => y < (x - (l2 + 1%r))%e) _; 1: by exists (x - (l2 + 1%r)) => /#.
    exists (max N1 N2) => /= n hn; smt (lte_add). 
  have [N1 hN1]:= h1 (fun y => y < (x + (l2 + 1%r))%e) _; 1: by exists (x + (l2 + 1%r)) => /#.
  exists (max N1 N2) => /= n hn; smt (lte_add).     
+ move=> h1 h2 ? [x [hx ->]].
  have [N2 hN2]:= h1 (fun y => l1%e - 1%e < y < l1%e + 1%e) _; 1: by exists (1%r).
  case (0%r <= l1 - 1%r) => hl11.
  + have [N1 hN1]:= h2 (fun y => (x + (l1 - 1%r))%e < y) _; 1: by exists (x + (l1 - 1%r)) => /#.
    exists (max N1 N2) => /= n hn; smt (lte_add). 
  have [N1 hN1]:= h2 (fun y => (x - (l1 - 1%r))%e < y) _; 1: by exists (x - (l1 - 1%r)) => /#.
  exists (max N1 N2) => /= n hn; smt (lte_add).  
move=> _ h1 h2 p [e [he ->]].
have hx2: 0%r < e/2%r by smt().
have [N1 hN1] := h1 (fun y => l1%e - (e/2%r)%e < y < l1%e + (e/2%r)%e) _; 1: by exists (e/2%r) => //.
have [N2 hN2] := h2 (fun y => l2%e - (e/2%r)%e < y < l2%e + (e/2%r)%e) _; 1: by exists (e/2%r) => //.
exists (max N1 N2) => /= n hn; smt (lte_add).  
qed.

(*
(* -------------------------------------------------------------------- *)
op lim : (int -> xreal) -> xreal.

axiom limP (s : int -> xreal) (l : xreal) : cvgto s l => lim s = l.

(* -------------------------------------------------------------------- *)

*)
