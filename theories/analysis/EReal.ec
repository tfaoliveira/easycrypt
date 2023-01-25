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

lemma eqe_opp x y : -x = -y <=> x = y.
proof. by case: x; case y => //= ??; apply eqr_opp. qed.

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

lemma leee (x : ereal) : x <= x.
proof. by case: x. qed.
hint simplify leee. 

lemma nosmt lee_asym (x y : ereal): x <= y <= x => x = y.
proof. case: x y => [ | | x] [ | | y] //=; apply ler_asym. qed.

lemma eqe_le (x y : ereal): x = y <=> x <= y <= x.
proof. split=> [-> // | ]; apply lee_asym. qed.

lemma lee_bot x : #-oo <= x.
proof. by case x. qed.
hint simplify lee_bot.

lemma lee_top x : x <= #+oo.
proof. by case x. qed.
hint simplify lee_top.

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

lemma lte_neqAle x y :
  (x < y) <=> (x <> y) /\ (x <= y).
proof. case: x y => [ | |x] [ | |y] //=; apply ltr_neqAle. qed.

lemma lee_eqVlt x y :
  (x <= y) <=> (x = y) \/ (x < y).
proof. by rewrite lte_neqAle; case: (x = y)=> // ->. qed.

lemma lte_trans y x z : x < y => y < z => x < z.
proof. case: x y z => [ | |x] [ | |y] [ | |z] //=; apply ltr_trans. qed.

lemma lee_trans y x z: x <= y => y <= z => x <= z.
proof. case: x y z => [ | |x] [ | |y] [ | |z] //=; apply ler_trans. qed.

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

lemma lte_pmul x1 y1 x2 y2 :
  0%e <= x1 => 0%e <= x2 => x1 < y1 => x2 < y2 => x1 * x2 < y1 * y2.
proof. smt(ltr_pmul). qed.

lemma lte_add2r z x y : x + z%e < y + z%e <=> x < y.
proof. case: x y => [ | |x] [ | |y] //=; apply ltr_add2r. qed.

lemma lte_add2l z x y : z%e + x < z%e + y <=> x < y.
proof. by rewrite !(addeC z%e) lte_add2r. qed.

lemma lee_lt_trans y x z : x <= y => y < z => x < z.
proof. case: x y z => [ | |x] [ | |y] [ | |z] //=; apply ler_lt_trans. qed.

lemma nosmt lte_le_trans y x z : x < y => y <= z => x < z.
proof. case: x y z => [ | |x] [ | |y] [ | |z] //=; apply ltr_le_trans. qed.

lemma lee_add2lW x y z : y <= z => x + y <= x + z.
proof. case: x y z => [ | |x] [ | |y] [ | |z] //=; apply ler_add2l. qed.

lemma lee_add2rW x y z : y <= z => y + x <= z + x.
proof. rewrite !(addeC _ x); apply lee_add2lW. qed.

lemma lte_add x y z t : x < y => z < t => x + z < y + t.
proof. case: x y z t => [ | |x] [ | |y] [ | |z] [ | |t] //=; apply ltr_add. qed.

op mul_def l1 l2 = 
  (l1 = 0%e => l2 <> #+oo /\ l2 <> #-oo) /\
  (l2 = 0%e => l1 <> #+oo /\ l1 <> #-oo).

lemma mul_defN l1 l2 : mul_def (-l1) l2 = mul_def l1 l2.
proof. smt(). qed.

lemma mul_defC l1 l2 : mul_def l1 l2 = mul_def l2 l1.
proof. smt(). qed.

lemma normr_bound (x e : real) : -e < x < e <=> `|x| < e.
proof. smt(). qed.

(* TODO: move this ? *)
lemma normrB_bound (x y e : real) : y - e < x < y + e <=> `|x - y| < e.
proof. smt(). qed.
(* TODO: move this ? *)
lemma norme_bound (x e : ereal) : -e < x < e <=> `|x| < e.
proof. smt(). qed.

lemma normeB_bound (x y : ereal) (e : real) : y - e%e < x < y + e%e <=> `|x - y| < e%e.
proof. smt(). qed.

lemma normeM (x y : ereal) : `|x * y| = `|x| * `|y|.
proof. smt(). qed.

lemma gee0_norm x : 0%e <= x => `|x| = x.
proof. smt(). qed.

lemma norme_ge0 x : 0%e <= `|x|.
proof. smt(). qed.

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

op cvg (s: int -> ereal) = exists l, cvgto s l.

(* -------------------------------------------------------------------- *)
lemma cvgto_eq (s1 s2 : int -> ereal) l1 l2 :
  s1 == s2 => l1 = l2 => cvgto s1 l1 <=> cvgto s2 l2.
proof. by move=> /fun_ext -> ->. qed.

lemma cvgtoC c : cvgto (fun _ => c) c.
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

lemma cvgtoB (s1 s2 : int -> ereal) (l1 l2 : ereal) :
  add_def l1 (-l2) => 
  cvgto s1 l1 => cvgto s2 l2 => cvgto (fun x => s1 x - s2 x) (l1 - l2).
proof. by move=> ha h1 h2; apply cvgtoD => //; rewrite -cvgtoN. qed.

lemma cvgtoM (s1 s2: int -> ereal) (l1 l2 : ereal) :
  mul_def l1 l2 => 
  cvgto s1 l1 => cvgto s2 l2 => cvgto (fun x => s1 x * s2 x) (l1 * l2).
proof.
wlog: s1 l1 / (0%e <= l1).
+ move => h; case (0%e <= l1); 1: by apply h.
  rewrite -lteNge => /lte_opp2 /= hlt; have {h} := (h (fun x => - s1 x) (-l1) _); 1: by apply lteW.
  by rewrite mul_defN -cvgtoN => h hm h1 h2; apply cvgtoN; apply: cvgto_eq (h hm h1 h2) => [? /= | ]; rewrite mulNe.
move=> h0l1; wlog: s2 l2/ (0%e <= l2).
+ move=> h; case (0%e <= l2); 1: by apply h.
  rewrite -lteNge => /lte_opp2 /= hlt; have {h} := (h (fun x => -s2 x) (-l2) _); 1: by apply lteW.
  rewrite mul_defC mul_defN mul_defC -cvgtoN => h hm h1 h2; apply cvgtoN.
  by apply: cvgto_eq (h hm h1 h2) => [? /= | ]; rewrite muleN.
move: h0l1; wlog: s1 s2 l1 l2 / (l1 <= l2).
+ move=> h; case (l1 <= l2); 1: by apply h.
  rewrite -lteNge mul_defC => /lteW hle h1 h2 hm hc1 hc2.
  by apply: cvgto_eq (h _ _ _ _ hle h2 h1 hm hc2 hc1) => [ ? /= | ]; rewrite muleC.
move=> + h0l1 h0l2; rewrite /mul_def.
case /lee_r_x : h0l1 => [[r1 [hr1]]|] ->>; (case /lee_r_x : h0l2 => [[r2 [hr2]]|] ->> //=).
+ move=> _ h1 h2 _ [e [he ->]].
  have [N21 /=]:= h2 (fun y => r2%e - 1%e < y < r2%e + 1%e) _; 1: by exists 1%r.
  (pose M := r2 + 1%r) => hM.
  case (r1 = 0%r) => [->> /= | hne].
  + pose e1 := e / M; have [N1 hN1] := h1 (fun y => - e1%e < y < e1%e) _; 1: by exists e1 => /= /#.  
    exists (max N21 N1) => n hn. 
    apply/(norme_bound (s1 n * s2 n) e%e); rewrite normeM.
    case (s1 n = 0%e) => [-> /= | hne]; 1: by rewrite ger0_norm 1:// mul0e.
    have -> : e%e = e1%e * M%e by rewrite /e1 /=; field => /#.
    by apply lte_pmul; 1,2: apply norme_ge0; smt().
  pose e1 := e /(2%r*M); pose e2 := e/(2%r*r1).
  have [N1 hN1] := h1 (fun y => r1%e - e1%e < y < r1%e + e1%e) _; 1: by exists e1 => /#. 
  have [N2 hN2] := h2 (fun y => r2%e - e2%e < y < r2%e + e2%e) _; 1: by exists e2 => /#.
  exists (max N21 (max N1 N2)) => n hn.
  apply/(normeB_bound (s1 n * s2 n) (r1 * r2)%e e).
  have {hN1 h1} /= := hN1 n _; 1: smt(); case: (s1 n) => //= {s1} s1 /normrB_bound h1.
  have := hM n _; 1: smt().
  have {hN2 h2} /= := hN2 n _; 1: smt(); case: (s2 n) => //= {s2 hM} s2 /normrB_bound h2 hM.
  have -> : s1 * s2 - r1 * r2 = (s1 - r1) * s2 + (s2 - r2) * r1 by ring.
  apply (ler_lt_trans (`|(s1 - r1) * s2| + `|(s2 - r2) * r1|)); 1: smt().
  have -> : e = e1 * M + e2 * r1 by rewrite /e1 /e2 ;field; smt().
  by rewrite !normrM; apply ltr_add; [smt(ltr_pmul) | smt(ltr_pmul2r)].
+ move=> hne h1 h2; have h0r1: 0%r < r1 by smt().
  move/rsign_Pos : (h0r1) => -> /= _ [x [hx ->]].
  have [N1 /= hN1]:= h1 (fun y => r1%e - (r1/2%r)%e < y < r1%e + (r1/2%r)%e) _; 1: by exists (r1/2%r) => /#.
  have [N2 /= hN2]:= h2 (fun y => (x/(r1 - r1/2%r))%e < y) _; 1: by exists (x/(r1 - r1/2%r)) => /= /#.
  exists (max N1 N2) => n hn /=.
  have -> : x%e = (r1 - r1/2%r)%e * (x / (r1 - r1/2%r))%e by rewrite /=; field => /#. 
  by apply lte_pmul => /#.
move=> h1 h2 _ [x [hx ->]].
have [N1 /= hN1]:= h1 (fun y => 1%e < y) _; 1: by exists 1%r.
have [N2 /= hN2]:= h2 (fun y => x%e < y) _; 1: by exists x.
exists (max N1 N2) => h hn.
rewrite -(mul1e x%e); apply lte_pmul => // /#.
qed.

lemma cvgtoZ (c : real) (s : int -> ereal) (l : ereal) :
  cvgto s l => cvgto (fun x => c%e * s x) (c%e * l).
proof.
move=> h; case (c = 0%r) => [-> | hne].
+ by apply: cvgto_eq (cvgtoC 0%e) => [x | ]; rewrite mul0e.
apply : cvgtoM (cvgtoC c%e) h; 1: by rewrite /mul_def hne.
qed.

lemma cvgtoV s l : l <> 0%e => cvgto s l => cvgto (fun n => inve (s n)) (inve l).
proof.
case: l => /= [ | |l].
+ move=> h _ [e [he ->]] /=.
  have [N /= hN] := h (fun y => (inv e)%e < y) _; 1: exists (inv e) => /#.
  exists N => n /hN; case: (s n) => //=; 1: smt().
  move=> r hr; have -> /= : r <> 0%r by smt().
  by rewrite -{2}(invrK e); smt (ltf_pinv).
+ move=> h _ [e [he ->]] /=.
  have [N /= hN] := h (fun y => y < (-inv e)%e ) _; 1: exists (-inv e) => /#.
  exists N => n /hN; case: (s n) => //=; 1: smt().
  move=> r hr; have -> /= : r <> 0%r by smt().
  by rewrite -{1}(invrK e); smt (ltf_ninv).
move=> hl h; rewrite hl /= => _ [e [he ->]].
have [N1 /= hN1] := h (fun y => l%e - (`|l|/2%r)%e < y < l%e + (`|l|/2%r)%e) _; 1: by exists (`|l|/2%r) => /#.
have [N2 /= hN2] := h (fun y => l%e - (`|l|*`|l|*e/2%r)%e < y < l%e + (`|l|*`|l|*e/2%r)%e) _; 1: by  exists (`|l|*`|l|*e/2%r) => /#.
exists (max N1 N2) => n hn.
have := hN1 n _; 1: smt(); have := hN2 n _; 1: smt().
case: (s n) => //= {s h hN1 hN2} s /normrB_bound h1 /normrB_bound h2.
have hs0: s <> 0%r by smt().
rewrite hs0 /= normrB_bound.
have -> : inv s - inv l = (l - s) / (s * l); 1:by field; smt().
have -> : e = (`|l| * `|l|*e / 2%r) /  (`|l| * `|l| / 2%r) by field; rewrite // expr2 /#. 
rewrite normrM; apply ltr_pmul; 1..3:smt(). 
rewrite normrV 1:/#; apply ltf_pinv => /#.
qed.

lemma cvgto_div (s1 s2: int -> ereal) (l1 l2 : ereal) : 
  (inve l2 = 0%e => l1 <> #+oo /\ l1 <> #-oo) => l2 <> 0%e =>
  cvgto s1 l1 => cvgto s2 l2 => cvgto (fun x => s1 x / s2 x) (l1 / l2).
proof.
move=> hm hl2 h1 h2;apply cvgtoM => //; last by apply cvgtoV.
by rewrite /mul_def; split => //; case: (l2) hl2 => //= ? ->.
qed.

lemma cnvto_opp_oo s : cvgto s #+oo => cvgto s #-oo => false.
proof. 
move=> h1 h2.
have [N1 hN1]:= h1 (fun y => 1%e < y) _; 1: by exists 1%r.
have [N2 hN2]:= h2 (fun y => y < (-1)%e) _; 1: by exists (-1)%r.
move: (hN1 _ (IntOrder.maxrl N1 N2)) (hN2 _ (IntOrder.maxrr N1 N2)) => /= /#.
qed.

lemma cnvto_oo_r s x : cvgto s #+oo => cvgto s x%e => false.
proof.
move=> h1 h2.
have [N1 hN1]:= h1 (fun y => (`|x| + 1%r)%e < y) _; 1: by exists (`|x| + 1%r)=> /#.
have [N2 hN2]:= h2 (fun y => x%e - 1%e < y < x%e + 1%e) _; 1: by exists 1%r.
move: (hN1 _ (IntOrder.maxrl N1 N2)) (hN2 _ (IntOrder.maxrr N1 N2)) => /= /#.
qed.

lemma uniq_cnvto s x y: cvgto s x => cvgto s y => x = y.
proof.
case: x y => [ | | x] [ | | y] // h1 h2.
+ by have := cnvto_opp_oo _ h1 h2.
+ by have := cnvto_oo_r _ _ h1 h2.
+ by have := cnvto_opp_oo _ h2 h1.
+ move/cvgtoN: h1; move/cvgtoN: h2 => h2 h1.
  by have := cnvto_oo_r _ (-y) h1 h2. 
+ by have := cnvto_oo_r _ _ h2 h1.
  move/cvgtoN: h1; move/cvgtoN: h2 => h2 h1.
  by have := cnvto_oo_r _ (-x) h2 h1. 
rewrite /=; case: (x = y)=> // ne_xy.
pose e := `|x - y| / 2%r; have gt0e: 0%r < e.
+ by rewrite divr_gt0 ?(normr_gt0, subr_eq0).
have [Nx hNx]:= h1 (fun y => x%e - e%e < y < x%e + e%e) _; 1: by exists e.
have [Ny hNy]:= h2 (fun z => y%e - e%e < z < y%e + e%e) _; 1: by exists e.
case: (IntOrder.maxr_ub Nx Ny); (pose N := max _ _).
move=> /hNx + /hNy; case: (s N) => //= { s h1 h2 hNx hNy} s /normrB_bound hNx; apply/negP => /normrB_bound hNy.
have := ltr_add _ _ _ _ hNx hNy; rewrite ltrNge.
by rewrite /e double_half (@distrC s) ler_dist_add.
qed.

(* -------------------------------------------------------------------- *)
lemma cnvP l s: cvgto s l => cvg s.
proof. by move=> cnv_sl; exists l. qed.

lemma cnvC x : cvg (fun _ => x).
proof. exists x; apply cvgtoC. qed.

lemma cnvZ c (s : int -> ereal) :
  cvg s => cvg (fun x => c%e * s x).
proof. by case=> [l h]; exists (c%e * l); apply/cvgtoZ. qed.

lemma cnvZ_iff c (s : int -> ereal) : c <> 0%r =>
  cvg (fun x => c%e * s x) <=> cvg s.
proof.
move=> nz_c; split; last by apply/cnvZ.
suff {2}->: s = fun x => (inv c)%e * (c%e * s x) by apply/cnvZ.
by apply/fun_ext=> x; rewrite muleA /= divff // mul1e.
qed.

lemma cnvN s : cvg s => cvg (fun x => -s x).
proof. by move/(@cnvZ (-1)%r) => /#. qed.

(* -------------------------------------------------------------------- *)
lemma eq_cnvto_from N s1 s2 l:
     (forall n, (N <= n)%Int => s1 n = s2 n)
  => cvgto s1 l => cvgto s2 l.
proof.
move=> eq_s lim_s1 p hp; case: (lim_s1 p hp).
move=> Ns lim_s1N; exists (max N Ns)=> n /IntOrder.ler_maxrP [leN leNs].
by rewrite -eq_s // lim_s1N.
qed.

lemma eq_cnvto_fromP N s1 s2 l:
     (forall n, (N <= n)%Int => s1 n = s2 n)
  => cvgto s1 l <=> cvgto s2 l.
proof.
move=> eq; split; apply/(eq_cnvto_from N)=> // n leNn.
by rewrite eq_sym eq.
qed.

(* -------------------------------------------------------------------- *)
lemma eq_cnv_fromP N s1 s2:
     (forall n, (N <= n)%Int => s1 n = s2 n)
  => cvg s1 <=> cvg s2.
proof.
move=> eq; split; case=> l h; exists l; move: h.
  by apply/(@eq_cnvto_from N).
by apply/(@eq_cnvto_from N)=> n leNn; apply/eq_sym/eq.
qed.

(* -------------------------------------------------------------------- *)

op lim (s : int -> ereal) : ereal =
  choiceb (fun l => cvgto s l) 0%e.

(* -------------------------------------------------------------------- *)
lemma limP (s : int -> ereal):
  cvg s <=> cvgto s (lim s).
proof. by split=> [/choicebP /(_ 0%e)|lims]; last exists (lim s). qed.

lemma lim_cnvto (s : int -> ereal) l:
  cvgto s l => lim s = l.
proof. by move=> ^h /cnvP /limP /uniq_cnvto; apply. qed.

lemma lim_Ncnv (s : int -> ereal):
  !cvg s => lim s = 0%e.
proof. by move=> h; apply/choiceb_dfl/negb_exists. qed.

lemma lim_eq (N : int) (s1 s2 : int -> ereal):
     (forall n, N <= n => s1 n = s2 n)
  => lim s1 = lim s2.
proof. move=> eq.
case: (cvg s1) => ^cv1; rewrite (@eq_cnv_fromP N _ s2) // => cv2;
  last by rewrite !lim_Ncnv.
apply/lim_cnvto; case: cv2 => [l2 ^c2 /lim_cnvto ->]; move: c2.
by apply/(@eq_cnvto_from N)=> n leNn; apply/eq_sym/eq.
qed.

lemma limC c : lim (fun _ => c) = c.
proof. apply/lim_cnvto/cvgtoC. qed.

lemma limZ c (s : int -> ereal) :
  lim (fun x => c%e * s x) = c%e * lim s.
proof.
case: (cvg s) => [ [l] ^/lim_cnvto <- h|].
+ by apply/lim_cnvto/cvgtoZ.
case: (c = 0%r) => [-> _ /=|nz_c ^h1].
+ by apply lim_cnvto; apply: cvgto_eq (cvgtoC 0%e) => [/= ? | ]; rewrite mul0e.
by rewrite -(@cnvZ_iff c) // => h2; rewrite !lim_Ncnv.
qed.

lemma limD (s1 s2 : int -> ereal) :
  add_def (lim s1) (lim s2) =>
  cvgto s1 (lim s1) => 
  cvgto s2 (lim s2) => 
  lim (fun x => s1 x + s2 x) = lim s1 + lim s2.
proof. by move=> ha h1 h2; have /lim_cnvto -> := cvgtoD _ _ _ _ ha h1 h2. qed.

lemma limN (s : int -> ereal) : lim (fun x => - s x) = - lim s.
proof. by rewrite -mulN1e -(limZ (-1%r)); apply (lim_eq 0) => /= ??; rewrite mulN1e. qed.

lemma limB (s1 s2 : int -> ereal) :
  add_def (lim s1) (-lim s2) =>
  cvgto s1 (lim s1) => 
  cvgto s2 (lim s2) => 
  lim (fun x => s1 x - s2 x) = lim s1 - lim s2.
proof. by move=> ha h1 h2; rewrite limD // limN // 1:-cvgtoN. qed.

lemma limM (s1 s2 : int -> ereal) :
  mul_def (lim s1) (lim s2) =>
  cvgto s1 (lim s1) => 
  cvgto s2 (lim s2) => 
  lim (fun x => s1 x * s2 x) = lim s1 * lim s2.
proof. by move=> hm h1 h2; have /lim_cnvto -> := cvgtoM _ _ _ _ hm h1 h2. qed.

lemma limV s : lim s <> 0%e => lim (fun n => inve (s n)) = inve (lim s).
proof.
move=> h; have hl: cvgto s (lim s).
+ by apply limP; case: (cvg s) => // /lim_Ncnv; rewrite h.
by have /lim_cnvto := cvgtoV _ _ h hl.
qed.

lemma lim_div (s1 s2: int -> ereal) : 
  (inve (lim s2) = 0%e => lim s1 <> #+oo /\ lim s1 <> #-oo) => lim s2 <> 0%e =>
  cvgto s1 (lim s1) => lim (fun x => s1 x / s2 x) = lim s1 / lim s2.
proof.
move=> hm hl2 h1.
have h2: cvgto s2 (lim s2).
+ by apply limP; case: (cvg s2) => // /lim_Ncnv; rewrite hl2.
by have /lim_cnvto:= cvgto_div _ _ _ _ hm hl2 h1 h2.
qed.


