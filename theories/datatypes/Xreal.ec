require import AllCore RealSeries List Distr StdBigop DBool DInterval.  
require Subtype Bigop.
import Bigreal Bigint.

(* -------------------------------------------------------------------- *)
(* Definition of R+                                                     *)

abstract theory MonoidD.
  clone include Monoid 
    rename "idm" as "zero"
    rename "iteropE" as "iteraddE". 

  op ( * ) : t -> t -> t.

  clone export Monoid as MulMonoid with 
    type t <- t,
    op ( + ) <- ( * )
    rename "idm" as "one"
    rename "add0m" as "mul1m"
    rename "addm0" as "mulm1"
    rename "add" as "mul"
    rename "iteropE" as "itermulE". 

  axiom one_neq0 : one <> zero.
  axiom mulmDl    : left_distributive ( * ) (+).

  lemma nosmt mulmACA: interchange ( * ) ( * ).
  proof. by move=> x y z t; rewrite -!mulmA (mulmCA y). qed.

  lemma nosmt mulmDr: right_distributive ( * ) (+).
  proof. by move=> x y z; rewrite mulmC mulmDl !(@mulmC _ x). qed.

  lemma nosmt addm0_simpl x : x + zero = x by apply addm0.
  lemma nosmt add0m_simpl x : zero + x = x by apply add0m.
  lemma nosmt mul1m_simpl x : one * x = x by apply mul1m.
  lemma nosmt mulm1_simpl x : x * one = x by apply mulm1.

  hint simplify addm0_simpl, add0m_simpl, mul1m_simpl, mulm1_simpl.

end MonoidD.

abstract theory MonoidDI.
  clone include MonoidD.
 
  axiom addmI: right_injective (+).

  lemma addIm: left_injective (+).
  proof. by move=> x y z; rewrite !(addmC _ x) => /addmI. qed.

  lemma nosmt mul0m: left_zero zero ( * ).
  proof. by move=> x; apply: (@addIm (one * x)); rewrite -mulmDl !add0m mul1m. qed.

  lemma nosmt mulm0: right_zero zero ( * ).
  proof. by move=> x; rewrite mulmC mul0m. qed.

  lemma nosmt mul0m_simpl x : zero * x = zero by apply mul0m.
  lemma nosmt mulm0_simpl x : x * zero = zero by apply mulm0.
  hint simplify mul0m_simpl, mulm0_simpl.

end MonoidDI.

theory Rp.

type realp.

clone include Subtype
  with type T <- real,
       type sT <- realp,
       pred P <- fun x => 0.0 <= x
   rename "insubd" as "of_real"
   rename "val" as "to_real".

abbrev (%r) = to_real.
abbrev (%rp) = of_real.

lemma to_realK_simpl (x:realp) : x%r%rp = x by apply: to_realKd.
hint simplify to_realK_simpl, of_realK.

lemma to_realP_simpl x : (0.0 <= x%r) = true by rewrite to_realP. 
hint simplify to_realP_simpl.

op ( + ) (x y : realp) = (x%r + y%r)%rp.

op ( * ) (x y : realp) = (x%r * y%r)%rp.

op inv (x : realp) = (inv x%r)%rp.

abbrev (/) (x y : realp) : realp = x * inv y.

abbrev (<=) (x y : realp) = x%r <= y%r.
abbrev (<) (x y : realp)  = x%r < y%r.

clone include MonoidDI with
   type t  <- realp,
   op zero <- of_real 0.0,
   op MulMonoid.one  <- of_real 1.0,
   op ( + ) <- Rp.( + ),
   op ( * ) <- Rp.( * )
proof * by smt(of_realK to_realP to_real_inj).

lemma to_realD (x y:realp) : (x + y)%r = x%r + y%r.
proof. smt (of_realK to_realP). qed.

lemma to_realM (x y:realp) : (x * y)%r = x%r * y%r.
proof. smt (of_realK to_realP). qed.

lemma to_realI x : (inv x)%r = inv x%r.
proof. smt (of_realK to_realP Real.invr0). qed.

hint simplify to_realD, to_realM, to_realI.

lemma of_realD x y : 0.0 <= x => 0.0 <= y => 
   (x + y)%rp = x%rp + y%rp.
proof. smt (of_realK to_realP). qed.

lemma of_realM x y : 0.0 <= x => 0.0 <= y => 
   (x * y)%rp = x%rp * y%rp.
proof. smt (of_realK to_realP). qed.

lemma to_realK_d ['a] (d : 'a distr) (e: 'a -> bool) : 
  (mu d e)%rp%r = mu d e.
proof. rewrite of_realK //. qed.

hint simplify to_realK_d.

end Rp.
export Rp.

(* -------------------------------------------------------------------- *)
(* Definition of R+oo *)

theory Rpbar.

type xreal = [rp of realp | oo].
abbrev (%xr) (x:real) = rp (of_real x).

theory IntNotation.
abbrev (%xr) (i:int)  = i%r%xr.
end IntNotation. export IntNotation.

theory BoolNotation.
abbrev (%xr) (b:bool)  = (b2r b)%xr.
end BoolNotation. export BoolNotation.

(* -------------------------------------------------------------------- *)
abbrev ('0) = 0.0%xr.
abbrev ('1) = 1.0%xr.

op xadd (x y : xreal) =
  with x = rp x, y = rp y => rp (x + y)
  with x = rp _, y = oo  => oo
  with x = oo , y = rp _ => oo
  with x = oo , y = oo  => oo.

op xmul (x y : xreal) =
  with x = rp x, y = rp y => rp (x * y)
  with x = rp _, y = oo  => oo
  with x = oo , y = rp _ => oo
  with x = oo , y = oo  => oo.

op xinv (x : xreal) = 
  with x = rp x => rp (inv x)
  with x = oo  => oo.  (* Does this make sense *)

abbrev ( + ) = xadd.
abbrev ( * ) = xmul.

abbrev (/) (x y : xreal) : xreal = x * xinv y.

op ( ** ) c x =
  if c = 0.0%rp then '0 else rp c * x. 

theory Notation.
abbrev ( ** ) (x:real) (z:xreal) = of_real x ** z.
end Notation. export Notation.

op to_real (x:xreal) = 
  with x = rp y => y%r
  with x = oo => 0.0.

op is_real (x:xreal) = 
  with x = rp _  => true
  with x = oo => false.

op is_oo (x:xreal) = 
  with x = rp _ => false
  with x = oo => true.

op xle (x y : xreal) = 
  with x = rp x, y = rp y => x <= y
  with x = rp _, y = oo  => true 
  with x = oo , y = rp _ => false
  with x = oo , y = oo  => true.

op xlt (x y : xreal) = 
  with x = rp x, y = rp y => x < y
  with x = rp _, y = oo  => true 
  with x = oo , y = rp _ => false
  with x = oo , y = oo  => false.

abbrev (<=) = xle.
abbrev (<) = xlt.

(* -------------------------------------------------------------- *)
clone include MonoidD with 
  type t <- xreal,
  op zero <- 0.0%xr,
  op MulMonoid.one  <- 1.0%xr,
  op ( + ) <- xadd,
  op ( * ) <- xmul
  proof *.
realize Axioms.addmA by move=> [x|] [y|] [z|] //=; apply Rp.addmA. 
realize Axioms.addmC by move=> [x|] [y|] //=; apply Rp.addmC.
realize Axioms.add0m by move=> [x|] //=; apply Rp.add0m.
realize MulMonoid.Axioms.mulmA by move=> [x|] [y|] [z|] //=; apply Rp.MulMonoid.mulmA.
realize MulMonoid.Axioms.mulmC by move=> [x|] [y|] //=; apply Rp.MulMonoid.mulmC.
realize MulMonoid.Axioms.mul1m by move=> [x|] //=; apply Rp.MulMonoid.mul0m.
realize one_neq0 by apply/negP => /(congr1 to_real).
realize mulmDl by move=> [x|] [y|] [z|] //=; apply Rp.mulmDl.

(* -------------------------------------------------------------- *)
lemma xaddxoo x : x + oo = oo.
proof. by case: x. qed.

lemma xaddoox x : oo + x = oo.
proof. by case: x. qed.

lemma xmulxoo x : x * oo = oo.
proof. by case: x. qed.

lemma xmuloox x : oo * x = oo.
proof. by case: x. qed.

hint simplify xaddxoo, xaddoox, xmulxoo, xmuloox.

(* -------------------------------------------------------------- *)

lemma smul0m x : 0%r ** x = '0.
proof. by rewrite /( ** ). qed.

lemma smul1m x : 1%r ** x = x.
proof. by rewrite /( ** ) one_neq0. qed.

hint simplify smul0m, smul1m.

lemma smulmDr x y z: x ** (y + z) = x ** y + x ** z. 
proof. by rewrite /( ** ); case: (x = of_real 0%r) => //= ?; apply mulmDr. qed.

lemma smulmCA d x y : d ** (rp x * y) = rp x * (d ** y).
proof. by rewrite /( ** ); case: (d = of_real 0.0) => //=; rewrite mulmCA. qed.

lemma smulmA d x y : d ** (x * rp y) = (d ** x) * rp y.
proof. by rewrite /( ** ); case: (d = of_real 0.0) => //=;rewrite mulmA. qed.

lemma smulmAC d x y : d ** (x * rp y) = rp y * (d ** x) .
proof. by rewrite mulmC smulmCA. qed.

lemma smulrp x y : x ** rp y =  rp (x * y).
proof. by rewrite /( ** ); case: (x = of_real 0.0). qed.
hint simplify smulrp.

(* -------------------------------------------------------------- *)
lemma xlexx x : x <= x.
proof. by case: x. qed.

lemma xlexoo x : x <= oo.
proof. by case: x. qed.

lemma xlexx_simpl x y : x = y => x <= y = true.
proof. by move=> ->; rewrite xlexx. qed.

lemma xlexoo_simpl x : x <= oo = true.
proof. by case: x. qed.

hint simplify xlexx_simpl, xlexoo_simpl.

lemma xltxx x : !x < x.
proof. by case: x. qed.

lemma xltxx_simpl x y : x = y => x < y = false.
proof. by move=> ->; rewrite xltxx. qed.

hint simplify xltxx_simpl.

lemma xle_add_r x y : x <= x + y.
proof. case: x y => [x|] [y|] //=; smt(@Rp). qed.

lemma xle_add_l x y : x <= y + x.
proof. rewrite addmC xle_add_r. qed.

lemma ler_add2r (x:realp) (y z : xreal) : y + rp x <= z + rp x <=> y <= z.
proof. case: z => // z; case: y => //= y; smt(@Rp). qed.

lemma ler_add2l (x:realp) (y z : xreal) : rp x + y <= rp x + z <=> y <= z.
proof. rewrite !(addmC (rp x)); apply ler_add2r. qed.

lemma ler_addr (x y z : xreal) : y <= z => y + x <= z + x.
proof. case x => // x /ler_add2r; apply. qed.

lemma ler_addl (x y z : xreal) : y <= z => x + y <= x + z.
proof. case x => // x /ler_add2l; apply. qed.

lemma le_trans (y x z : xreal) : x <= y => y <= z => x <= z.
proof.
  case: z => // z; case: y => // y; case: x => //=; smt(@Rp).
qed.

lemma ler_add (x y z t : xreal) : x <= y => z <= t => x + z <= y + t.
proof. by move=> /(ler_addr z) h1 /(ler_addl y); apply le_trans. qed.

(* -------------------------------------------------------------- *)

lemma is_real_le x y : x <= y => is_real y => is_real x.
proof. by case: x y => [x|] [y|]. qed.

lemma is_realZ p x : is_real (rp p * x) = is_real x.
proof. by case: x. qed.

lemma is_realD x y : is_real (x + y) <=> is_real x /\ is_real y.
proof. by case: x y => [x|] [y|]. qed.

lemma is_realM x y : is_real (x * y) <=> is_real x /\ is_real y.
proof. by case: x y => [x|] [y|]. qed.

lemma to_realP x : 0.0 <= to_real x.
proof. case: x => //=; apply to_realP. qed.

lemma to_realD (x y : xreal) : 
  is_real x => is_real y =>
  to_real (x + y) = to_real x + to_real y.
proof. by case: x y => [x|] [y|]. qed.

lemma to_realM (x y : xreal) : 
  to_real (x * y) = to_real x * to_real y.
proof. by case: x y => [x|] [y|]. qed.

end Rpbar. export Rpbar.

theory Lift.

  abbrev ( + ) (f1 f2 : 'a -> xreal) = 
    fun (x : 'a) => f1 x + f2 x.

  abbrev ( * ) (f1 f2 : 'a -> xreal) = 
    fun (x : 'a) => f1 x * f2 x.

  abbrev ( ** ) (d : 'a distr) (f : 'a -> xreal) =
    fun (x : 'a) => of_real (mu1 d x) ** f x.

  op is_real ['a] (f : 'a -> xreal) = 
    forall x, is_real (f x).

  op to_real ['a] (f : 'a -> xreal) = 
    fun x => to_real (f x).

  lemma eq_is_real ['a] (f g : 'a -> xreal) :
    (forall (x : 'a), f x = g x) => 
    is_real f = is_real g.
  proof. move=> h; congr; apply/fun_ext/h. qed.

  lemma eq_to_real ['a] (f g : 'a -> xreal) : 
    (forall (x : 'a), f x = g x) => 
    to_real f = to_real g.
  proof. move=> h; congr; apply/fun_ext/h. qed.

  lemma eq_md ['a] (d : 'a distr) (f g : 'a -> xreal) :
    (forall (x : 'a), x \in d => f x = g x) => 
    d ** f = d ** g.
  proof. move=> h; apply/fun_ext => x; smt(ge0_mu). qed.

  lemma eq_is_real_md ['a] (d : 'a distr) (f g : 'a -> xreal) :
    (forall (x : 'a), x \in d => f x = g x) => 
    is_real (d ** f) = is_real (d ** g).
  proof. by move=> /eq_md ->. qed.

  lemma eq_to_real_md ['a] (d : 'a distr) (f g : 'a -> xreal) : 
    (forall (x : 'a), x \in d => f x = g x) => 
    to_real (d ** f) = to_real (d ** g).
  proof. by move=> /eq_md ->. qed.
  
  lemma mdDr ['a] : right_distributive Lift.( ** )<:'a> Lift.( + ).
  proof. by move=> d f1 f2; apply fun_ext => x; apply smulmDr. qed.

  lemma mdCA ['a] (d : 'a distr) x f : d ** (fun z => rp x * f z) = fun z => rp x * (d ** f) z.
  proof. by apply fun_ext => z; rewrite smulmCA. qed.

  lemma mdA ['a] (d : 'a distr) f y : d ** (fun z => f z * rp y) = fun z => (d ** f) z * rp y.
  proof. by apply fun_ext => z; rewrite smulmA. qed.

  lemma mdAC ['a] (d : 'a distr) f y : d ** (fun z => f z * rp y) = fun z => rp y * (d ** f) z.
  proof. by apply fun_ext => z; rewrite smulmAC. qed.

  lemma is_realZ ['a] c (f : 'a -> xreal) : is_real (fun x => rp c * f x) <=> is_real f.
  proof. by split => h x; have := h x; rewrite is_realZ. qed.

  lemma is_realD ['a] (f1 f2 : 'a -> xreal) :
    is_real (f1 + f2) <=> (is_real f1 /\ is_real f2).
  proof.
    rewrite /is_real; split.
    + by move=> h; split => x; have /is_realD := h x.
    by move=> [h1 h2] x; apply /is_realD; move: (h1 x) (h2 x).
  qed.

  lemma is_realM ['a] (f1 f2 : 'a -> xreal) :
    is_real (f1 * f2) <=> (is_real f1 /\ is_real f2).
  proof.
    rewrite /is_real; split.
    + by move=> h; split => x; have /is_realM := h x.
    by move=> [h1 h2] x; apply /is_realM; move: (h1 x) (h2 x).
  qed.

  lemma is_realMd (f2 f1 : 'a -> xreal) (d : 'a distr) : 
    (forall x, x \in d => is_real (f1 x) = is_real (f2 x)) => 
    is_real (d ** f1) <=> is_real (d ** f2).
  proof.
    move=> h; split => h1 x; have := h1 x; rewrite /( ** );
    case: (of_real (mu1 d x) = of_real 0.0) => // ?; rewrite !is_realM h //; smt(mu_bounded).
  qed.

  lemma is_real_rp ['a] (f:'a -> realp) : is_real (fun x => rp (f x)).
  proof. done. qed.

  lemma is_real_sM ['a] (d : 'a  distr) f : 
    is_real (d ** f) <=> forall x, x \in d => is_real (f x).
  proof. split => h x; have := h x; smt (mu_bounded @Rp). qed.

  lemma to_real_rp ['a] (f:'a -> realp) : to_real (fun x => rp (f x)) = fun x => to_real (f x).
  proof. by apply fun_ext. qed.

  lemma to_realZ ['a] c (f: 'a  -> xreal) : 
    to_real (fun x => rp c * f x) = fun x => to_real c * to_real (f x).
  proof. by apply fun_ext => x; rewrite /to_real /= to_realM. qed.

  lemma to_realD ['a] (f g : 'a -> xreal) : 
    is_real f => is_real g =>
    to_real (f + g) = fun x => to_real (f x) + to_real (g x).
  proof.
    rewrite /to_real; move=> h1 h2; apply fun_ext => ?.
    apply to_realD; [apply h1 | apply h2]. 
  qed.

  lemma to_realM ['a] (f g : 'a -> xreal) : 
    to_real (f * g) = fun x => to_real (f x) * to_real (g x).
  proof. rewrite /to_real; apply fun_ext => ?; apply to_realM. qed.

end Lift. export Lift.

clone import Bigop as BXA with
  type t <= xreal,
  op Support.idm <- Rpbar.('0),
  op Support.(+) <- Rpbar.xadd,
  theory Support.Axioms <- Rpbar.Axioms.

lemma is_real_bigRX ['a] (f : 'a -> xreal) l: 
  is_real f => 
  (BRA.big predT (to_real f) l)%xr = big predT f l.
proof.
  move=> hf; elim: l => //= x l hrec.
  rewrite big_cons BRA.big_cons /predT /= -hrec /to_real.
  have := hf x; case: (f x) => //= z.
  by rewrite of_realD // sumr_ge0 /= => a; apply to_realP.
qed.

lemma bigR_to_real ['a] (f : 'a -> real) (l : 'a list) : 
  (forall a, a \in l => 0%r <= f a) =>
   BRA.big predT (to_real (fun a => (f a)%xr)) l = BRA.big predT f l.
proof.
  move=> hpos; apply BRA.eq_big_seq; rewrite /to_real => x /hpos; smt(@Rp).
qed.

lemma bigXR ['a] (f : 'a -> real) (l : 'a list) : 
  (forall a, a \in l => 0%r <= f a) =>
  big predT (fun x => (f x)%xr) l = (BRA.big predT f l)%xr.
proof. by move=> hpos; rewrite -is_real_bigRX 1:// bigR_to_real. qed.

lemma bigXI ['a] (f : 'a -> int) (l : 'a list) : 
  (forall a, a \in l => 0 <= f a) =>
  big predT (fun x => (f x)%xr) l = (BIA.big predT f l)%xr.
proof. by move=> h; rewrite bigXR 1:/# sumr_ofint. qed.

lemma bigiXR (f : int -> real) (m n : int) : 
  (forall i, m <= i < n => 0%r <= f i) =>
  bigi predT (fun x => (f x)%xr) m n = (BRA.bigi predT f m n)%xr.
proof. move=> hpos; apply bigXR => i /mem_range; apply hpos. qed.

lemma bigiXI (f : int -> int) (m n : int) : 
  (forall i, m <= i < n => 0 <= f i) =>
  bigi predT (fun x => (f x)%xr) m n = (BIA.bigi predT f m n)%xr.
proof. move=> hpos; apply bigXI => i /mem_range; apply hpos. qed.

lemma big_oo ['a] (J : 'a list) (f : 'a -> xreal) : 
  (exists (x : 'a), (x \in J) /\ f x = oo) => 
  big predT f J = oo.
proof.
  move=> [x [hj hf]]; rewrite (bigID _ _ (pred1 x)) -big_filter predTI filter_pred1.
  have [n [hn ->]]: exists n, 0 <= n /\ count (pred1 x) J = n + 1.
  + have [+ _]:= has_count (pred1 x) J; rewrite hasP; smt().
  by rewrite nseqS // big_cons /predT hf.
qed.

lemma mulr_sumr ['a] (P : 'a -> bool) (F : 'a -> xreal) (s : 'a list) (x : realp) : 
  x ** (big P F s) = (big P (fun (i : 'a) => x ** F i) s).
proof. apply (big_comp (fun y => x ** y)) => //=; apply smulmDr. qed.


(* -------------------------------------------------------------------- *)

op psuminf ['a] (f : 'a -> xreal) =
  if summable (to_real f) then (sum (to_real f))%xr else oo.

op Ep ['a] (d : 'a distr) (f : 'a -> xreal) =
  let g = d ** f in
  if is_real g then psuminf g else oo.

lemma psuminfZ ['a] (c:realp) (f: 'a -> xreal) :
  is_real f => c <> of_real 0.0 =>
  psuminf (fun x => rp c * f x) = rp c * psuminf f.
proof.
  move=> hf hc; have heq := summableZ_iff (to_real f) (to_real c) _; 1:smt(@Rp).
  rewrite /psuminf to_realZ -heq. 
  case: (summable (to_real f)) => // hs.
  rewrite sumZ of_realM //.
  by apply ge0_sum => /= x; apply to_realP.
qed.

lemma psumifD (f1 f2 : 'a -> xreal) : 
  is_real f1 => is_real f2 => 
  psuminf (fun x => f1 x + f2 x) = psuminf f1 + psuminf f2.
proof.
  move=> h1 h2; rewrite /psuminf; rewrite to_realD //.
  case: (summable (fun (x : 'a) => to_real (f1 x) + to_real (f2 x))) => hs.
  + have hs1 := summable_le _ (to_real f1) hs _; 1: smt(Rpbar.to_realP).
    have hs2 := summable_le _ (to_real f2) hs _; 1: smt(Rpbar.to_realP).
    by rewrite hs1 hs2 /= sumD // of_realD //; apply ge0_sum => x /=; apply to_realP.
  by case: (summable (to_real f1)); case (summable (to_real f2)) => // hs1 hs2 /=; apply/hs/summableD.
qed.

lemma eq_Ep ['a] (d : 'a distr) (f g : 'a -> xreal) :
  (forall (x : 'a), x \in d => f x = g x) => 
  Ep d f = Ep d g.
proof. by rewrite /Ep /= => /eq_md ->. qed.

lemma EpC ['a] (d : 'a distr) (c : realp):
   Ep d (fun (_ : 'a) => rp c) = rp (c * of_real (weight d)).
proof.
  rewrite /Ep /= is_real_rp /=. 
  rewrite /psuminf /= to_real_rp /=.
  have -> : (fun (x : 'a) => mu1 d x * to_real c) = (fun (x : 'a) => to_real c * mu1 d x ).
  + by apply fun_ext => x; apply RField.mulrC.
  have /summableZ /= -> /= := summable_mu1 d.
  rewrite sumZ /= of_realM // 1: ge0_sum //= weightE; do 3! congr.
qed.

lemma EpZ ['a] (d: 'a distr) (c:realp) (f: 'a -> xreal) :
  c <> of_real 0.0 => 
  Ep d (fun x => rp c * f x) = rp c * Ep d f.
proof. 
  move=> hc; rewrite /Ep /= (is_realMd f); 1: by move=> x _ /=; rewrite is_realM. 
  case: (is_real (d ** f)) => // hr; rewrite /psuminf.
  rewrite mdCA /= to_realM /=.
  rewrite -summableZ_iff 1:#smt:(@Rp); rewrite /to_real.
  case: (summable (fun (x : 'a) => to_real (of_real (mu1 d x) ** f x))) => // ?.
  rewrite sumZ /= of_realM // ge0_sum => /= ?; apply to_realP.
qed.

lemma EpsZ ['a] (d: 'a distr) (c:realp) (f: 'a -> xreal) :
  Ep d (fun x => c ** f x) = c ** Ep d f.
proof. 
  rewrite /( ** ); case: (c = of_real 0%r) => ?; last by apply EpZ.
  by rewrite EpC.
qed.

lemma EpD ['a] (d : 'a distr) (f1 f2 : 'a -> xreal) : 
  Ep d (f1 + f2) = Ep d f1 + Ep d f2.
proof.
  rewrite /Ep /= mdDr.
  have /= := is_realD (d ** f1) (d ** f2).
  case: (is_real (fun x => of_real (mu1 d x) ** f1 x + of_real (mu1 d x) ** f2 x)) => h />.
  + by move=> h1 h2; rewrite -psumifD.
  by case: (is_real (d ** f1)) => />.
qed.

(* -------------------------------------------------------------------- *)
lemma Ep_fin ['a] J (d : 'a distr) f : 
  uniq J => 
  (forall (x : 'a), mu1 d x <> 0%r => x \in J) =>
  Ep d f = big predT (d ** f) J.
proof.
  move=> hu hJ; rewrite /Ep /=.
  case: (is_real (d ** f)) => his.
  + have hJ' : forall (x : 'a), to_real (d ** f) x <> 0%r => x \in J.
    + by rewrite /to_real /( ** )=> x; case: (of_real (mu1 d x) = of_real 0.0) => //; smt(@Rp).
    by rewrite  /psuminf (summable_fin _ J hJ') /= (sumE_fin _ J hu hJ') is_real_bigRX.
  rewrite big_oo //.
  move/negb_forall: his => /> x hx; exists x.
  move: hx; case _: (mu1 d x ** f x) => //=.
  rewrite /( ** ); case: (of_real (mu1 d x) = of_real 0.0) => //=; smt(@Rp).
qed.

(* -------------------------------------------------------------------- *)
lemma Ep_dnull ['a] f : Ep dnull<:'a> f = Rpbar.('0).
proof. by rewrite (Ep_fin []) // => x; rewrite dnull1E. qed.

(* -------------------------------------------------------------------- *)
lemma Ep_dunit ['a] (x : 'a) f : Ep (dunit x) f = f x.
proof. 
  rewrite (Ep_fin [x]) //; 1: by move=> x'; rewrite dunit1E /#.
  by rewrite big_seq1 /( ** ) /= dunit1E /= one_neq0.
qed.

(* -------------------------------------------------------------------- *)
lemma Ep_duniform ['a] (s : 'a list) (f : 'a -> xreal) :
  Ep (duniform s) f =
    of_real (1%r / (size ((undup s)))%r) ** big predT f (undup s).
proof.
  rewrite (Ep_fin (undup s)) 1:undup_uniq.
  + move=> x hx; rewrite mem_undup -supp_duniform; smt(ge0_mu).
  rewrite mulr_sumr; apply eq_big_seq => //= x; rewrite mem_undup => hx.
  by rewrite duniform1E hx.
qed.

(* -------------------------------------------------------------------- *)
lemma Ep_dbool (f : bool -> xreal) :
  Ep {0,1} f = of_real 0.5 ** f true + of_real 0.5 ** f false.
proof.
  rewrite (Ep_fin [true; false]) //; 1: smt(supp_dbool).
  by rewrite big_consT big_seq1 /= !dbool1E.
qed.

(* -------------------------------------------------------------------- *)
lemma Ep_dinterval (f : int -> xreal) i j:
  Ep [i..j] f = 
    (if i <= j then 1%r / (j - i + 1)%r else 0%r) ** 
       big predT f (range i (j + 1)).
proof.
  rewrite (Ep_fin (range i (j + 1))) 1:range_uniq. 
  + by move=> x; have := supp_dinter i j x; rewrite mem_range; smt (ge0_mu).
  rewrite mulr_sumr; apply eq_big_seq => x /mem_range hx /=.
  rewrite dinter1E /#.   
qed.

lemma Ep_dinterval_le (f : int -> xreal) (i j : int) :
  i <= j => 
  Ep [i..j] f = (1%r / (j - i + 1)%r) ** big predT f (range i (j + 1)).
proof. by move=> h; rewrite Ep_dinterval h. qed.

(* -------------------------------------------------------------------- *)
op (`|`) (b:bool) (x : xreal) = 
   if b then x else oo.

lemma xle_interp_form b1 b2 (f1 f2 : xreal): 
  (b2 => (b1 /\ f1 <= f2)) => 
  xle (b1 `|` f1) (b2 `|` f2).
proof. by rewrite /(`|`); case: b2 => />. qed.

lemma xle_interp_form_b b1 b2 f : 
   (b1 => b2) =>
   b2 `|` f <= b1 `|` f.
proof. by move=> h; apply xle_interp_form. qed.

lemma xle_interp_form_f b (f1 f2 : xreal) : 
   (b => f1 <= f2) =>
   b `|` f1 <= b `|` f2.
proof. by move=> h;apply xle_interp_form => />. qed.

(* TODO: move this *)
lemma Rp_to_real_eq (x y : realp) : (x = y) <=> (to_real x = to_real y).
proof. smt(to_realKd). qed.

(* -------------------------------------------------------------------- *)
lemma Ep_interp_form (d:'a distr) (b:'a -> bool) (f:'a -> xreal) : 
  Ep d (fun x => b x `|` f x) = 
  (forall x, x \in d => b x) `|` Ep d f. 
proof.
  rewrite /Ep /(`|`) /=. 
  case: (forall (x : 'a), x \in d => b x) => hb; last first. 
  + have /> x xin xb: exists x, x \in d /\ !b x by smt().
    have -> // : !is_real (fun (x0 : 'a) => mu1 d x0 ** if b x0 then f x0 else oo). 
    rewrite /is_real; apply /negP => h.
    by have := h x; rewrite xb /= /( ** ) /= Rp_to_real_eq /= /#.
  rewrite (eq_is_real_md _ _ f).
  + by move=> x /hb /= ->.
  case: (is_real (d ** f)) => // _; congr; apply fun_ext => x.
  rewrite /( **) Rp_to_real_eq /=; smt(ge0_mu1).
qed.

lemma if_interp_form (b b1 b2:bool) (f1 f2: xreal) : 
  (if b then (b1 `|` f1) else (b2 `|` f2)) = 
  (if b then b1 else b2) `|` if b then f1 else f2.
proof. smt(). qed.

lemma if_interp_forml (b b1:bool) (f1 f2: xreal) : 
  (if b then (b1 `|` f1) else f2) = 
  (b => b1) `|` if b then f1 else f2
by smt().

lemma if_interp_formr (b b2:bool) (f1 f2: xreal) : 
  (if b then f1 else (b2 `|` f2) ) = 
  (!b => b2) `|` if b then f1 else f2
by smt().

lemma intern_form_true x : true `|` x = x
by done.


