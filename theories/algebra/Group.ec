(* -------------------------------------------------------------------- *)
require import AllCore List IntExtra IntMin IntDiv.
require (*--*) FinType Ring Number StdOrder.

import Ring.IntID StdOrder.IntOrder.

(* ==================================================================== *)
op gcd : int -> int -> int.

lemma gcdP a b :
     gcd a b %| a
  /\ gcd a b %| b
  /\ (forall z, z %| a => z %| b => z %| gcd a b).
proof. admitted.

lemma gcd_uniq a b z : ! (a = 0 /\ b = 0) =>
     0 <= z => z %| a => z %| b
  => (forall x, x %| a => x %| b => x %| z)
  => z = gcd a b.
proof. admitted.

lemma gcd0z a : gcd 0 a = `|a|.
proof. admitted.

lemma Bachet_Bezout (a b : int) :
  exists u v, u * a + v * b = gcd a b.
proof.
case: (a = 0) => [->/=|nz_a].
+ by exists (signz b); rewrite gcd0z signVzE.
pose E d := 0 < d /\ exists u v, d = u * a + v * b.
have nzE: !empty (pcap E).
+ apply/emptyNP; exists `|a| => @/E @/pcap /=.
 rewrite normr_ge0 normr_gt0 nz_a /=.
  by exists (signz a) 0 => /=; apply: signVzE.
case: (pmin_mem _ nzE); (pose d0 := pmin E) => gt0_d [a0 b0] d0E.
exists a0 b0; apply: gcd_uniq; rewrite ?nz_a // -?d0E.
+ by rewrite ltrW.
+ rewrite eqr_le modz_ge0 1:gtr_eqF //= lerNgt; apply/negP.
  move=> gt0_ad0; have: E (a %% d0); 1: move=> @/E.
  * rewrite gt0_ad0 /=; rewrite modzE {2}d0E.
    rewrite mulrDr opprD addrA !mulrA -{1}(mul1r a) -mulrBl.
    move: (1 - _)%Int => u; move: (_ %/ _ * _)%Int => v.
    by exists u (-v); rewrite mulNr.
  move=> Ead0; have := pmin_min _ _ nzE _ Ead0.
  * by rewrite ltrW. * by rewrite lerNgt /= ltz_pmod.
+ rewrite eqr_le modz_ge0 1:gtr_eqF //= lerNgt; apply/negP.
  move=> gt0_bd0; have: E (b %% d0); 1: move=> @/E.
  * rewrite gt0_bd0 /=; rewrite modzE {2}d0E.
    rewrite mulrDr opprD !addrA !mulrA -addrAC -{1}(mul1r b) -mulrBl.
    move: (1 - _)%Int => u; move: (_ %/ _ * _)%Int => v.
    by exists (-v) u; rewrite mulNr addrC.
  move=> Ebd0; have := pmin_min _ _ nzE _ Ebd0.
  * by rewrite ltrW. * by rewrite lerNgt /= ltz_pmod.
+ by move=> z za zb; rewrite d0E &(dvdzD) dvdz_mull.
qed.

(* ==================================================================== *)
abstract theory Group.
type group.

(* -------------------------------------------------------------------- *)
op e     : group.
op ( * ) : group -> group -> group.
op inv   : group -> group.

abbrev ( / ) x y = x * inv y.

axiom mul1c : left_id e ( * ).
axiom mulc1 : right_id e ( * ).
axiom mulcA : associative ( * ).
axiom mulVc : left_inverse e inv ( * ).
axiom mulcV : right_inverse e inv ( * ).

(* -------------------------------------------------------------------- *)
lemma mulcI : right_injective ( * ).
proof.
move=> x y z /(congr1 (( * ) (inv x))).
by rewrite !mulcA mulVc !mul1c.
qed.

lemma mulIc : left_injective ( * ).
proof.
move=> x y z /(congr1 (fun y => y / x)) /=.
by rewrite -!mulcA mulcV !mulc1.
qed.

lemma invM x y : inv (x * y) = inv y * inv x.
proof.
rewrite &(mulcI (x * y)) mulcV eq_sym.
by rewrite mulcA -(mulcA x) mulcV mulc1 mulcV.
qed.

lemma invc1 : inv e = e.
proof. by rewrite &(mulIc e) mulVc mulc1. qed.

lemma invK : involutive inv.
proof.
by move=> x; apply: (mulcI (inv x)); rewrite mulVc mulcV.
qed.

lemma inv_inj : injective inv.
proof. by apply/inv_inj/invK. qed.

(* -------------------------------------------------------------------- *)
op ( ^+ ) x k = iter `|k|%Int (fun y => y * x) e.
op ( ^  ) x k = if k < 0 then inv (x ^+ k) else x ^+ k.

(* -------------------------------------------------------------------- *)
op (\com) (x y : group) = x * y = y * x.

lemma com_refl (x : group) : x \com x.
proof. by []. qed.

lemma com_sym : commutative (\com).
proof. by move=> x y @/(\com); rewrite (eq_sym (x * y)). qed.

lemma com1 x : x \com e.
proof. by rewrite /(\com) mulc1 mul1c. qed.

lemma comMr x y z : x \com y => x \com z => x \com (y * z).
proof.
by move=> xCy xCz @/(\com); rewrite -mulcA -xCz !mulcA xCy.
qed.

lemma comVr x y : x \com y => x \com inv y.
proof.
move=> xCy @/(\com); rewrite &(mulcI y) !mulcA.
by rewrite -xCy mulcV mul1c -mulcA mulcV mulc1.
qed.

lemma comXr x y k : x \com y => x \com (y ^+ k).
proof.
move=> xCy @/(^+); elim: `|k| (normr_ge0 k) => {k} [|k ge0_k ih].
+ by rewrite iter0 // com1.
+ by rewrite iterS //= comMr.
qed.

lemma comXzr x y k : x \com y => x \com (y ^ k).
proof.
move=> xCy @/(^); case: (k < 0) => _.
+ by apply/comVr/comXr.
+ by apply/comXr.
qed.

(* -------------------------------------------------------------------- *)
lemma expp0 x : x ^+ 0 = e.
proof. by rewrite /(^+) normr0 iter0. qed.

lemma expp1 x : x ^+ 1 = x.
proof. by rewrite /(^+) normr1 iter1 /= mul1c. qed.

lemma exppN x (k : int) : x ^+ (-k) = x ^+ k.
proof. by rewrite /(^+) normrN. qed.

lemma expp_abs x (k : int) : x ^+ `|k| = x ^+ k.
proof. by rewrite /(^+) normr_id. qed.

lemma exppS x (k : int) : 0 <= k => x ^+ (k + 1) = x ^+ k * x.
proof.
by move=> ge0_k; rewrite /(^+) !ger0_norm 1,2://# iterS.
qed.

lemma exppSN x (k : int) : k < 0 => x ^+ (k + 1) = x ^+ k / x.
proof.
move=> lt0_k; rewrite -(exppN _ k) (_ : -k = -(k+1) + 1) 1:/#.
by rewrite eq_sym exppS 1:/# exppN -mulcA mulcV mulc1.
qed.

lemma exppD x (k1 k2 : int) :
  0 <= k1 => 0 <= k2 => x ^+ (k1 + k2) = x ^+ k1 * x ^+ k2.
proof.
move=> ge0_k1; elim: k2 => /= [|k2 ge0_k2 ih].
+ by rewrite expp0 mulc1.
by rewrite addrA !exppS 1,2://# ih mulcA.
qed.

lemma exppD_sign x (k1 k2 : int) : 0 <= k1 * k2 =>
  x ^+ (k1 + k2) = x ^+ k1 * x ^+ k2.
proof. move=> ge0M; case: (0 <= k1).
+ rewrite ler_eqVlt => -[<<-/=|]; 1: by rewrite expp0 mul1c.
  move=> gt0_k1; move: ge0M; rewrite pmulr_rge0 //.
  by move=> ge0_k2; rewrite exppD 1:ltrW.
+ move/ltrNge=> lt0_k1; move: ge0M; rewrite nmulr_rge0 //.
  move=> le0_k2; rewrite -(opprK (k1 + k2)) exppN.
  by rewrite opprD exppD 1,2:/# !exppN.
qed.

lemma exppcM_com x y k : x \com y =>
  (x * y) ^+ k = (x ^+ k) * (y ^+ k).
proof.
move=> xCy. rewrite -!(expp_abs _ k).
elim: `|k| (normr_ge0 k) => {k} [|k ge0_k ih].
+ by rewrite !expp0 mulc1.
+ rewrite exppS // ih !exppS // !mulcA; congr.
  by rewrite -!mulcA; congr; rewrite comXr.
qed.

lemma exppcV x k : (inv x) ^+ k = inv (x ^+ k).
proof.
rewrite -!(expp_abs _ k); elim: `|k| (normr_ge0 k) => {k} [|k ge0_k ih].
+ by rewrite !iter0 // invc1.
+ by rewrite !exppS // invM ih comVr // com_sym comVr comXr.
qed.

lemma exp0 x : x ^ 0 = e.
proof. by rewrite /(^) expp0. qed.

lemma exp1 x : x ^ 1 = x.
proof. by rewrite /(^) expp1. qed.

lemma expN x (k : int) : x ^ (- k) = inv (x ^ k).
proof.
case: (k = 0) => [->/=|nz_k]; 1: by rewrite exp0 invc1.
rewrite /(^) /(^+) /= normrN ltr_neqAle oppr_eq0 nz_k /= oppr_le0.
by rewrite (fun_if inv) invK lerNgt if_neg.
qed.

lemma expE_ge0 x (k : int) : 0 <= k => x ^ k = x ^+ k.
proof. by rewrite /(^) ltrNge => ->. qed.

lemma expE_le0 x (k : int) : k <= 0 => x ^ k = inv (x ^+ k).
proof.
by rewrite ler_eqVlt => -[->|@/(^) ->/=]; 1: rewrite exp0 invc1.
qed.

lemma expS x k : x ^ (k + 1) = x ^ k * x.
proof.
case: (0 <= k) => [ge0_k|].
+ by rewrite !expE_ge0 1,2://# exppD // expp1.
move=> /ltrNge /= lt0_k; rewrite !expE_le0 1,2://#.
case: (k = -1) => [->/=|ne_k_N1] .
+ by rewrite expp0 -expp_abs normrN1 expp1 invc1 mulVc.
by rewrite -!exppcV exppSN // invK.
qed.

lemma expcV x k : (inv x) ^ k = inv (x ^ k).
proof.
by rewrite /(^) (fun_if inv) !invK -!exppcV invK.
qed.

lemma expcM_com x y k : x \com y => (x * y) ^ k = x ^ k * y ^ k.
proof.
move=> xCy @/(^); case: (k < 0) => _; 2: by rewrite exppcM_com.
rewrite exppcM_com // invM comVr // com_sym.
by rewrite comVr comXr com_sym comXr com_sym.
qed.

lemma expD x (k1 k2 : int) : x ^ (k1 + k2) = x ^ k1 * x ^ k2.
proof.
wlog: k1 k2 / 0 <= k2 => [wlog|].
+ case: (leVge 0 k2) => [|le0_k2]; first by apply: wlog.
  rewrite -(opprK (k1 + k2)) expN opprD wlog 1:oppr_ge0 //.
  by rewrite !expN invM !invK comXzr // com_sym comXzr com_refl.
elim: k2 => /= [|k2 ge0_k2 ih]; first by rewrite exp0 mulc1.
by rewrite addrA !expS mulcA -ih.
qed.

lemma expc1 k : e ^ k = e.
proof.
elim/intswlog: k => [ih i lt0_i| |i ge0_i ih].
+ by rewrite -opprK expN ih 1:2!(oppr_ge0, ltrW) // invc1.
+ by rewrite exp0.
+ by rewrite expS ih mulc1.
qed.

lemma expB x (k1 k2 : int) : x ^ (k1 - k2) = x ^ k1 / x ^ k2.
proof. by rewrite expD expN. qed.

lemma expM x (k1 k2 : int) : x ^ (k1 * k2) = (x ^ k1) ^ k2.
proof.
elim/intwlog: k2 => [i| |i ge0_i ih].
+ by rewrite !mulrN !expN => /inv_inj.
+ by rewrite mulr0 !exp0.
+ by rewrite mulrDr /= !expD exp1 ih.
qed.
end Group.

(* ==================================================================== *)
abstract theory ComGroup.
type group.

op e     : group.
op ( * ) : group -> group -> group.
op inv   : group -> group.

axiom mulcC : commutative ( * ).

clone include Group
  with type group <- group,
         op e     <- e    ,
         op ( * ) <- ( * ),
         op inv   <- inv  
  proof mulc1, mulcV
  rename "invM" as "invM_com".

realize mulc1 by move=> x; rewrite mulcC mul1c.
realize mulcV by move=> x; rewrite mulcC mulVc.

(* -------------------------------------------------------------------- *)
lemma invM x y : inv (x * y) = inv x * inv y.
proof. by rewrite invM_com mulcC. qed.

(* -------------------------------------------------------------------- *)
lemma expcpM x y k : (x * y) ^+ k = x ^+ k * y ^+ k.
proof. by apply/exppcM_com/mulcC. qed.

(* -------------------------------------------------------------------- *)
lemma expcM x y k : (x * y) ^ k = x ^ k * y ^ k.
proof. by apply/expcM_com/mulcC. qed.
end ComGroup.

(* ==================================================================== *)
abstract theory CyclicGroup.

type group.

(* -------------------------------------------------------------------- *)
clone include FinType
  with type t <- group
  rename "card" as "order"
  rename "enum" as "elems".

(* -------------------------------------------------------------------- *)
(* FIXME: add a mechanism to add the generator during the clone         *)
(*        s.t. mulcC is provable (see below)                            *)
clone include ComGroup
  with type group <- group
  rename "mulcC" as "mulcC_com".

(* -------------------------------------------------------------------- *)
op g : group.

axiom monogenous : forall x, exists k, x = g ^ k.

(* -------------------------------------------------------------------- *)
lemma mulcC : commutative ( * ).
proof.
move=> x y; move: (monogenous x) (monogenous y).
by move=> [kx ->] [ky ->]; rewrite -!expD addrC.
qed.

(* -------------------------------------------------------------------- *)
op log_spec (x : group) =
  fun k => 0 <= k < order /\ g ^ k = x.

op log (x : group) = choiceb (log_spec x) 0.

lemma gt0_order : 0 < order.
proof.
rewrite /order ltr_neqAle size_ge0 /= eq_sym size_eq0.
by apply/negP=> z_elems; have := elemsP g; rewrite z_elems.
qed.

lemma ge0_order : 0 <= order.
proof. by apply/ltrW/gt0_order. qed.

(* -------------------------------------------------------------------- *)
lemma uniq_cg : uniq (map (fun i => g ^ i) (range 0 order)).
proof.
have nz: forall k, 1 <= k < order => g ^ k <> e.
+ move=> k rg_k; apply/negP=> u_gk; have gt0_: 0 < k by smt().
  have mg: forall x, exists l, 0 <= l < k /\ x = g ^ l.
  * move=> x; case: (monogenous x)=> l ->; exists (l %% k).
    rewrite modz_ge0 1:gtr_eqF //= ltz_pmod //=.
    by rewrite {1}(@divz_eq l k) expD mulrC expM u_gk expc1 mul1c.
  have: perm_eq elems (undup (map (fun i => g ^ i) (range 0 k))).
  * rewrite &(uniq_perm_eq) ?(undup_uniq, elems_uniq).
    move=> x; rewrite elemsP /= mem_undup; apply/mapP.
    by case: (mg x)=> l mg_x; exists l; rewrite mem_range.
  move/perm_eq_size; rewrite -/order => orderE.
  rewrite -(@ltrr order) {1}orderE (ler_lt_trans _ _ _ (size_undup _)).
  by rewrite size_map size_range /= max_ler 1:ltrW /=; case: rg_k.
rewrite map_inj_in_uniq 2:range_uniq => /= i j.
wlog: i j / i <= j => [wlog rgi rgj|le_ij].
+ case: (leVge i j) => [le_ij|le_ji]; first by apply: wlog.
  by rewrite eq_sym (eq_sym i j) &(wlog).
rewrite !mem_range => rgi rgj; case/ler_eqVlt: le_ij => //.
move=> lt_ij /(congr1 (fun x => x / g ^ i)) /=.
by rewrite mulcV -expB eq_sym nz //#.
qed.

(* -------------------------------------------------------------------- *)
lemma expg_eq0 k : 0 <= k < order => (g ^ k = e <=> k = 0).
proof.
move=> rgk; split=> [|->]; last by rewrite exp0.
apply: contraLR => nz_k; apply/negP => z_gk.
have := uniq_cg; rewrite range_ltn 1:gt0_order /=.
rewrite negb_and /= exp0; left; apply/mapP.
by exists k; rewrite eq_sym z_gk mem_range /#.
qed.

(* -------------------------------------------------------------------- *)
lemma expg_order : g ^ order = e.
proof.
pose s := map (fun i => g ^ i) (range 0 order).
have /perm_eq_size := perm_filterC (mem s) elems.
have: perm_eq (filter (mem s) elems) (filter (mem elems) s).
+ rewrite &(uniq_perm_eq) ?filter_uniq ?(elems_uniq, uniq_cg).
  by move=> x; rewrite !mem_filter andbC.
rewrite -/order eq_sym size_cat => /perm_eq_size ->.
rewrite eq_in_filter_predT => [x _|]; 1: by rewrite elemsP.
rewrite size_map size_range /= max_ler 1:ge0_order.
rewrite -{1}(addr0 order) eq_sym => /addrI.
rewrite size_eq0 => /(congr1 (fun s => g ^ order \in s)) /=.
rewrite neqF mem_filter elemsP /predC /=.
case/mapP=> x /= [/mem_range rg_x]; apply: contraLR => _.
apply/negP => /(congr1 (fun y => y / g ^ x)) /=.
rewrite mulcV -expB; case: (x = 0) => [->//=|nz_k].
by rewrite expg_eq0 /#.
qed.

(* -------------------------------------------------------------------- *)
lemma log_spec x : exists k, log_spec x k.
proof.
case: (monogenous x) => k ->>; exists (k %% order).
rewrite /log_spec modz_ge0 1:!(gtr_eqF, gt0_order) //=.
rewrite ltz_pmod 1:gt0_order /= modzE expB.
by rewrite mulrC expM expg_order expc1 invc1 mulc1.
qed.

(* -------------------------------------------------------------------- *)
lemma elemsE : perm_eq (map (fun i => g ^ i) (range 0 order)) elems.
proof.
rewrite &(uniq_perm_eq) ?(elems_uniq, uniq_cg) => x.
rewrite elemsP /=; apply/mapP; case: (log_spec x).
by move=> k @/log_spec hk; exists k; rewrite mem_range eq_sym.
qed.

(* -------------------------------------------------------------------- *)
lemma ge0_log x : 0 <= log x.
proof.
by have := log_spec x => @/log /choicebP /= /(_ 0) [].
qed.

lemma lt_order_log x : log x < order.
proof.
by have := log_spec x => @/log /choicebP /= /(_ 0) [].
qed.

(* -------------------------------------------------------------------- *)
lemma expg_modz k : g ^ (k %% order) = g ^ k.
proof.
apply/eq_sym; rewrite {1}(divz_eq k order).
by rewrite mulrC expD expM expg_order expc1 mul1c.
qed.

lemma expg_inj i j : 0 <= i < order => 0 <= j < order =>
  g ^ i = g ^ j => i = j.
proof.
wlog: i j / (i <= j) => [wlog|le_ij].
+ case: (leVge i j) => [|le_ji]; first by apply: wlog.
  by move=> ??; rewrite eq_sym (eq_sym i) &(wlog).
move=> rgi rgj /(congr1 (fun x => x / g ^ i)) /=.
by rewrite mulcV eq_sym -expB expg_eq0 /#.
qed.

lemma expg_inj_mod i j : g ^ i = g ^ j => i %% order = j %% order.
proof.
rewrite -(expg_modz i) -(expg_modz j) &(expg_inj);
  by rewrite modz_ge0 1:gtr_eqF //= ?ltz_pmod order_gt0.
qed.

(* -------------------------------------------------------------------- *)
lemma expgK x : g ^ (log x) = x.
proof. by rewrite /log; case: (choicebP _ 0 (log_spec x)). qed.

lemma logK k : log (g ^ k) = k %% order.
proof.
rewrite -(pmod_small (log _) order) 1:!(ge0_log, lt_order_log).
by rewrite &(expg_inj_mod) expgK.
qed.

end CyclicGroup.
