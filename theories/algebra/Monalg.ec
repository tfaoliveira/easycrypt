(* -------------------------------------------------------------------- *)
require import AllCore IntExtra Finite List.
require (*--*) Monoid Ring Subtype Bigalg.

pragma -oldip.

(* -------------------------------------------------------------------- *)
abstract theory MonAlg.
type M, R.

clone import Monoid as ZM with type t <- M.
clone import Ring.IDomain as ZR with type t <- R.

clear [ZR.* ZR.AddMonoid.* ZR.MulMonoid.*].

(* -------------------------------------------------------------------- *)
clone import Bigalg.BigComRing as Big with
  type t <- R,
  pred CR.unit   <- ZR.unit,
    op CR.zeror  <- ZR.zeror,
    op CR.oner   <- ZR.oner,
    op CR.( + )  <- ZR.( + ),
    op CR.([-])  <- ZR.([-]),
    op CR.( * )  <- ZR.( * ),
    op CR.invr   <- ZR.invr,
    op CR.intmul <- ZR.intmul,
    op CR.ofint  <- ZR.ofint,
    op CR.exp    <- ZR.exp

    proof * remove abbrev CR.(-) remove abbrev CR.(/).

realize CR.addrA     . proof. by apply/ZR.addrA     . qed.
realize CR.addrC     . proof. by apply/ZR.addrC     . qed.
realize CR.add0r     . proof. by apply/ZR.add0r     . qed.
realize CR.addNr     . proof. by apply/ZR.addNr     . qed.
realize CR.oner_neq0 . proof. by apply/ZR.oner_neq0 . qed.
realize CR.mulrA     . proof. by apply/ZR.mulrA     . qed.
realize CR.mulrC     . proof. by apply/ZR.mulrC     . qed.
realize CR.mul1r     . proof. by apply/ZR.mul1r     . qed.
realize CR.mulrDl    . proof. by apply/ZR.mulrDl    . qed.
realize CR.mulVr     . proof. by apply/ZR.mulVr     . qed.
realize CR.unitP     . proof. by apply/ZR.unitP     . qed.
realize CR.unitout   . proof. by apply/ZR.unitout   . qed.

(* -------------------------------------------------------------------- *)
type monalg.

pred qnull (C : M -> R) = is_finite (fun x => C x <> zeror).

lemma qnullP (C : M -> R) : qnull C <=>
  (exists s, forall x, C x <> zeror => x \in s).
proof.                          (* FIXME: move to Finite *)
split=> [qC|]; pose F := fun x => C x <> zeror.
+ by exists (Finite.to_seq F) => x nz_Cx; apply/Finite.mem_to_seq.
case=> s x_in_s; exists (undup (filter F s)).
rewrite undup_uniq /= => x; rewrite mem_undup mem_filter /F.
by apply/andb_idr/x_in_s.
qed.

(* -------------------------------------------------------------------- *)
clone Subtype as Supp with
  type T <- (M -> R), type sT <- monalg, pred P C <- qnull C.

(* -------------------------------------------------------------------- *)
op monalg0 = Supp.insubd (fun _ => zeror).

op mkmonalg (C : M -> R) = odflt monalg0 (Supp.insub C).
op mcoeff (m : monalg) = Supp.val m.

abbrev "_.[_]" m z = mcoeff m z.

(* -------------------------------------------------------------------- *)
lemma monalg_eqE m1 m2 : (m1 = m2) <=> (forall x, m1.[x] = m2.[x]).
proof.
split=> [->//|eq]; apply/Supp.val_inj.
by apply/fun_ext=> x; rewrite eq.
qed.

(* -------------------------------------------------------------------- *)
op support (m : monalg) = Finite.to_seq (fun x => m.[x] <> zeror).

lemma supportP (m : monalg) z : z \in support m <=> m.[z] <> zeror.
proof. by apply/mem_to_seq/Supp.valP. qed.

lemma supportPn (m : monalg) z : !(z \in support m) <=> m.[z] = zeror.
proof. by rewrite -iff_negb /= supportP. qed.

lemma uniq_support m : uniq (support m).
proof. by apply/uniq_to_seq/Supp.valP. qed.

(* -------------------------------------------------------------------- *)
lemma mcoeff0 z : monalg0.[z] = zeror.
proof. by rewrite Supp.insubdK //; exists []. qed.

hint rewrite mcoeff : mcoeff0.

(* -------------------------------------------------------------------- *)
lemma mcoeffE C z : qnull C => (mkmonalg C).[z] = C z.
proof.
move=> qC; case: (Supp.insubP C) => // {qC} |> m.
by rewrite /mcoeff /mkmonalg => _ ->.
qed.

(* -------------------------------------------------------------------- *)
op monalgC z = mkmonalg (fun x => if x = idm then z else zeror).
op monalg1   = monalgC oner.

(* -------------------------------------------------------------------- *)
op MC (x : M) =
  mkmonalg (fun y => if y = x then oner else zeror).

op [ - ] (m : monalg) =
  mkmonalg (fun x => - m.[x]).

op ( + ) (m1 m2 : monalg) =
  mkmonalg (fun x => m1.[x] + m2.[x]).

op ( *& ) (c : R) (m : monalg) =
  mkmonalg (fun x => c * m.[x]).

op ( * ) (m1 m2 : monalg) =
  mkmonalg (fun x : M => BAdd.big predT idfun
    (allpairs (fun x1 x2 : M =>
      if x = x1 + x2 then m1.[x1] * m2.[x2] else zeror)
      (support m1) (support m2))).

(* -------------------------------------------------------------------- *)
lemma monalgCE c x : (monalgC c).[x] = if x = idm then c else zeror.
proof.
by rewrite mcoeffE // qnullP; exists [idm] => /= y; case: (y = idm).
qed.

(* -------------------------------------------------------------------- *)
lemma msuppC c : c <> zeror => support (monalgC c) = [idm].
proof.
move=> nz_c; apply/perm_eq_small/uniq_perm_eq => //.
+ by apply/uniq_support.
+ by move=> x; rewrite mem_seq1 supportP monalgCE; case: (x = idm).
qed.

hint rewrite mcoeff : msuppC.

(* -------------------------------------------------------------------- *)
lemma msupp1 : support monalg1 = [idm].
proof. by apply/msuppC/oner_neq0. qed.

(* -------------------------------------------------------------------- *)
lemma moppE m x : (- m).[x] = - m.[x].
proof.
rewrite mcoeffE // qnullP; exists (support m) => /=.
by move=> {x}x; rewrite oppr_eq0 => /supportP.
qed.

hint rewrite mcoeff : moppE.

(* -------------------------------------------------------------------- *)
lemma maddE m1 m2 x : (m1 + m2).[x] = m1.[x] + m2.[x].
proof.
rewrite mcoeffE // qnullP; exists (support m1 ++ support m2) => /=.
move=> {x}x; apply/absurd=> /=; rewrite mem_cat negb_or; case.
by move=> /supportPn-> /supportPn->; rewrite addr0.
qed.

hint rewrite mcoeff : maddE.

(* -------------------------------------------------------------------- *)
lemma mscaleE c m x : (c *& m).[x] = c * m.[x].
proof.
rewrite mcoeffE // qnullP; exists (support m) => /=.
by move=> {x}x; rewrite mulf_eq0 negb_or supportP.
qed.

(* -------------------------------------------------------------------- *)
lemma mmulE m1 m2 x :
  (m1 * m2).[x] =
    BAdd.big predT idfun
      (allpairs (fun x1 x2 : M =>
        if x = x1 + x2 then m1.[x1] * m2.[x2] else zeror)
        (support m1) (support m2)).
proof.
pose s := allpairs (fun (x y : M) => x + y) (support m1) (support m2).
rewrite mcoeffE // qnullP; exists s => /= {x}x; apply: contraR => /=.
move=> xNs; rewrite BAdd.big_seq &(BAdd.big1) /=.
move=> y /allpairsP[] [x1 x2 /=] [# x1s x2s ->] @/idfun /=.
case: (x = x1 + x2) => // ->>; apply: contraR xNs => _.
by apply/allpairsP; exists (x1, x2).
qed.

(* -------------------------------------------------------------------- *)
op CM1 (x : M) (xm1 xm2 : M * monalg) =
  if   xm1.`1 + xm2.`1 = x
  then xm1.`2.[xm1.`1] * xm2.`2.[xm2.`1]
  else zeror.

lemma mmulELw m1 m2 E1 E2 x : uniq E1 => uniq E2 =>
     (forall x, x \in support m1 => x \in E1)
  => (forall x, x \in support m2 => x \in E2)
  => (m1 * m2).[x] =
       BAdd.big predT (fun x1 : M =>
       BAdd.big predT (fun x2 : M => CM1 x (x1, m1) (x2, m2))
       E2) E1.
proof.
move=> uq1 uq2 supp1 supp2; rewrite /CM1 mmulE BAdd.big_allpairs /=.
have peq: forall E m,
  uniq E => (forall x, x \in support m => x \in E) =>
    perm_eq E (support m ++ filter (fun y => !(y \in support m)) E).
+ move=> E m uqE suppE; apply: uniq_perm_eq => //.
    - rewrite &(cat_uniq) filter_uniq // uniq_support /=.
      by apply/hasPn=> y; rewrite mem_filter.
    - move=> y; rewrite mem_cat mem_filter /=.
      by rewrite -{1}(andb_idl _ _ (suppE y)) andbC orDandN.
have peq1 := peq _ _ uq1 supp1; have peq2 := peq _ _ uq2 supp2 => {peq}.
apply/eq_sym; rewrite (BAdd.eq_big_perm _ _ _ _ peq1) BAdd.big_cat.
rewrite addrC BAdd.big_seq BAdd.big1 /= 2:add0r.
+ move=> y1; rewrite mem_filter /= => -[/supportPn] z_m1y1 _.
  rewrite BAdd.big1 //= => y2 _; case: (_ = x) => //=.
  by rewrite z_m1y1 mul0r.
apply: BAdd.eq_bigr=> y1 _ /=; rewrite (BAdd.eq_big_perm _ _ _ _ peq2).
rewrite BAdd.big_cat addrC BAdd.big_seq BAdd.big1 /= 2:add0r.
+ move=> y2; rewrite mem_filter /= => -[/supportPn] -> _.
  by rewrite mulr0 if_same.
by apply: BAdd.eq_bigr => y2 _ /=; rewrite (eq_sym _ x).
qed.

(* -------------------------------------------------------------------- *)
lemma mmulERw m1 m2 E1 E2 x : uniq E1 => uniq E2 =>
     (forall x, x \in support m1 => x \in E1)
  => (forall x, x \in support m2 => x \in E2)
  => (m1 * m2).[x] =
       BAdd.big predT (fun x2 : M =>
       BAdd.big predT (fun x1 : M => CM1 x (x1, m1) (x2, m2))
       E1) E2.
proof.
move=> uq1 uq2 supp1 supp2; rewrite (mmulELw m1 m2 E1 E2) //.
by rewrite BAdd.exchange_big /=.
qed.

(* -------------------------------------------------------------------- *)
lemma mmulEL m1 m2 x :
  (m1 * m2).[x] =
    BAdd.big predT (fun x1 : M =>
    BAdd.big predT (fun x2 : M => CM1 x (x1, m1) (x2, m2))
    (support m2)) (support m1).
proof. by apply: mmulELw => //; apply: uniq_support. qed.

(* -------------------------------------------------------------------- *)
lemma mmulER m1 m2 x :
  (m1 * m2).[x] =
    BAdd.big predT (fun x2 : M =>
    BAdd.big predT (fun x1 : M => CM1 x (x1, m1) (x2, m2))
    (support m1)) (support m2).
proof. by apply: mmulERw => //; apply: uniq_support. qed.

(* -------------------------------------------------------------------- *)
lemma mulmC : commutative ( * ).
proof.
move=> m1 m2; apply: monalg_eqE=> x; rewrite mmulEL mmulER.
apply: BAdd.eq_bigr=> x1 _ /=; apply: BAdd.eq_bigr=> x2 _ /=.
by rewrite /CM1 /= (addmC x2) mulrC.
qed.

(* -------------------------------------------------------------------- *)
lemma mul1m : left_id monalg1 ( * ).
proof.
move=> m; apply: monalg_eqE => x; rewrite mmulEL.
rewrite msupp1 BAdd.big_seq1 /= (@BAdd.bigD1_cond_if _ _ _ x).
+ by apply: uniq_support.
rewrite /predT /= BAdd.big1 ?addr0 ?supportP.
+ by move=> y @/predI @/predC1 /=; rewrite /CM1 /= add0m => ->.
case: (m.[x] = zeror) => [<-//|] @/CM1 /= _.
by rewrite add0m /= monalgCE /= mul1r.
qed.

(* -------------------------------------------------------------------- *)
lemma mulm1 : right_id monalg1 ( * ).
proof. by move=> m; rewrite mulmC &(mul1m). qed.

(* -------------------------------------------------------------------- *)
op b2r (b : bool) = if b then oner else zeror.

lemma ifb2rE b E : (if b then E else zeror) = b2r b * E.
proof. by rewrite /b2r; case: b => _; rewrite (mul1r, mul0r). qed.

lemma mulmA : associative ( * ).
proof.
move=> m1 m2 m3; apply/monalg_eqE=> x.
pose E1 := support m1; pose E2 := support m2; pose E3 := support m3.
pose E := E1 ++ E2 ++ E3 ++ support (m1 * m2) ++ support (m2 * m3).
pose F (x : M) (x1 x2 x3 : M) :=
  if   x1 + x2 + x3 = x
  then m1.[x1] * m2.[x2] * m3.[x3]
  else zeror.
pose G := BAdd.big predT (fun x1 =>
            BAdd.big predT (fun x2 =>
              BAdd.big predT (fun x3 => F x x1 x2 x3) (undup E))
            (undup E)) (undup E).
apply (@eq_trans _ G) => @/G => {G}.
rewrite (@mmulELw _ _ (undup E) (undup E)) ?undup_uniq.
- by move=> ? @/E; rewrite mem_undup !mem_cat => ->.
- by move=> ? @/E; rewrite mem_undup !mem_cat => ->.
- apply: BAdd.eq_bigr=> /= x1 _ @/CM1 /=.
  pose G (y : M) :=
    BAdd.big predT (fun x2 : M =>
      BAdd.big predT
        (fun x3 => b2r (x2 + x3 = y) * F x x1 x2 x3)
        (undup E))
    (undup E).
  rewrite (@BAdd.eq_bigr _ _ G) => /= [y _|].
  + rewrite /G (@mmulELw _ _ (undup E) (undup E)) ?undup_uniq.
    * by move=> ? @/E; rewrite mem_undup !mem_cat => ->.
    * by move=> ? @/E; rewrite mem_undup !mem_cat => ->.
  + rewrite ifb2rE !BAdd.mulr_sumr; apply: BAdd.eq_bigr=> x2 _ /=.
    rewrite !BAdd.mulr_sumr; apply: BAdd.eq_bigr=> x3 _ @/CM1 @/F /=.
    rewrite ifb2rE. case: (x2 + x3 = y) => [<-|]; 2: by rewrite !(mulr0, mul0r).
    rewrite addmA /=; case: (_ = x) => //=.
    * by rewrite !(mulr1, mul1r) mulrA.
    * by rewrite !(mulr0, mul0r).
  rewrite /G.

(* -------------------------------------------------------------------- *)
clone Ring.ZModule as MAZM with
  type t     <- monalg,
    op zeror <- monalg0,
    op [-]   <- ([-]),
    op (+)   <- (+)
  proof *.

realize addrA.
proof. by move=> m n p; apply/monalg_eqE=> x; rewrite !mcoeff addrA. qed.

realize addrC.
proof. by move=> m p; apply/monalg_eqE=> x; rewrite !mcoeff addrC. qed.

realize add0r.
proof. by move=> m; apply/monalg_eqE=> x; rewrite !mcoeff add0r. qed.

realize addNr.
proof. by move=> m; apply/monalg_eqE=> x; rewrite !mcoeff addNr. qed.
end MonAlg.

(* -------------------------------------------------------------------- *)
abstract theory MPoly.
type vars, monom.

(* -------------------------------------------------------------------- *)
pred qmonom (M : vars -> int) =
  (forall x, 0 <= M x) /\ is_finite (fun x => M x <> 0).

(* -------------------------------------------------------------------- *)
lemma qmonomP (M : vars -> int) : qmonom M <=>
  (forall i, 0 <= M i) /\ (exists s, forall i, M i <> 0 => i \in s).
proof.                          (* FIXME: move to Finite *)
split=> [[pM qM]|]; pose F := fun i => M i <> 0.
+ split=> [i|]; first by rewrite pM.
  by exists (Finite.to_seq F) => x nz_Mx; apply/Finite.mem_to_seq.
case=> pM [s x_in_s]; split=> //; exists (undup (filter F s)).
rewrite undup_uniq /= => x; rewrite mem_undup mem_filter /F.
by apply/andb_idr/x_in_s.
qed.

(* -------------------------------------------------------------------- *)
clone Subtype as Monom with
  type T <- (vars -> int), type sT <- monom, pred P M <- qmonom M.

(* -------------------------------------------------------------------- *)
op monom1 = Monom.insubd (fun _ => 0).

op mkmonom (M : vars -> int) = odflt monom1 (Monom.insub M).
op mpow (M : monom) i = Monom.val M i.

lemma mpow_ge0 (M : monom) i : 0 <= mpow M i.
proof. by have [] := Monom.valP M => + _; apply. qed.

lemma mpow_fin (M : monom) : is_finite (fun i => mpow M i <> 0).
proof. by have [] := Monom.valP M. qed.

hint exact : mpow_ge0 mpow_fin.

(* -------------------------------------------------------------------- *)
lemma mpow1 i : mpow monom1 i = 0.
proof. by rewrite Monom.insubdK //; exists []. qed.

hint rewrite mpow : mpow1.

(* -------------------------------------------------------------------- *)
lemma mpowE M i : qmonom M => mpow (mkmonom M) i = M i.
proof.
move=> qM; case: (Monom.insubP M) => // {qM} |> m.
by rewrite /mpow /mkmonom => _ ->.
qed.

(* -------------------------------------------------------------------- *)
op ( ** ) (M1 M2 : monom) =
  mkmonom (fun i => mpow M1 i + mpow M2 i).

lemma mpowM (M1 M2 : monom) i :
  mpow (M1 ** M2) i = mpow M1 i + mpow M2 i.
proof.
rewrite mpowE // qmonomP => /=; split=> [{i} i|].
+ by rewrite addz_ge0.
pose s1 := Finite.to_seq (fun x => mpow M1 x <> 0).
pose s2 := Finite.to_seq (fun x => mpow M2 x <> 0).
exists (s1 ++ s2) => {i}i; apply/absurd=> /=; rewrite mem_cat negb_or.
by rewrite !mem_to_seq //=; case=> -> ->.
qed.

hint rewrite mpow : mpowM.

(* -------------------------------------------------------------------- *)
lemma monom_eqE M1 M2 : (M1 = M2) <=>
  (forall x, mpow M1 x = mpow M2 x).
proof.
split=> [->//|eq]; apply/Monom.val_inj.
by apply/fun_ext=> x; rewrite eq.
qed.

(* -------------------------------------------------------------------- *)
clone Monoid as MonomMonoid with
  type t   <- monom,
    op idm <- monom1,
    op (+) <- ( ** )
  proof *.

realize Axioms.addmA.
proof. by move=> M N P; apply/monom_eqE=> x; rewrite !mpow addzA. qed.

realize Axioms.addmC.
proof. by move=> M N; apply/monom_eqE=> x; rewrite !mpow addzC. qed.

realize Axioms.add0m.
proof. by move=> M; apply/monom_eqE=> x; rewrite !mpow. qed.

clear [MonomMonoid.Axioms.*].   (* FIXME: do not work?! *)

(* -------------------------------------------------------------------- *)
type mpoly.

clone include MonAlg with
  type   M      <- monom,
  type   monalg <- mpoly,
    op   ZM.idm <- monom1,
    op   ZM.(+) <- ( ** )
  rename "monalg" as "mpoly"
  proof   ZM.Axioms.*.

realize ZM.Axioms.addmA by exact MonomMonoid.addmA.
realize ZM.Axioms.addmC by exact MonomMonoid.addmC.
realize ZM.Axioms.add0m by exact MonomMonoid.add0m.
end MPoly.
