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
op [ - ] (m : monalg) =
  mkmonalg (fun x => - m.[x]).

op ( + ) (m1 m2 : monalg) =
  mkmonalg (fun x => m1.[x] + m2.[x]).

op ( * ) (m1 m2 : monalg) =
  mkmonalg (fun x : M => BAdd.big predT idfun
    (allpairs (fun x1 x2 : M =>
      if x = x1 + x2 then m1.[x1] * m2.[x2] else zeror)
      (support m1) (support m2))).

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
