require import AllCore CHoareTactic Xint.

module type O = { proc o () : unit }.

module type F2 (O0 : O) (O1 : O) = { 
  proc f () : unit
}.

module type F1 (O1 : O) = { 
  proc f () : unit
}.

module type F0 = { 
  proc f () : unit
}.

(* -------------------------------------------------------------------- *)
(* axiom test0 (c1 c2 : cost) (k1 k2 : int) (H <: O): *)
(*   `[a : `[: c1, H.o : N k1]] = `[a : `[: c2, H.o : N k2]]. *)

(* lemma test0_inst (k k1 k2 : int) (H <: O) : false. *)
(* proof. *)
(*   have U := test0 `[: N k] `[: N k] k1 k2 H. move: U => /=. *)
(* qed. *)

(* -------------------------------------------------------------------- *)
section.
  op k1 : int.
  op c : cost.
  op c2 : cost.

  declare module A <: O.

  declare module F1_A <: F1.
  declare module F1_B <: F1[f : [2 * c , #O1.o : N k1]].
  declare module F1_C <: F1[f : [    c , #O1.o : N k1]].
  declare module F1_D <: F1[f : [    .., #O1.o :   ..]].
  declare module F1_E <: F1[f : [    c , #O1.o :   ..]].
  declare module F1_F <: F1[f : [    .., #O1.o : N k1]].

  (* test printers *)
  print F1_A.
  print F1_B. 
  print F1_C.
  print F1_D. 
  print F1_E.

  (* this goal is false, and should not go through *)
  lemma SHOULD_FAIL (OO <: O) : 
    0 <= k1 =>
    choare[F1_B(OO).f] time `[: N 0, F1_B.f : N 1, OO.o : N 0].
  proof.
    move => H.
    proc*; call (_: true) => /=. 
    + by move => *; proc*; call(_:true). 
    auto; rewrite !bigi_constz //=. 
    admit. (* if the previous tactic did not fail, this admit will *)
  qed.


  (* test modules *)
  lemma test_B (OO <: O) : 
    0 <= k1 =>
    choare[F1_B(OO).f] time `[: N 0, F1_B.f : N 1, OO.o : N k1].
  proof.
    move => H.
    proc*; call (_: true) => /=.
    + by move => *; proc*; call(_:true).
    auto; rewrite !bigi_constz //=. 
  qed.

  lemma test_C (OO <: O) : 
    0 <= k1 =>
    choare[F1_C(OO).f] time `[: N 0, F1_C.f : N 1, OO.o : N k1].
  proof.
    move => H.
    proc*; call (_: true) => /=.
    + by move => *; proc*; call(_:true).
    auto; rewrite !bigi_constz //=. 
  qed.

  lemma test_D (OO <: O) : 
    0 <= k1 =>
    choare[F1_F(OO).f] time `[: N 0, F1_F.f : N 1, OO.o : N k1].
  proof.
    move => H.
    proc*; call (_: true) => /=.
    + by move => *; proc*; call(_:true).
    auto; rewrite !bigi_constz //=. 
  qed.

  (* 2: abstract *) 
  declare module O0 <: O.
 
  (* 3: abstract with restr *)
  local module F_A = F1_A(O0).
  local module F_B = F1_B(O0).
  local module F_C = F1_C(O0).
  local module F_D = F1_D(O0).
  local module F_E = F1_E(O0).
  local module F_F = F1_F(O0).

  print module F_A.
  print module F_B.
  print module F_C.
  print module F_D.
  print module F_E.
  print module F_F.
end section.

(* ==================================================================== *)
(* tests on projections *)

(* -------------------------------------------------------------------- *)
lemma test_proj6 (j, i : int) : j = i + 1 => `[: N j, ..] = `[: N (i + 1), ..].
proof. move=> H; simplify; exact H. qed.

lemma test_proj7 (j, i : int) : j = i + 1 => `[: N j, ..] = `[: N (i + 1)].
proof. try (move=> H; simplify; exact H). admit. qed.

(* -------------------------------------------------------------------- *)
lemma test_proj8 (O <: O) (c : cost) (i : int) : 
  `[f: `[: c, O.o : N i]].#f:O.o = N i.
proof. simplify; done. qed.

lemma test_proj9 (O <: O) (c : cost) (i j : int) : 
  `[f: `[: c, O.o : N j]].#f:O.o = N i.
proof. simplify; try done. admit. qed.

lemma test_proj10 (O <: O) (c : cost) (i : int) :
  `[f: `[: c, O.o : N i]].#f:O.o = N i.
proof. simplify; done. qed.

lemma test_proj11 (O <: O) (c : cost) : 
  `[f: `[: c, O.o : ..]].#f:O.o = Inf.
proof. simplify; done. qed.

lemma test_proj12 (O <: O) (c : cost) : 
  `[f: `[: c, ..]].#f:O.o = Inf.
proof. simplify; done. qed.

(* -------------------------------------------------------------------- *)
lemma test_proj13 (O <: O) (c : cost) (i : int) : 
  `[f: `[: c, O.o : N i, ..]].#f:A.o = N i.
proof. simplify; try done. admit. qed.

lemma test_proj14 (O <: O) (c : cost) (i j : int) : 
  `[f: `[: c, O.o : .., ..]].#f:A.o = N i.
proof. simplify; try done. admit. qed.

lemma test_proj15 (O0 <: O) (O <: O) (c : cost) (i j : int) :
  `[f: `[: c, O.o : N i, O0.o : N j]].#f:O0.o = N i.
proof. simplify; try done. admit. qed.

lemma test_proj16 (O0 <: O) (O <: O) (c : cost) (i j : int) :
  `[f: `[: c, O.o : N i, O0.o : N j]].#f:O0.o = N j.
proof. simplify; done. qed.

(* -------------------------------------------------------------------- *)
lemma test_proj17 (O <: O) (c : cost) (i : int) : 
  `[f: `[: c, O.o : N i]].#f:intr = c.
proof. simplify; done. qed.

lemma test_proj18 (O <: O) (c : cost) : 
  `[f: `[: c, O.o : ..]].#f:intr = c.
proof. simplify; done. qed.

lemma test_proj19 (O <: O) (c : cost) : 
  `[f: `[: c, ..]].#f:intr = c.
proof. simplify; done. qed.

lemma test_proj20 (O <: O) (c : cost) (i : int) : 
  `[f: `[: .., O.o : N i]].#f:intr = inf.
proof. simplify; done. qed.

(* -------------------------------------------------------------------- *)
lemma test_add_simpl (O <: O) (c : cost) :
c + `[: '0, O.o : N (-1)] + `[: '0, O.o : '1] = c.
proof.
  by rewrite addcC (addcC c) addcA.
qed. 

(* -------------------------------------------------------------------- *)
lemma test_is_int (a b  : cost) : 
  subcond (a + b) (2 * `[: N 42] + `[: N 42]).
proof. done. qed. 

lemma test_is_int2 (a b  : cost) : 
  b = `[: N 42] =>
  subcond (a + b) (2 * `[: N 42] + `[: N 42] + b).
proof. done. qed. 
 
(* -------------------------------------------------------------------- *)
section.
  op c0 : cost.
  declare module A1 <: F1 [f: [c0      , #O1.o : N 10]].
  declare module A0 <: F1 [f: [`[:N 42], #O1.o : N 10]].

  (* [A0]: subtyping concludes: no proof obligation *)
  lemma test_ex &m: exists (B <: F1 [open f : [.., #O1.o : N 42]]),
     (glob B){m} = (glob B){m} => (glob B){m} = (glob B){m}. 
  proof.
    exists A0; split.
  qed.

  (* [A1]: proof obligation, calls at most 42 *)  
  lemma test_ex2 &m: exists (B <: F1 [open f : [.., #O1.o : N 42]]),
     (glob B){m} = (glob B){m} => (glob B){m} = (glob B){m}. 
  proof.
    exists A1; split.
    move => /= O1; proc*; call(:true) => /=.
    + by move=> ??; proc*; call(:true).
    + by auto; rewrite bigi_constz.
    move => ?; assumption.
  qed.  

  (* [A1]: proof obligation, calls at most 1 *)  
  lemma test_ex3 &m: exists (B <: F1 [open f : [.., #O1.o : N 1]]),
     (glob B){m} = (glob B){m} => (glob B){m} = (glob B){m}. 
  proof.
    exists A1; split.
    move => /= O1; proc*; call(:true) => /=.
    + by move=> ??; proc*; call(:true).
    + auto; rewrite bigi_constz //=. 
      admit.
      (* checks that previous tactic failed to conclude *)
    move => ?; assumption.
  qed.  

  declare module O <: O.
  module B = { proc f() = {var x; x <@ O.o (); }}.

  lemma test (c : cost) : 
    choare[B.f] time `[: '0, O.o : '1].
  proof.
    proc*; inline*; call(:true); done.
  qed.
end section.
