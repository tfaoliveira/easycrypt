(* -------------------------------------------------------------------- *)
require import AllCore List Distr Ring.
require import StdRing StdOrder StdBigop FelTactic.
require (*--*) Mu_mem.
(*---*) import RField IntOrder RealOrder.

(** An input type **)
type in_t.

(** An output type out_t with an input-parameterised distribution **)
type out_t.

op dout: in_t -> out_t distr.

(**
(** A further transformation under which we catch collisions **)
type fin_t.

op f : out_t -> fin_t.
op pr_predict : { real | forall x y, mu1 (dmap (dout x) f) y <= pr_predict }
  as predictP.
**)
(** A module that samples in `dout x` on queries `s(x)` **)
module Sample = {
  var l : out_t list

  proc init(): unit = {
    l <- [];
  }

  proc s(x : in_t): out_t = {
    var r;

    r <$ dout x;
    l <- r::l;
    return r;
  }
}.

module type Sampler = {
  proc init(): unit
  proc s(_ : in_t): out_t
}.

(** Adversaries that may query an s oracle **)
module type ASampler = {
  include Sampler [s]
}.

module type Adv (S : ASampler) = {
  proc a(): unit
}.

(** And an experiment that initializes the sampler and runs the adversary **)
module Exp (S : Sampler) (A : Adv) = {
  proc main(): unit = {
    S.init();
    A(S).a();
  }
}.

(** Forall adversary A that makes at most q queries to its s oracle,
    the probability that the same output is sampled twice is bounded
    by q^2/|T|                                                        **)
section.
  declare module A <: Adv {-Sample}.
  declare axiom A_ll (S <: ASampler {-A}): islossless S.s => islossless A(S).a.

  declare op q : { int | 0 <= q } as ge0_q.

  declare type fin_t.
  declare op f : out_t -> fin_t.

  declare op pr_predict : { real | forall x y, mu1 (dmap (dout x) f) y <= pr_predict }
    as predictP.

  lemma pr_Sample_le &m:
       Pr[Exp(Sample,A).main() @ &m : size Sample.l <= q /\ !uniq (map f Sample.l)]
    <= (q * (q - 1))%r/2%r * pr_predict.
  proof.
  fel 1 (size Sample.l) (fun x, x%r * pr_predict) q (!uniq (map f Sample.l)) []=> //.
  + by rewrite -Bigreal.BRA.mulr_suml  Bigreal.sumidE 1:ge0_q.
  + by inline*; auto.
  + proc;wp; rnd (mem (map f Sample.l) \o f); skip=> // /> &hr ???.
    rewrite -dmapE -(size_map f).
    apply: (Mu_mem.mu_mem_le_size (map f Sample.l{hr}) (dmap (dout x{hr}) f) pr_predict). 
    by move=> x _;rewrite predictP.
  by move=> c; proc; auto=> /#.
  qed.

  lemma pr_Sample_le_q2 &m:
    Pr[Exp(Sample,A).main() @ &m: size Sample.l <= q /\ !uniq (map f Sample.l)]
    <= (q^2)%r * pr_predict.
  proof.
  apply (ler_trans _ _ _ (pr_Sample_le &m)). 
  apply ler_wpmul2r.
  + exact/(ler_trans _ _ _ _ (predictP witness witness))/ge0_mu.
  have -> : q^2 = q*q by ring.
  smt(ge0_q).
  qed.

  declare axiom A_bounded: hoare [A(Sample).a : size Sample.l = 0 ==> size Sample.l <= q].

  local lemma aux &m :
      Pr[Exp(Sample,A).main() @ &m: !uniq (map f Sample.l)]
    = Pr[Exp(Sample,A).main() @ &m: size Sample.l <= q /\ !uniq (map f Sample.l)].
  proof.
  byequiv (: ={glob A} ==> ={Sample.l} /\ size Sample.l{2} <= q)=> //=.
  conseq (: _ ==> ={Sample.l}) _ (: _ ==> size Sample.l <= q)=> //=;2:by sim.
  by proc; call A_bounded; inline *; auto.
  qed.

  lemma pr_collision &m:
       Pr[Exp(Sample,A).main() @ &m: !uniq (map f Sample.l)]
    <= (q * (q - 1))%r / 2%r * pr_predict.
  proof. by rewrite (aux &m); exact: (pr_Sample_le &m). qed.

  lemma pr_collision_q2 &m:
       Pr[Exp(Sample,A).main() @ &m: !uniq (map f Sample.l)]
    <= (q^2)%r * pr_predict.
  proof. by rewrite (aux &m); apply (pr_Sample_le_q2 &m). qed.

end section.

(*** The same result using a bounding module ***)
abstract theory BoundedOracle.
op q : { int | 0 <= q } as ge0_q.

module Bounder (S : Sampler) = {
  var c : int

  proc init(): unit = {
         S.init();
    c <- 0;
  }

  proc s(x : in_t): out_t = {
    var r <- witness;

    if (c < q) {
      r <@ S.s(x);
      c <- c + 1;
    }
    return r;
  }
}.

module ABounder (S : ASampler) = {
  proc s(x : in_t): out_t = {
    var r <- witness;

    if (Bounder.c < q) {
      r         <@ S.s(x);
      Bounder.c <- Bounder.c + 1;
    }
    return r;
  }
}.

module Bounded (A : Adv) (S : ASampler) = {
  proc a(): unit = {
    Bounder.c <- 0;
    A(ABounder(S)).a();
  }
}.

equiv PushBound (S <: Sampler {-Bounder}) (A <: Adv {-S,-Bounder}):
  Exp(Bounder(S),A).main ~ Exp(S,Bounded(A)).main:
    ={glob A, glob S} ==> ={glob A,glob S}.
proof. by proc; inline *; sim. qed.

(** Forall adversary A with access to the bounded s oracle, the
    probability that the same output is sampled twice is bounded by
    q^2/|T|                                                         **)
section.
  declare module A <: Adv {-Sample, -Bounder}.
  declare axiom A_ll (S <: ASampler {-A}): islossless S.s => islossless A(S).a.

  declare type fin_t.
  declare op f : out_t -> fin_t.

  declare op pr_predict : { real | forall x y, mu1 (dmap (dout x) f) y <= pr_predict }
    as predictP.


  lemma pr_collision_bounded_oracles &m:
       Pr[Exp(Bounder(Sample),A).main() @ &m: !uniq (map f Sample.l)]
    <= (q^2)%r * pr_predict.
  proof.
  have ->: Pr[Exp(Bounder(Sample),A).main() @ &m: !uniq (map f Sample.l)] =
           Pr[Exp(Sample,Bounded(A)).main() @ &m: !uniq (map f Sample.l)].
  + by byequiv (PushBound Sample A).
  apply (pr_collision_q2 (Bounded(A)) _ _ ge0_q _ _ predictP _ &m)=> //.
  + move=> S HS; proc; call (A_ll (ABounder(S)) _); 2:by auto.
    by proc; sp; if; auto; call HS.
  move=> /=; proc; call (: size Sample.l <= Bounder.c <= q).
  + by proc; sp; if=> //; inline *; auto=> /#.
  by auto; smt(ge0_q).
  qed.

end section.
end BoundedOracle.
