(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

require import AllCore List Distr DBool DInterval.
require (*--*) LorR Hybrid.

type ('a, 'b) sum = [Left of 'a | Right of 'b].

op is_left ['a 'b] (s : ('a,'b) sum) = 
  with s = Left _ => true
  with s = Right _ => false.

op left ['a 'b] (s : ('a,'b) sum) = 
  with s = Left x => x
  with s = Right _ => witness.

op right ['a 'b] (s : ('a,'b) sum) = 
  with s = Right x => x
  with s = Left _ => witness.

theory CCA.

type pkey, skey, plaintext, ciphertext.

op Ndec : int.
op Nenc : { int | 0 < Nenc } as Nenc_gt0.

clone import Hybrid as Hyb with
  type input <- plaintext * plaintext,
  type output <- ciphertext,
  type inleaks = (unit, ciphertext) sum,
  type outleaks = (pkey, plaintext option) sum,
  type outputA <- bool,
  op q <- Nenc.

module type Scheme = {
  proc kg () : pkey * skey
  proc enc (pk : pkey, m : plaintext)  : ciphertext
  proc dec (sk : skey, c : ciphertext) : plaintext option
}.

module type CCA_Oracle = {
  proc l_or_r (m0 m1 : plaintext) : ciphertext
  proc dec (c : ciphertext) : plaintext option
}.

module type CCA_Oracle_i = {
  include CCA_Oracle
  proc init () : unit
}.

module type Adversary (O : CCA_Oracle) = {
  proc main (pk : pkey) : bool
}.

module type LR = { 
  proc init () : unit
  proc l_or_r (m0 m1 : plaintext) : plaintext
}.

module LorR : LR = {
  var b : bool

  proc init () = { 
    b <$ {0,1};
  }

  proc l_or_r (m0 m1 : plaintext) = {
    return b?m0:m1;
  } 
}.

module L : LR = {
  proc init () = { } 

  proc l_or_r (m0 m1 : plaintext) = {
    return m0;
  } 
}.

module R : LR = {
  proc init () = { } 

  proc l_or_r (m0 m1 : plaintext) = {
    return m1;
  } 
}.

(* Oracles for CCA games *)

module Wrap (S : Scheme, LR : LR) : CCA_Oracle_i = {
  var sk : skey
  var pk : pkey
  var cs : ciphertext list

  proc init () = {
    LR.init();
    (pk, sk) <@ S.kg();
    cs <- [];
  }
  
  proc l_or_r (m0 m1 : plaintext) : ciphertext = {
    var c, m;

    m <@ LR.l_or_r(m0, m1);
    c <@ S.enc(pk, m);
    cs <- c :: cs;
    return c;
  }
  
  proc dec (c : ciphertext) : plaintext option = {
    var m;
    
    m <- witness;
    if (! c \in cs) {
      m <- S.dec(sk, c);
    }
    return m;
  }
}.

module CountCCA (O : CCA_Oracle) = {
  var ndec, nenc : int

  proc init () : unit = {
    ndec <- 0;
    nenc <- 0;
  } 

  proc l_or_r (m0 m1 : plaintext) : ciphertext = {
    var c; 

    c <@ O.l_or_r(m0, m1);
    nenc <- nenc + 1;
    return c;
  }

  proc dec (c : ciphertext) : plaintext option = {
    var m; 

    m <@ O.dec(c);
    ndec <- ndec + 1;
    return m;
  }
}.

module CountAdv (A : Adversary) (O : CCA_Oracle) = {
  proc main(pk) = {
    var b;

    CountCCA(O).init();
    b <@ A(CountCCA(O)).main(pk);
    return b;
  }
}.

(** Plan: 
    1. Create Wraper for Adversaries that does (only) the counting
    2. Remove counting from Wrap 
    3. CCA games call wrapped/restricted adversaries 
    4. express A_bound using counting wrapper
    5. A' used restricted adversary (and so satisfies call restrictions) *)

module CCA (S : Scheme, A : Adversary) = {
  proc main () : bool = {
    var b';

    Wrap(S, LorR).init();
    b' <@ CountAdv(A,Wrap(S, LorR)).main(Wrap.pk);
    return LorR.b = b';
  }
}.

module CCA_ (S : Scheme, A : Adversary, LR : LR) = {
  proc main() : bool = {
    var b';

    Wrap(S,LR).init();
    b' <@ CountAdv(A,Wrap(S, LR)).main(Wrap.pk);

    return b';
  }
}.

module CCA_L (S : Scheme, A : Adversary) = CCA_(S, A, L).
module CCA_R (S : Scheme, A : Adversary) = CCA_(S, A, R).

module B (S : Scheme, A : Adversary, O : CCA_Oracle) = {
  var i, iS : int
  var pk : pkey
  var cs : ciphertext list
  
  module O' : CCA_Oracle = {
    proc l_or_r (m0 m1 : plaintext) = {
      var c;

      if (iS < i) c <- S.enc(pk, m0);
      else { 
        if (i = iS) c <- O.l_or_r(m0, m1);
        else c <- S.enc(pk, m1);
      }
      i <- i + 1;
      cs <- c :: cs;
      return c;
    }

    proc dec (c : ciphertext) : plaintext option = {
      var m;

      m <- witness;
      if (! c \in cs) m <@ O.dec(c);
      return m;
    }
  }

  proc main (pk0 : pkey) : bool = {
    var b';

    i <- 0;
    iS <$ [0..Nenc-1];
    pk <- pk0;
    cs <- [];
    b' <@ A(O').main(pk);
    return b';
  }
}.

section.

declare module S : Scheme {Wrap, LorR, B, CountCCA, CountAdv, Count, HybOrcl}.
declare module A : Adversary {Wrap, S, LorR, B, CountCCA, CountAdv, Count, HybOrcl}.

axiom A_ll (O <: CCA_Oracle {A}) : 
  islossless O.l_or_r => islossless O.dec => islossless A(O).main.

axiom kg_ll : islossless S.kg.
axiom enc_ll : islossless S.enc.
axiom dec_ll : islossless S.dec.

axiom A_bound (O <: CCA_Oracle {A, CountCCA}): 
  hoare[ CountAdv(A, O).main : true ==> CountCCA.ndec <= Ndec /\ CountCCA.nenc <= Nenc].

equiv foo (O <: CCA_Oracle {A,CountCCA}) : A(CountCCA(O)).main ~ CountAdv(A, O).main : 
  ={glob A, glob O, arg} /\ CountCCA.ndec{1} = 0 /\ CountCCA.nenc{1} = 0 ==> ={glob CountCCA}.
proof.
  proc *; inline *; sp; auto. call (: ={glob O, glob CountCCA}); try by sim.
  by skip => />.
qed.

lemma A_bound' (O <: CCA_Oracle {A, CountCCA}): 
  hoare[ A(CountCCA(O)).main : 
    CountCCA.ndec = 0 /\ CountCCA.nenc = 0 ==> CountCCA.ndec <= Ndec /\ CountCCA.nenc <= Nenc].
proof.
by conseq (foo (<: O)) (A_bound (<: O)); smt().
qed.

lemma CCA_LR &m : 
  `| Pr[ CCA(S, A).main() @ &m : res] - 1.0/2.0 | = 
  1%r / 2%r * `| Pr[ CCA_L(S, A).main() @ &m : res ] - Pr[ CCA_R(S, A).main() @ &m : res ] |.
proof.
  rewrite (Top.LorR.pr_AdvLR_AdvRndLR (CCA_L(S, A)) (CCA_R(S, A)) &m).
    byphoare => //. 
    islossless; last by apply: kg_ll.
    apply: (A_ll(CountCCA(Wrap(S, R)))); first by islossless; apply: enc_ll. 
    islossless; apply: dec_ll.
  suff <- : Pr[CCA(S, A).main() @ &m : res] = 
            Pr[Top.LorR.RandomLR(CCA_L(S, A),CCA_R(S, A)).main() @ &m : res] by smt().
  byequiv=> //. proc; inline *.
  seq 1 1 : (={glob A,glob S} /\ LorR.b{1} = b{2}); first by rnd.
  if{2}; wp. 
  - call (: ={glob S, glob Wrap} /\ LorR.b{1}).
    + by proc; inline *; sp; auto; call (: true); auto => />.
    + by sim / (LorR.b{1}) : (={res,glob S, glob Wrap}).
    + by wp; call (: true); auto => />.
  - call (: ={glob S, glob Wrap} /\ !LorR.b{1}).
    + by proc; inline *; sp; auto; call (: true); auto => />.
    + by sim / (!LorR.b{1}) : (={res,glob S, glob Wrap}).
    + by wp; call (: true); auto => />.
qed.

local module LRB (O : CCA_Oracle) : CCA_Oracle = {
  import var B

  proc l_or_r (m0 m1 : plaintext) = {
    var c;

    if (iS < i) c <- S.enc(pk, m0);
    else { 
      if (i = iS) c <- O.l_or_r(m0, m1);
      else c <- S.enc(pk, m1);
    }
    i <- i + 1;
    cs <- c :: cs;
    return c;
  }

  proc dec (c : ciphertext) : plaintext option = {
    var m;

    m <- witness;
    if (! c \in cs) m <@ O.dec(c);
    return m;
  }
}.

local equiv eqv_CountCCALRB (O <: CCA_Oracle {S, CountCCA, A, B}) : 
  A(B(S, A, CountCCA(O)).O').main ~ A(CountCCA(LRB(O))).main : 
  ={glob O, glob S, glob A, B.iS, B.i, B.pk, CountCCA.ndec, arg} /\
  CountCCA.ndec{1} = 0 /\
  (forall c, c \in B.cs{1} <=> c \in B.cs{2})
  ==>
  CountCCA.ndec{1} <= CountCCA.ndec{2}.
proof.
  proc *; inline *; sp; auto.
  call ( : ={glob O, glob S, B.iS, B.i, B.pk} /\
           (forall c, c \in B.cs{1} <=> c \in B.cs{2}) /\
           CountCCA.ndec{1} <= CountCCA.ndec{2}); 3: skip => />.
  - proc; inline *; sp; auto.
    if => //; 1: by call (: true); skip => /> /#.
    if => //; 1: wp; call (: true); auto => /> /#.
  - proc; inline *; sp; auto.
    if; 1: move => /> /#; 2: skip => /> /#.
    sp; auto; call (: true); skip => /> /#.
qed.

lemma B_bound (O <: CCA_Oracle {S, CountCCA, A, B}): 
  hoare[ CountAdv(B(S, A), O).main : true ==> CountCCA.ndec <= Ndec /\ CountCCA.nenc <= 1].
proof.
proc; inline *; swap 5 -2; sp; auto.
  conseq (: CountCCA.ndec = 0 ==> CountCCA.ndec <= Ndec)
         (: CountCCA.nenc = 0 ==> CountCCA.nenc <= 1) => //.
- call (: CountCCA.nenc = b2i (B.iS < B.i)).
  + proc; inline *.
    if; first by wp; call (: true); skip; smt().
    if; last by wp; call (: true); skip; smt().
    wp; sp; call (: true); skip; smt().
  + by conseq />.
  + auto => />; smt(supp_dinter).
- call (: CountCCA.ndec = 0 ==> CountCCA.ndec <= Ndec); 2: auto.
  conseq (eqv_CountCCALRB(O)) (A_bound' (<: LRB(O))) => /> /#.
qed.

local module Ob : Orclb = {
  var sk : skey
  var pk : pkey
  var cs : ciphertext list
  var ndec : int

  proc leaks (il : inleaks) : outleaks = {
    var ol, m;

    if (is_left il) {
        (pk, sk) <@ S.kg();
        ndec <- 0;
        cs <- [];
        ol <- Left pk;

    }
    else {
      m <- witness;
      if (! right il \in cs) {
        m <- S.dec(sk, right il);
        ndec <- ndec + 1;
      }
      ol <- Right m;
    }
    return ol;
  }
  
  proc orclL (m0 m1 : plaintext) : ciphertext = { 
    var c;

    c <@ S.enc(pk, m0);
    cs <- c :: cs;
    return c;
  }
  
  proc orclR (m0 m1 : plaintext) : ciphertext = {
    var c;

    c <@ S.enc(pk, m1);
    cs <- c :: cs;
    return c;
  }
}.

local lemma Obl_ll : islossless Ob.leaks.
proof.
  islossless; [exact kg_ll|exact dec_ll].
qed.

local lemma orclL_ll : islossless Ob.orclL.
proof.
  islossless; exact enc_ll.
qed.

local lemma orclR_ll : islossless Ob.orclR.
proof.
  islossless; exact enc_ll.
qed.

(* : AdvOrclb *)
local module A' (Ob : Orclb) (O : Orcl) = {
  module O' : CCA_Oracle = {
    proc l_or_r = O.orcl

    proc dec (c : ciphertext) : plaintext option = {
      var m; 

      m <@ Ob.leaks(Right c);
      return right m;
    } 
  }

  proc main() : bool = {
    var b', ol, pk;

    ol <@ Ob.leaks(Left());
    pk <- left ol;
    b' <@ CountAdv(A, O').main(pk);
    return b';
  }
}.

local lemma A'_ll (Ob <: Orclb{A'}) (LR <: Orcl{A'}) : 
  islossless LR.orcl => islossless Ob.leaks =>
  islossless Ob.orclL => islossless Ob.orclR =>
  islossless A'(Ob, LR).main.
proof.
  move=> orcl_ll leaks_ll orclL_ll orclR_ll; islossless.
  apply (A_ll (<: CountCCA(A'(Ob, LR).O'))); islossless.
qed.

local lemma CCA_Ln &m : 
   Pr[ CCA_L(S, A).main() @ &m : res ] = Pr[ Ln(Ob, A').main() @ &m : res ].
proof.
  byequiv => //; proc. inline *; sp; wp; rcondt{2} 1 => //.
  call (: ={glob S} /\ ={sk, pk, cs}(Wrap,Ob)).
  + proc; auto; inline *; auto. 
    by call (: true); auto => />.
  + proc; auto; inline *. sp; rcondf{2} 1 => //; sp.
    by if; 1: smt(); auto; call (: true).
  + by auto; call(: true).
qed.

local lemma CCA_Rn &m : 
   Pr[ CCA_R(S, A).main() @ &m : res ] = Pr[ Rn(Ob, A').main() @ &m : res].
proof.
  byequiv => //; proc. inline *; sp; wp; rcondt{2} 1 => //.
  call (: ={glob S} /\ ={sk,pk,cs}(Wrap,Ob)).
  + proc; auto; inline *; auto. 
    by call (: true); auto => />.
  + proc; auto; inline *. sp; rcondf{2} 1 => //; sp.
    by if; 1: smt(); auto; call (: true).
  + by auto; call(: true).
qed.

local lemma toto (O <: Orcl{Count, A'}) :
  hoare[ CountAdv(A, A'(Ob, OrclCount(O)).O').main :
            Count.c = 0 ==> Count.c <= Nenc].
proof.
conseq (A_bound (<: A'(Ob, OrclCount(O)).O')) (: Count.c = 0 ==> CountCCA.nenc = Count.c) => />.
proc.
call (: CountCCA.nenc = Count.c).
- by proc; inline *; auto; call (: true); auto.
- by conseq />.
- by inline *; auto.
qed.

local lemma A'_call (O <: Orcl{Count, A'(* , CountCCA , Ob *) }) :
  hoare[ AdvCount(A'(Ob, OrclCount(O))).main : true ==> Count.c <= Nenc].
proof.
proc. inline A'(Ob, OrclCount(O)).main; wp.
call (toto O).
inline *; rcondt 3; 1: by auto.
by auto; call (: true); auto.
qed.

import StdOrder.RealOrder.

lemma CCA_1n &m :
    `| Pr[ CCA_L(S, A).main() @ &m : res ] - Pr[ CCA_R(S, A).main() @ &m : res ] |
    <= 
    Nenc%r * `| Pr[ CCA_L(S,B(S, A)).main() @ &m : res ] - Pr[ CCA_R(S,B(S, A)).main() @ &m : res ] |.
proof.
rewrite -ler_pdivr_mull; 1: smt(Nenc_gt0).
have -> : inv Nenc%r * `|Pr[CCA_L(S, A).main() @ &m : res] - Pr[CCA_R(S, A).main() @ &m : res]| = 
          `| (Pr[ CCA_L(S, A).main() @ &m : res ] - Pr[ CCA_R(S, A).main() @ &m : res]) / Nenc%r |.
smt(Nenc_gt0).
rewrite CCA_Ln CCA_Rn. 
have /= H := Hybrid_restr Ob A' A'_call Obl_ll orclL_ll orclR_ll A'_ll &m (fun _ _ _ r => r).
rewrite -H; clear H.
have <- : Pr[CCA_(S, B(S, A), L).main() @ &m : res] = Pr[HybGame(A', Ob, Hyb.L(Ob)).main() @ &m : res].
  byequiv => //; proc; inline *; auto. 
  swap{2} 1 5; swap{1} 6 2; sp. 
  rcondt{2} 1; 1: by move => &m'; skip => />.
  call (: ={glob S} /\ ={pk, sk}(Wrap, Ob) /\ 
            B.i{1} = HybOrcl.l{2} /\ B.iS{1} = HybOrcl.l0{2} /\ ={cs, pk}(B, Ob) /\
            (forall c, c \in Wrap.cs{1} => c \in B.cs{1})).
  - proc; auto; inline *; sp; if; 1: by move => />.
    + by auto; call (: true); auto => /> /#.
    + if; 1: by move => />.
      * by auto; call(: true); auto => /> /#.
      * by auto; call(: true); auto => /> /#.
  - proc; inline *; sp. rcondf{2} 1; 1: by move => &m'; skip => />.
    sp. if; 1: by move => &m1 &m2 />. 
    + sp. rcondt{1} 1. move => &m1; skip => /> /#. 
      by auto; call(: true); skip => />.
    + by auto; skip => />.
  by wp; rnd; auto; call(: true); skip => &m1 &m2 />.
have <- : Pr[CCA_(S, B(S, A), R).main() @ &m : res] = Pr[HybGame(A', Ob, Hyb.R(Ob)).main() @ &m : res].
  byequiv => //; proc; inline *; auto. 
  swap{2} 1 5; swap{1} 6 2; sp. 
  rcondt{2} 1; 1: by move => &m'; skip => />.
  call (: ={glob S} /\ ={pk,sk}(Wrap,Ob) /\ 
            B.i{1} = HybOrcl.l{2} /\ B.iS{1} = HybOrcl.l0{2} /\ ={cs,pk}(B,Ob) /\
            (forall c, c \in Wrap.cs{1} => c \in B.cs{1})).
  - proc; auto; inline *; sp; if; 1: by move => />.
    + by auto; call (: true); auto => /> /#.
    + if; 1: by move => />.
      * by auto; call(: true); auto => /> /#.
      * by auto; call(: true); auto => /> /#.
  - proc; inline *; sp. rcondf{2} 1; 1: by move => &m'; skip => />.
    sp. if; 1: by move => &m1 &m2 />. 
    + sp. rcondt{1} 1. move => &m1; skip => /> /#. 
      by auto; call(: true); skip => />.
    + by auto; skip => />.
  by wp; rnd; auto; call(: true); skip => &m1 &m2 />.
smt().
qed.

end section.
