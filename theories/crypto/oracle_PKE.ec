(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

require import AllCore List Distr DBool DInterval Hybrid.
require (*--*) LorR.

theory CCA.

type pkey, skey, plaintext, ciphertext.

module type Scheme = {
  proc kg() : pkey * skey
  proc enc(pk:pkey, m:plaintext)  : ciphertext
  proc dec(sk:skey, c:ciphertext) : plaintext option
}.

module type CCA_Oracle = {
  proc l_or_r (m0 m1 : plaintext) : ciphertext
  proc dec (c:ciphertext) : plaintext option
}.

module type CCA_Oracle_i = {
  include CCA_Oracle
  proc init() : unit
}.

module type Adversary (O : CCA_Oracle) = {
  proc main(pk : pkey) : bool
}.

module type LR = { 
  proc init() : unit
  proc l_or_r (m0 m1 : plaintext) : plaintext
}.

module LorR : LR = {
  var b : bool

  proc init() = { 
    b <$ {0,1};
  }

  proc l_or_r (m0 m1 : plaintext) = {
    return b?m0:m1;
  } 
}.

module L : LR = {
  proc init() = { } 

  proc l_or_r (m0 m1 : plaintext) = {
    return m0;
  } 
}.

module R : LR = {
  proc init() = { } 

  proc l_or_r (m0 m1 : plaintext) = {
    return m1;
  } 
}.

(* Oracles for CCA games *)

module Wrap (S : Scheme, LR : LR) : CCA_Oracle_i = {
  var sk : skey
  var pk : pkey
  var cs : ciphertext list
  var ndec : int

  proc init() = {
    LR.init();
    (pk,sk) <@ S.kg();
    cs <- [];
    ndec <- 0;
  }
  
  proc l_or_r (m0 m1 : plaintext) : ciphertext = {
    var c, m;

    m <@ LR.l_or_r(m0, m1);
    c <@ S.enc(pk, m);
    cs <- c::cs;
    return c;
  }
  
  proc dec (c:ciphertext) : plaintext option = {
    var m;
    
    m <- witness;
    if (! c \in cs) {
      m <- S.dec(sk, c);
      ndec <- ndec + 1;
    }
    return m;
  }
}.

module CCA (S : Scheme, A : Adversary) = {
  proc main() : bool = {
    var b';

    Wrap(S,LorR).init();
    b' <@ A(Wrap(S, LorR)).main(Wrap.pk);
    return LorR.b = b';
  }
}.

module CCA_ (S : Scheme, A : Adversary, LR : LR) = {
  proc main() : bool = {
    var b';

    Wrap(S,LR).init();
    b' <@ A(Wrap(S,LR)).main(Wrap.pk);

    return b';
  }
}.

module CCA_L (S : Scheme, A : Adversary) = CCA_(S, A, L).
module CCA_R (S : Scheme, A : Adversary) = CCA_(S, A, R).

op Ndec : int.
op Nenc : int.

module B (S : Scheme, A : Adversary, O : CCA_Oracle) = {
  var i,iS : int
  var pk : pkey
  var cs : ciphertext list
  
  module O' : CCA_Oracle = {
    proc l_or_r(m0 m1 : plaintext) = {
      var c;

      if (i < iS) c <- S.enc(pk,m0);
      else { 
        if (i = iS) c <- O.l_or_r(m0,m1);
        else c <- S.enc(pk,m1);
      }
      i <- i+1;
      cs <- c::cs;
      return c;
    }

    proc dec(c:ciphertext) : plaintext option = {
      var m;

      m <- witness;
      if (! c \in cs) m <@ O.dec(c);
      return m;
    }
  }

  proc main(pk0 : pkey) : bool = {
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

declare module S : Scheme {Wrap, LorR, B}.
declare module A : Adversary {Wrap, S, LorR, B}.

axiom A_ll (O <: CCA_Oracle {A}) : 
  islossless O.l_or_r => islossless O.dec => islossless A(O).main.


axiom kg_ll : islossless S.kg.
axiom enc_ll : islossless S.enc.
axiom dec_ll : islossless S.dec.

lemma CCA_LR &m : 
  `| Pr[ CCA(S, A).main() @ &m : res] - 1.0/2.0 | = 
  1%r / 2%r * `| Pr[ CCA_L(S, A).main() @ &m : res ] - Pr[ CCA_R(S, A).main() @ &m : res ] |.
proof.
  rewrite (Top.LorR.pr_AdvLR_AdvRndLR (CCA_L(S,A)) (CCA_R(S,A)) &m).
    byphoare => //. 
    islossless; last by apply: kg_ll.
    apply: (A_ll(Wrap(S, R))); first by islossless; apply: enc_ll. 
    islossless; apply: dec_ll.
  suff <- : Pr[CCA(S, A).main() @ &m : res] = 
            Pr[Top.LorR.RandomLR(CCA_L(S,A),CCA_R(S,A)).main() @ &m : res] by smt().
  byequiv=> //. proc; inline *.
  seq 1 1 : (={glob A,glob S} /\ LorR.b{1} = b{2}); first by rnd.
  if{2}; wp. 
  - call (_ : ={glob S,glob Wrap} /\ LorR.b{1}).
    + proc; inline LorR.l_or_r L.l_or_r; auto. 
      by call (_ : true); auto => />.
    + by sim / (LorR.b{1}) : (={res,glob S, glob Wrap}).
    + by wp; call (_ : true); auto => />.
  - call (_ : ={glob S,glob Wrap} /\ !LorR.b{1}).
    + proc; inline LorR.l_or_r R.l_or_r; auto. 
      by call (_ : true); auto => />.
    + by sim / (!LorR.b{1}) : (={res,glob S, glob Wrap}).
    + by wp; call (_ : true); auto => />.
qed.

axiom A_bound (O <: LR {Wrap, S, A}): 
  hoare[ A(Wrap(S, O)).main : 
    Wrap.ndec = 0 /\ Wrap.cs = [] ==> Wrap.ndec <= Ndec /\ size Wrap.cs <= Nenc].

local module LRB (O : LR) : LR = {
  import var B
  
  proc init = O.init

  proc l_or_r(m0 m1 : plaintext) = {
    var m;

    if (i < iS) m <- m0;
    else { 
      if (i = iS) m <- O.l_or_r(m0,m1);
      else m <- m1;
    }
    i <- i+1;
    return m;
  }
}.

local equiv eqv_WrapLRB (O <: LR {Wrap, S, A, B}) : 
  A(B(S, A, Wrap(S, O)).O').main ~ A(Wrap(S, LRB(O))).main : 
  ={glob Wrap, glob O, glob S, glob A, glob B} /\ ={pk} /\
  Wrap.pk{1} = B.pk{1} /\ B.cs{1} = Wrap.cs{2} /\
  (forall c, c \in Wrap.cs{1} => c \in Wrap.cs{2}) ==> ={Wrap.ndec}.
proof.
  proc (={glob O, glob S} /\ ={Wrap.ndec, Wrap.sk, Wrap.pk, B.iS, B.i, B.pk} /\ 
        B.cs{1} = Wrap.cs{2} /\ (forall c, c \in Wrap.cs{1} => c \in Wrap.cs{2}) /\
        Wrap.pk{1} = B.pk{1}) => //.
  - proc; inline *; sp.
    if => //; first by wp; call (:true); auto => /> /#.
    if => //; first by do 2!(wp; call (:true)); auto => /> /#.
    by wp; call (:true); auto => /> /#.
  - proc; sp; if => //.
  inline *; rcondt{1} ^if; 1: by auto => /> /#.
  by wp; call(:true); auto.
qed.

lemma B_bound (O <: LR {Wrap, S, A, B}): 
  hoare[B(S, A, Wrap(S,O)).main : 
    Wrap.ndec = 0 /\ Wrap.cs = [] /\
    Wrap.pk = pk0 ==> Wrap.ndec <= Ndec /\ size Wrap.cs <= 1].
proof.
  conseq (_ :
    Wrap.ndec = 0 /\ Wrap.cs = [] /\ Wrap.pk = pk0
    ==>
    Wrap.ndec <= Ndec)
         (_ : Wrap.cs = [] ==> size Wrap.cs <= 1) => //.
  - proc. 
    call (_ : size Wrap.cs = b2i (B.iS < B.i)).
    + proc; inline *. 
      if; first by wp; call (:true); skip; smt().
      if; last by wp; call (: true); skip; smt().
      wp; sp; call (: true); call (: true); skip; smt().
    + by conseq />. 
    + auto => />; smt(supp_dinter).
  - proc.
    call (_ : Wrap.ndec = 0 /\ Wrap.cs = [] /\ Wrap.pk = B.pk /\
              B.cs = Wrap.cs ==> Wrap.ndec <= Ndec).
    conseq (eqv_WrapLRB(O)) (A_bound(<: LRB(O))) => />; 1: smt().
    by auto.
qed.

lemma CCA_1n &m :
    `| Pr[ CCA_L(S,A).main() @ &m : res ] -
       Pr[ CCA_R(S,A).main() @ &m : res ] |
    <= 
    Nenc%r
    *
    `| Pr[ CCA_L(S,B(S, A)).main() @ &m : res ] -
       Pr[ CCA_R(S,B(S, A)).main() @ &m : res ] |.
proof.
admitted.

end section.
