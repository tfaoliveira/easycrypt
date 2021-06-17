require import AllCore List Distr DBool DInterval.
require import Oracle_PKE.

(* Real/Ideal variant of IND-CCA2 *)

theory ICCA.

type pkey, skey, plaintext, ciphertext, encseed, keyseed.

op dkeyseed : { keyseed distr | is_uniform dkeyseed } as dkeyseed_d.
op dencseed : { encseed distr | is_uniform dencseed } as dencseed_d.

op Ndec : int.
op Nenc : { int | 0 < Nenc } as Nenc_gt0.

op enc : plaintext * pkey * encseed -> ciphertext.
op dec : ciphertext * skey -> plaintext option.
op pkgen : keyseed -> pkey.
op skgen : keyseed -> skey.
op m0 : plaintext.

axiom encK (k : keyseed) (m : plaintext) (e : encseed) : 
  dec (enc(m, pkgen k, e), skgen k) = Some m.

clone import CCA as C with
  type pkey <- pkey,
  type skey <- skey,
  type plaintext <- plaintext,
  type ciphertext <- ciphertext,
  op Ndec <- Ndec,
  op Nenc <- Nenc.

module type ICCA = {
  proc enc (_ : plaintext) : ciphertext
  proc dec (_ : ciphertext)  : plaintext option
}.

module type ICCA_i = {
  include ICCA
  proc init() : unit
}.

module Real : ICCA = {
  var pk : pkey
  var sk : skey

  proc init() : unit = {
    var ks;

    ks <$ dkeyseed;
    pk <- pkgen ks;
    sk <- skgen ks;
  }

  proc enc (m : plaintext) : ciphertext = {
    var e,c;

    e <$ dencseed;
    c <- enc(m,pk,e);
    return c;
  }
  proc dec (c : ciphertext) : plaintext option = {
    var m;

    m <- dec(c,sk);
    return m;    
  }
}.

module Ideal : ICCA = { 
  import var Real
  var cs : (ciphertext * plaintext) list

  proc init() : unit = {
    var ks;

    ks <$ dkeyseed;
    pk <- pkgen ks;
    sk <- skgen ks;
    cs <- [];
  }

  proc enc (m : plaintext) : ciphertext = {
    var e,c;

    e <$ dencseed;
    c <- enc(m0,pk,e);
    cs <- (c,m) :: cs;
    return c;
  }
  proc dec (c : ciphertext) : plaintext option = {
    var m;
    
    m <- assoc cs c;
    if (m = None) { 
      m <- dec(c,sk);
    }
    return m;    
  }
}.

module Real' : ICCA = { 
  import var Real
  import var Ideal

  proc init() : unit = {
    var ks;

    ks <$ dkeyseed;
    pk <- pkgen ks;
    sk <- skgen ks;
    cs <- [];
  }

  proc enc (m : plaintext) : ciphertext = {
    var e,c;

    e <$ dencseed;
    c <- enc(m,pk,e);
    cs <- (c,m) :: cs;
    return c;
  }
  proc dec (c : ciphertext) : plaintext option = {
    var m;
    
    m <- assoc cs c;
    if (m = None) { 
      m <- dec(c,sk);
    }
    return m;    
  }
}.

module type Adversary (G : ICCA) = {
  proc main () : bool
}.

module Game (O : ICCA_i, A : Adversary) = {
  
  proc main() = {
    var r;
    
    O.init();
    r <@ A(O).main();
    return r;
  }
}.

(*-------------------------------*)

module CountICCA (O : ICCA) = {
  var ndec, nenc : int

  proc init () : unit = {
    ndec <- 0;
    nenc <- 0;
  } 

  proc enc (m : plaintext) : ciphertext = {
    var c; 

    c <@ O.enc(m);
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

module CountAdv (A : Adversary) (O : ICCA) = {
  proc main() = {
    var b;

    CountICCA(O).init();
    b <@ A(CountICCA(O)).main();
    return b;
  }
}.

module B (A : Adversary) (O : CCA_Oracle) = {
  var cs : (ciphertext * plaintext) list
           
  module O' : ICCA = {           
    proc enc (m : plaintext) = {
      var c;
           
      c <- O.l_or_r(m, m0);
      cs <- (c, m) :: cs;
      return c;
    }      
           
    proc dec (c : ciphertext) = {
      var m;
           
      m <- assoc cs c;
      if (m = None) { 
        m <- O.dec(c);
      }
      return m;    
    }
  }

  proc main(pk : pkey) : bool = {
    var r; 
      
    cs <-[];
    r <@ A(O').main();
    return r;
  }
}.

section.

declare module A : Adversary {Real, Real', Ideal, C.Wrap, B, CountCCA}.

axiom A_bound (O <: ICCA {CountICCA}) : hoare [CountAdv(A, O).main :
               true ==> CountICCA.ndec <= Ndec /\ CountICCA.nenc <= Nenc].

equiv Real_Real' :
  Game(Real,A).main ~ Game(Real',A).main : ={glob A} ==> ={res}.
proof.
proc; inline *. 
call (: ={glob Real} /\ (exists ks, (Real.pk,Real.sk){2} = (pkgen ks, skgen ks)) /\
  (forall c m, assoc Ideal.cs c = Some m => dec(c,Real.sk) = Some m){2}) .
+ proc. wp. rnd. auto=> /> &m2 ks Hcs e _ c m'.
  rewrite assoc_cons. case: (c = enc (m{m2}, pkgen ks, e)) => />. by rewrite encK.
  move => _. apply: Hcs.
+ proc. wp. skip => /> &m2 ks Hcs. smt().
+ wp. rnd. skip => />. smt().
qed.

module S : Scheme = {
  proc kg () : pkey * skey = {
    var ks, pk, sk;

    ks <$ dkeyseed;
    pk <- pkgen ks;
    sk <- skgen ks;
    return (pk, sk);
  }

  proc enc (pk : pkey, m : plaintext) : ciphertext = {
    var e, c;

    e <$ dencseed;
    c <- enc (m, pk, e);
    return c;
  }

  proc dec(sk : skey, c : ciphertext) : plaintext option = {
    var m;

    m <- dec (c, sk);
    return m;
  }
}.

equiv Real'_CCA_L :
  Game(Real',A).main ~ CCA_L(S, B(A)).main : ={glob A} ==> ={res}.
proof.
proc; inline *; wp.
call (: ={pk,sk}(Real,Wrap) /\ unzip1 Ideal.cs{1} = Wrap.cs{2} /\
      (forall c m, assoc Ideal.cs c = Some m => dec(c,Real.sk) = Some m){1} /\ 
      (exists ks, (Wrap.pk,Wrap.sk){2} = (pkgen ks, skgen ks)) /\ 
      Ideal.cs{1} = B.cs{2}).
+ proc; inline *; auto => /> &m1 &m2 Hcs ks ? ? e _ c m'. 
  rewrite assoc_cons. case : (c = enc (m{m2}, pkgen ks, e)) => />; smt(encK).
+ proc; inline *; auto => /> &m1 &m2 Hcs ks ? ?. 
  by rewrite -assocTP.
+ wp; rnd; skip => />. smt().
qed.

equiv Ideal_CCA_R :
  Game(Ideal,A).main ~ CCA_R(S, B(A)).main : true ==> ={res}.
proof.
admitted.

equiv AB_bound (O <: CCA_Oracle{CountICCA, CountCCA, A}) :
  C.CountAdv(B(A), O).main ~ CountAdv(A, B(A, O).O').main :
  true ==> CountCCA.ndec{1} <= CountICCA.ndec{2} /\ CountCCA.nenc{1} = CountICCA.nenc{2}.
proof.
admitted.

lemma B_bound (O <: CCA_Oracle{CountCCA, A}) : hoare [C.CountAdv(B(A), O).main :
               true ==> CountCCA.ndec <= Ndec /\ CountCCA.nenc <= Nenc].
proof.
admitted.

lemma ICCA_CCALR &m :
  Pr[Game(Real,A).main() @ &m : res] - Pr[Game(Ideal,A).main() @ &m : res] =
  Pr[CCA_L(S, B(A)).main() @ &m : res] - Pr[CCA_R(S, B(A)).main() @ &m : res].
proof.
have -> : Pr[Game(Real,A).main() @ &m : res] = Pr[Game(Real',A).main() @ &m : res].
- byequiv => //; conseq (: true ==> ={res}); exact Real_Real'.
have -> : Pr[Game(Real',A).main() @ &m : res] = Pr[CCA_L(S, B(A)).main() @ &m : res].
- byequiv => //; conseq (: true ==> ={res}); exact Real'_CCA_L.
have -> : Pr[Game(Ideal,A).main() @ &m : res] = Pr[CCA_R(S, B(A)).main() @ &m : res]; 2: by smt().
byequiv => //; conseq (: true ==> ={res}); exact Ideal_CCA_R.
qed.
