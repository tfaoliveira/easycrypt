require import AllCore List Distr DBool DInterval.
require import Oracle_PKE.

import Distr.MRat.

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
  op Nenc <- Nenc,
  axiom Nenc_gt0 <- Nenc_gt0.

module type ICCA_Oracle = {
  proc pk () : pkey
  proc enc (_ : plaintext) : ciphertext
  proc dec (_ : ciphertext)  : plaintext option
}.

module type ICCA_i = {
  include ICCA_Oracle
  proc init() : unit
}.

module Real : ICCA_Oracle = {
  var pk : pkey
  var sk : skey

  proc init() : unit = {
    var ks;

    ks <$ dkeyseed;
    pk <- pkgen ks;
    sk <- skgen ks;
  }

  proc pk () = {
    return pk;
  }

  proc enc (m : plaintext) : ciphertext = {
    var e, c;

    e <$ dencseed;
    c <- enc(m, pk, e);
    return c;
  }
  proc dec (c : ciphertext) : plaintext option = {
    var m;

    m <- dec(c, sk);
    return m;
  }
}.

module Ideal : ICCA_Oracle = {
  import var Real
  var cs : (ciphertext * plaintext) list

  proc init() : unit = {
    var ks;

    ks <$ dkeyseed;
    pk <- pkgen ks;
    sk <- skgen ks;
    cs <- [];
  }

  proc pk () = {
    return pk;
  }

  proc enc (m : plaintext) : ciphertext = {
    var e, c;

    e <$ dencseed;
    c <- enc(m0, pk, e);
    cs <- (c, m) :: cs;
    return c;
  }

  proc dec (c : ciphertext) : plaintext option = {
    var m;

    m <- assoc cs c;
    if (m = None) {
      m <- dec(c, sk);
    }
    return m;
  }
}.

module Ideal' : ICCA_Oracle = {
  import var Real
  var n : int
  var cs : (int * (ciphertext * plaintext)) list

  proc init() : unit = {
    var ks;

    ks <$ dkeyseed;
    pk <- pkgen ks;
    sk <- skgen ks;
    n <- 0;
    cs <- [];
  }

  proc pk () = {
    return pk;
  }

  proc enc (m : plaintext) : ciphertext = {
    var e, c;

    e <$ dencseed;
    c <- enc(m0, pk, e);
    n <- n + 1;
    cs <- (n, (c, m)) :: cs;
    return c;
  }

  proc dec (c : ciphertext) : plaintext option = {
    var fcs, m, p;

    fcs <- List.filter (fun p => fst (snd p) = c) cs;
    if (fcs <> []) {
      p <$ drat fcs;
      m <- Some (snd (snd p));
    } else {
      m <- dec(c, sk);
    }
    return m;
  }
}.

module Real' : ICCA_Oracle = {
  import var Real
  import var Ideal

  proc init() : unit = {
    var ks;

    ks <$ dkeyseed;
    pk <- pkgen ks;
    sk <- skgen ks;
    cs <- [];
  }

  proc pk () = {
    return pk;
  }

  proc enc (m : plaintext) : ciphertext = {
    var e, c;

    e <$ dencseed;
    c <- enc(m, pk, e);
    cs <- (c, m) :: cs;
    return c;
  }

  proc dec (c : ciphertext) : plaintext option = {
    var m;

    m <- assoc cs c;
    if (m = None) {
      m <- dec(c, sk);
    }
    return m;
  }
}.

module Real'' : ICCA_Oracle = {
  import var Real
  import var Ideal'

  proc init() : unit = {
    var ks;

    ks <$ dkeyseed;
    pk <- pkgen ks;
    sk <- skgen ks;
    n <- 0;
    cs <- [];
  }

  proc pk () = {
    return pk;
  }

  proc enc (m : plaintext) : ciphertext = {
    var e, c;

    e <$ dencseed;
    c <- enc(m, pk, e);
    n <- n + 1;
    cs <- (n, (c, m)) :: cs;
    return c;
  }

  proc dec (c : ciphertext) : plaintext option = {
    var fcs, m, p;

    fcs <- List.filter (fun p => fst (snd p) = c) cs;
    if (fcs <> []) {
      p <$ drat fcs;
      m <- Some (snd (snd p));
    } else {
      m <- dec(c, sk);
    }
    return m;
  }
}.

module type Adversary (G : ICCA_Oracle) = {
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

module CountICCA (O : ICCA_Oracle) = {
  var ndec, nenc : int

  proc init () : unit = {
    ndec <- 0;
    nenc <- 0;
  }

  proc pk = O.pk

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

module CountAdv (A : Adversary) (O : ICCA_Oracle) = {
  proc main() = {
    var b;

    CountICCA(O).init();
    b <@ A(CountICCA(O)).main();
    return b;
  }
}.

module B (A : Adversary) (O : CCA_Oracle) = {
  var cs : (ciphertext * plaintext) list
  var pk : pkey

  module O' : ICCA_Oracle = {

    proc init (p : pkey) = { pk <- p; }

    proc pk () = { return pk; }

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

  proc main (pk : pkey) : bool = {
    var r;

    cs <- [];
    O'.init(pk);
    r <@ A(O').main();
    return r;
  }
}.

module B' (A : Adversary) (O : CCA_Oracle) = {
  var n : int
  var cs : (int * (ciphertext * plaintext)) list
  var pk : pkey

  module O' : ICCA_Oracle = {

    proc init (p : pkey) = { pk <- p; }

    proc pk () = { return pk; }

    proc enc (m : plaintext) = {
      var c;

      c <- O.l_or_r(m, m0);
      n <- n + 1;
      cs <- (n, (c, m)) :: cs;
      return c;
    }

    proc dec (c : ciphertext) : plaintext option = {
      var fcs, m, p;

      fcs <- List.filter (fun p => fst (snd p) = c) cs;
      if (fcs <> []) {
        p <$ drat fcs;
        m <- Some (snd (snd p));
      } else {
        m <- O.dec(c);
      }
      return m;
    }
  }

  proc main (pk : pkey) : bool = {
    var r;

    n <- 0;
    cs <- [];
    O'.init(pk);
    r <@ A(O').main();
    return r;
  }
}.

section.

declare module A : Adversary {Real, Real', Ideal, Ideal', C.Wrap, B, B', CountCCA, CountICCA}.

axiom A_bound (O <: ICCA_Oracle {A, CountICCA}) : hoare [CountAdv(A, O).main :
               true ==> CountICCA.ndec <= Ndec /\ CountICCA.nenc <= Nenc].

equiv AB_bound (O <: CCA_Oracle{CountICCA, CountCCA, A, B}) :
  C.CountAdv(B(A), O).main ~ CountAdv(A, B(A, O).O').main :
  ={glob A, glob O} /\ B.cs{2} = [] /\ arg{1} = B.pk{2} ==>
  CountCCA.ndec{1} <= CountICCA.ndec{2} /\ CountCCA.nenc{1} = CountICCA.nenc{2}.
proof.
proc. inline*; sp; auto.
call (: ={glob O, glob B} /\ CountCCA.ndec{1} <= CountICCA.ndec{2} /\
        CountCCA.nenc{1} = CountICCA.nenc{2}) => //.
- by proc; auto.
- by proc; inline *; sp; auto; call (: true); auto => /> /#.
- proc; inline *; sp; auto.
  if; auto => />; 2: by smt().
  by sp; call (: true); auto => /> /#.
qed.

lemma B_bound (O <: CCA_Oracle{CountCCA, CountICCA, A, B}) :
  hoare [C.CountAdv(B(A), O).main :
    true ==> CountCCA.ndec <= Ndec /\ CountCCA.nenc <= Nenc].
proof.
by conseq (AB_bound (<: O)) (A_bound (<: B(A, O).O')) => // /#.
qed.

equiv Real_Real' :
  Game(Real, A).main ~ Game(Real', A).main : ={glob A} ==> ={res}.
proof.
proc; inline *.
call (: ={glob Real} /\ (exists ks, (Real.pk, Real.sk){2} = (pkgen ks, skgen ks)) /\
        (forall c m, assoc Ideal.cs c = Some m => dec(c, Real.sk) = Some m){2}).
- by proc; auto.
- proc; wp; rnd; auto=> /> &m2 ks Hcs e _ c m'.
  rewrite assoc_cons. case: (c = enc (m{m2}, pkgen ks, e)) => />; 1: by rewrite encK.
  by move => _; apply: Hcs.
- by proc; wp; skip => /> &m2 ks Hcs /#.
- by wp; rnd; skip => /> /#.
qed.

equiv Real_Real'' :
  Game(Real, A).main ~ Game(Real'', A).main : ={glob A} ==> ={res}.
proof.
proc; inline *.
call (: ={glob Real} /\ (exists ks, (Real.pk, Real.sk){2} = (pkgen ks, skgen ks)) /\
        (forall c p, p \in drat (List.filter (fun p => fst (snd p) = c) Ideal'.cs) =>
                     dec(c, Real.sk) = Some (snd (snd p))){2}).
- by proc; auto.
- proc; wp; rnd; auto => /> &m2 ks csP e ? c ?.
  case: (enc (m{m2}, pkgen ks, e) = c); 2: by move => _; apply csP.
  rewrite supp_drat in_cons.
  move => ? [|]; 1: smt(encK).
  by rewrite -supp_drat; apply csP.
- proc; sp; if{2}; 2: by auto => />.
  auto => /> &m2 ks Hcs fP; split; 1: smt(drat_ll).
  by move => _; apply Hcs.
- by wp; rnd; skip => />; smt(supp_drat).
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
  Game(Real', A).main ~ CCA_L(S, B(A)).main : ={glob A} ==> ={res}.
proof.
proc; inline *; wp.
call (: ={pk, sk}(Real, Wrap) /\ unzip1 Ideal.cs{1} = Wrap.cs{2} /\
        (forall c m, assoc Ideal.cs c = Some m => dec(c, Real.sk) = Some m){1} /\
        (exists ks, (Wrap.pk, Wrap.sk){2} = (pkgen ks, skgen ks)) /\
        Ideal.cs{1} = B.cs{2} /\ B.pk{2} = Wrap.pk{2}).
- by proc; inline *; auto => />.
- proc; inline *; auto => /> &m1 &m2 Hcs ks ? ? e _ c m'.
  by rewrite assoc_cons; case : (c = enc (m{m2}, pkgen ks, e)) => />; smt(encK).
- proc; inline *; auto => /> &m1 &m2 Hcs ks ? ?.
  by rewrite -assocTP.
- by wp; rnd; skip => /> /#.
qed.

equiv Real''_CCA_L :
  Game(Real'', A).main ~ CCA_L(S, B'(A)).main : ={glob A} ==> ={res}.
proof.
proc; inline *; wp.
call (: ={pk, sk}(Real,Wrap) /\ unzip1 (unzip2 Ideal'.cs{1}) = Wrap.cs{2} /\
        (forall c i m, (i, (c, m)) \in List.filter (fun p => fst (snd p) = c)
                                                   Ideal'.cs =>
                       dec(c, Real.sk) = Some m){1} /\
        (exists ks, (Wrap.pk, Wrap.sk){2} = (pkgen ks, skgen ks)) /\
        Ideal'.cs{1} = B'.cs{2} /\ B'.pk{2} = Wrap.pk{2} /\
        Ideal'.n{1} = B'.n{2}).
- by proc; inline *; auto => />.
- proc; inline *; auto => /> &m1 &m2 Hcs ks skP ? e _ c i ?.
  case: (enc (m{m2}, pkgen ks, e) = c).
  + move => ? [|?]; 1: smt(encK).
    by rewrite -skP; apply (Hcs c i); smt().
  + by move => _ ?; rewrite -skP; apply (Hcs c i); smt().
- proc; inline *; sp; auto; if; auto => /> &m1 &m2 Hcs ks ? ? csP.
  rewrite mem_map_fst; move => [?].
  rewrite mem_map_snd; smt(mem_filter).
- by wp; rnd; skip => /> /#.
qed.

equiv Ideal_CCA_R :
  Game(Ideal, A).main ~ CCA_R(S, B(A)).main : ={glob A} ==> ={res}.
proof.
proc; inline *; wp.
call (: ={pk, sk}(Real,Wrap) /\ unzip1 Ideal.cs{1} = Wrap.cs{2} /\
        (forall c m, assoc Ideal.cs c = Some m => dec(c, Real.sk) = Some m0){1} /\
        (exists ks, (Wrap.pk, Wrap.sk){2} = (pkgen ks, skgen ks)) /\
        Ideal.cs{1} = B.cs{2} /\ B.pk{2} = Wrap.pk{2}).
- by proc; inline *; auto => />.
- proc; inline *; auto => /> &m1 &m2 Hcs ks ? ? e _ c m'.
  by rewrite assoc_cons; case : (c = enc (m0, pkgen ks, e)) => />; smt(encK).
- proc; inline *; auto => /> &m1 &m2 Hcs ks ? ?.
  by rewrite -assocTP.
- by wp; rnd; skip => /> /#.
qed.

equiv Ideal'_CCA_R :
  Game(Ideal', A).main ~ CCA_R(S, B'(A)).main : ={glob A} ==> ={res}.
proof.
proc; inline *; wp.
call (: ={pk, sk}(Real,Wrap) /\ unzip1 (unzip2 Ideal'.cs{1}) = Wrap.cs{2} /\
        (forall c i m, (i, (c, m)) \in List.filter (fun p => fst (snd p) = c)
                                                   Ideal'.cs =>
                       dec(c, Real.sk) = Some m0){1} /\
        (exists ks, (Wrap.pk, Wrap.sk){2} = (pkgen ks, skgen ks)) /\
        Ideal'.cs{1} = B'.cs{2} /\ B'.pk{2} = Wrap.pk{2} /\
        Ideal'.n{1} = B'.n{2}).
- by proc; inline *; auto => />.
- proc; inline *; auto => /> &m1 &m2 Hcs ks skP ? e _ c i m'.
  case: (enc (m0, pkgen ks, e) = c); 1: smt(encK).
  by move => _ ?; rewrite -skP; apply (Hcs c i m'); smt().
- proc; inline *; sp; auto; if; auto => /> &m1 &m2 Hcs ks ? ? csP.
  rewrite mem_map_fst; move => [?].
  rewrite mem_map_snd; smt(mem_filter).
- by wp; rnd; skip => /> /#.
qed.

lemma ICCA_CCALR &m :
  Pr[Game(Real, A).main() @ &m : res] - Pr[Game(Ideal, A).main() @ &m : res] =
  Pr[CCA_L(S, B(A)).main() @ &m : res] - Pr[CCA_R(S, B(A)).main() @ &m : res].
proof.
have -> : Pr[Game(Real, A).main() @ &m : res] = Pr[Game(Real', A).main() @ &m : res].
- byequiv => //; conseq (: ={glob A} ==> ={res}) => //; exact Real_Real'.
have -> : Pr[Game(Real', A).main() @ &m : res] = Pr[CCA_L(S, B(A)).main() @ &m : res].
- byequiv => //; conseq (: ={glob A} ==> ={res}) => //; exact Real'_CCA_L.
have -> : Pr[Game(Ideal, A).main() @ &m : res] = Pr[CCA_R(S, B(A)).main() @ &m : res]; 2: by smt().
byequiv => //; conseq (: ={glob A} ==> ={res}) => //; exact Ideal_CCA_R.
qed.

lemma ICCA_CCALR' &m :
  Pr[Game(Real, A).main() @ &m : res] - Pr[Game(Ideal', A).main() @ &m : res] =
  Pr[CCA_L(S, B'(A)).main() @ &m : res] - Pr[CCA_R(S, B'(A)).main() @ &m : res].
proof.
have -> : Pr[Game(Real, A).main() @ &m : res] = Pr[Game(Real'', A).main() @ &m : res].
- byequiv => //; conseq (: ={glob A} ==> ={res}) => //; exact Real_Real''.
have -> : Pr[Game(Real'', A).main() @ &m : res] = Pr[CCA_L(S, B'(A)).main() @ &m : res].
- byequiv => //; conseq (: ={glob A} ==> ={res}) => //; exact Real''_CCA_L.
have -> : Pr[Game(Ideal', A).main() @ &m : res] = Pr[CCA_R(S, B'(A)).main() @ &m : res]; 2: by smt().
byequiv => //; conseq (: ={glob A} ==> ={res}) => //; exact Ideal'_CCA_R.
qed.

end section.

end ICCA.
