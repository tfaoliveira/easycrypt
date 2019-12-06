require import AllCore List DBool SmtMap.

abstract theory SKE.

type key.
type plaintext.
type ciphertext.

module type SKE = {
  proc * init(): unit {}
  proc kg(): key
  proc enc(k:key,p:plaintext): ciphertext 
  proc dec(k:key,c:ciphertext): plaintext option
}.

module Correctness (S:SKE) = {
  proc main (p:plaintext) = {
    var k, c, q;
    S.init();
    k <@ S.kg();
    c <@ S.enc(k,p);
    q <@ S.dec(k,c);
    return q = Some p;
  } 
}.

end SKE.

abstract theory SKE_RND.

clone include SKE.

module type Oracles = {
  proc * init() : unit
  proc enc(p:plaintext): ciphertext 
  proc dec(c:ciphertext): plaintext option
}.

module type CCA_Oracles = {
  include Oracles [-init]
}.

module type CCA_Adv (O:CCA_Oracles) = {
  proc main() : bool 
}.

module type CPA_Oracles = {
  include Oracles [-init, dec]
}.

module type CPA_Adv (O:CPA_Oracles) = {
  proc main() : bool 
}.

module CCA_game(A:CCA_Adv, O:Oracles) = {
  proc main() = {
    var b;
    O.init();
    b <@ A(O).main();
    return b;
  }
}.

module CPA_game(A:CPA_Adv, O:Oracles) = CCA_game(A,O).

module Mem = {
  var k   : key
  var log :  (ciphertext, plaintext) fmap
  var lc  : ciphertext list
}.

(* ------------------------------------------------------------------ *)
(* Real word: simply call the encryption/decryption with the key      *)

module RealOrcls (S:SKE) : CCA_Oracles = {

  proc init() = {
    S.init();
    Mem.k <@ S.kg();
  }

  proc enc(p:plaintext) = {
    var c;
    c <@ S.enc(Mem.k,p);
    return c;
  }

  proc dec(c:ciphertext) = {
    var p;
    p <@ S.dec(Mem.k,c);
    return p;
  } 
}.

module CPA_CCA_Orcls(O:CPA_Oracles) : CCA_Oracles = {
  proc init () = {
    Mem.log <- empty;
    Mem.lc  <- [];
  }

  proc enc(p:plaintext) = {
    var c;
    c <@ O.enc(p);
    Mem.log.[c] <- p;
    return c;
  }

  proc dec(c:ciphertext) = {
     Mem.lc <- if c \in Mem.log then Mem.lc else c :: Mem.lc;
    return Mem.log.[c];
  } 
}.

module CCA_CPA_Adv(A:CCA_Adv, O:CPA_Oracles) = {
  proc main () = {
    var b;
    CPA_CCA_Orcls(O).init();
    b <@ A(CPA_CCA_Orcls(O)).main();
    return b;
  }
}.
      
(* ------------------------------------------------------------------- *)
(* In this game we log the answers to the encryption queries.          *)
(* We prove that if the scheme is correct this does not change.        *)

abstract theory CCA_CPA_UFCMA.

(* We assume that we have a deterministic and stateless algorithm for the decryption *)

type globS.
op enc : globS -> key -> plaintext -> ciphertext.
op dec : globS -> key -> ciphertext -> plaintext option.
op valid_key : key -> bool.
axiom dec_enc : 
  forall k, valid_key k =>
    forall gs p, dec gs k (enc gs k p) = Some p.

module type StLOrcls = {
  proc * init () : globS
  proc kg () : key
}.

module StLSke (StL:StLOrcls) : SKE = {
  var gs : globS

  proc init () = { 
    gs <- StL.init();
  }
 
  proc kg = StL.kg

  proc enc(k:key, p:plaintext) = {
    return enc gs k p;
  }

  proc dec(k:key, c:ciphertext) = {
    return dec gs k c;
  }

}.

module UFCMA(A:CCA_Adv, StL:StLOrcls) = 
  CPA_game(CCA_CPA_Adv(A), RealOrcls(StLSke(StL))).
(* event : exists c, c \in Mem.lc /\ dec StLSke.gs Mem.k c <> None *)

section PROOFS.

  declare module St : StLOrcls { StLSke, Mem }.
  axiom valid_kg : hoare [St.kg : true ==> valid_key res].

  declare module A  : CCA_Adv { StLSke, Mem, St }.
  axiom A_ll : forall (O <: CCA_Oracles{A}), islossless O.enc => islossless O.dec => islossless A(O).main.

  equiv eqv_CCA_UFCMA : CCA_game(A, RealOrcls(StLSke(St))).main ~ UFCMA(A, St).main :
     ={glob A} ==> !(exists c, c \in Mem.lc /\ dec StLSke.gs Mem.k c <> None){2} => ={res}.
  proof.
    proc; inline *; wp.
    call (_: (exists c, c \in Mem.lc /\ dec StLSke.gs Mem.k c <> None),
              ={StLSke.gs, Mem.k} /\ 
              valid_key Mem.k{1} /\
              (forall c, c \in Mem.log => dec StLSke.gs Mem.k c = Mem.log.[c]){2}).
    + by apply A_ll.
    + proc; inline *; conseq />.
      by auto => />; smt (mem_set get_setE dec_enc).
    + by move=> _ _; islossless.
    + by move=> _; conseq />; islossless.
    + by proc; inline *; auto => /> /#.
    + by move=> _ _; islossless.
    + by move=> _; proc; auto => /#.
    wp; conseq (_: ={glob A} ==> ={glob A, StLSke.gs, Mem.k}) (_: true ==> valid_key Mem.k) _ => />.
    + smt (mem_empty).
    + by call valid_kg.
    by sim.
  qed.

  lemma CCA_CPA_UFCMA &m : 
    Pr[CCA_game(A, RealOrcls(StLSke(St))).main() @ &m : res] <=
     Pr[CPA_game(CCA_CPA_Adv(A), RealOrcls(StLSke(St))).main() @ &m : res] + 
     Pr[UFCMA(A, St).main() @ &m : (exists c, c \in Mem.lc /\ dec StLSke.gs Mem.k c <> None)].
  proof. byequiv eqv_CCA_UFCMA => /> /#. qed.
  
end section PROOFS.

end CCA_CPA_UFCMA.

end SKE_RND.

(*
lemma Real_Log 
  (S <: SKE { Mem })
  (A <: CCA_Adv { Mem, S })
  (gdec : glob S -> glob_dec): 
  (* We assume that we have a deterministic stateless algorithm for the decryption *)
  (forall (s0:glob S) (k0:key) (c0:ciphertext),
     phoare[ S.dec : 
             glob S = s0 /\ k = k0 /\ c = c0 ==>
             res = odec (gdec s0) k0 c0 /\ glob S = s0] = 1%r) =>
  (* Encryption does not modify decryption *)
  (forall (kc:key) (c:ciphertext) k0 p0,
     hoare [S.enc : glob S = s0 /\ k = k0 /\ p = p0 ==> 
                    odec (gdec (glob S) k0 res = Some p0  
                    odec (gdec (glob S)) k0 c0 
  equiv [ CCA_game(A, RealOrcls(S)).main ~ CCA_game(A, LogOrcls(S)).main : 
           ={glob A} ==> 
           ={res, glob A, glob S, Mem.k}].
proof.
  



.
 : true.

  declare module S: SKE { Mem }.
  declare module A: CCA_Adv { Mem, S}.

  axiom dec_spec (s0:glob S) (k0:key) (c0:ciphertext):
    phoare [S.dec : glob S = s0 /\ 

islossless S.dec.
 

  
  op odec
  axiom dec_stateless : 
     exists odec : glob S -> plaintext -> ciphertext option,
       forall (s:glob S) p, phoare [ S.dec : glob S = s
  op odec : glob S -> plaintext option.

  local module RealLog = {
    include LogOrcls(S) [init, enc]
    include RealOrcls(S) [dec]
  }.

  lemma Real_Log : 
    equiv [ CCA_game(A, RealOrcls(S)).main ~ CCA_game(A, LogOrcls(S)).main : 
             ={glob A} ==> ={res, glob A, Mem.k}].
  proof.
    proc; inline *.
    transitivity*{1} { S.init();          
                       Mem.k <@ S.kg();         
                       Mem.log <- empty;
                       Mem.lc <- [];
                       LogOrcls(S).all_decs();
                       b <@ A(RealLog).main(); } => //; 1: smt().
    + inline *; rcondf{2} ^while; last by sim.
      by auto; do 2! call (_:true). 
    transitivity*{2} { S.init();          
                       Mem.k <@ S.kg();         
                       Mem.log <- empty;
                       Mem.lc <- [];
                       b <@ A(LogOrcls(S)).main();
                       LogOrcls(S).all_decs(); } => //; 1: smt(); last first.
    + inline *; while{1} true (size Mem.lc{1} - i{1}).
      + by move=> _ z; wp; call dec_ll; auto => /#.
      by sim : (={Mem.k, b, glob A}) => /#.
    seq 4 4 : (={glob A, glob S, glob Mem}); 1: by sim.
    eager call (: ={glob A, glob S, glob Mem} ==> 
                  ={res, glob A, glob S, glob Mem}) => //.
    eager proc (H : LogOrcls(S).all_decs(); ~ LogOrcls(S).all_decs(); :
                     ={glob S, glob Mem} ==> ={glob S,glob Mem})
               (={glob S, glob Mem});auto => //; 1,3,5: by sim.
    + eager proc.
      swap{2} 4 1; wp 4 4.
      transitivity*{1} { LogOrcls(S).all_decs();
                         c <@ S.enc(Mem.k, p);
                         Mem.log.[c] <@ S.    
                         
                         Mem.log.[c] <- p;    
                         Mem.lc <- rcons Mem.lc c;
                         result <- c;

      
admit.
    + admit.
    
 1,3,5,7 : by sim.
      conseq (_: ={Mem.k, b, glob A}); 1: smt().
      by sim.
    
      sim.
smt ().
    

  
  






















op dciphertext : plaintext -> ciphertext distr.

module IdealSKE : CCA_Oracles = {

  proc init() = {
    Mem.log <- empty;
  }

  proc enc(p:plaintext) = {
    var c;
    c <$ dciphertext p;
    Mem.log.[c] <- p;
    return c;
  }

  proc dec(c:ciphertext) = {
    return Mem.log.[c];
  }
}.







end SKE_RND.

(*

module type CPA_Oracles = {
  proc lr(p1 p2: plaintext) : ciphertext option
  proc enc(p:plaintext): ciphertext 
}.

module type CCA_Oracles = {
  include CPA_Oracles
  proc dec(c:ciphertext): plaintext option
}.

module type Adv_INDCPA (O:CPA_Oracles) = {
  proc guess(): bool
}.

module type Adv_INDCCA (O:CCA_Oracles) = {
  proc guess(): bool
}.

module WrapS (S:Scheme) : CCA_Oracles = {
  var k   : key
  var b   : bool
  var cs  : ciphertext option
  var log : (ciphertext, plaintext) fmap

  proc init(): unit = {
    S.init();
    k  <- S.kg();
    b  <$ {0,1};
    cs <- None;
    log <- empty;
  }

  proc lr(p1 p2:plaintext) : ciphertext option = {
    var c, r;
    r = None;
    (* We do not answer if the [lr] oracle has been already queried *)
    if (cs = None) {
      c  <@ S.enc(k, if b then p1 else p2);
      cs <- Some c;
      r  <- cs;
    }
    return r;
  } 

  proc enc(p:plaintext): ciphertext = {
    var c:ciphertext;
    c = S.enc(k,p);
    log.[c] <- p;
    return c;
  }

  proc dec(c:ciphertext): plaintext option = {
    var r = None;
    (* We do not answer if [c] correspond to the challenge [cs] or if the cipher has been generated by 
       [enc] *)
    if (cs <> Some c) {
    (* If it is an answer to the encryption oracle we return the msg directly *)
      if (c \in log) r <- log.[c]; 
      else r <@ S.dec(k,c); 
    }
    return r;
  }
}.

module INDCPA (S:Scheme, A:Adv_INDCPA) = {
  module O = WrapS(S)

  proc main(): bool = {
    var b';
    O.init();
    b' <@ A(O).guess();
    return (WrapS.b = b');
  }
}.

module INDCCA (S:Scheme, A:Adv_INDCCA) = {
  module O = WrapS(S)

  proc main(): bool = {
    var b';
    O.init();
    b' <@ A(O).guess();
    return (WrapS.b = b');
  }
}.

module type UFCMA_Oracles = {
  proc sign (_:plaintext) : ciphertext
  proc submit (_:ciphertext) : unit 
}.

module type Adv_UFCMA (O:UFCMA_Oracles) = {
  proc forge () : unit
}.
 
module WrapUF(S:Scheme) = {
  var k:key
  var lc: ciphertext list
  var forged: bool

  proc init () = {
    S.init();
    k  <- S.kg();
    forged <- false;
    lc <- [];
  }
    
  proc sign (m:plaintext) : ciphertext = {
    var c;
    c <@ S.enc(k, m);
    lc <- c :: lc;
    return c;
  }

  proc submit(c:ciphertext) : unit = {
    var d;
    d <@ S.dec(k,c);
    forged <- forged || (d <> None && !(c \in lc));
  }
}.
  
module UFCMA(S:Scheme, A:Adv_UFCMA) = {
  module O = WrapUF(S)
  proc main () = {
    O.init();
    A(O).forge();
    return WrapUF.forged;
  }
}.

(* *************************************************************** *)
(* We prove that CCA <= CPA + CMA                                  *)

module Adv_INDCPA (A:Adv_INDCCA, O:CPA_Oracles) = {

  var m : (ciphertext, plaintext) fmap
  var cs : ciphertext option

  module OCCA = {
    proc enc(p:plaintext) : ciphertext = {
      var c;
      c <@ O.enc(p);
      m.[c] <- p;
      return c;
    }
    
    proc lr(p1 p2:plaintext) = {
      var r = None;
      if (cs = None) {
        cs  <@ O.lr(p1, p2);
        r <- cs;
      }
      return r;
    }

    proc dec(c:ciphertext) = {
      var r = None;
      if (cs <> Some c) r <- m.[c];
      return r;
    }  
  }
  
  proc guess() : bool = {
    var b;
    m  <- empty;
    cs <- None;
    b <@ A(OCCA).guess();
    return b;
  }
}.

module Adv_UFCMA(A:Adv_INDCCA, O:UFCMA_Oracles) = {

  module OCCA = {
    proc lr(p1 p2:plaintext) : ciphertext option = {
      var c, r;
      r = None;
      (* We do not answer if the [lr] oracle has been already queried *)
      if (WrapS.cs = None) {
        c  <@ O.sign(if WrapS.b then p1 else p2);
        WrapS.cs <- Some c;
        r  <- WrapS.cs;
      }
      return r;
    } 
  
    proc enc(p:plaintext): ciphertext = {
      var c:ciphertext;
      c = O.sign(p);
      WrapS.log.[c] <- p;
      return c;
    }
  
    proc dec(c:ciphertext): plaintext option = {
      var r = None;
      (* We do not answer if [c] correspond to the challenge [cs] or if the cipher has been generated by 
        [enc] *)
      if (WrapS.cs <> Some c) {
      (* If it is an answer to the encryption oracle we return the msg directly *)
        if (c \in WrapS.log) r <- WrapS.log.[c]; 
        else O.submit(c); 
      }
      return r;
    }
  }

  proc forge () = {
    var b';
    WrapS.b  <$ {0,1};
    WrapS.cs <- None;
    WrapS.log <- empty;
    b' <@ A(OCCA).guess();
  }

}.

module E2 (S : Scheme) = {
  proc enc_dec (k : key, p1: plaintext, c2 : ciphertext) : ciphertext * plaintext option = {
    var c1, p2;
    c1 <@ S.enc(k,p1);
    p2 <@ S.dec(k,c2);
    return (c1,p2);
  }
  proc dec_enc (k : key, p1: plaintext, c2 : ciphertext) : ciphertext * plaintext option = {
    var c1, p2;
    p2 <@ S.dec(k,c2);
    c1 <@ S.enc(k,p1);
    return (c1,p2);
  }
}.

section PROOFS.

  declare module S:Scheme{ WrapS, WrapUF, Adv_INDCPA}.
  declare module A:Adv_INDCCA {S,WrapS, WrapUF, Adv_INDCPA}.


  axiom enc_ll : islossless S.enc.
  axiom dec_ll : islossless S.dec.
  axiom A_ll   : 
    forall (O <: CCA_Oracles{A}), 
      islossless O.lr => islossless O.enc => islossless O.dec => islossless A(O).guess.

  local module WrapS1 : CCA_Oracles = {
    var bad : bool
    var lc  : ciphertext list

    proc init(): unit = {
      S.init();
      WrapS.k  <- S.kg();
      WrapS.b  <$ {0,1};
      WrapS.cs <- None;
      WrapS.log <- empty;
      bad <- false;
      lc <- [];
    }
  
    proc lr(p1 p2:plaintext) : ciphertext option = {
      var c, r;
      r = None;
      (* We do not answer if the [lr] oracle has been already queried *)
      if (WrapS.cs = None) {
        c <- witness;
        c <@ S.enc(WrapS.k, if WrapS.b then p1 else p2);
        WrapS.cs <- Some c;
        r  <- WrapS.cs;
      }
      return r;
    } 
  
    proc enc(p:plaintext): ciphertext = {
      var c:ciphertext;
      c <- witness;
      c = S.enc(WrapS.k,p);
      WrapS.log.[c] <- p;
      return c;
    }
  
    proc dec(c:ciphertext): plaintext option = {
      var r = None;
      (* We do not answer if [c] correspond to the challenge [cs] or if the cipher has been generated by 
         [enc] *)
      if (WrapS.cs <> Some c) {
      (* If it is an answer to the encryption oracle we return the msg directly *)
        if (c \in WrapS.log) r <- WrapS.log.[c]; 
        else {
          lc <- rcons lc c;
          r <@ S.dec(WrapS.k,c); 
          bad <- bad || r <> None;
          r <- None;
        }
      }
      return r;
    }

    proc all_decs () = {
      var i, p, c;
      i = 0;
      p <- witness;
      c <- witness;
      while (i < size lc) {
        c <- nth witness lc i;
        p <@ S.dec(WrapS.k, c);
        i <- i + 1;
      }
    }

  }.

  local module AUX = {
    proc main(): bool = {
      var b';
      WrapS1.init();
      b' <@ A(WrapS1).guess();
      return (WrapS.b = b');
    }
  }.
  
  local equiv CCA_AUX : INDCCA(S,A).main ~ AUX.main : ={glob A, glob S} ==> (!WrapS1.bad{2} => ={res}).
  proof.
    proc;inline *; wp.
    call (_: WrapS1.bad, ={glob S, glob WrapS}).
    + by apply A_ll.
    + by proc;inline *; sp; if => //;wp;call(_:true); auto.
    + by move=> &2 _; islossless; apply enc_ll.
    + move=> _; conseq />; islossless; apply enc_ll.
    + by proc;inline *; sim />.
    + by move=> &2 _; islossless; apply enc_ll.
    + by move=> &2; conseq />; islossless; apply enc_ll.
    + proc; sp 1 1; if => //. 
      if; 1,2: by auto.
      by auto; call(_:true); auto => />.
    + by move=> &2 _; islossless; apply dec_ll.
    + by move=> &2;proc; sp; if => //; if => //; auto; call dec_ll; auto => />.
    by auto; do 2! call(_:true); auto => /> /#.
  qed.

  local equiv AUX_UFCMA : AUX.main ~ UFCMA(S, Adv_UFCMA(A)).main : ={glob A, glob S} ==> WrapS1.bad{1} = res{2}.
  proof.
    proc; inline *; wp.
    call (_:  WrapS1.bad{1} = WrapUF.forged{2} /\ 
              ={glob S, WrapS.b, WrapS.cs, WrapS.log} /\ WrapS.k{1} = WrapUF.k{2} /\
              (forall c, c \in WrapUF.lc => (c \in  WrapS.log \/ WrapS.cs = Some c)){2}).
    + proc; inline *; sp 1 1; if => //.
      by auto; call (_:true); auto => /> /#. 
    + by proc; inline *; wp; call (_:true); auto => />; smt (mem_set).
    + proc; inline *; sp; if => //; if => //; auto.
      by call (_:true); auto => /> /#.
    by auto; do 2! call (_: true); auto.
  qed.

  local module WrapS2 = {
    include WrapS1 [-dec, init]
    proc init () : unit = {
      S.init();
      WrapS.k  <- S.kg();
      WrapS.b  <$ {0,1};
      WrapS.cs <- None;
      WrapS.log <- empty;
      WrapS1.lc <- [];
      WrapS1.all_decs();
    }
      
    proc dec(c:ciphertext): plaintext option = {
      var r = None;
      (* We do not answer if [c] correspond to the challenge [cs] or if the cipher has been generated by 
         [enc] *)
      if (WrapS.cs <> Some c) {
      (* If it is an answer to the encryption oracle we return the msg directly *)
        if (c \in WrapS.log) r <- WrapS.log.[c]; 
        else {
          WrapS1.lc <- rcons WrapS1.lc c;
          r <@ S.dec(WrapS.k,c); 
          r <- None;
        }
      }
      return r;
    }
  }.

  local module WrapS3 = {
    include WrapS1 [-dec, init]
    proc init () : unit = {
      S.init();
      WrapS.k  <- S.kg();
      WrapS.b  <$ {0,1};
      WrapS.cs <- None;
      WrapS.log <- empty;
      WrapS1.lc <- [];
    }
      
    proc dec(c:ciphertext): plaintext option = {
      var r = None;
      (* We do not answer if [c] correspond to the challenge [cs] or if the cipher has been generated by 
         [enc] *)
      if (WrapS.cs <> Some c) {
      (* If it is an answer to the encryption oracle we return the msg directly *)
        if (c \in WrapS.log) r <- WrapS.log.[c]; 
        else {
          WrapS1.lc <- rcons WrapS1.lc c;
        }
      }
      return r;
    }
  }.
 
  axiom enc_dec : equiv [ E2(S).enc_dec ~ E2(S).dec_enc : ={arg, glob S} ==> ={res, glob S}].

  local equiv AUX_CPA : AUX.main ~INDCPA(S, Adv_INDCPA(A)).main : ={glob A, glob S} ==> ={res}.
  proof.
    proc.
    transitivity* {1} { WrapS2.init();
                        b' <@ A(WrapS2).guess(); } => />; 1: by smt().
    + inline *; sim.
      by rcondf{2} ^while; auto; do 2!call (_:true).
    transitivity*{1} { WrapS3.init();
                       b' <@ A(WrapS3).guess(); 
                       WrapS1.all_decs();
                      } => />; 1: smt(); last first.
    + inline{1} WrapS1.all_decs.
      while{1} true (size WrapS1.lc - i){1}.
      + by move=> _ z; wp; call dec_ll; auto; smt(head_behead).
      wp; conseq (_: ={b', WrapS.b}); 1: smt(size_eq0 size_ge0).
      inline *; wp.
      call (_:  ={glob S, glob WrapS} /\ 
                 Adv_INDCPA.m{2} = WrapS.log{1} /\
                 Adv_INDCPA.cs{2} = WrapS.cs{1}).
      + proc; inline *; sp; if => //.
        by rcondt{2} 4; auto; call (_: true); auto.
      + by proc; inline *; auto; call (_: true); auto.
      + by proc; inline *; auto => /> ??; rewrite domNE => ->. 
      by auto; do 2!call (_:true); auto.
    (* Eager stuff *)
    inline WrapS2.init WrapS3.init.  
    seq 6 6 : ( ={glob S, glob A, glob WrapS, WrapS1.lc} ).
    + by auto; do 2! call (_:true).
    eager call (: ={glob A, glob S, glob WrapS, WrapS1.lc} ==> 
                   ={res, glob A, glob S, glob WrapS, WrapS1.lc}) => //.
    eager proc (H : WrapS1.all_decs(); ~ WrapS1.all_decs(); :
       ={glob S, glob WrapS, WrapS1.lc}
       ==> ={glob S,glob WrapS, WrapS1.lc})
       (={glob S, glob WrapS, WrapS1.lc});auto => //; 1,3,5,7 : by sim.

    + eager proc.
      swap{1} 2 -1; sp 1 1.
      swap{2} 2 1; wp.
      eager if => //; last by sim.
      + by move=> &m2 b1; conseq />.
      swap{1} 1 1; sp 1 1.
      swap{2} -2; wp; inline WrapS1.all_decs.
      swap{2} 3; sp 3 3.
      conseq (_: ={glob S, glob WrapS, WrapS1.lc, p1, p2, c, i, c0, p} ==> ={glob S, c}) => />.
      symmetry.
      eager while (H1: c <@ S.enc(WrapS.k, if WrapS.b then p1 else p2); ~
                       c <@ S.enc(WrapS.k, if WrapS.b then p1 else p2); : 
                       ={glob S, glob WrapS, WrapS1.lc, p1, p2, c, i, c0, p} ==>
                       ={glob S, glob WrapS, WrapS1.lc, p1, p2, c, i, c0, p}) => //; 1,3: by sim.
      swap{1} 1; seq 1 1 : (#pre); 1: by auto.
      swap{2} 2 1; wp; conseq />.
      transitivity*{1} { (c,p) <@ E2(S).enc_dec(WrapS.k, if WrapS.b then p1 else p2, c0); } => //; 1: smt().
      + by inline *; auto; do 2! call (_: true); auto.
      transitivity*{2} { (c,p) <@ E2(S).dec_enc(WrapS.k, if WrapS.b then p1 else p2, c0); } => //; 1: smt().
      + by call enc_dec.
      by inline *; auto; do 2! call (_: true); auto.

    + eager proc.
      swap{1} 1; sp 1 1.
      swap{2} -2; wp; inline WrapS1.all_decs.
      swap{2} 3; sp 3 3.
      conseq (_: ={glob S, glob WrapS, WrapS1.lc, p0, c, i, c0, p} ==> ={glob S, c}) => />.
      symmetry.
      eager while (H1: c <@ S.enc(WrapS.k, p); ~
                       c <@ S.enc(WrapS.k, p); : 
                       ={glob S, glob WrapS, WrapS1.lc, p0, c, i, c0, p} ==>
                       ={glob S, glob WrapS, WrapS1.lc, p0, c, i, c0, p}) => //; 1,3: by sim.
      swap{1} 1; seq 1 1 : (#pre); 1: by auto.
      swap{2} 2 1; wp; conseq />.
      transitivity*{1} { (c,p0) <@ E2(S).enc_dec(WrapS.k, p, c0); } => //; 1: smt().
      + by inline *; auto; do 2! call (_: true); auto.
      transitivity*{2} { (c,p0) <@ E2(S).dec_enc(WrapS.k, p, c0); } => //; 1: smt().
      + by call enc_dec.
      by inline *; auto; do 2! call (_: true); auto.

    eager proc.      
    swap{1} 2 -1; sp 1 1.
    swap{2} -1; wp.
    eager if => //; 1: by move=> &m2 b1; conseq />.
    + eager if => //; 1: by move=> &m2 b1; conseq />.
      + by swap{1} 1;sim.
      swap{1} 2 1; wp; inline WrapS1.all_decs.
      conseq (: ={glob S} /\ rcons WrapS1.lc{1} c{1} = WrapS1.lc{2}); 1: by progress.
      splitwhile{2} 5 : (i < size WrapS1.lc - 1).
      seq 4 5 : (={glob S, WrapS.k, i} /\ rcons WrapS1.lc{1} c{1} = WrapS1.lc{2} /\ (i = size WrapS1.lc){1}).
      + while (={glob S, WrapS.k, i} /\ rcons WrapS1.lc{1} c{1} = WrapS1.lc{2} /\ (0 <= i <= size WrapS1.lc){1}).
        + by wp; call (_:true); auto => />; smt (size_rcons nth_rcons).
        by auto => />; smt (size_rcons size_ge0).
      rcondt{2} ^while.   
      + move=> &m; auto => />; smt(size_rcons).
      rcondf{2} ^while.
      + move=> &m;auto; conseq (:true) => // />; smt (size_rcons).
      wp; call (_:true); auto => />; smt (nth_rcons).
    by sim. 
  qed.

  lemma CCA_from_CPA_UFCMA &m : 
    Pr[INDCCA(S,A).main() @ &m : res] <=
    Pr[INDCPA(S,Adv_INDCPA(A)).main() @ &m : res] +
    Pr[UFCMA(S,Adv_UFCMA(A)).main() @ &m : res].
  proof.
    have : Pr[INDCCA(S,A).main() @ &m : res] <=
           Pr[AUX.main() @ &m : res] + Pr[AUX.main() @ &m : WrapS1.bad].
    + by byequiv CCA_AUX => /> /#.
    have -> : Pr[AUX.main() @ &m : WrapS1.bad] = Pr[UFCMA(S, Adv_UFCMA(A)).main() @ &m : res].
    + by byequiv AUX_UFCMA.
    have -> //: Pr[AUX.main() @ &m : res] = Pr[INDCPA(S, Adv_INDCPA(A)).main() @ &m : res].
    by byequiv AUX_CPA.
  qed.

end section PROOFS.

print CCA_from_CPA_UFCMA.
*)
*)