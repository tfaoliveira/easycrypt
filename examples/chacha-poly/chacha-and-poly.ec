require import AllCore Int IntExtra Distr Real SmtMap DBool List DProd FSet.

require (****) CCA_from_CPA_and_UF_CMA Indistinguishability PROM RndProd.


type cckey.
type cct1.
type cct2.


type polykey, polyt1, polyt2, polyt4.
type last_block.
type nonce, associated_data, plaintext, ciphertext.
type tag = polyt4.

op good_size : int -> bool.
axiom good_size_leq i j : 0 <= i <= j => good_size j => good_size i.

op cc_concat : int -> nonce -> cct1.
axiom cc_concat_neq_i i j n : good_size i => good_size j => i <> j => 
  cc_concat i n <> cc_concat j n.
axiom cc_concat_neq_nonce i j n1 n2 : good_size i => good_size j => n1 <> n2 => 
  cc_concat i n1 <> cc_concat j n2.
axiom good_size_ge0 i : good_size i => 0 <= i.
axiom cc_concat_inj i j n m : good_size i => good_size j => cc_concat i n = cc_concat j m => (i,n) = (j,m).


op trunc32 : cct2 -> polykey * polyt4.
op concat32 : polykey * polyt4 -> cct2.
axiom trunc32_K : cancel trunc32 concat32.
axiom concat32_K : cancel concat32 trunc32.

op dcct2 : cct2 distr.
op dpolykey : polykey distr.
op dpolyt4 : polyt4 distr.

axiom dcct2_ll : is_lossless dcct2.
axiom dcct2_fu : is_funiform dcct2.
axiom dpolykey_ll : is_lossless dpolykey.
axiom dpolyt4_ll : is_lossless dpolyt4.
axiom dpolyt4_fu : is_funiform dpolyt4.

axiom dcct2_dpkey_dpt4 : dmap dcct2 trunc32 = dpolykey `*` dpolyt4.

op poly_concat : associated_data -> ciphertext -> polyt1.

op (+^) : cct2 -> cct2 -> cct2.
op (+) : polyt2 -> polyt4 -> tag.
op (-) : polyt4 -> polyt2 -> tag.
axiom add_sub_A : forall x y z, z + (x - y) = z + x - y.
axiom add_sub_K : forall x y, x = y + (x - y).
op (^+) : last_block -> last_block -> last_block.


(* plaintext operators *)
op plength : plaintext -> int.
axiom plength_ge0 p : 0 <= plength p.

op pnth : cct2 -> plaintext -> int -> cct2.
op empty_ptxt : plaintext.
op pappend : plaintext -> cct2 -> plaintext.
op pappend_last : plaintext -> last_block -> plaintext.
op ptrunc_last : plaintext -> cct2 -> last_block.
op plast_block : plaintext -> last_block.

axiom ptrunc_last_block: forall p, exists b, plast_block p = ptrunc_last p b.
axiom ptrunc_add p b1 b2 :
  ptrunc_last p (b1 +^ b2) = (ptrunc_last p b1) ^+ (ptrunc_last p b2).
axiom add_block_K b1 b2: b1 = b1 +^ b2 +^ b2.

(* ciphertext operators *)
op clength : ciphertext -> int.
axiom clength_ge0 c : 0 <= clength c.
op cnth : cct2 -> ciphertext -> int -> cct2.
op empty_ctxt : ciphertext.
op cappend : ciphertext -> cct2 -> ciphertext.
op cappend_last : ciphertext -> last_block -> ciphertext.
op ctrunc_last : ciphertext -> cct2 -> last_block.
op clast_block : ciphertext -> last_block.


(* op dcipher : plaintext -> ciphertext distr. *)
(* axiom dcipher_ll (p : plaintext) : is_lossless (dcipher p). *)

(* op sigma : int. *)
(* axiom sigma_gt0 : 0 < sigma. *)
(* op q : int. *)
(* axiom a_gt0 : 0 < q. *)

(* op dtag : tag distr. *)

(* type counter = int * int. *)
(* op update_poly_p (c : int) (a : associated_data) (p : plaintext) : int. *)
(* op update_poly_c (c : int) (a : associated_data) (c : ciphertext) : int. *)
(* op update_cost_enc (c : counter) (n : nonce) (a : associated_data) (p : plaintext) : counter = *)
(*   (c.`1 + max 1 (plength p) + 1, c.`2 + update_poly_p c.`2 a p). *)
(* op update_cost_dec (c : counter) (n : nonce) (a : associated_data) (ci : ciphertext) (t : tag) : counter = *)
(*   (c.`1 + max 1 (clength ci) + 1, c.`2 + update_poly_c c.`2 a ci). *)
(* op overcome_cost_enc (c : counter) (n : nonce) (a : associated_data) (p : plaintext) : bool = *)
(*   let (c1, c2) = update_cost_enc c n a p in c1 <= sigma /\ c2 <= q. *)
(* op overcome_cost_dec (c : counter) (n : nonce) (a : associated_data) (ci : ciphertext) (t : tag) : bool = *)
(*   let (c1, c2) = update_cost_dec c n a ci t in c1 <= sigma /\ c2 <= q. *)


clone import CCA_from_CPA_and_UF_CMA as AEAD with
  type plain <- nonce * associated_data * plaintext,
  type cipher <- nonce * associated_data * ciphertext * tag,
  type key <- cckey
proof *.

(* module Fresh (E : SKE) : SKE = { *)
(*   var nonce : (nonce, associated_data * plaintext * ciphertext * tag) fmap *)
(*   proc init () : unit = { *)
(*     nonce = empty; *)
(*     E.init(); *)
(*   } *)
(*   proc enc (n : nonce, a : associated_data, p : plaintext) : ciphertext * tag = { *)
(*     var a1, p1, c1, t1, c, t; *)
(*     (c, t) <- witness; *)
(*     if (n \in nonce) { *)
(*       (a1, p1, c1, t1) <- oget nonce.[n]; *)
(*       if (a1 = a /\ p1 = p) { *)
(*         (c, t) <- (c1,t1); *)
(*       } *)
(*     } elif (good_size (plength p)) { *)
(*       (c, t) <- E.enc(n,a,p); *)
(*       nonce.[n] <- (a,p,c,t); *)
(*     } *)
(*     return (c, t); *)
(*   } *)
(*   proc dec (n : nonce, a : associated_data, c : ciphertext, t : tag) : plaintext option = { *)
(*     var a1, p1, c1, t1, opt; *)
(*     opt <- None; *)
(*     if (n \in nonce) { *)
(*       (a1, p1, c1, t1) <- oget nonce.[n]; *)
(*       if (a1 = a /\ c1 = c /\ t1 = t) { *)
(*         opt <- Some p1; *)
(*       } *)
(*     } elif (good_size (clength c)) { *)
(*       opt <@ E.dec(n,a,c,t); *)
(*       if (opt <> None) { *)
(*         nonce.[n] <- (a,oget opt, c,t); *)
(*       } *)
(*     } *)
(*     return opt; *)
(*   } *)
(* }. *)

(* module A_fresh_nonce (A : Adversary) (E : Oracle) = { *)
(*   proc challenge () : nonce * associated_data * plaintext = { *)
(*     var r; *)
(*     Fresh(E).init(); *)
(*     r <@ A(Fresh(E)).challenge(); *)
(*     return r; *)
(*   } *)
(*   proc guess = A(Fresh(E)).guess *)
(* }. *)

module type CC = {
  proc enc (_: cckey * cct1) : cct2
}.

module type FCC = {
  proc keygen () : cckey
  proc enc (_: cckey * cct1) : cct2
}.

module type KRO = {
  proc mac (_: polykey * polyt1) : polyt2
}.

module (Composition (CC : FCC) (Poly : KRO) : SKE) = {
  proc keygen = CC.keygen
  proc enc (k : cckey, nap : nonce * associated_data * plaintext) : 
    (nonce * associated_data * ciphertext * tag) option  = {
    var n, a, p, x, r, s, i, z, y, c, c', t, t';

    t' <- witness;
    (n,a,p) <- nap;
    c     <- empty_ctxt;
    x     <@ CC.enc(k, cc_concat 0 n);
    (r,s) <- trunc32 x;
    i     <- 1;
    while (i < plength p) {
      z <@ CC.enc(k, cc_concat i n);
      y <- z +^ pnth witness p (i-1);
      c <- cappend c y;
      i <- i + 1;
    }
    y  <@ CC.enc(k, cc_concat i n);
    c' <- ptrunc_last p y;
    c' <- c' ^+ plast_block p;
    c  <- cappend_last c c';
    t' <@ Poly.mac(r, poly_concat a c);
    t  <- t' + s;
    return Some (n,a,c,t);
  }
  proc dec (k : cckey, nact : nonce * associated_data * ciphertext * tag) : 
    (nonce * associated_data * plaintext) option = {
    var n, a, c, t, opt, x, r, s, t', t2, i, z, y, p, p';

    t' <- witness;
    (n,a,c,t) <- nact;
    p     <- witness;
    opt   <- None;
    x     <@ CC.enc(k, cc_concat 0 n);
    (r,s) <- trunc32 x;
    t' <@ Poly.mac(r, poly_concat a c);
    t2 <- t' + s;
    if (t = t2) {
      i     <- 1;
      while (i < clength c) {
        z <@ CC.enc(k, cc_concat i n);
        y <- z +^ cnth witness c (i-1);
        p <- pappend p y;
        i <- i + 1;
      }
      y  <@ CC.enc(k, cc_concat i n);
      p' <- ctrunc_last c y;
      p' <- p' ^+ clast_block c;
      p  <- pappend_last p p';
      opt <- Some (n,a,p);
    }
    return opt;
  }
}.

module IdealSKE : SKE = {
  proc keygen () : cckey = {
    return witness;
  }
  proc enc (k : cckey, nap : nonce * associated_data * plaintext) : 
    (nonce * associated_data * ciphertext * tag) option  = {
    var n, a, p, i, y, c, c', t;

    (n,a,p) <- nap;
    c     <- empty_ctxt;
    t     <$ dpolyt4;
    i     <- 1;
    while (i < plength p) {
      y <$ dcct2;
      c <- cappend c y;
      i <- i + 1;
    }
    y  <$ dcct2;
    c' <- ptrunc_last p y;
    c  <- cappend_last c c';
    return Some (n,a,c,t);
  }
  proc dec (k : cckey, nact : nonce * associated_data * ciphertext * tag) : 
    (nonce * associated_data * plaintext) option = {
    return None;
  }
}.

clone import Indistinguishability as Indist with
  type t_in <- cct1,
  type t_out <- cct2
proof *.

module (WrapCC (CC : FCC) : Function) = {
  proc init () : unit = {
    Wrap.k <@ CC.keygen();
  }
  proc f (c : cct1) = {
    var y;
    y <@ CC.enc(Wrap.k,c);
    return y;
  }
}.


module IndistCC (A : Distinguisher) (CC : FCC) = Distinguish(A,WrapCC(CC)).

module (CCA_to_CC_indist (Poly : KRO) (A : CCA_Adv) : Distinguisher) (CC : Oracle) = {
  module C = {
    proc keygen () : cckey = {
      return Wrap.k;
    }
    proc enc (k : cckey, x) = {
      var y;
      y <@ CC.f(x);
      return y;
    }
  }
  module E = Composition(C,Poly)
  proc guess () : bool = {
    var b;

    Wrap(E).init();
    b <@ A(Wrap(E)).guess();
    return b;

  }
}.

(* nonce respecting adversary *)
module NR (C : SKE) = {
  var nonces : (nonce, associated_data * plaintext * ciphertext * tag) fmap
  proc keygen () = {
    var k;
    nonces <- empty;
    k <@ C.keygen();
    return k;
  }
  proc enc (k : cckey, nap : nonce * associated_data * plaintext) = {
    var n, a, p, opt, c, t;

    (n,a,p) <- nap;
    opt <- None;
    if (n \notin nonces /\ good_size (plength p + 1)) {
      opt <@ C.enc(k,nap);
      if (opt <> None) {
        (n,a,c,t) <- oget opt;
        nonces.[n] <- (a,p,c,t);
      }
    }
    return opt;
  }
  proc dec (k : cckey, nact : nonce * associated_data * ciphertext * tag) = {
    var n, a, c, t, opt, p;

    (n,a,c,t) <- nact;
    opt <- None;
    if (n \notin nonces /\ good_size (clength c + 1)) {
      opt <@ C.dec(k,nact);
      if (opt <> None) {
        (n,a,p) <- oget opt;
        nonces.[n] <- (a,p,c,t);
      }
    }
    return opt;
  }
}.

module (NR_Adv (C : CCA_SKE) : CCA_SKE) = {
  proc init() : unit = {
    NR.nonces <- empty;
  }
  proc enc (nap : nonce * associated_data * plaintext) = {
    var n, a, p, opt, c, t;

    (n,a,p) <- nap;
    opt <- None;
    if (n \notin NR.nonces /\ good_size (plength p + 1)) {
      opt <@ C.enc(nap);
      if (opt <> None) {
        (n,a,c,t) <- oget opt;
        NR.nonces.[n] <- (a,p,c,t);
      }
    }
    return opt;
  }
  proc dec (nact : nonce * associated_data * ciphertext * tag) = {
    var n, a, c, t, opt, p;

    (n,a,c,t) <- nact;
    opt <- None;
    if (n \notin NR.nonces /\ good_size (clength c + 1)) {
      opt <@ C.dec(nact);
      if (opt <> None) {
        (n,a,p) <- oget opt;
        NR.nonces.[n] <- (a,p,c,t);
      }
    }
    return opt;
  }
}.

module A_nonce_respecting (A : CCA_Adv) (C : CCA_SKE) = {
  proc guess () : bool = {
    var b;
    NR_Adv(C).init();
    b <@ A(NR_Adv(C)).guess();
    return b;
  }
}.

module URF : Function = {
  var map : (cct1, cct2) fmap
  proc init () : unit = {
    map <- empty;
  }
  proc f (x : cct1) : cct2 = {
    if (x \notin map) {
      map.[x] <$ dcct2;
    }
    return oget map.[x];
  }
}.

module CC_URF : FCC = {
  proc keygen () : cckey= {
    URF.init();
    return witness;
  }
  proc enc (k : cckey, x : cct1) = {
    var y;
    y <@ URF.f(x);
    return y;
  }
}.

module Swap_Poly (Poly : KRO) = {
  proc double_mac (a1 : polykey * polyt1, a2 : polykey * polyt1) : polyt2 * polyt2 = {
    var r1, r2;
    r1 <@ Poly.mac(a1);
    r2 <@ Poly.mac(a2);
    return (r1,r2);
  }
  proc double_reverse_mac (a1 : polykey * polyt1, a2 : polykey * polyt1) : polyt2 * polyt2 = {
    var r1, r2;
    r2 <@ Poly.mac(a2);
    r1 <@ Poly.mac(a1);
    return (r1,r2);
  }
}.

clone PROM.GenEager as PolyURF with
  type from <- cct1,
  type to   <- cct2,
  op sampleto <- fun _ => dcct2
proof * by smt(dcct2_ll).

module TestPoly (Poly : KRO) = {
  var forgery : bool
  proc loop (l : (nonce * associated_data * ciphertext * tag) list) = {
    var i, n, a, c, t, t', t2, x, r, s;

    forgery <- false;
    PolyURF.RO.init();
    i <- 0;
    while (i < size l) {
      (n, a, c, t) <- nth witness l i;
      x <@ PolyURF.RO.get(cc_concat 0 n);
      (r, s) <- trunc32 x;
      t' <@ Poly.mac(r, poly_concat a c);
      t2 <- t' + s;
      if (t = t2) {
        forgery <- true;
      }
      i <- i + 1;
    }
  }
}.

module type Output = {
  proc list () : (nonce * associated_data * ciphertext * tag) list
}.

module TestListPoly (O : Output) (Poly : KRO) = {
  proc game () = {
    var l;
    l <@ O.list();
    TestPoly(Poly).loop(l);
    return TestPoly.forgery;
  }
}.

module Order (E : SKE) : SKE = {
  var dec : (nonce * associated_data * ciphertext * tag) list
  proc keygen () : cckey = {
    var key;
    dec <- [];
    key <@ E.keygen();
    return key;
  }
  proc enc = E.enc
  proc dec (k : cckey, nact : nonce * associated_data * ciphertext * tag) : 
    (nonce * associated_data * plaintext) option = {
    var r;
    dec <- rcons dec nact;
    r <@ E.dec(k,nact);
    return r;
  }
}.

module OutputDecOrder (A : CCA_Adv) (E : SKE) : Output = {
  proc list () = {
    EncDec(A,Order(E)).game();
    return Order.dec;
  }
}.

(*----------------------------------------------------------------------------*)
section.

declare module Chacha  : FCC { Wrap, NR, URF, WrapForgery, Order }.
declare module Poly    : KRO { Chacha, Wrap, NR, URF, WrapForgery, Order }.
(* Poly -> changer en opérateur *)
declare module CCA_Adv : CCA_Adv { Poly, Chacha, Wrap, NR, URF, WrapForgery, Order }.


(* local equiv equiv_enc (A <: CCA_Adv { Chacha, Poly })  *)
(*   (CC <: FCC { A, Poly }) :  *)
(*   Count(Log(Composition(CC, Poly))).enc ~  *)
(*   Count(Log(Composition(CCA_to_CC_indist(Poly, A, CountCC(CC)).C, Poly))).enc : *)
(*     ={n, a, p} /\ ={glob Count, glob Log, glob CC, glob Poly} /\ *)
(*     CountCC.c{2} <= Counter.c{1}.`1 *)
(*   ==> *)
(*     ={res} /\ ={glob Count, glob Log, glob CC, glob Poly} /\ *)
(*     CountCC.c{2} <= Counter.c{1}.`1. *)
(* proof. *)
(* proc; inline*; if; auto; sp. *)
(*  rcondt{2} 1=> /=; 1: by auto; smt(plength_ge0). *)
(*  conseq/>. *)
(*  call(: ={glob CC})=> />; 1: smt().  *)
(*  wp=> />. conseq/>. *)
(*  conseq(:_==> ={r, c1, s, glob CC} /\ y{1} = y2{2} /\  *)
(*     CountCC.c{2} <= (update_cost_enc Counter.c{2} n{2} a{2} p{2}).`1)=> />. *)
(*  rewrite/update_cost_enc/=. *)
(*  case: (plength p{2} <= 1). *)
(*  + rcondf{2} 6; 1: auto. *)
(*    - by call(:true); auto; smt(). *)
(*    rcondf{1} 4; 1: auto. *)
(*    - by call(:true); auto; smt(). *)
(*    rcondt{2} 8; 1: auto. *)
(*    - by call(:true); auto; smt(plength_ge0). *)
(*    by auto; call(: true); auto; call(: true); auto; smt(). *)
(*  conseq(:_==> ={r, c1, s, glob CC} /\ y{1} = y2{2} /\ i{2} = plength p{2} /\ *)
(*     CountCC.c{2} <= Counter.c{1}.`1 + i{2} + 1)=> />; 1: smt(). *)
(*  rewrite /overcome_cost_enc/update_cost_enc/=. *)
(*  rcondt{2} 9. *)
(*  + auto. *)
(*    while(CountCC.c + plength p - i + 1 <= sigma /\ 1 <= i <= plength p /\ p1 = p). *)
(*    - auto. *)
(*      sp; rcondt 1; 1: by auto; smt(). *)
(*      by auto; call(: true); auto; smt(). *)
(*    by wp; call(: true); auto; smt(). *)
(*  wp; conseq(:_==> ={r, c1, s, glob CC} /\ y{1} = y2{2} /\ i{2} = plength p{2} /\ *)
(*     CountCC.c{2} <= Counter.c{1}.`1 + i{2})=> />; 1: smt(). *)
(*  call(: true); auto=> />. *)
(*  conseq(:_==> ={i, n, glob CC, c1, r, s} /\ i{2} = plength p1{2} /\  *)
(*       CountCC.c{2} <= Counter.c{2}.`1 + i{2})=>/>. *)
(*  while(={i, p1, n1, c1, r, s, glob CC} /\ 1 <= i{2} <= plength p1{2} /\ *)
(*     CountCC.c{2} <= Counter.c{2}.`1 + i{2} /\ *)
(*     Counter.c{2}.`1 + plength p1{2} + 1 <= sigma). *)
(*  + by auto; sp; rcondt{2} 1; auto; 2: call(: true); auto; smt(). *)
(*  by auto; call(: true); auto; smt(). *)
(* qed. *)

(* local equiv equiv_dec (A <: Adversary { Count, Log, CountCC, Chacha, Poly })  *)
(*   (CC <: FCC { A, Poly, Log, CountCC, Count }) : *)
(*   Count(Log(Composition(CC, Poly))).dec ~  *)
(*   Count(Log(Composition(CCA_to_CC_indist(Poly, A, CountCC(CC)).C, Poly))).dec : *)
(*     ={n, a, c, t} /\ ={glob Count, glob Log, glob CC, glob Poly} /\ *)
(*     CountCC.c{2} <= Counter.c{1}.`1 *)
(*   ==> *)
(*     ={res} /\ ={glob Count, glob Log, glob CC, glob Poly} /\ *)
(*     CountCC.c{2} <= Counter.c{1}.`1. *)
(* proof. *)
(* proc; inline*; if; auto; sp=> /=; if; auto; 1: smt(). *)
(*  if; 1,2: by auto; smt(). *)
(*  sp; rcondt{2} 1; 1: by auto; smt(). *)
(*  wp=> />. *)
(*  swap{2} 2 4. *)
(*  rewrite /overcome_cost_dec/update_cost_dec/=. *)
(*  seq 4 5 : (={t2, t1, c1, c, n1, p, opt, glob CC, glob Poly, Counter.c} /\ *)
(*      Counter.c{1}.`1 + max 1 (clength c1{1}) + 1 <= sigma /\ c1{1} = c{1} /\ *)
(*      CountCC.c{2} <= Counter.c{1}.`1). *)
(*  + by auto; call(: true); auto; call(: true); auto. *)
(*  sp; if; auto; -1: smt(). *)
(*  conseq(:_==> ={p, c1, glob CC} /\ y{1} = y2{2} /\  *)
(*      CountCC.c{2} <= Counter.c{2}.`1 + max 1 (clength c1{2}) + 1)=> />. *)
(*  rcondt{2} 5; auto. *)
(*  + case(clength c1 <= 1). *)
(*    - by rcondf 2; auto; smt(). *)
(*    while(CountCC.c + 1 <= Counter.c.`1 + i + 1 <= Counter.c.`1 + max 1 (clength c1) + 1 <= sigma); auto. *)
(*    - by sp; rcondt 1; auto; 2: call(: true); auto; smt(). *)
(*    smt(). *)
(*  call(: true); auto=> />; sp. *)
(*  case: (clength c1{1} <= 1). *)
(*  + rcondf{1} 1; 1: by auto; smt(). *)
(*    by rcondf{2} 1; auto; smt(). *)
(*  conseq(:_==> ={i, n1, glob CC, p, c1} /\ i{2} = clength c1{2} /\ *)
(*            CountCC.c{2} + 1 <= Counter.c{2}.`1 + i{2} + 1); 1: smt(). *)
(*  while(={i, n1, p, c1, glob CC} /\ 1 <= i{2} <= clength c1{2} /\ *)
(*      CountCC.c{2} + 1 <= Counter.c{2}.`1 + i{2} + 1/\ *)
(*      Counter.c{2}.`1 + clength c1{2} + 1 <= sigma). *)
(*  + sp; rcondt{2} 1; 1: by auto; smt(). *)
(*    by auto; call(: true); auto; smt(). *)
(*  auto; smt(). *)
(* qed. *)

local lemma rewrite1 (A <: CCA_Adv { Chacha, Poly, Wrap }) &m
  (CC <: FCC { A, Poly, Wrap }) : 
  Pr [EncDec(A,Composition(CC,Poly)).game() @ &m : res ] = 
  Pr [IndistCC(CCA_to_CC_indist(Poly,A),CC).game() @ &m : res ].
proof.
byequiv=> //; proc.
inline *; wp.
call(: ={glob CC, glob Poly, glob Wrap})=> />; auto.
+ proc; sim.
  inline {1} 1; inline {2} 1; sp; sim.
  seq 4 4 : (={t2, t, c0, k, n, p0, a, glob CC, glob Poly, glob Wrap, opt, c} /\ 
    k{2} = Wrap.k{2}).
  - by inline*; wp; call(: true); auto=> />; 1: smt(); call(: true); auto=> />.
  if; auto=> />.
  inline*; wp; call(: true); auto.
  conseq(:_==> ={i, n, glob CC, p0} /\ k{1} = Wrap.k{2})=> />.
  by while(={i, c0, n, p0, glob CC} /\ k{1} = Wrap.k{2}); auto; call(: true); auto.
+ proc; sim.
  inline {1} 1; inline {2} 1; sp; sim.
  inline {2} 5; wp.
  inline {2} 7; wp; call(: true); auto=> />.
  conseq(:_==> ={i, n, glob CC, c0, s, r})=> />.
  by inline *; while(={i, n, c0, s, r, k, p0, glob CC} /\ k{1} = Wrap.k{2}); 
    auto; call(: true); auto=> />.
call(: true); auto=> />.
qed.


local lemma Chacha_to_URF
  (A <: CCA_Adv { URF, Wrap, Chacha, Poly }) &m :
  `| Pr [ EncDec(A,Composition(Chacha,Poly)).game() @ &m : res ] - 
     Pr [ EncDec(A,Composition(CC_URF,Poly)).game() @ &m : res ]| <=
  `| Pr [ IndistCC(CCA_to_CC_indist(Poly,A),Chacha).game() @ &m : res ] -
     Pr [ IndistCC(CCA_to_CC_indist(Poly,A),CC_URF).game() @ &m : res ] |.
proof.
by rewrite (rewrite1 A &m Chacha) (rewrite1 A &m CC_URF).
qed.

local module Random : CC = {
  proc keygen () : cckey = {
    return witness;
  }
  proc enc (k: cckey, x: cct1) : cct2 = {
    var y;
    y <$ dcct2;
    return y;
  }
}.

local lemma enc_to_encdec
    (CC <: FCC { Wrap, Poly })
    (A <: CCA_Adv { URF, Wrap, Chacha, Poly, WrapForgery, CC }) &m : 
    Pr[Enc   (Adv_Dec_None(A), Composition(CC, Poly)).game() @ &m : res] =
    Pr[EncDec(Adv_Dec_None(A), Composition(CC, Poly)).game() @ &m : res].
proof. by byequiv=>//=; proc; sim. qed.


local lemma chacha_poly_to_URF_and_forge (A <: CCA_Adv { URF, Wrap, Chacha, Poly, WrapForgery }) &m :
  islossless Poly.mac => islossless Chacha.enc =>
  (forall (C <: CCA_SKE{A}), islossless C.dec => islossless C.enc => islossless A(C).guess) =>
  (equiv[ E2(Composition(CC_URF, Poly)).enc_dec ~
          E2(Composition(CC_URF, Poly)).dec_enc :
         ={arg, glob Composition(CC_URF, Poly)} ==>
         ={res, glob Composition(CC_URF, Poly)}]) =>
  `| Pr [ EncDec(             A ,Composition( Chacha ,Poly)).game() @ &m : res ]
   - Pr [ EncDec(Adv_Dec_None(A),Composition( CC_URF ,Poly)).game() @ &m : res ] |

    <= Pr [ Forge(A,Composition(CC_URF,Poly)).game() @ &m : res ]

       + `| Pr [ IndistCC(CCA_to_CC_indist(Poly,A), Chacha ).game() @ &m : res ]
          - Pr [ IndistCC(CCA_to_CC_indist(Poly,A), CC_URF ).game() @ &m : res ] |.
proof.
move=> Poly_ll Chacha_enc_ll A_ll E_swap.
rewrite-(enc_to_encdec CC_URF A &m).
have bound:=Chacha_to_URF A &m. 
have:= cca_from_cpa_and_uf_cma (Composition(CC_URF,Poly)) A &m _ _ A_ll E_swap.
+ proc; auto.
  seq 8 : true; auto.
  + inline*; auto; call(Poly_ll); auto; sp; if; auto; smt(dcct2_ll). 
  if; auto. 
  inline*; sp; auto. 
  seq 1 : true; auto; last first.
  - by sp; if; auto; smt(dcct2_ll).
  while(true)(clength c - i); auto; -1: smt(). 
  by sp; if; auto; smt(dcct2_ll).
+ proc; inline*; auto.
  call(Poly_ll); auto.
  by seq 13 : true; auto; 1: while(true)(plength p - i); auto; sp; if; auto; smt(dcct2_ll).
smt().
qed.


(******************************************************************************)
(* treatment of : Pr [ EncDec(Adv_Dec_None(A),Composition(CC_URF,Poly)).game() @ &m : res ] *)

op log_is_fresh (m : (nonce * associated_data * ciphertext * tag,
                      nonce * associated_data * plaintext) fmap)
  (m2 : (nonce, associated_data * plaintext * ciphertext * tag) fmap) =
  forall n a p c t,
    m2.[n] = Some (a,p,c,t) <=> m.[(n,a,c,t)] = Some (n,a,p).

op urf_is_fresh (map : (cct1, cct2) fmap)
  (m2 : (nonce, associated_data * plaintext * ciphertext * tag) fmap) =
  forall (n : nonce), n \notin m2 =>
  forall (i : int), good_size i =>
  cc_concat i n \notin map.

op invariant m2 m3 = urf_is_fresh m3 m2.

local lemma invariant_set m2 m3 n:
    invariant m2 m3 =>
    forall i,
    good_size i =>
    forall a p c t b,
    invariant m2.[n <- (a, p, c, t)] m3.[cc_concat i n <- b].
proof. smt(mem_set cc_concat_neq_nonce). qed.

local lemma invariant_setS m2 m3 n i:
    good_size (i+1) =>
    forall a1 p1 c1 t1 b1,
    invariant m2.[n <- (a1, p1, c1, t1)] m3.[cc_concat i n <- b1] =>
    forall a2 p2 c2 t2 b2,
    invariant m2.[n <- (a2, p2, c2, t2)] m3.[cc_concat (i+1) n <- b2].
proof. smt(mem_set cc_concat_neq_nonce). qed.


local lemma URF_indist_random
  (A <: CCA_Adv { URF, Wrap, Chacha, Poly, NR }) &m :
  Pr[EncDec(Adv_Dec_None(A_nonce_respecting(A)),Composition(CC_URF,Poly)).game() @ &m : res ] =
  Pr[EncDec(Adv_Dec_None(A_nonce_respecting(A)),Composition(Random,Poly)).game() @ &m : res ].
proof. 
byequiv=> //=; proc; inline*; sp; sim.
call(: ={glob Poly, glob Wrap, glob NR} /\ invariant NR.nonces{2} URF.map{1}).
+ by proc; inline*; auto.
+ proc; inline*; sp; if; 1, 3: auto; sp.
  rcondt{1} 1; 1: by auto; smt(good_size_leq plength_ge0).
  rcondt{1} 19; 1: auto.
  - by conseq(:_==> true);auto.
  rcondt{1} 21; 1: auto.
  - by conseq(:_==> true);auto.
  rcondt{2} 16; 1: auto.
  - by conseq(:_==> true);auto.
  rcondt{2} 18; 1: auto.
  - by conseq(:_==> true);auto.
  wp=> />. 
  conseq(:_==> ={c1, t', s, glob Poly} /\
    invariant (NR.nonces.[n0 <- (a0, p1, c1, t' + s)]){2} URF.map{1})=>/>.
  call(: true); wp=> />; 1: smt().
  conseq(:_==> ={r, c1, s} /\ y2{2} = (oget URF.map{1}.[x5{1}]) /\
      forall result,
      invariant NR.nonces{2}.[n0{2} <- (a0{2}, p1{2}, cappend_last c1{2}
            (ptrunc_last p1{2} y2{2} ^+ plast_block p1{2}), result + s{2})] URF.map{1})=> />.
  rcondt{1} 10; 1: auto.
  - case: (1 < plength p1); last first.
    + rcondf 6; auto=> />. 
      move=> &h Hinv Hnin_nonces Hgood_size Hi y ?.
      rewrite mem_set negb_or.
      have//=H1:=good_size_leq 1 _ _ Hgood_size; 1:smt(plength_ge0).
      rewrite (Hinv n0{m0} Hnin_nonces 1 _)//=.
      have/=->//:=cc_concat_neq_i 1 0 n0{m0}.
      by have//=->//:=good_size_leq 0 1.
    conseq(:_==> cc_concat (plength p1) n0 \notin URF.map /\ i = plength p1)=>/>.
    while(cc_concat (plength p1) n0 \notin URF.map /\ good_size (plength p1) /\ 
              0 <= i <= plength p1).
    + sp; if; auto=> />.
      - move=> &h Hnin_map Hgoodsize Hi0 ? Hisize Hnini y ?.
        rewrite mem_set Hnin_map /=.
        by have->/=:=cc_concat_neq_i (plength p1{h}) i{h} n0{h} _ _ _; smt(good_size_leq).
      smt().
    auto=> /> &h Hinv Hnin_nonce Hgood_size Hgt1 y ?; split; 2: smt().
    split; 2: smt(good_size_leq).
    rewrite mem_set negb_or.
    smt(cc_concat_neq_i good_size_leq plength_ge0).
  auto=> /=.
  conseq(:_==> ={r, c1, s} /\ forall result y,
      invariant NR.nonces{2}.[n0{2} <-
        (a0{2}, p1{2}, cappend_last c1{2} (ptrunc_last p1{2} y ^+ plast_block p1{2}),
          result + s{2})] URF.map{1}.[cc_concat i{1} n0{1} <- y]).
  - smt(get_setE).
  alias {1} 1 urf = URF.map; sp.
  conseq(:_==> ={r, c1, s} /\ good_size i{1} /\
      invariant NR.nonces{2} urf{1} /\ n0{2} \notin NR.nonces{2} /\
      (forall nonce j, good_size j => cc_concat j nonce \in URF.map{1} => 
        cc_concat j nonce \in urf{1} \/ (0 <= j < i{1} /\ nonce = n0{1})) /\
      (forall nonce j, cc_concat j nonce \in urf{1} => 
        urf{1}.[cc_concat j nonce] = URF.map{1}.[cc_concat j nonce]) /\
      (forall j, 0 <= j < i{1} => cc_concat j n0{1} \in URF.map{1})).
  + move=> /> &l &r Hinv n0_nin_nonces pS_good_size 3? i_good_size H1 H2 H3 2?.
    rewrite mem_set negb_or/= => [#] n_nin_nonces n_neq_n0 j j_good_size.
    rewrite mem_set negb_or.
    split; 2: smt(domE cc_concat_neq_nonce).
    by have:=Hinv n n_nin_nonces j j_good_size; smt(). 
  case: (1 < plength p1{1}); last first.
  - rcondf{2} 5; 1: auto.
    rcondf{1} 6; auto=> />.
    move=> &l &r Hinv n0_nin_nonces pS_good_size p1_leq1 y h{h}.
    rewrite get_setE/= oget_some/=.
    have good_size_1//=:good_size 1 by smt(good_size_leq plength_ge0).
    rewrite good_size_1/=; do!split.
    - move=> nonce j j_good_size; rewrite mem_set.
      by have:=cc_concat_inj j 0 nonce n0{r} j_good_size _; smt(good_size_leq plength_ge0).
    - move=> nonce j n_in_urf.
      rewrite get_setE.
      by have:=Hinv _ n0_nin_nonces 0 _; smt(good_size_leq).
    smt(mem_set cc_concat_inj good_size_leq get_setE).
  while(={i, p1, k, n0, c1} /\ 1 <= i{1} <= plength p1{1} /\ 
        good_size (plength p1{1} + 1) /\ n0{1} \notin NR.nonces{2} /\
        invariant NR.nonces{2} urf{1} /\
      (forall nonce j, good_size j => cc_concat j nonce \in URF.map{1} => 
        cc_concat j nonce \in urf{1} \/ (0 <= j < i{1} /\ nonce = n0{1})) /\
      (forall nonce j, cc_concat j nonce \in urf{1} => 
        urf{1}.[cc_concat j nonce] = URF.map{1}.[cc_concat j nonce]) /\
      (forall j, 0 <= j < i{1} => cc_concat j n0{1} \in URF.map{1})).
  - sp; rcondt{1} 1; auto=> />.
    + smt(good_size_leq).
    smt(get_setE mem_set cc_concat_neq_i cc_concat_neq_nonce good_size_leq domE cc_concat_inj).
  auto=> /> &l &r hinv n0_nin_nonces pS_good_size p_gt_1 y h{h}; do!split.
  - smt().
  - move=> nonce j j_good_size; rewrite mem_set.
    by have:=cc_concat_inj j 0 nonce n0{r} j_good_size _; smt(good_size_leq plength_ge0).
    - move=> nonce j n_in_urf.
      rewrite get_setE.
      by have:=hinv _ n0_nin_nonces 0 _; smt(good_size_leq).
  - smt(mem_set cc_concat_inj good_size_leq get_setE).
  - smt(mem_set cc_concat_inj good_size_leq get_setE).
by auto; smt(mem_empty).
qed.


local module (Composition2 (CC : FCC) (Poly : KRO) : SKE) = {
  proc keygen = CC.keygen
  proc enc (k : cckey, nap : nonce * associated_data * plaintext) : 
    (nonce * associated_data * ciphertext * tag) option  = {
    var n, a, p, x, r, s, i, z, y, c, c', t, t';

    t' <- witness;
    (n,a,p) <- nap;
    c     <- empty_ctxt;
    x     <@ CC.enc(k, cc_concat 0 n);
    (r,t) <- trunc32 x;
    i     <- 1;
    while (i < plength p) {
      z <@ CC.enc(k, cc_concat i n);
      y <- z +^ pnth witness p (i-1);
      c <- cappend c y;
      i <- i + 1;
    }
    y  <@ CC.enc(k, cc_concat i n);
    c' <- ptrunc_last p y;
    c' <- c' ^+ plast_block p;
    c  <- cappend_last c c';
    t' <@ Poly.mac(r, poly_concat a c);
    s  <- t - t';
    return Some (n,a,c,t);
  }
  proc dec (k : cckey, nact : nonce * associated_data * ciphertext * tag) : 
    (nonce * associated_data * plaintext) option = {
    return None;
  }
}.

local clone ProdSampling as PD with
  type t1 <- polykey,
  type t2 <- polyt4
proof *.


local lemma step1_Poly_to_random
  (A <: CCA_Adv { URF, Wrap, Chacha, Poly, NR }) &m :
  Pr[EncDec(Adv_Dec_None(A_nonce_respecting(A)), Composition  (CC_URF,Poly)).game() @ &m : res ] =
  Pr[EncDec(Adv_Dec_None(A_nonce_respecting(A)), Composition2 (Random,Poly)).game() @ &m : res ].
proof.
rewrite(URF_indist_random A &m).
byequiv=>//=; proc; inline*; sp; sim.
call(: ={glob NR, glob Wrap, glob Poly}); auto.
+ by proc; inline*; auto.
proc; inline*; auto; sim; sp.
if; 1, 3: auto; sp; sim.
swap [1..3] 9.
conseq/>.
seq 9 9 : (={c1, a0, glob Poly}); 1: sim.
conseq/>.
replace{1} { <$; <-; <- as sample; rest } by {
    (r, s) <@ PD.S.sample(dpolykey,dpolyt4);
    rest;
  }
  (={c1, a0, glob Poly} ==> ={t0, glob Poly})
  (={c1, a0, glob Poly} ==> ={t0, glob Poly})=> //=; 1: smt().
+ sim; inline*; sim; wp.
  rnd trunc32 concat32; auto=> />; do ! split; 1: smt(trunc32_K concat32_K).
  move=> ?; do ! split.
  - move=> y; rewrite supp_dprod => [#] 2?.
    rewrite-dcct2_dpkey_dpt4 dmapE; apply mu_eq=> a //=.
    by rewrite /pred1 /(\o); smt(trunc32_K concat32_K).
  move=> ? y; rewrite -dcct2_dpkey_dpt4 supp_dmap => ?; split; 1: smt().
  smt(trunc32_K concat32_K).
replace{1} {| <@ as sample; rest } by {
    (r, s) <@ PD.S.sample2(dpolykey,dpolyt4);
    rest;
  }
  (={c1, a0, glob Poly} ==> ={t0, glob Poly})
  (={c1, a0, glob Poly} ==> ={t0, glob Poly})=> //=; 1: smt().
+ by sim; call PD.sample_sample2; auto.
replace{2} { <$; <-; <- as sample; rest } by {
    (r, t0) <@ PD.S.sample(dpolykey,dpolyt4);
    rest;
  }
  (={c1, a0, glob Poly} ==> ={t0, glob Poly})
  (={c1, a0, glob Poly} ==> ={t0, glob Poly})=> //=; 1: smt(); last first.
+ sim; inline*; sim; wp.
  rnd concat32 trunc32; auto=> />; do ! split; 1: smt(trunc32_K concat32_K).
  move=> ?; do ! split.
  - move=> y ?.
    rewrite-dcct2_dpkey_dpt4 dmapE; apply mu_eq=> a //=.
    by rewrite /pred1 /(\o); smt(trunc32_K concat32_K).
  move=> ? y; rewrite -dcct2_dpkey_dpt4 supp_dmap => ?; split; 1: smt().
  smt(trunc32_K concat32_K).
replace{2} {| <@ as sample; rest } by {
    (r, t0) <@ PD.S.sample2(dpolykey,dpolyt4);
    rest;
  }
  (={c1, a0, glob Poly} ==> ={t0, glob Poly})
  (={c1, a0, glob Poly} ==> ={t0, glob Poly})=> //=; 1: smt(); last first.
+ by symmetry; sim; call PD.sample_sample2; auto.
inline{1} 1; inline{2} 1.
replace{1} { <$ ; <$ ; <- as sample; rest } by {
    r <$ dpolykey;
    s <$ dpolyt4;
    rest;
  }
  (={c1, a0, glob Poly} ==> ={t0, glob Poly})
  (={c1, a0, glob Poly} ==> ={t0, glob Poly})=> //=; 1: smt().
+ by inline*; auto; sim; auto.
replace{2} { <$ ; <$ ; <- as sample; rest } by {
    r <$ dpolykey;
    t0 <$ dpolyt4;
    rest;
  }
  (={c1, a0, glob Poly} ==> ={t0, glob Poly})
  (={c1, a0, glob Poly} ==> ={t0, glob Poly})=> //=; 1: smt(); last first.
+ by inline*; auto; sim; auto.
sp; swap 2 1; wp.
seq 2 2 : (={t', glob Poly, r}); 1: sim.
exists* t'{1}; elim* => y.
rnd (fun x => y + x) (fun x=> x - y); auto=> />.
smt(dpolyt4_fu add_sub_K add_sub_A).
qed.



local module (Compo (CC : FCC) (Poly : KRO) : SKE) = {
  var order_enc : (polykey * associated_data * ciphertext) list
  var b : bool
  proc keygen () = {
    var key;
    order_enc <- [];
    b <- false;
    key <@ CC.keygen();
    return key;
  }
  proc enc (k : cckey, nap : nonce * associated_data * plaintext) : 
    (nonce * associated_data * ciphertext * tag) option  = {
    var n, a, p, i, z, y, c, c', t, x, r;

    (n,a,p) <- nap;
    x     <@ CC.enc(k, cc_concat 0 n);
    (r,t) <- trunc32 x;
    c     <- empty_ctxt;
    i     <- 1;
    while (i < plength p) {
      z <@ CC.enc(k, cc_concat i n);
      y <- z +^ pnth witness p (i-1);
      c <- cappend c y;
      i <- i + 1;
    }
    y  <@ CC.enc(k, cc_concat i n);
    c' <- ptrunc_last p y;
    c' <- c' ^+ plast_block p;
    c  <- cappend_last c c';
    order_enc <- rcons order_enc (r, a, c);
    return Some (n,a,c,t);
  }
  proc dec (k : cckey, nact : nonce * associated_data * ciphertext * tag) : 
    (nonce * associated_data * plaintext) option = {
    return None;
  }
  proc all_enc () = {
    var i, r, a, c;
    i <- 0;
    while (i < size order_enc) {
      (r, a, c) <- nth witness order_enc i;
      Poly.mac(r, poly_concat a c);
      i <- i + 1;
    }
  }
}.

local module (Compo2 (CC : FCC) (Poly : KRO) : SKE) = {
  proc keygen () = {
    var key;
    Compo.order_enc <- [];
    Compo.b <- false;
    key <@ CC.keygen();
    return key;
  }
  proc enc (k : cckey, nap : nonce * associated_data * plaintext) : 
    (nonce * associated_data * ciphertext * tag) option  = {
    var n, a, p, i, z, y, c, c', t, x, r;

    (n,a,p) <- nap;
    x     <@ CC.enc(k, cc_concat 0 n);
    (r,t) <- trunc32 x;
    c     <- empty_ctxt;
    i     <- 1;
    while (i < plength p) {
      z <@ CC.enc(k, cc_concat i n);
      y <- z +^ pnth witness p (i-1);
      c <- cappend c y;
      i <- i + 1;
    }
    y  <@ CC.enc(k, cc_concat i n);
    c' <- ptrunc_last p y;
    c' <- c' ^+ plast_block p;
    c  <- cappend_last c c';
    Poly.mac(r, poly_concat a c);
    Compo.order_enc <- rcons Compo.order_enc (r, a, c);
    return Some (n,a,c,t);
  }
  proc dec (k : cckey, nact : nonce * associated_data * ciphertext * tag) : 
    (nonce * associated_data * plaintext) option = {
    return None;
  }
}.


local lemma step2_Poly_to_random
  (A <: CCA_Adv { URF, Wrap, Chacha, Poly, NR, Compo }) &m :
  islossless Poly.mac =>
  Pr[EncDec(Adv_Dec_None(A_nonce_respecting(A)), Composition  ( CC_URF ,Poly)).game() @ &m : res ] =
  Pr[EncDec(Adv_Dec_None(A_nonce_respecting(A)), Compo        ( Random ,Poly)).game() @ &m : res ].
proof.
move=> Poly_ll.
rewrite (step1_Poly_to_random A &m).
have->:Pr[EncDec(Adv_Dec_None(A_nonce_respecting(A)), Composition2(Random, Poly)).game () @ &m : res] =
       Pr[EncDec(Adv_Dec_None(A_nonce_respecting(A)), Compo2(Random, Poly)).game() @ &m : res].
+ byequiv=> //=; proc; inline*; sp; sim.
  call(: ={glob Poly, glob Wrap, glob NR}); auto.
  - by proc; inline*; auto.
  proc; inline*; auto; sp; if; 1, 3: auto; sim; sp; sim.
  call(: true)=> //= />.
  by conseq(:_==> ={r, a0, c1, t0})=> //=; sim; auto.
byequiv(: ={glob A, glob Poly, Wrap.k} ==> ={res})=>//=; proc.
inline{1} 2; inline{2} 2; wp.
replace{1} { init; <@ |} by {
    init;
    Compo(Random,Poly).all_enc();
    Compo.b <@ A(NR_Adv(None(Wrap(Compo2(Random, Poly))))).guess();
    b0 <- Compo.b;
  }
  (={glob A, glob Poly, Wrap.k} ==> ={b0})
  (={glob A, glob Poly, Wrap.k} ==> ={b0})=> //=; 1: smt().
+ by sim; inline*; sp; rcondf{2} 1; 1: auto=> />; sim.
replace{2} { init; <@ |} by {
    init;
    Compo.b <@ A(NR_Adv(None(Wrap(Compo(Random, Poly))))).guess();
    Compo(Random,Poly).all_enc();
    b0 <- Compo.b;
  }
  (={glob A, glob Poly, Wrap.k} ==> ={b0})
  (={glob A, glob Poly, Wrap.k} ==> ={b0})=> //=; 1: smt(); last first.
+ swap{1} -1; sim.
  seq 4 3 : (={b0}); 1: by sim.
  inline*; conseq=>/>; auto.
  by while{1}(true)(size Compo.order_enc{1} - i{1}); auto; 1: call Poly_ll; auto; smt().
sim.
inline{1} 1; sp.
inline{1} 1; sp.
inline{1} 1; sp.
inline{1} 1; sp.
inline{2} 1; sp.
inline{2} 1; sp.
inline{2} 1; sp.
inline{2} 1; sp.
eager call (: ={glob Wrap, glob NR, glob Poly, glob A, glob Compo}
    ==> ={res, glob Wrap, glob NR, glob Poly, glob A, glob Compo}); auto.
eager proc (H : 
      Compo(Random, Poly).all_enc(); ~ 
      Compo(Random, Poly).all_enc(); :
    ={glob Wrap, glob NR, glob Compo, glob Poly}
    ==> ={glob Wrap, glob NR, glob Compo, glob Poly})
    (={glob Wrap, glob NR, glob Compo, glob Poly})=> />; 1, 3, 5: sim.
+ eager proc.
  by swap{2} -4; sim.
eager proc.
swap{1} 2; swap{2} -1; sim; sp.
if{2}; last first.
+ by rcondf{1} 2; 2: sim; 1: auto; conseq(:_==> true); auto.
rcondt{1} 2; 1: by auto; conseq(:_==> true)=>//=/>. 
swap{2} -1; sim.
inline{2} 1; inline{1} 2.
swap{1} 1; swap{2} -2; sp; sim.
inline{2} 1; inline{1} 2.
inline Random.enc.
swap{2} -1; sim. 
swap{1} 18.
sp=>/>.
seq 13 13 : (={r, a0, c1, t0, Compo.order_enc, glob Poly}); 1: by sim.
inline* => />; sp; wp.
splitwhile{2} 1 : i0 < size Compo.order_enc - 1.
seq 1 1 : (={i0, glob Poly} /\ i0{1} = size Compo.order_enc{1} /\
      Compo.order_enc{2} = rcons Compo.order_enc{1} (r{1}, a0{1}, c1{1})); last first.
+ rcondt{2} 1; 1: by auto; smt(size_rcons).
  rcondf{2} 4; 1: by auto; call(: true); auto; smt(size_rcons).
  auto; call(: true); auto=> /> &h.
  by rewrite nth_rcons /=.
while(={i0, glob Poly} /\ 0 <= i0{1} <= size Compo.order_enc{1} /\
      Compo.order_enc{2} = rcons Compo.order_enc{1} (r{1}, a0{1}, c1{1})).
+ auto; call(: true); auto=> /> &l &r.
  by rewrite size_rcons/= nth_rcons => 4?; smt().
by auto=> />; smt(size_rcons nth_rcons size_ge0).
qed.



local lemma step_1_chacha_poly_to_URF_and_forge
    (A <: CCA_Adv { URF, Wrap, Chacha, Poly, NR, WrapForgery, NR, Compo }) &m :
  islossless Poly.mac => islossless Chacha.enc =>
  (forall (C <: CCA_SKE{A}), islossless C.dec => islossless C.enc => islossless A(C).guess) =>
  (equiv[ E2(Composition(CC_URF, Poly)).enc_dec ~
          E2(Composition(CC_URF, Poly)).dec_enc :
         ={arg, glob Composition(CC_URF, Poly)} ==>
         ={res, glob Composition(CC_URF, Poly)}]) =>
  `| Pr[EncDec(             A_nonce_respecting(A) , Composition ( Chacha ,Poly)).game() @ &m : res ]
   - Pr[EncDec(Adv_Dec_None(A_nonce_respecting(A)), Compo       ( Random ,Poly)).game() @ &m : res ] |

    <= Pr [ Forge(A_nonce_respecting(A),Composition(CC_URF,Poly)).game() @ &m : res ]

       + `| Pr [ IndistCC(CCA_to_CC_indist(Poly,A_nonce_respecting(A)), Chacha ).game() @ &m : res ]
          - Pr [ IndistCC(CCA_to_CC_indist(Poly,A_nonce_respecting(A)), CC_URF ).game() @ &m : res ] |.
proof.
move=> Poly_ll CC_ll A_ll swap_enc_dec.
rewrite -(step2_Poly_to_random A &m Poly_ll).
have//:=chacha_poly_to_URF_and_forge (A_nonce_respecting(A)) &m Poly_ll CC_ll _ swap_enc_dec.
move=> C C_dec_ll C_enc_ll; proc; inline*; sp.
call(A_ll (NR_Adv(C)) _ _); auto.
+ by proc; inline*; sp; if; auto=> /=; call C_dec_ll; auto.
by proc; inline*; sp; if; auto=> /=; call C_enc_ll; auto.
qed.

(******************************************************************************)
(* treatment of Pr [ Forge(A,Composition(CC_URF,Poly)).game() @ &m : res ] *)



local module Update_Success (E : SKE) = {
  proc keygen () = {
    var key;
    WrapForgery.success <- false;
    key <@ E.keygen();
    return key;
  }
  proc enc = E.enc
  proc dec (k : cckey, nact : nonce * associated_data * ciphertext * tag) = {
    var r;
    r <@ E.dec(k, nact);
    if (r <> None) {
      WrapForgery.success <- true;
    }
    return r;
  }
}.

local lemma forge_to_encdec (E <: SKE { Wrap, WrapForgery }) (A <: CCA_Adv { E, Wrap, WrapForgery }) &m :
    Pr[Forge(A,E).game() @ &m : res ] = 
    Pr[EncDec(A,Update_Success(E)).game() @ &m : WrapForgery.success ].
proof.
byequiv=> //=; proc; inline*.
call(: ={glob Wrap, glob E, glob WrapForgery}); auto.
+ proc; inline*; sim.
  by swap{2} 4 3; sim.
+ by proc; sim.
by call(: true); auto.
qed.


local lemma step_2_chacha_poly_to_URF_and_forge
    (A <: CCA_Adv { URF, Wrap, Chacha, Poly, NR, WrapForgery, NR, Compo }) &m :
  islossless Poly.mac => islossless Chacha.enc =>
  (forall (C <: CCA_SKE{A}), islossless C.dec => islossless C.enc => islossless A(C).guess) =>
  (equiv[ E2(Composition(CC_URF, Poly)).enc_dec ~
          E2(Composition(CC_URF, Poly)).dec_enc :
         ={arg, glob Composition(CC_URF, Poly)} ==>
         ={res, glob Composition(CC_URF, Poly)}]) =>
  `| Pr[EncDec(             A_nonce_respecting(A) , Composition ( Chacha ,Poly)).game() @ &m : res ]
   - Pr[EncDec(Adv_Dec_None(A_nonce_respecting(A)), Compo       ( Random ,Poly)).game() @ &m : res ] |

    <= Pr [ EncDec(A_nonce_respecting(A),Update_Success(Composition(CC_URF,Poly))).game() @ &m : WrapForgery.success ]

       + `| Pr [ IndistCC(CCA_to_CC_indist(Poly,A_nonce_respecting(A)), Chacha ).game() @ &m : res ]
          - Pr [ IndistCC(CCA_to_CC_indist(Poly,A_nonce_respecting(A)), CC_URF ).game() @ &m : res ] |.
proof.
move=> Poly_ll CC_ll A_ll swap_enc_dec.
have<-:= forge_to_encdec (Composition(CC_URF,Poly)) (A_nonce_respecting(A)) &m.
exact(step_1_chacha_poly_to_URF_and_forge A &m Poly_ll CC_ll A_ll swap_enc_dec).
qed.


local module (Comp (CC : FCC) (Poly : KRO) : SKE) = {
  var order_dec : (cckey * (nonce * associated_data * ciphertext * tag)) list
  var b : bool
  proc keygen () = {
    var key;
    order_dec <- [];
    b <- false;
    WrapForgery.success <- false;
    key <@ CC.keygen();
    return key;
  }
  proc enc  = Composition(CC,Poly).enc
  proc dec (k : cckey, nact : nonce * associated_data * ciphertext * tag) : 
    (nonce * associated_data * plaintext) option = {

    order_dec <- rcons order_dec (k,nact);
    return None;
  }
  proc call_all_poly_dec () = {
    var k, nact, i, n, a, c, t, t', t2, x, r, s;
    i <- 0;
    while (i < size order_dec) {
      (k, nact) <- nth witness order_dec i;
      (n, a, c, t) <- nact;
      x <@ CC.enc(k, cc_concat 0 n);
      (r, s) <- trunc32 x;
      t' <@ Poly.mac(r, poly_concat a c);
      t2 <- t' + s;
      if (t = t2) {
        WrapForgery.success <- true;
      }
      i <- i + 1;
    }
  }
}.

local module Dec_None (E : SKE) = {
  proc keygen () = {
    var key;
    Comp.order_dec <- [];
    Comp.b <- false;
    key <@ E.keygen();
    return key;
  }
  proc enc = E.enc
  proc dec (k : cckey, nact : nonce * associated_data * ciphertext * tag) :
    (nonce * associated_data * plaintext) option = {
    Comp.order_dec <- rcons Comp.order_dec (k,nact);
    E.dec(k,nact);
    return None;
  }
}.


local module ForgeryList (A : CCA_Adv) (CC : FCC) (Poly : KRO) = {
  proc game () = {
    WrapForgery.success <- false;
    EncDec(A,Comp(CC,Poly)).game();
    Comp(CC,Poly).call_all_poly_dec();
  }
}.

local lemma rewrite_1 (A <: CCA_Adv { URF, Wrap, Chacha, Poly, WrapForgery, Comp }) &m :
  (forall (C <: CCA_SKE{A}),
    islossless C.dec => islossless C.enc => islossless A(C).guess) =>
  islossless Poly.mac =>
  Pr[EncDec(A,Update_Success(Composition(CC_URF,Poly))).game() @ &m : WrapForgery.success] =
  Pr[EncDec(A,Dec_None(Update_Success(Composition(CC_URF,Poly)))).game() @ &m : WrapForgery.success].
proof.
move=> A_ll Poly_ll.
byequiv=> //=; proc; inline*; sp.
call(: WrapForgery.success,
       ={glob Poly, glob CC_URF, glob Wrap, WrapForgery.success},
       ={WrapForgery.success} /\ WrapForgery.success{1})=> //=.
- proc; inline*; sp.
  seq 6 6 : (={glob Poly, WrapForgery.success, glob Wrap, URF.map, 
         t, t2, t, n, a, p0, c0, opt, c} /\ opt{1} = None /\
         k{1} = k0{2} /\ !WrapForgery.success{2}); last first.
  * if; 1, 3: auto=> />. 
    rcondf{2} 17; 1: by auto=> //=.
    rcondt{2} 14; 1: by auto=> //=.
    rcondt{1} 14; 1: by auto=> //=.
    rcondt{1} 17; 1: by auto=> //=.
    by wp=> /=; auto; sim.
  by conseq(:_==> ={glob Poly, WrapForgery.success, glob Wrap, URF.map, 
         t, t2, c, n, a, p0, c0, opt})=> //=; sim=> />.
- move=> &h Hh; proc; inline*.
  wp 19=> //=.
  conseq(:_==> true)=> />; auto=> /=; sp.
  seq 1 : true; auto. 
  + by if; auto=> />; smt(dcct2_ll).
  sp; seq 1 : true; auto.
  + by call Poly_ll; auto.
  sp; if; auto; sp.
  seq 1 : true; auto.
  + while(true)(clength c0 - i); auto=> />.
    + by sp; if; auto; smt(dcct2_ll).
    smt().
  by sp; if; auto; smt(dcct2_ll).
- move=> &1; proc; inline*.
  wp=> //=.
  conseq(:_==> true)=> />; auto=> /=; sp.
  seq 1 : true; auto. 
  + by if; auto=> />; smt(dcct2_ll).
  sp; seq 1 : true; auto.
  + by call Poly_ll; auto.
  sp; if; auto; sp.
  seq 1 : true; auto.
  + while(true)(clength c0 - i); auto=> />.
    + by sp; if; auto; smt(dcct2_ll).
    smt().
  by sp; if; auto; smt(dcct2_ll).
- by proc; conseq(:_==> ={c, glob Poly, URF.map, glob Wrap, WrapForgery.success})=> />; sim.
- move=> &h Hh; proc; inline* => />.
  auto; sp.
  seq 1 : true; auto. 
  + by if; auto=> />; smt(dcct2_ll).
  sp; seq 1 : true; auto.
  + while(true)(plength p0 - i); auto=> />.
    + by sp; if; auto; smt(dcct2_ll).
    smt().
  call Poly_ll; auto.
  by sp; if; auto; smt(dcct2_ll).
- move=> &h; proc; inline* => />.
  sp; auto.
  seq 1 : true; auto. 
  + by if; auto=> />; smt(dcct2_ll).
  sp; seq 1 : true; auto.
  + while(true)(plength p0 - i); auto=> />.
    + by sp; if; auto; smt(dcct2_ll).
    smt().
  call Poly_ll; auto.
  by sp; if; auto; smt(dcct2_ll).
by auto=> />; smt().
qed.

local clone PROM.GenEager as EG with
  type from <- cct1,
  type to <- cct2,
  type input <- unit,
  type output <- bool,
  op sampleto <- fun _ => dcct2

proof * by smt(dcct2_ll).


module FCC_of_RO (F : EG.RO) : FCC = {
  proc keygen() : cckey = {
    F.init();
    return witness;
  }
  proc enc (k : cckey, x : cct1) : cct2 = {
    var y;
    y <@ F.get(x);
    return y;
  }
}.

local module Composition'(F : EG.RO) (Poly : KRO) = {
  proc keygen () = {
    var key;
    Comp.order_dec <- [];
    Comp.b <- false;
    WrapForgery.success <- false;
    key <@ Composition(FCC_of_RO(F),Poly).keygen();
    return key;
  }
  proc enc = Composition(FCC_of_RO(F),Poly).enc
  proc dec (k : cckey, nact : nonce * associated_data * ciphertext * tag) :
    (nonce * associated_data * plaintext) option = {
    var n, a, c, t, x, r, s, t', t2, i;

    t' <- witness;
    (n,a,c,t) <- nact;
    x     <@ F.get(cc_concat 0 n);
    (r,s) <- trunc32 x;
    t' <@ Poly.mac(r, poly_concat a c);
    t2 <- t' + s;
    if (t = t2) {
      i     <- 1;
      while (i < clength c) {
        F.sample(cc_concat i n);
        i <- i + 1;
      }
      F.sample(cc_concat i n);
      WrapForgery.success <- true;
    }
    return None;
  }
}.

local equiv urf_ro_sample :
  CC_URF.enc ~ EG.RO.sample : 
  arg{1}.`2 = arg{2} /\ URF.map{1} = EG.RO.m{2} ==> URF.map{1} = EG.RO.m{2}.
proof.
proc; inline*; sp.
if{1}.
+ by rcondt{2} 2; auto.
by rcondf{2} 2; auto; smt(dcct2_ll).
qed.

local equiv urf_ro_get :
  CC_URF.enc ~ EG.RO.get : 
  arg{1}.`2 = arg{2} /\ URF.map{1} = EG.RO.m{2} ==> ={res} /\ URF.map{1} = EG.RO.m{2}.
proof.
proc; inline*; sp.
if{1}.
+ by rcondt{2} 2; auto.
by rcondf{2} 2; auto; smt(dcct2_ll).
qed.

local module (Dist (A : CCA_Adv) (Poly : KRO) : EG.RO_Distinguisher) (R : EG.RO) = {
  proc distinguish () : bool = {
    EncDec(A, Dec_None(Composition'(R, Poly))).game();
    return WrapForgery.success;
  }
}.

local lemma rewrite_2 (A <: CCA_Adv { URF, Wrap, Chacha, Poly, WrapForgery, Comp, EG.RO, EG.FRO }) &m :
  equiv [ Swap_Poly(Poly).double_mac ~ Swap_Poly(Poly).double_reverse_mac :
      ={arg, glob Poly} ==> ={res, glob Poly} ] =>
  islossless Poly.mac =>
  Pr[EncDec(A,Dec_None(Update_Success(Composition(CC_URF,Poly)))).game() @ &m : WrapForgery.success] =
  Pr[ForgeryList(A,CC_URF,Poly).game() @ &m : WrapForgery.success].
proof.
move=> swap_poly Poly_ll.
have->:Pr[EncDec(A,Dec_None(Update_Success(Composition(CC_URF, Poly)))).game() @ &m : WrapForgery.success] =
       Pr[EncDec(A,Dec_None(Composition'(EG.RO, Poly))).game() @ &m : WrapForgery.success].
+ byequiv=> //=; proc; inline*; sp; auto.
  call(: ={glob Wrap, glob Comp, glob Poly} /\ URF.map{1} = EG.RO.m{2}); auto.
  + proc; sp; sim.
    inline{1} 1; inline{2} 1; sp; sim.
    inline{1} 1; inline{2} 1; sp; sim.
    inline{1} 1; sim; sp=> />.
    conseq(:_==> URF.map{1} = EG.RO.m{2} /\ ={WrapForgery.success, glob Wrap, glob Poly})=> //=.
    seq 4 4 : (URF.map{1} = EG.RO.m{2} /\ opt{1} = None /\
         ={glob Poly, glob Wrap, WrapForgery.success, t, t2, c0, n}); last first.
    - if; 1,3: auto.
      rcondt{1} 9; 1: auto=> //=; sim.
      call urf_ro_sample=> />.
      while(={i, n, c0} /\ URF.map{1} = EG.RO.m{2}); auto.
      by call urf_ro_sample; auto=> />.
    conseq=>/>; sim.
    by call urf_ro_get; auto.
  proc; sim.
  inline{1} 1; inline{2} 1; sp; sim.
  inline FCC_of_RO(EG.RO).enc; sp; sim.
  call urf_ro_get=> />; auto=> />.
  while(={i, n, c0, r, s, p0} /\ URF.map{1} = EG.RO.m{2}); auto.
  - by call urf_ro_get; auto.
  by call urf_ro_get; auto.
have->:Pr[ForgeryList(A, CC_URF, Poly).game() @ &m : WrapForgery.success]=
       Pr[ForgeryList(A, FCC_of_RO(EG.LRO), Poly).game() @ &m : WrapForgery.success].
+ byequiv=>//=; proc; sp; sim.
  inline{1} 2; inline{2} 2; inline FCC_of_RO(EG.LRO).enc.
  while(={i, Comp.order_dec, WrapForgery.success, glob Poly} /\ URF.map{1} = EG.RO.m{2}).
  + sim; call urf_ro_get; auto.
  auto=> />.
  conseq(:_==> ={Comp.order_dec, WrapForgery.success, glob Poly} /\ URF.map{1} = EG.RO.m{2})=>//=.
  inline*; sp; sim.
  call(: ={glob Comp, glob Wrap, glob Poly, WrapForgery.success} /\ URF.map{1} = EG.RO.m{2})=>//=.
  + by proc; sim.
  proc; sim.
  inline{1} 1; inline{2} 1; inline FCC_of_RO(EG.LRO).enc; sp; sim.
  call urf_ro_get; auto=> />.
  by while(={i, n, c0, r, s, p0} /\ URF.map{1} = EG.RO.m{2}); auto; call urf_ro_get; auto.
have->:Pr[ForgeryList(A, FCC_of_RO(EG.LRO), Poly).game() @ &m : WrapForgery.success]=
       Pr[EncDec(A, Dec_None(Composition'(EG.LRO, Poly))).game() @ &m : WrapForgery.success]; last first.
+ byequiv=> //=; proc.
  replace{1} { init; <@ |} by {
      init;
      WrapForgery.success <@ Dist(A, Poly, EG.RO).distinguish();
    }
    (={glob A, glob Poly} ==> ={WrapForgery.success})
    (={glob A, glob Poly} ==> ={WrapForgery.success})=> //=; 1: smt().
  - by inline*; sim.
  replace{2} { init; <@ |} by {
      init;
      WrapForgery.success <@ Dist(A, Poly, EG.LRO).distinguish();
    }
    (={glob A, glob Poly} ==> ={WrapForgery.success})
    (={glob A, glob Poly} ==> ={WrapForgery.success})=> //=; 1: smt(); last first.
  - by inline*; sim.
  by call (EG.RO_LRO_D (Dist(A,Poly))); inline*; auto.
rewrite eq_sym; byequiv=> //=; proc.
inline{2} 2.
replace{1} { init; <@ |} by {
    init;
    Comp(FCC_of_RO(EG.LRO), Poly).call_all_poly_dec();
    Comp.b <@ A(Wrap(Dec_None(Composition'(EG.LRO, Poly)))).guess();
    b <- Comp.b;
  }
  (={glob Poly, glob A} ==> ={WrapForgery.success})
  (={glob Poly, glob A} ==> ={WrapForgery.success})=> //=; 1: smt().
+ by sim; inline*; sp; rcondf{2} 1; auto=> />.
replace{2} { init; <@; (<@ as loop) |} by {
    init;
    Comp.b <@ A(Wrap(Comp(FCC_of_RO(EG.LRO), Poly))).guess();
    loop;
    b <- Comp.b;
  }
  (={glob Poly, glob A} ==> ={WrapForgery.success})
  (={glob Poly, glob A} ==> ={WrapForgery.success})=> //=; 1: smt(); sim; sp.
inline{1} 1; inline{2} 1; sp.
inline{1} 1; inline{2} 1; sp.
inline{1} 1; inline{2} 1; sp.
inline{1} 1; inline{2} 1; sp.
inline{1} 1; sp.
eager call (: ={glob Wrap, glob Comp, glob Poly, glob A, glob EG.RO, WrapForgery.success}
    ==> ={res, glob Wrap, glob Comp, glob Poly, glob A, glob EG.RO, WrapForgery.success}); auto.
eager proc (H : 
      Comp(FCC_of_RO(EG.LRO), Poly).call_all_poly_dec(); ~ 
      Comp(FCC_of_RO(EG.LRO), Poly).call_all_poly_dec(); :
    ={glob Wrap, glob Comp, glob Poly, glob EG.RO, WrapForgery.success}
    ==> ={glob Wrap, glob Comp, glob Poly, glob EG.RO, WrapForgery.success})
    (={glob Wrap, glob Comp, glob Poly, glob EG.RO, WrapForgery.success})=> />; 1, 3, 5: sim.
+ eager proc.
  swap{2} -3; sim.
  inline{1} 2; inline{2} 1.
  swap{2} -1; sim; sp.
  swap{1} 2; sp.
  swap{1} -1; wp.
  inline Comp(FCC_of_RO(EG.LRO), Poly).call_all_poly_dec.
  splitwhile{2} 2 : i < size Comp.order_dec - 1=> />.
  conseq(:_==> ={c, EG.RO.m, Comp.b, WrapForgery.success, Wrap.dqs, Wrap.log, Wrap.k, glob Poly} /\
      rcons Comp.order_dec{1} (k{1}, nact{1}) = Comp.order_dec{2})=>//=.
  seq 2 2 : (={i, c, glob EG.RO, glob Poly, WrapForgery.success, Comp.b, glob Wrap} /\
      rcons Comp.order_dec{1} (k{1}, nact{1}) = Comp.order_dec{2} /\
      i{1} = size Comp.order_dec{1}); last first.
  - rcondt{2} 1; 1: by auto; smt(size_rcons).
    rcondf{2} 9; 1: by auto; conseq(:_==> true)=> //=; smt(size_rcons).
    inline*; sp=> />.
    seq 6 7 : ((t0,t20){1} = (t,t2){2} /\ ={WrapForgery.success, glob Poly, EG.RO.m}); 1: sim=> />.
    + by move=> &l &r; rewrite nth_rcons /= => [#] 5->> /=.
    if; auto=> /> //.
    by while{1}(true)(clength c1{1} - i0{1}); auto; smt().
  move=> />.
  while(={i, c, EG.RO.m, glob Poly, WrapForgery.success, Comp.b, glob Wrap} /\
      rcons Comp.order_dec{1} (Wrap.k{1}, c{1}) = Comp.order_dec{2} /\
      0 <= i{1} <= size Comp.order_dec{1}).
  + wp 7 7; conseq(:_==> ={i, EG.RO.m, glob Poly, WrapForgery.success}); 1: smt(size_rcons).
    inline*; wp; call(: true); auto=> /> &l &r.
    rewrite size_rcons/= =>/> 3? y ?.
    by rewrite nth_rcons /=; rewrite H2/=; smt(get_setE).
  by auto; smt(size_ge0 size_rcons).
eager proc.
swap{2} -2; sim.
inline{2} 1; inline{1} 2; sp.
swap{2} -2; sim.
swap{1} 5; sp=> />.
inline FCC_of_RO(EG.LRO).enc.
replace{2} { all; (<@ as c); (<@ as loop) |} by {
    all;
    loop;
    c;
  }
  (={t', p0, n, EG.RO.m, glob Poly, c0, a, WrapForgery.success, Comp.order_dec} ==> 
    ={t', c0, s, EG.RO.m, WrapForgery.success, glob Poly})
  (={t', p0, n, EG.RO.m, glob Poly, c0, a, WrapForgery.success, Comp.order_dec} ==> 
    ={t', c0, s, EG.RO.m, WrapForgery.success, glob Poly})=> //=; 1: smt(); last first.
+ seq 14 14 : (={t', c0, s, EG.RO.m, WrapForgery.success, glob Poly, r, a, Comp.order_dec}); 1: sim.
  conseq/>; inline*.
  swap{2} 1; sp; sim.
  conseq(: ={t', r, a, c0, glob Poly, i0, Comp.order_dec, EG.RO.m, WrapForgery.success} ==>
      ={t', r, a, c0, glob Poly, i0, Comp.order_dec, EG.RO.m, WrapForgery.success})=>//= />.
  symmetry; eager while (H : 
      t' <@ Poly.mac(r, poly_concat a c0); ~
      t' <@ Poly.mac(r, poly_concat a c0); :
      ={t', r, a, c0, glob Poly, i0, Comp.order_dec, EG.RO.m, WrapForgery.success} ==>
      ={t', r, a, c0, glob Poly, i0, Comp.order_dec, EG.RO.m, WrapForgery.success})=> //=; 1, 3: sim=> />.
  swap{2} -3; sim.
  swap{1} 10=> />.
  seq 10 10 : (={s0, t0, EG.RO.m, glob Poly, r, a, c0, r0, a0, c1}); 1: sim.
  conseq/>.
  transitivity{1} {
      (t', t'0) <@ Swap_Poly(Poly).double_mac((r, poly_concat a c0), (r0, poly_concat a0 c1));
    }
    (={r, a, c0, r0, a0, c1, glob Poly} ==> ={t'0, t', glob Poly})
    (={r, a, c0, r0, a0, c1, glob Poly} ==> ={t'0, t', glob Poly})=> //=; 1: smt().
  + by inline*; sp; sim; call(: true); auto; call(: true); auto.
  transitivity{2} {
      (t', t'0) <@ Swap_Poly(Poly).double_reverse_mac((r, poly_concat a c0), (r0, poly_concat a0 c1));
    }
    (={r, a, c0, r0, a0, c1, glob Poly} ==> ={t'0, t', glob Poly})
    (={r, a, c0, r0, a0, c1, glob Poly} ==> ={t'0, t', glob Poly})=> //=; 1: smt(); last first.
  + by inline*; sp; sim; call(: true); auto; call(: true); auto.
  by call swap_poly; auto.
sim.
swap{2} -4; sim=> />.
replace{2} { all; (<@ as c); (<@ as loop) |} by {
    all;
    y2 <- witness;
    loop;
    c;
  }
  (={t', p0, n, EG.RO.m, glob Poly, c0, a, WrapForgery.success, Comp.order_dec} ==> 
    ={y2, c0, s, r, EG.RO.m, WrapForgery.success, glob Poly})
  (={t', p0, n, EG.RO.m, glob Poly, c0, a, WrapForgery.success, Comp.order_dec} ==> 
    ={y2, c0, s, r, EG.RO.m, WrapForgery.success, glob Poly})=> //=; 1: smt(); last first.
+ seq 9 9 : (={x2, c0, s, r, EG.RO.m, WrapForgery.success, glob Poly, Comp.order_dec}); 1: sim.
  inline Comp(FCC_of_RO(EG.LRO), Poly).call_all_poly_dec FCC_of_RO(EG.LRO).enc.
  swap 1; sp 1 1.
  replace{2} {all} by {
      y2 <- witness;
      all;
    }
    (={i0, x2, c0, s, r, EG.RO.m, WrapForgery.success, glob Poly, Comp.order_dec} ==>
      ={y2, c0, s, r, EG.RO.m, WrapForgery.success, glob Poly})
    (={i0, x2, c0, s, r, EG.RO.m, WrapForgery.success, glob Poly, Comp.order_dec} ==>
      ={y2, c0, s, r, EG.RO.m, WrapForgery.success, glob Poly})=> //=; 1: smt(); 2: by sim.
  sp=> {H} />.
  symmetry; conseq(: ={i0, y2, x2, Comp.order_dec, EG.RO.m, glob Poly, WrapForgery.success} ==>
      ={i0, y2, x2, Comp.order_dec, EG.RO.m, glob Poly, WrapForgery.success})=> //=.
  eager while(H : y2 <@ EG.LRO.get(x2); ~ y2 <@ EG.LRO.get(x2); :
      ={i0, y2, x2, Comp.order_dec, EG.RO.m, glob Poly, WrapForgery.success} ==>
      ={i0, y2, x2, Comp.order_dec, EG.RO.m, glob Poly, WrapForgery.success})=>//=; 1, 3: sim.
  swap{2} -6; sim.
  swap{1} 4; sp; inline*; sp.
  swap{1} [4..5] -3.
  swap{2} [4..5] -2.
  swap{2} 1; sp.
  case: (x5{1} = x5{2}).
  + swap{1} 1.
    rcondf{1} 5; 1: by auto; smt(mem_set).
    rcondf{2} 5; 1: by auto; smt(mem_set).
    auto=> />.
    move=> &l &r h; rewrite -h /= => [#] 5->> ? y1 ? y2 ?.
    by rewrite get_setE /=.
  wp; rnd; rnd; auto=> />.
  move=> &l &r h; rewrite -h /= => [#] 5->> ?? y1 ? y2 ?.
  rewrite 2!mem_set 2!get_setE/=.
  case: (cc_concat 0 n0{r} \in EG.RO.m{r})=> ? //=; 1: smt().
  rewrite negb_or.
  case: (x2{r} \in EG.RO.m{r})=> ? //=; 1: smt(get_setE); split=> ?; split => />//=.
  by rewrite get_setE/= get_setE/= get_setE/= set_setE => ->//=.
sim.
swap{2} -3; sim=> />.
replace{2} { all; (while as c); (<@ as loop) |} by {
    all;
    loop;
    c;
  }
  (={t', p0, n, EG.RO.m, glob Poly, c0, a, WrapForgery.success, Comp.order_dec} ==> 
    ={c0, i, s, r, EG.RO.m, WrapForgery.success, glob Poly})
  (={t', p0, n, EG.RO.m, glob Poly, c0, a, WrapForgery.success, Comp.order_dec} ==> 
    ={c0, i, s, r, EG.RO.m, WrapForgery.success, glob Poly})=> //=; 1: smt().
+ sim=> />.
  swap{2} -3; sim; swap{1} 2; sp=> />.
  replace{1} { all } by {
      y0 <- witness;
      all;
    }
    (={x0, EG.RO.m, glob Poly, c0, a, WrapForgery.success, Comp.order_dec} ==> 
      ={y0, EG.RO.m, WrapForgery.success, glob Poly})
    (={x0, EG.RO.m, glob Poly, c0, a, WrapForgery.success, Comp.order_dec} ==> 
      ={y0, EG.RO.m, WrapForgery.success, glob Poly})=> //=; 1: smt(); 1: by sim.
  replace{2} { all } by {
      y0 <- witness;
      all;
    }
    (={x0, EG.RO.m, glob Poly, c0, a, WrapForgery.success, Comp.order_dec} ==> 
      ={y0, EG.RO.m, WrapForgery.success, glob Poly})
    (={x0, EG.RO.m, glob Poly, c0, a, WrapForgery.success, Comp.order_dec} ==> 
      ={y0, EG.RO.m, WrapForgery.success, glob Poly})=> //=; 1: smt(); 2: by sim.
  sp.
  inline Comp(FCC_of_RO(EG.LRO), Poly).call_all_poly_dec FCC_of_RO(EG.LRO).enc.
  swap{2} 1; sp.
  symmetry; conseq(: ={x0, y0, i0, Comp.order_dec, glob Poly, WrapForgery.success, EG.RO.m} ==>
      ={x0, y0, i0, Comp.order_dec, glob Poly, WrapForgery.success, EG.RO.m})=>//=.
  eager while (J: y0 <@ EG.LRO.get(x0); ~ y0 <@ EG.LRO.get(x0); :
      ={x0, y0, i0, Comp.order_dec, glob Poly, WrapForgery.success, EG.RO.m} ==>
      ={x0, y0, i0, Comp.order_dec, glob Poly, WrapForgery.success, EG.RO.m})=> //=; 1, 3: sim.
  swap{2} -6; sim.
  swap{1} 4; sp; inline*.
  swap 5 -4; sp.
  swap 4 -2.
  case: (x5{1} = x5{2}).
  + rcondf{1} 5; 1: by auto; smt(mem_set).
    rcondf{2} 5; 1: by auto; smt(mem_set).
    by auto; smt().
  swap{1} 1; wp; rnd; rnd; auto=> />.
  move=> &l &r h; rewrite -h /= => [#] 5->> ?? y1 ? y2 ?.
  rewrite 2!mem_set 2!get_setE/=.
  case: (cc_concat 0 n0{r} \in EG.RO.m{r})=> ? //=; 1: smt().
  rewrite negb_or.
  case: (x0{r} \in EG.RO.m{r})=> ? //=; 1: smt(get_setE); split=> ?; split => />//=.
  by rewrite get_setE/= get_setE/= get_setE/= set_setE => ->//=.
conseq/>.
seq 6 6 : (={i, p0, n, EG.RO.m, c0, r, s, WrapForgery.success, glob Poly, Comp.order_dec}); 1: sim.
conseq/> => {H}.
eager while (J : 
      Comp(FCC_of_RO(EG.LRO), Poly).call_all_poly_dec(); ~
      Comp(FCC_of_RO(EG.LRO), Poly).call_all_poly_dec(); :
      ={i, p0, n, c0, WrapForgery.success, glob Poly, Comp.order_dec, EG.RO.m} ==>
      ={i, p0, n, c0, WrapForgery.success, glob Poly, Comp.order_dec, EG.RO.m})=> //=; 1, 3: sim.
swap{1} 2; swap{2} -4; sim; sp.
inline Comp(FCC_of_RO(EG.LRO), Poly).call_all_poly_dec FCC_of_RO(EG.LRO).enc.
swap{2} 1; sp=> />.
symmetry=>/>.
replace{1} { all } by {
    y1 <- witness;
    all;
  }
  (={x1, i0, EG.RO.m, glob Poly, WrapForgery.success, Comp.order_dec} ==> 
    ={y1, EG.RO.m, WrapForgery.success, glob Poly})
  (={x1, i0, EG.RO.m, glob Poly, WrapForgery.success, Comp.order_dec} ==> 
    ={y1, EG.RO.m, WrapForgery.success, glob Poly})=> //=; 1: smt(); 1: by sim.
replace{2} { all } by {
    y1 <- witness;
    all;
  }
  (={x1, i0, EG.RO.m, glob Poly, WrapForgery.success, Comp.order_dec} ==> 
    ={y1, EG.RO.m, WrapForgery.success, glob Poly})
  (={x1, i0, EG.RO.m, glob Poly, WrapForgery.success, Comp.order_dec} ==> 
    ={y1, EG.RO.m, WrapForgery.success, glob Poly})=> //=; 1: smt(); 2: by sim.
sp=> /> {J}.
conseq(: ={y1, x1, i0, Comp.order_dec, EG.RO.m, glob Poly, WrapForgery.success} ==>
    ={y1, x1, i0, Comp.order_dec, EG.RO.m, glob Poly, WrapForgery.success})=>//=.
eager while(J : y1 <@ EG.LRO.get(x1); ~ y1 <@ EG.LRO.get(x1); :
    ={y1, x1, i0, Comp.order_dec, EG.RO.m, glob Poly, WrapForgery.success} ==>
    ={y1, x1, i0, Comp.order_dec, EG.RO.m, glob Poly, WrapForgery.success})=> //=; 1, 3: sim.
swap{1} 4; sp; swap{2} -6; sim=> />.
conseq(:_==> ={y3, y1, EG.RO.m})=> />; 1: smt().
inline*.
swap 5 -4; sp; swap 4 -2.
case: (x5{1} = x5{2}).
+ rcondf{1} 5; 1: by auto; smt(mem_set).
  rcondf{2} 5; 1: by auto; smt(mem_set).
  by auto; smt().
swap{1} 1; wp; rnd; rnd; auto=> />.
move=> &l &r h; rewrite -h /= => [#] 5->> ?? y1 ? y2 ?.
rewrite 2!mem_set 2!get_setE/=.
case: (cc_concat 0 n0{r} \in EG.RO.m{r})=> ? //=; 1: smt().
rewrite negb_or.
case: (x1{r} \in EG.RO.m{r})=> ? //=; 1: smt(get_setE); split=> ?; split => />//=.
by rewrite get_setE/= get_setE/= get_setE/= set_setE => ->//=.
qed.




local lemma step_3_chacha_poly_to_URF_and_forge
    (A <: CCA_Adv { URF, Wrap, Chacha, Poly, NR, WrapForgery, NR, Compo, Comp, EG.RO, EG.FRO }) &m :
  islossless Poly.mac => islossless Chacha.enc =>
  (forall (C <: CCA_SKE{A}), islossless C.dec => islossless C.enc => islossless A(C).guess) =>
  (equiv [ Swap_Poly(Poly).double_mac ~ Swap_Poly(Poly).double_reverse_mac :
      ={arg, glob Poly} ==> ={res, glob Poly} ]) =>
  (equiv[ E2(Composition(CC_URF, Poly)).enc_dec ~
          E2(Composition(CC_URF, Poly)).dec_enc :
         ={arg, glob Composition(CC_URF, Poly)} ==>
         ={res, glob Composition(CC_URF, Poly)}]) =>
  `| Pr[EncDec(             A_nonce_respecting(A) , Composition ( Chacha ,Poly)).game() @ &m : res]
   - Pr[EncDec(Adv_Dec_None(A_nonce_respecting(A)), Compo       ( Random ,Poly)).game() @ &m : res] |

    <= Pr[ForgeryList(A_nonce_respecting(A),CC_URF,Poly).game() @ &m : WrapForgery.success]

       + `| Pr[IndistCC(CCA_to_CC_indist(Poly,A_nonce_respecting(A)), Chacha ).game() @ &m : res]
          - Pr[IndistCC(CCA_to_CC_indist(Poly,A_nonce_respecting(A)), CC_URF ).game() @ &m : res] |.
proof.
move=> Poly_ll CC_ll A_ll swap_poly swap_enc_dec.
rewrite -(rewrite_2 (A_nonce_respecting(A)) &m swap_poly Poly_ll).
rewrite -(rewrite_1 (A_nonce_respecting(A)) &m _ Poly_ll).
+ move=> F dec_ll enc_ll; proc; inline*; call (A_ll (NR_Adv(F)) _ _); auto; proc; inline*.
  - by sp; if; auto; call dec_ll; auto.
  by sp; if; auto; call enc_ll; auto.
exact(step_2_chacha_poly_to_URF_and_forge A &m Poly_ll CC_ll A_ll swap_enc_dec).
qed.


local lemma compo_to_idealSKE (A <: CCA_Adv { Compo, Wrap, NR }) &m :
    Pr[EncDec(Adv_Dec_None(A_nonce_respecting(A)),Compo(Random,Poly)).game() @ &m : res] =
    Pr[EncDec(             A_nonce_respecting(A) ,IdealSKE).game() @ &m : res].
proof.
byequiv=> //=; proc; inline*; sp; auto.
call(: ={Wrap.log, glob NR}); auto.
+ by proc; inline*; auto=> />.
proc; inline*; sp; if; 1, 3: auto; sim.
wp; sp=> />.
exists* p1{1}; elim* => plain.
have[] b Hb:=ptrunc_last_block plain.
conseq(:_==> y2{1} +^ b = y{2} /\ ={t0, c1}); 1: smt(ptrunc_add).
rnd (fun x=> x +^ b).
wp; conseq(:_==> ={t0, c1}); 1: smt(dcct2_fu add_block_K).
while(={i, p1, c1, t0}).
+ sim; wp; rnd (fun x=> x +^ pnth witness p1{1} (i{1}-1)); auto=> />.
  smt(dcct2_fu add_block_K).
wp 3 1=> />.
transitivity{1} {
    (r, t0) <@ PD.S.sample(dpolykey,dpolyt4);
  }
  (true ==> ={t0}) (true ==> ={t0})=> //=.
+ inline*; wp; auto.
  rnd trunc32 concat32; auto=> />.
  split; 1: smt(concat32_K trunc32_K).
  move=> ?.
  split=>/> ??. 
  - rewrite -dcct2_dpkey_dpt4 dmapE; apply mu_eq=> //= x.
    smt(concat32_K trunc32_K).
  by rewrite -dcct2_dpkey_dpt4 supp_dmap; smt(concat32_K trunc32_K).
transitivity{1} {
    (r, t0) <@ PD.S.sample2(dpolykey,dpolyt4);
  }
  (true ==> ={t0}) (true ==> ={t0})=> //=. 
+ by call PD.sample_sample2; auto.
inline*; auto=> />.
exact dpolykey_ll.
qed.


local module Eager = {
  var x : cct1
  var y : cct2
}.

local lemma swap_urf :
  eager[ 
    Eager.y <@ URF.f(Eager.x);, URF.f ~ 
    URF.f, Eager.y <@ URF.f(Eager.x); :
    ={x, Eager.x, Eager.y, URF.map} ==>
    ={res, Eager.x, Eager.y, URF.map} ].
proof.
eager proc.
inline*.
swap{2} 3 -2; sp.
if{1}.
+ case: (x{1} = x0{1}).
  - rcondt{2} 1; 1: auto.
    rcondf{1} 3; 1: by auto; smt(mem_set).
    rcondf{2} 3; 1: by auto; smt(mem_set).
    by auto=> />.
  rcondt{2} 3; 1: by auto; if; auto; smt(mem_set).
  if{2}; last first.
  - rcondf{1} 3; 1: by auto; smt(mem_set).
    by auto; smt(get_setE).
  rcondt{1} 3; 1: by auto; smt(mem_set).
  conseq/>.
  transitivity{1} {
      Eager.y <$ dcct2;
      URF.map.[x0] <- Eager.y;
      Eager.y <- oget URF.map.[x0];
      result <$ dcct2;
      URF.map.[x] <- result;
      result <- oget URF.map.[x];
    }
    (={x0, x, Eager.y, URF.map} /\ x{1} <> x0{1} /\ x{1} \notin URF.map{2} ==>
      ={result, Eager.y, URF.map})
    (={x0, x, Eager.y, URF.map} /\ x{1} <> x0{1} /\ x{1} \notin URF.map{2} ==>
      ={result, Eager.y, URF.map})=> //=; 1: smt(); 1: by auto.
  transitivity{1} {
      result <$ dcct2;
      URF.map.[x] <- result;
      result <- oget URF.map.[x];
      Eager.y <$ dcct2;
      URF.map.[x0] <- Eager.y;
      Eager.y <- oget URF.map.[x0];
    }
    (={x0, x, Eager.y, URF.map} /\ x{1} <> x0{1} /\ x{1} \notin URF.map{2} ==>
      ={result, Eager.y, URF.map})
    (={x0, x, Eager.y, URF.map} /\ x{1} <> x0{1} /\ x{1} \notin URF.map{2} ==>
      ={result, Eager.y, URF.map})=> //=; 1: smt(); 2: by auto.
  swap 4 -2; swap{2} 1; wp; rnd; rnd; auto=> /> &h 4?.
  by rewrite get_setE/= get_setE/= get_setE/= get_setE/= set_setE/= H/=.
rcondf{2} 3; 1: by auto; if; auto; smt(mem_set).
by sp; if; auto; smt(get_setE).
qed.

local lemma eager_urf_composition_enc :
  eager [ 
    Eager.y <@ URF.f(Eager.x);, 
    Composition(CC_URF, Poly).enc
    ~
    Composition(CC_URF, Poly).enc, 
    Eager.y <@ URF.f(Eager.x);
    :
    ={arg, URF.map, glob Poly, Eager.x, Eager.y}
    ==>
    ={res, URF.map, glob Poly, Eager.x, Eager.y} ].
proof.
eager proc.
inline CC_URF.enc.
swap{2} -7; sim=> />.
replace{2} { start; (<@ as call1); (<@ as call2) } by {
    start;
    call2;
    call1;
  }
  (={k, nap, URF.map, glob Poly, Eager.x, Eager.y} ==>
    ={Eager.y, y2, s, r, p, c, n, a, URF.map})
  (={k, nap, URF.map, glob Poly, Eager.x, Eager.y} ==>
    ={Eager.y, y2, s, r, p, c, n, a, URF.map})=> //=; 1: smt(); last first.
+ seq 12 12 : (={Eager.y, x2, Eager.x, URF.map, s, r, p, c, n, a}); 1: by sim.
  conseq/>.
  by eager call (swap_urf); auto.
sim; swap{2} -2; sim=> />.
replace{2} { start; (while as call1); (<@ as call2) } by {
    start;
    call2;
    call1;
  }
  (={k, nap, URF.map, glob Poly, Eager.x, Eager.y} ==>
    ={Eager.y, i, s, r, p, c, a, n, URF.map})
  (={k, nap, URF.map, glob Poly, Eager.x, Eager.y} ==>
    ={Eager.y, i, s, r, p, c, a, n, URF.map})=> //=; 1: smt(); last first.
+ sp=> />.
  seq 4 4 : (={i, p, s, r, c, URF.map, n, c, Eager.y, Eager.x}); 1: by sim.
  conseq/>.
  eager while(J : Eager.y <@ URF.f(Eager.x); ~ Eager.y <@ URF.f(Eager.x); :
    ={i, p, URF.map, n, c, Eager.y, Eager.x} ==>
    ={i, p, URF.map, n, c, Eager.y, Eager.x})=> //=; 1, 3: sim.
  swap{2} -4; sim.
  by swap{1} 2; sp; eager call swap_urf; auto.
sim.
by swap{2} -3; sim; swap{1} 5; sp; eager call swap_urf; auto.
qed.



local lemma step_4_chacha_poly_to_URF_and_forge
    (A <: CCA_Adv { URF, Wrap, Chacha, Poly, NR, WrapForgery, NR, Compo, Comp, EG.RO, EG.FRO }) &m :
  islossless Poly.mac => islossless Chacha.enc =>
  (forall (C <: CCA_SKE{A}), islossless C.dec => islossless C.enc => islossless A(C).guess) =>
  (equiv [ Swap_Poly(Poly).double_mac ~ Swap_Poly(Poly).double_reverse_mac :
      ={arg, glob Poly} ==> ={res, glob Poly} ]) =>
  `| Pr[EncDec(A_nonce_respecting(A), Composition(Chacha,Poly) ).game() @ &m : res]
   - Pr[EncDec(A_nonce_respecting(A), IdealSKE                 ).game() @ &m : res] |

    <= Pr[ForgeryList(A_nonce_respecting(A),CC_URF,Poly).game() @ &m : WrapForgery.success]

       + `| Pr[IndistCC(CCA_to_CC_indist(Poly,A_nonce_respecting(A)), Chacha ).game() @ &m : res]
          - Pr[IndistCC(CCA_to_CC_indist(Poly,A_nonce_respecting(A)), CC_URF ).game() @ &m : res] |.
proof.
move=> Poly_ll CC_ll A_ll swap_poly.
rewrite-(compo_to_idealSKE A &m).
apply(step_3_chacha_poly_to_URF_and_forge A &m Poly_ll CC_ll A_ll _ _)=> //=.
proc; sp.
inline{1} 2; inline{2} 1.
swap{1} 6; swap{2}-1; sim=> />.
replace{2} { all; (if as cond) ; (<@ as loop) } by {
    all;
    y <- witness;
    c1 <- witness;
    loop;
    cond;
  }
  (={k1, k2, p1, c2, URF.map, glob Poly} ==> ={opt, c1, URF.map, glob Poly})
  (={k1, k2, p1, c2, URF.map, glob Poly} ==> ={opt, c1, URF.map, glob Poly})=> //=;
  1: smt(); last first.
+ sp=> />.
  seq 4 4 : (={k, t2, t, c, URF.map, n, p, a, k1, p1, opt, glob Poly}); 1: by sim.
  if{2}; last first.
  - rcondf{1} 4; 2: by sim.
    by auto; inline*; auto=> />; conseq(:_==> true); auto.
  rcondt{1} 4; 1: by auto; inline*; auto=> />; conseq(:_==> true); auto.
  swap{2} -4; sim.
  swap{1} 4 -3; sp 1 1=> />.
  replace{1} { start; (<@ as loop); (while as cond); fin } by {
      start;
      cond;
      loop;
      fin;
    }
    (={k, k1, p1, i, c, n, p, glob Poly, URF.map} ==> ={y, p, c1, URF.map, glob Poly})
    (={k, k1, p1, i, c, n, p, glob Poly, URF.map} ==> ={y, p, c1, URF.map, glob Poly})=> //=;
    1: smt(); last first.
  - replace{2} { all } by {
        y <- witness;
        c1 <- witness;
        all;
      }
      (={k1, p1, i, c, n, p, glob Poly, URF.map} ==> ={y, p, c1, URF.map, glob Poly})
      (={k1, p1, i, c, n, p, glob Poly, URF.map} ==> ={y, p, c1, URF.map, glob Poly})=> //=;
      1: smt(); 2: by inline*; sim.
    seq 3 3 : (={y, c1, c, p, k1, p1, i, n, URF.map, glob Poly}); 1: by inline*; sim=> />.
    inline CC_URF.enc.
    swap{1} 2; swap{2} -1; sp; sim=> />.
    replace{1} { start; <@ |} by {
        Eager.y <- witness;
        Eager.x <- x0;
        start;
        Eager.y <@ URF.f(Eager.x);
        y0 <- Eager.y;
      }
      (={c1, k1, p1, x0, URF.map, glob Poly} ==> ={y0, c1, URF.map, glob Poly})
      (={c1, k1, p1, x0, URF.map, glob Poly} ==> ={y0, c1, URF.map, glob Poly})=> //=;
      1: smt(); 1: by sim.
    replace{2} {| <@; fin|} by {
        Eager.y <- witness;
        Eager.x <- x0;
        Eager.y <@ URF.f(Eager.x);
        fin;
        y0 <- Eager.y;
      }
      (={c1, k1, p1, x0, URF.map, glob Poly} ==> ={y0, c1, URF.map, glob Poly})
      (={c1, k1, p1, x0, URF.map, glob Poly} ==> ={y0, c1, URF.map, glob Poly})=> //=;
      1: smt(); 2: by sim.
    sp; sim.
    symmetry; eager call eager_urf_composition_enc; auto=> />.
  sim.  
  inline  CC_URF.enc; sp.
  conseq(: ={k, c1, k1, p1, i, c, n, p, glob Poly, URF.map} ==>
        ={k, c1, k1, p1, i, c, n, p, glob Poly, URF.map})=> //= />.
  eager while (J : 
        c1 <@ Composition(CC_URF, Poly).enc(k1, p1); ~
        c1 <@ Composition(CC_URF, Poly).enc(k1, p1); :
        ={k, c1, k1, p1, i, c, n, p, glob Poly, URF.map} ==>
        ={k, c1, k1, p1, i, c, n, p, glob Poly, URF.map})=> //=; 1, 3: sim.
  swap{2} -4; sim; swap{1} 2; sp=> />.
  replace{1} { start; <@ |} by {
      Eager.y <- witness;
      Eager.x <- x0;
      start;
      Eager.y <@ URF.f(Eager.x);
      y0 <- Eager.y;
    }
    (={c1, k1, p1, x0, URF.map, glob Poly} ==> ={y0, c1, URF.map, glob Poly})
    (={c1, k1, p1, x0, URF.map, glob Poly} ==> ={y0, c1, URF.map, glob Poly})=> //=;
    1: smt(); 1: by sim.
  replace{2} {| <@; fin|} by {
      Eager.y <- witness;
      Eager.x <- x0;
      Eager.y <@ URF.f(Eager.x);
      fin;
      y0 <- Eager.y;
    }
    (={c1, k1, p1, x0, URF.map, glob Poly} ==> ={y0, c1, URF.map, glob Poly})
    (={c1, k1, p1, x0, URF.map, glob Poly} ==> ={y0, c1, URF.map, glob Poly})=> //=;
    1: smt(); 2: by sim.
  by sim; sp; symmetry; eager call eager_urf_composition_enc; auto.
sim.
swap{2} [12..13] -2; sim.
swap{2} 10 -1=> />.
replace{2} { all; (<@ as call1); (<@ as call2) |} by {
    all;
    call2;
    call1;
  }
  (={k1, k2, p1, c2, URF.map, glob Poly} ==> 
    ={p, t', s, opt, t, c, a, n, k, c1, URF.map, glob Poly})
  (={k1, k2, p1, c2, URF.map, glob Poly} ==> 
    ={p, t', s, opt, t, c, a, n, k, c1, URF.map, glob Poly})=> //=; 1: smt(); last first.
+ sp=> />.
  seq 3 3 : (={c1, t', s, r, a, c, p1, glob Poly, URF.map}); 1: by sim.
  conseq/>.
  inline Composition(CC_URF, Poly).enc CC_URF.enc.
  symmetry; sim.
  swap{2} -2; sim=> />.
  replace{2} { all; (<@ as call1); (<@ as call2) } by {
      all;
      call2;
      call1;
    }
    (={c1, t', s, r, a, c, p1, URF.map, glob Poly} ==>
      ={t'0, c0, s0, a0, n0, t', URF.map, glob Poly})
    (={c1, t', s, r, a, c, p1, URF.map, glob Poly} ==>
      ={t'0, c0, s0, a0, n0, t', URF.map, glob Poly})=> //=; 1: smt(); last first.
  - seq 19 19 : (={s0, n0, r, a, c, r0, a0, c0, t'0, t', URF.map, glob Poly}); 1: by sim=> />.
    conseq/>.
    transitivity{1} {
        (t', t'0) <@ Swap_Poly(Poly).double_mac((r, poly_concat a c), (r0, poly_concat a0 c0));
      }
      (={r, a, c, r0, a0, c0, t'0, t', URF.map, glob Poly} ==>
        ={t'0, t', URF.map, glob Poly})
      (={r, a, c, r0, a0, c0, t'0, t', URF.map, glob Poly} ==>
        ={t'0, t', URF.map, glob Poly})=> //=; 1: smt().
    + by inline*; auto; call(: true); auto; call(: true); auto=> />.
    transitivity{2} {
        (t', t'0) <@ Swap_Poly(Poly).double_reverse_mac((r, poly_concat a c), (r0, poly_concat a0 c0));
      }
      (={r, a, c, r0, a0, c0, t'0, t', URF.map, glob Poly} ==>
        ={t'0, t', URF.map, glob Poly})
      (={r, a, c, r0, a0, c0, t'0, t', URF.map, glob Poly} ==>
        ={t'0, t', URF.map, glob Poly})=> //=; 1: smt(); last first.
    + by inline*; auto; call(: true); auto; call(: true); auto=> />.
    by call swap_poly; auto.
  sim.
  by swap{2} -19; sim.
sim.
swap{2} 9 -3.
swap{2} -1; sim; sp=> />.
inline CC_URF.enc.
swap{1} 2; swap{2} -1; sim; sp.
replace{1} { all } by {
    c1 <- witness;
    all;
  }
  (={k1, p1, x0, URF.map, glob Poly} ==> ={y0, c1, URF.map, glob Poly})
  (={k1, p1, x0, URF.map, glob Poly} /\ c1{2} = witness ==> ={y0, c1, URF.map, glob Poly})=> //=;
  1: smt(); 1: by sim.
sp.
replace{1} { start; <@ |} by {
    Eager.y <- witness;
    Eager.x <- x0;
    start;
    Eager.y <@ URF.f(Eager.x);
    y0 <- Eager.y;
  }
  (={c1, k1, p1, x0, URF.map, glob Poly} ==> ={y0, c1, URF.map, glob Poly})
  (={c1, k1, p1, x0, URF.map, glob Poly} ==> ={y0, c1, URF.map, glob Poly})=> //=;
  1: smt(); 1: by sim.
replace{2} {| <@; fin|} by {
    Eager.y <- witness;
    Eager.x <- x0;
    Eager.y <@ URF.f(Eager.x);
    fin;
    y0 <- Eager.y;
  }
  (={c1, k1, p1, x0, URF.map, glob Poly} ==> ={y0, c1, URF.map, glob Poly})
  (={c1, k1, p1, x0, URF.map, glob Poly} ==> ={y0, c1, URF.map, glob Poly})=> //=;
  1: smt(); 2: by sim.
by sim; sp; symmetry; eager call eager_urf_composition_enc; auto.
qed.

local clone RndProd as RP with
  type a <- polykey,
  type b <- polyt4,
  type t_in <- cct1,
  type d_input <- unit,
  type d_output <- bool,
  op da <- dpolykey,
  op db <- dpolyt4
proof * by smt(dpolyt4_ll dpolykey_ll).


local module (Com (O : RP.Oracles) (Poly : KRO) : SKE) = {
  var order_enc : (nonce * associated_data * ciphertext * tag) list
  proc keygen () : cckey = {
    Comp.order_dec <- [];
    Comp.b <- false;
    order_enc <- [];
    WrapForgery.success <- false;
    O.init();
    return witness;
  }
  proc enc (k : cckey, nap : nonce * associated_data * plaintext) : 
    (nonce * associated_data * ciphertext * tag) option  = {
    var n, a, p, i, z, y, c, c', t, r, t';
    (n,a,p) <- nap;
    c     <- empty_ctxt;
    i     <- 1;
    while (i < plength p) {
      z <@ O.f(cc_concat i n);
      y <- concat32 z +^ pnth witness p (i-1);
      c <- cappend c y;
      i <- i + 1;
    }
    z  <@ O.f(cc_concat i n);
    c' <- ptrunc_last p (concat32 z);
    c' <- c' ^+ plast_block p;
    c  <- cappend_last c c';
    (r,t) <@ O.f(cc_concat 0 n);
    order_enc <- rcons order_enc (n, a, c, t);
    t' <@ Poly.mac(r, poly_concat a c);
    return Some (n,a,c,t);
  }
  proc dec (k : cckey, nact : nonce * associated_data * ciphertext * tag) : 
    (nonce * associated_data * plaintext) option = {
    Comp.order_dec <- rcons Comp.order_dec (k,nact);
    return None;
  }
  proc call_all_poly_dec () = {
    var k, nact, i, n, a, c, t, t', t2, r, s;
    i <- 0;
    while (i < size Comp.order_dec) {
      (k, nact) <- nth witness Comp.order_dec i;
      (n, a, c, t) <- nact;
      (r, s) <@ O.f(cc_concat 0 n);
      t' <@ Poly.mac(r, poly_concat a c);
      t2 <- t' + s;
      if (t = t2) {
        WrapForgery.success <- true;
      }
      i <- i + 1;
    }
  }
}.

local module (Com' (O : RP.Oracles) (Poly : KRO) : SKE) = {
  proc keygen () : cckey = {
    Comp.order_dec <- [];
    Comp.b <- false;
    Com.order_enc <- [];
    WrapForgery.success <- false;
    O.init();
    return witness;
  }
  proc enc (k : cckey, nap : nonce * associated_data * plaintext) : 
    (nonce * associated_data * ciphertext * tag) option  = {
    var n, a, p, i, z, y, c, c', t, r, t', s;
    (n,a,p) <- nap;
    c     <- empty_ctxt;
    i     <- 1;
    while (i < plength p) {
      z <@ O.f(cc_concat i n);
      y <- concat32 z +^ pnth witness p (i-1);
      c <- cappend c y;
      i <- i + 1;
    }
    z  <@ O.f(cc_concat i n);
    c' <- ptrunc_last p (concat32 z);
    c' <- c' ^+ plast_block p;
    c  <- cappend_last c c';
    (r,s) <@ O.f(cc_concat 0 n);
    t' <@ Poly.mac(r, poly_concat a c);
    t <- t' + s;
    Com.order_enc <- rcons Com.order_enc (n, a, c, t);
    return Some (n,a,c,t);
  }
  proc dec (k : cckey, nact : nonce * associated_data * ciphertext * tag) : 
    (nonce * associated_data * plaintext) option = {
    Comp.order_dec <- rcons Comp.order_dec (k,nact);
    return None;
  }
}.


local module ForgeryList1 (A : CCA_Adv) (Poly : KRO) (O : RP.Oracles) = {
  proc game () = {
    WrapForgery.success <- false;
    EncDec(A,Com(O,Poly)).game();
    Com(O,Poly).call_all_poly_dec();
  }
}.

local module ForgeryList2 (A : CCA_Adv) (Poly : KRO) (O : RP.Oracles) = {
  proc game () = {
    WrapForgery.success <- false;
    EncDec(A,Com'(O,Poly)).game();
    Com(O,Poly).call_all_poly_dec();
  }
}.

module Trunc32 (O : EG.RO) : RP.ROab.RO = {
  proc init = O.init
  proc get (x : cct1) = {
    var r;
    r <@ O.get(x);
    return trunc32 r;
  }
  proc sample = O.sample
  proc rem = O.rem
  proc set (x : cct1, r : polykey * polyt4) = {
    O.set(x, concat32 r);
  }
}.

op inv_map (m1 : (cct1, cct2) fmap) (m2 : (cct1, polykey * polyt4) fmap) = 
  fdom m1 = fdom m2 && 
  forall x, x \in m1 => exists y, m1.[x] = Some y /\ m2.[x] = Some (trunc32 y).

local lemma step_1_rw_forgelist (A <: CCA_Adv { WrapForgery, Comp, URF, NR, EG.RO, Poly, Com, RP.ROab.RO, RP.ROab.FRO }) &m :
  Pr[ ForgeryList  (A_nonce_respecting(A),CC_URF,Poly).game() @ &m : WrapForgery.success] =
  Pr[ ForgeryList2 (A_nonce_respecting(A),Poly,RP.O1(Trunc32(EG.RO))).game() @ &m : WrapForgery.success].
proof. 
byequiv=> //=; proc; sim; sp.
inline{1} 1; inline{2} 1; sp.
inline{1} 1; inline{2} 1; sp.
inline{1} 1; inline{2} 1; sp.
inline{1} 1; inline{2} 1; sp.
inline{1} 1; inline{2} 1; sp.
inline{1} 1; inline{2} 1; sp.
inline{1} 1; inline{2} 1; sp.
swap -1; sim.
inline{1} 2; inline{2} 2; sp.
while(={i, glob Comp, glob Poly} /\ URF.map{1} = EG.RO.m{2}).
+ conseq(:_==> ={i, WrapForgery.success, glob Poly} /\ URF.map{1} = EG.RO.m{2})=>//=.
  sim; sp.
  inline{2} 1; sp; sim.
  by call urf_ro_get; auto; smt().
wp=> />.
conseq(:_==> ={glob Poly, glob Comp} /\ URF.map{1} = EG.RO.m{2})=> //=. 
call(: ={glob Wrap, glob NR, glob Comp, glob Poly} /\ URF.map{1} = EG.RO.m{2})=> //=.
+ by proc; inline*; auto.
+ proc; sp; if; 1, 3: auto; sp.
  inline{1} 1; inline{2} 1.
  inline{1} 2; inline{2} 2.
  rcondt{1} 18; 1: auto=> //=.
  rcondt{2} 17; 1: auto=> //=.
  rcondt{1} 20; 1: auto=> //=.
  rcondt{2} 19; 1: auto=> //=.
  wp=> /=/>.
  conseq(:_==> ={c1, t', s, n0, a0, p1, p, p0, glob Wrap, glob NR, glob Poly} /\
    URF.map{1} = EG.RO.m{2}); 1: smt().
  conseq/>.
  call(:true)=> />.
  wp 14 12=> /=.
  swap{2} -3; auto=> />.
  swap{1} 8 3.
  conseq(:_==> ={r, s, a0, c1, p1, s, n0, p0} /\ 
      URF.map{1} = EG.RO.m{2} /\ y{1} = concat32 z{2})=> />.
  replace{1} { all } by {
      x <- witness;
      all;
    }
    (={nap, n, a, p, glob Wrap, glob Poly, glob NR, glob URF} ==>
      ={r, s, a0, c1, p1, y, s, n0, p0, y, glob URF, glob NR})
    (={nap, n, a, p, glob Wrap, glob Poly, glob NR} /\ 
      URF.map{1} = EG.RO.m{2} /\ (nap = (n,a,p)){1} ==>
      ={r, s, a0, c1, p1, s, n0, p0} /\ 
      URF.map{1} = EG.RO.m{2} /\ y{1} = concat32 z{2})=> />; 1: smt().
  + by sim.
  replace{1} { init; ( <@ as cc_urf) ; (_;while as loop) ; (<@ as rest); set_x |} by {
      init;
      loop;
      rest;
      cc_urf;
      set_x;
    }
    (={nap, n, a, p, glob Wrap, glob Poly, glob NR, glob URF} ==>
      ={r, s, a0, c1, p1, y, s, n0, p0, y, glob URF, glob NR})
    (={nap, n, a, p, glob Wrap, glob Poly, glob NR} /\ 
      URF.map{1} = EG.RO.m{2} /\ (nap = (n,a,p)){1} ==>
      ={r, s, a0, c1, p1, s, n0, p0} /\ 
      URF.map{1} = EG.RO.m{2} /\ y{1} = concat32 z{2})=> />; 1: smt().
  + sim.
    replace{2} { (_;while as loop) ; (<@ as call1); (<@ as call2) |} by {
        loop;
        call2;
        call1;
      }
      (={nap, n, a, p, glob Wrap, glob Poly, glob NR, glob URF} ==>
        ={a0, c1, p1, x, n0, p0, y, glob URF})
      (={nap, n, a, p, glob Wrap, glob Poly, glob NR, glob URF} ==>
        ={a0, c1, p1, x, n0, p0, y, glob URF})=> />; 1: smt().
    + sim; sp.
      swap{1} 1; sp=> />.
      conseq(: ={x, k, n0, i, p1, c1, URF.map} ==> ={x, k, n0, i, p1, c1, URF.map})=> />.
      eager while (J: 
          x <@ CC_URF.enc(k, cc_concat 0 n0); ~
          x <@ CC_URF.enc(k, cc_concat 0 n0); :
          ={x, k, n0, i, p1, c1, URF.map} ==>
          ={x, k, n0, i, p1, c1, URF.map})=> />; 1, 3: sim.
      swap{2} -3; sim; inline*; sp=> />.
      case: (={x2}).
      - rcondf{1} 7; 1: by auto; if; auto; smt(mem_set).
        rcondf{2} 7; 1: by auto; if; auto; smt(mem_set).
        if; auto; smt(set_setE).
      if{1}; last first.
      - rcondf{2} 7; 1: by auto; if; auto; smt(mem_set).
        by sp; if; auto; smt(get_setE).
      rcondt{2} 7; 1: by auto; if; auto; smt(mem_set).
      if{2}; last first. 
      - rcondf{1} 7; 1: by auto; smt(mem_set).
        by auto; smt(get_setE).
      rcondt{1} 7; 1: by auto; smt(mem_set).
      swap [1..3] 3; sp.
      swap 3 2; wp 4 4.
      transitivity{1} {
          y0 <$ dcct2;
          URF.map.[x2] <- y0;
          y1 <$ dcct2;
          URF.map.[x3] <- y1;
        }
        (={x2, x3, URF.map} ==> ={y0, y1, URF.map})
        (={URF.map} /\ (x2,x3){1} = (x3,x2){2} /\ x2{1} <> x3{1} ==>
          ={URF.map} /\ (y0,y1){1} = (y1,y0){2})=> />; 1: smt().
      + by auto; smt(get_setE).
      transitivity{2} {
          y0 <$ dcct2;
          URF.map.[x2] <- y0;
          y1 <$ dcct2;
          URF.map.[x3] <- y1;
        }
        (={URF.map} /\ (x2,x3){1} = (x3,x2){2} /\ x2{1} <> x3{1} ==>
          ={URF.map} /\ (y0,y1){1} = (y1,y0){2})
        (={x2, x3, URF.map} ==> ={y0, y1, URF.map})=> />; 1: smt(); last first.
      + auto; smt(get_setE).
      wp; swap{1} -2; swap{2} -1; wp. 
      by rnd; rnd; auto=> /> &h neq y1 ? y2 ?; rewrite set_setE (eq_sym x2{h}) neq/=. 
    seq 9 9 : (={k, i, n0, URF.map, a0, c1, p1, n0, p0}); 1: by sim.
    conseq/>.
    inline*; sp=> />.
     case: (={x2}).
     - rcondf{1} 7; 1: by auto; if; auto; smt(mem_set).
       rcondf{2} 7; 1: by auto; if; auto; smt(mem_set).
       if; auto; smt(set_setE).
    if{1}; last first.
    - rcondf{2} 7; 1: by auto; if; auto; smt(mem_set).
      by sp; if; auto; smt(get_setE).
    rcondt{2} 7; 1: by auto; if; auto; smt(mem_set).
    if{2}; last first. 
    - rcondf{1} 7; 1: by auto; smt(mem_set).
      by auto; smt(get_setE).
    rcondt{1} 7; 1: by auto; smt(mem_set).
    swap [1..3] 3; sp.
    swap 3 2; wp 4 4.
    transitivity{1} {
        y0 <$ dcct2;
        URF.map.[x2] <- y0;
        y1 <$ dcct2;
        URF.map.[x3] <- y1;
      }
      (={x2, x3, URF.map} ==> ={y0, y1, URF.map})
      (={URF.map} /\ (x2,x3){1} = (x3,x2){2} /\ x2{1} <> x3{1} ==>
        ={URF.map} /\ (y0,y1){1} = (y1,y0){2})=> />; 1: smt().
    + by auto; smt(get_setE).
    transitivity{2} {
        y0 <$ dcct2;
        URF.map.[x2] <- y0;
        y1 <$ dcct2;
        URF.map.[x3] <- y1;
      }
      (={URF.map} /\ (x2,x3){1} = (x3,x2){2} /\ x2{1} <> x3{1} ==>
        ={URF.map} /\ (y0,y1){1} = (y1,y0){2})
      (={x2, x3, URF.map} ==> ={y0, y1, URF.map})=> />; 1: smt(); last first.
    + auto; smt(get_setE).
    wp; swap{1} -2; swap{2} -1; wp. 
    by rnd; rnd; auto=> /> &h neq y1 ? y2 ?; rewrite set_setE (eq_sym x2{h}) neq/=.
  inline{2}  RP.O1(Trunc32(EG.RO)).f; wp=> />.
  sp; call(urf_ro_get); wp=> /= />.
  call(urf_ro_get); wp=> /> ; 1: smt(concat32_K).
  conseq(:_==> ={i, n, c1} /\ URF.map{1} = EG.RO.m{2})=> />; 1: smt(concat32_K trunc32_K).
  while(={i, c1, p1, n0} /\ URF.map{1} = EG.RO.m{2}); auto=> />.
  by call urf_ro_get; auto; smt(concat32_K trunc32_K).
qed.


local lemma step_2_rw_forgelist  (A <: CCA_Adv { WrapForgery, Comp, URF, NR, EG.RO, Poly, Com, RP.ROab.RO, RP.ROab.FRO }) &m :
  Pr[ ForgeryList  (A_nonce_respecting(A),CC_URF,Poly).game() @ &m : WrapForgery.success] =
  Pr[ ForgeryList2 (A_nonce_respecting(A),Poly,RP.O1(RP.ROab.RO)).game() @ &m : WrapForgery.success].
proof.
rewrite (step_1_rw_forgelist A &m).
byequiv=> //=; proc; sim; sp.
inline{1} 1; inline{2} 1; sp.
inline{1} 1; inline{2} 1; sp.
inline{1} 1; inline{2} 1; sp.
inline{1} 1; inline{2} 1; sp.
inline{1} 1; inline{2} 1; sp.
inline{1} 1; inline{2} 1; sp.
inline{1} 1; inline{2} 1; sp.
swap -1; sim. print inv_map.
seq 1 1 : (={glob Poly, glob NR, glob Wrap, glob Com'} /\ 
  inv_map EG.RO.m{1} RP.ROab.RO.m{2}).
+ call(: ={glob Poly, glob NR, glob Wrap, glob Com'} /\ 
  inv_map EG.RO.m{1} RP.ROab.RO.m{2}); last first.
  - by auto; smt(fdom0 mem_empty).
  - by proc; inline*; auto.
  - proc; sp; if; 1, 3: auto.
    seq 1 1 : (={opt, glob Poly, glob NR, glob Wrap, glob Com', p} /\  
      inv_map EG.RO.m{1} RP.ROab.RO.m{2}); 2: by auto=> />.
    inline{1} 1; inline{2} 1; sp=> />.
    seq 1 1 : (={c0, p0, glob Poly, glob NR, glob Wrap, glob Com'} /\
      inv_map EG.RO.m{1} RP.ROab.RO.m{2}); 2: by auto=> />.
    inline{1} 1; inline{2} 1; sp.
    wp; call(: true).
    wp; swap -1; wp=> /=.
    conseq(:_==> ={r, a0, c1, n0, s, p0, c'} /\ inv_map EG.RO.m{1} RP.ROab.RO.m{2})=> />.
    inline*.
    wp 13 10=> /=.
    conseq(:_==> ={c1, c'} /\ inv_map EG.RO.m{1} RP.ROab.RO.m{2} /\ 
        x4{1} = x1{2} /\ x4{1} \in EG.RO.m{1}); 1: smt(mem_fdom domE trunc32_K concat32_K).
    seq 10 8 : (={x1, c1, c'} /\ inv_map EG.RO.m{1} RP.ROab.RO.m{2}); last first.
    + sp; wp. 
      conseq(:_==> trunc32 r5{1} = r2{2}); 1: smt(mem_fdom mem_set fdom_set get_setE).
      rnd trunc32 concat32; auto=> />.
      move=> &l &r eq_fdom inv; split; 1: smt(trunc32_K concat32_K).
      move=> h{h}; split.
      - move=> ab; rewrite /RP.dab=> ?.
        rewrite-dcct2_dpkey_dpt4 dmapE; apply mu_eq=> a /=.
        smt(trunc32_K concat32_K).
      move=> ?; rewrite /RP.dab -dcct2_dpkey_dpt4 => [] cc ?.
      smt(supp_dmap trunc32_K concat32_K).
    wp 5 4=> /=.
    conseq(:_==> x3{1} = x0{2} /\ ={c1} /\ x3{1} \in EG.RO.m{1} /\
        inv_map EG.RO.m{1} RP.ROab.RO.m{2})=> />.
    + smt(mem_fdom domE trunc32_K concat32_K).
    seq 2 2 : (={x0, c1} /\ inv_map EG.RO.m{1} RP.ROab.RO.m{2}); last first.
    + sp; wp. 
      conseq(:_==> trunc32 r4{1} = r1{2}); 1: smt(mem_fdom mem_set fdom_set get_setE).
      rnd trunc32 concat32; auto=> />.
      move=> &l &r eq_fdom inv; split; 1: smt(trunc32_K concat32_K).
      move=> h{h}; split.
      - move=> ab; rewrite /RP.dab=> ?.
        rewrite-dcct2_dpkey_dpt4 dmapE; apply mu_eq=> a /=.
        smt(trunc32_K concat32_K).
      move=> ?; rewrite /RP.dab -dcct2_dpkey_dpt4 => [] cc ?.
      smt(supp_dmap trunc32_K concat32_K).
    wp.
    while(={i, p1, n0, c1} /\ inv_map EG.RO.m{1} RP.ROab.RO.m{2}); auto.
    sp; conseq(:_==> trunc32 r3{1} = r0{2}); 1: smt(mem_fdom mem_set fdom_set get_setE).
    rnd trunc32 concat32; auto=> />.
    move=> &l &r eq_fdom inv ?; split; 1: smt(trunc32_K concat32_K).
    move=> h{h}; split.
    - move=> ab; rewrite /RP.dab=> ?. 
      rewrite-dcct2_dpkey_dpt4 dmapE; apply mu_eq=> a /=.
      smt(trunc32_K concat32_K).
    move=> ?; rewrite /RP.dab -dcct2_dpkey_dpt4 => [] cc ?.
    smt(supp_dmap trunc32_K concat32_K).
inline*; sp; wp.
while(={i, Comp.order_dec, glob Poly, WrapForgery.success} /\ 
    inv_map EG.RO.m{1} RP.ROab.RO.m{2}); auto.
call(: true); auto.
sp.
conseq(:_==> trunc32 r1{1} = r0{2}); 1: smt(mem_fdom mem_set fdom_set get_setE).
rnd trunc32 concat32; auto=> />.
move=> &l &r ? ? eq_fdom inv ?; split; 1: smt(trunc32_K concat32_K).
move=> h{h}; split.
- move=> ab; rewrite /RP.dab=> ?.
  rewrite-dcct2_dpkey_dpt4 dmapE; apply mu_eq=> a /=.
  smt(trunc32_K concat32_K).
move=> ?; rewrite /RP.dab -dcct2_dpkey_dpt4 => [] cc ?.
smt(supp_dmap trunc32_K concat32_K).
qed.


local module FL2 (A : CCA_Adv) (Poly : KRO) (O : RP.Oracles) = {
  proc distinguish () = {
    ForgeryList2(A_nonce_respecting(A), Poly, O).game();
    return WrapForgery.success;
  }
}.

local lemma step_3_rw_forgelist
    (A <: CCA_Adv { WrapForgery, Comp, URF, NR, EG.RO, Poly, Com, 
      RP.ROab.RO, RP.ROab.FRO, RP.ROa.RO, RP.ROa.FRO, RP.ROb.RO, RP.ROb.FRO}) &m :
  Pr[ ForgeryList  (A_nonce_respecting(A),CC_URF,Poly).game() @ &m : WrapForgery.success] =
  Pr[ ForgeryList2 (A_nonce_respecting(A),Poly,RP.O2(RP.ROa.RO,RP.ROb.RO)).game() @ &m : WrapForgery.success].
proof.
rewrite (step_2_rw_forgelist A &m).
have->:
  Pr[ ForgeryList2 (A_nonce_respecting(A),Poly,RP.O1(RP.ROab.RO)).game() @ &m : WrapForgery.success] =
  Pr[ RP.Game(FL2(A,Poly),RP.O1(RP.ROab.RO)).main() @ &m : res].
+ by byequiv=> //=; proc; inline*; sim.
have->:
  Pr[ ForgeryList2 (A_nonce_respecting(A),Poly,RP.O2(RP.ROa.RO,RP.ROb.RO)).game() @ &m : WrapForgery.success]=
  Pr[ RP.Game(FL2(A,Poly),RP.O2(RP.ROa.RO,RP.ROb.RO)).main() @ &m : res].
+ by byequiv=> //=; proc; inline*; sim.
by byequiv(RP.prod_split (FL2(A,Poly))) => //=.
qed.


(* TODO : reprendre ici *)

local module (Com2 (Oa : RP.ROa.RO) (Ob : RP.ROb.RO) (Poly : KRO) : SKE) = {
  proc keygen () : cckey = {
    Comp.order_dec <- [];
    Comp.b <- false;
    Com.order_enc <- [];
    WrapForgery.success <- false;
    Oa.init();
    Ob.init();
    return witness;
  }
  proc enc (k : cckey, nap : nonce * associated_data * plaintext) : 
    (nonce * associated_data * ciphertext * tag) option  = {
    var n, a, p, i, z, y, c, c', t, r, t';
    (n,a,p) <- nap;
    c     <- empty_ctxt;
    i     <- 1;
    while (i < plength p) {
      z <@ RP.O2(Oa,Ob).f(cc_concat i n);
      y <- concat32 z +^ pnth witness p (i-1);
      c <- cappend c y;
      i <- i + 1;
    }
    z  <@ RP.O2(Oa,Ob).f(cc_concat i n);
    c' <- ptrunc_last p (concat32 z);
    c' <- c' ^+ plast_block p;
    c  <- cappend_last c c';
    t <$ dpolyt4;
    Com.order_enc <- rcons Com.order_enc (n, a, c, t);
    r <@ Oa.get(cc_concat 0 n);
    t' <@ Poly.mac(r, poly_concat a c);
    map.[n] <- t;
    (* Ob.set(cc_concat 0 n, t - t'); *)
    return Some (n,a,c,t);
  }
  proc call_all_poly_dec () = {
    var k, nact, i, n, a, c, t, t', t2, r, s;
    i <- 0;
    while (i < size Comp.order_dec) {
      (k, nact) <- nth witness Comp.order_dec i;
      (n, a, c, t) <- nact;
      "t <- oget map.[n];"
      (r, s) <@ O.f(cc_concat 0 n);
      t' <@ Poly.mac(r, poly_concat a c);
      t2 <- if (n \in map) then oget map.[n] else t' + s;
      if (t = t2) {
        WrapForgery.success <- true;
      }
      i <- i + 1;
    }
  }
  proc all_enc () = {
    var nac, i, n, a, c, r, s, t;
    i <- 0;
    while (i < size Com.order_enc) {
      nac <- nth witness Com.order_enc i;
      (n, a, c, t) <- nac;
      r <@ Oa.get(cc_concat 0 n);
      t' <@ Poly.mac(r, poly_concat a c);
      Ob.set(cc_concat 0 n, t - t');
      map.[n] <- t;
      i <- i + 1;
    }
  }

  proc dec (k : cckey, nact : nonce * associated_data * ciphertext * tag) : 
    (nonce * associated_data * plaintext) option = {
    Comp.order_dec <- rcons Comp.order_dec (k,nact);
    return None;
  }

}.

local module ForgeryList3 (A : CCA_Adv) (Poly : KRO) (Oa : RP.ROa.RO) (Ob : RP.ROb.RO) = {
  proc game () = {
    WrapForgery.success <- false;
    EncDec(A,Com2(Oa,Ob,Poly)).game();
    Com(RP.O2(Oa,Ob),Poly).call_all_poly_dec();
    all_enc;
  }
}.

op inv_nonces (d1 : nonce fset) (d2 : cct1 fset) =
  forall n, ! n \in d1 => forall i, good_size i => ! cc_concat i n \in d2.


local lemma step_4_rw_forgelist
    (A <: CCA_Adv { WrapForgery, Comp, URF, NR, EG.RO, Poly, Com, 
      RP.ROa.RO, RP.ROa.FRO, RP.ROb.RO, RP.ROb.FRO}) &m :
  Pr[ ForgeryList2 (A_nonce_respecting(A),Poly,RP.O2(RP.ROa.RO,RP.ROb.RO)).game() @ &m : WrapForgery.success] =
  Pr[ ForgeryList3 (A_nonce_respecting(A),Poly,RP.ROa.RO,RP.ROb.RO).game() @ &m : WrapForgery.success].
proof.
byequiv=> //=; proc; sim; inline*; sp; sim.
call(: ={glob Poly, glob NR, glob Wrap, glob Com, glob RP.ROa.RO, glob RP.ROb.RO} /\
    inv_nonces (fdom NR.nonces{1}) (fdom RP.ROa.RO.m{1}) /\ 
    fdom RP.ROa.RO.m{1} = fdom RP.ROb.RO.m{1}); last first. 
+ by auto; smt(mem_fdom mem_empty fdom0).
+ by proc; inline*; auto.
proc; inline*; sp; if; 1, 3: auto.
rcondt{2} 32; 1: by auto=> //=.
rcondt{2} 34; 1: by auto=> //=.
rcondt{1} 35; 1: by auto=> //=.
rcondt{1} 37; 1: by auto=> //=.
sp; conseq/>.
wp 27 24=> /= />.
conseq(:_==> ={c1, t0, glob Poly, glob NR, glob Wrap, glob Com, glob RP.ROa.RO, 
    glob RP.ROb.RO} /\ inv_nonces (fdom NR.nonces{2} `|` fset1 n0{2})
    (fdom RP.ROa.RO.m{2}) /\ fdom RP.ROa.RO.m{1} = fdom RP.ROb.RO.m{1})=>/>.
+ smt(fdom_set).
seq 14 14 : (={n0, p1, a0, c1, glob Poly, glob Wrap, glob Com, glob RP.ROa.RO, 
      glob RP.ROb.RO, glob NR} /\ n0{2} \notin NR.nonces{1} /\ good_size 0 /\
      cc_concat 0 n0{1} \notin RP.ROa.RO.m{1} /\
      inv_nonces (fdom NR.nonces{2} `|` fset1 n0{2}) (fdom RP.ROa.RO.m{2}) /\ 
      fdom RP.ROa.RO.m{1} = fdom RP.ROb.RO.m{1})=>/>; last first.
+ sp.    
  rcondt{1} 2; 1: auto; rcondt{2} 2; 1: auto.
  rcondt{1} 6; 1: (auto; smt(mem_fdom)).
  swap{1} 5 -3.
  swap{1} 5 -4; sp=> />.
  swap{2} 4 -2.
  swap{2} 7 -6; sp=> />.
  swap{2} 5 -4; sp=> />.
  conseq(:_==> ={t0, glob Poly, RP.ROa.RO.m, RP.ROb.RO.m} /\
      inv_nonces (fdom NR.nonces{2} `|` fset1 n0{2}) (fdom RP.ROa.RO.m{2}) /\
      fdom RP.ROa.RO.m{1} = fdom RP.ROb.RO.m{1})=>/>.
  transitivity{1} {
      r4 <$ dpolykey;
      r5 <$ dpolyt4;
      RP.ROa.RO.m.[x3] <- r4;
      RP.ROb.RO.m.[x3] <- r5;
      t' <@ Poly.mac(r4, poly_concat a0 c1);
      t0 <- t' + r5;
    }
    (={x3, x4, c1, a0, n0, glob Poly, glob NR, RP.ROa.RO.m, RP.ROb.RO.m} /\ 
      fdom RP.ROa.RO.m{1} = fdom RP.ROb.RO.m{1} /\ x3{1} = x4{1} ==>
      ={c1, t0, glob Poly, glob NR, RP.ROa.RO.m, RP.ROb.RO.m} /\ 
      fdom RP.ROa.RO.m{1} = fdom RP.ROb.RO.m{1})
    (={c1, a0, n0, glob Poly, glob NR, RP.ROa.RO.m, RP.ROb.RO.m} /\ 
      (x3,x4,x4){1} = (x,x0,x){2} /\ x{2} = cc_concat 0 n0{1} /\ 
      good_size 0 /\
      inv_nonces (fdom NR.nonces{2} `|` fset1 n0{2}) (fdom RP.ROa.RO.m{2}) /\
      fdom RP.ROa.RO.m{1} = fdom RP.ROb.RO.m{1} ==>
      ={c1, t0, glob Poly, glob NR, RP.ROa.RO.m, RP.ROb.RO.m} /\ 
      inv_nonces (fdom NR.nonces{2} `|` fset1 n0{2}) (fdom RP.ROa.RO.m{2}) /\
      fdom RP.ROa.RO.m{1} = fdom RP.ROb.RO.m{1})=> //=; 1: smt().
  + by wp; call(: true); auto; smt(fdom_set get_setE fmap_eqP mem_fdom).
  move=>/>.
  transitivity{1} {
      r4 <$ dpolykey;
      r5 <$ dpolyt4;
      RP.ROa.RO.m.[x3] <- r4;
      t' <@ Poly.mac(r4, poly_concat a0 c1);
      t0 <- r5;
      RP.ROb.RO.m.[x3] <- r5 - t';
    }
    (={x3, a0, c1, n0, glob Poly, glob NR, RP.ROa.RO.m, RP.ROb.RO.m} /\
      x3{1} = cc_concat 0 n0{1} /\ good_size 0 /\
      inv_nonces (fdom NR.nonces{2} `|` fset1 n0{2}) (fdom RP.ROa.RO.m{2}) /\
      fdom RP.ROa.RO.m{1} = fdom RP.ROb.RO.m{1} ==>
      ={t0, glob Poly, RP.ROa.RO.m, RP.ROb.RO.m} /\
      inv_nonces (fdom NR.nonces{2} `|` fset1 n0{2}) (fdom RP.ROa.RO.m{2}) /\
      fdom RP.ROa.RO.m{1} = fdom RP.ROb.RO.m{1})
    (={a0, c1, n0, glob Poly, glob NR, RP.ROa.RO.m, RP.ROb.RO.m} /\
      (x3, x3){1} = (x, x0){2} /\ x{2} = cc_concat 0 n0{1} /\
      good_size 0 /\
      inv_nonces (fdom NR.nonces{2} `|` fset1 n0{2}) (fdom RP.ROa.RO.m{2}) /\
      fdom RP.ROa.RO.m{1} = fdom RP.ROb.RO.m{1} ==>
      ={t0, glob Poly, RP.ROa.RO.m, RP.ROb.RO.m} /\
      inv_nonces (fdom NR.nonces{2} `|` fset1 n0{2}) (fdom RP.ROa.RO.m{2}) /\
      fdom RP.ROa.RO.m{1} = fdom RP.ROb.RO.m{1})=> //=; 1: smt(); last first.
  + wp; call(: true); auto=> />.
    move=> &h good_size_0 hinv eq_fdom key ? t ?.
    rewrite !get_setE /= oget_some /= => r.
    rewrite !fdom_set -eq_fdom /= => n ^ n_nin_nonces_n0.
    rewrite in_fsetU1 negb_or /= => [#] n_nin_nonces n_neq_n0 j j_good_size.
    rewrite in_fsetU1 negb_or mem_fdom.
    have/=:= hinv n n_nin_nonces_n0 j j_good_size.
    rewrite mem_fdom => -> /=.
    by have /=/#:=cc_concat_inj j 0 n n0{h} j_good_size good_size_0.
  wp=> /=. 
  swap -1; wp=> /=; swap{1} -1; wp=> /=.
  conseq(:_==> ={r4, t', glob Poly} /\ t'{1} + r5{1} = r5{2})=> />.
  + move=> &h good_size_0 hinv eq_fdom r5 r4 t'.
    rewrite 2!fdom_set eq_fdom //= -add_sub_A -add_sub_K /=.
    move => n ^ n_nin_nonces_n0.
    rewrite in_fsetU1 negb_or /= => [#] n_nin_nonces n_neq_n0 j j_good_size.
    rewrite in_fsetU1 negb_or -eq_fdom mem_fdom.
    have/=:= hinv n n_nin_nonces_n0 j j_good_size.
    rewrite mem_fdom => -> /=.
    by have /=/#:=cc_concat_inj j 0 n n0{h} j_good_size good_size_0.
  swap -1.
  rnd (fun r => t'{1} + r) (fun r => r - t'{1}).
  conseq(:_==> ={r4, glob Poly, t'}); 2: by sim.
  smt(add_sub_K add_sub_A dpolyt4_fu).
case: (1 < plength p1{1}); last first.
+ rcondf{1} 1; 1: auto.
  rcondf{2} 1; 1: auto.
  rcondt{1} 4; 1: by auto; smt(mem_fdom good_size_leq plength_ge0).
  rcondt{2} 4; 1: by auto; smt(mem_fdom good_size_leq plength_ge0).
  rcondt{1} 8; 1: by auto; smt(mem_fdom good_size_leq plength_ge0).
  rcondt{2} 8; 1: by auto; smt(mem_fdom good_size_leq plength_ge0).
  auto=> />.
  move=> &h hinv eq_fdom n0_nin_nonces good_size_p1 p1_leq_1 key ? t ?.
  rewrite !fdom_set -eq_fdom/= mem_set negb_or /=. 
  have gs0 : good_size 0 by smt(mem_fdom good_size_leq plength_ge0).
  have gs1 : good_size 1 by smt(mem_fdom good_size_leq plength_ge0).
  rewrite gs0/=.
  have //=:=hinv n0{h} _ 0 gs0; rewrite mem_fdom //= => -> /=.
  have /= -> /=:=cc_concat_inj 0 1 n0{h} n0{h} gs0 gs1.
  move=> n ^ n_nin_nonces_n0. 
  rewrite in_fsetU1 mem_fdom negb_or => [#] n_nin_nonces n_neq_n0 j gsj.
  rewrite in_fsetU1 mem_fdom negb_or.
  have:=hinv n _ j gsj; rewrite mem_fdom //= => -> /=.
  by have/#:=cc_concat_inj j 1 n n0{h} gsj gs1.
seq 1 1 : (={n0, i, p1, a0, c1, glob Poly, RP.ROa.RO.m, RP.ROb.RO.m, glob NR} /\
      cc_concat 0 n0{2} \notin RP.ROa.RO.m{1} /\ 1 < plength p1{1} /\
      cc_concat i{1} n0{2} \notin RP.ROa.RO.m{1} /\
      good_size i{1} /\ i{1} = plength p1{1} /\
      inv_nonces (fdom NR.nonces{2} `|` fset1 n0{2}) (fdom RP.ROa.RO.m{2}) /\ 
      fdom RP.ROa.RO.m{1} = fdom RP.ROb.RO.m{1})=>/>; last first.
+ rcondt{1} 4; 1: by auto=> />. 
  rcondt{2} 4; 1: by auto=> />.
  rcondt{1} 8; 1: by auto=> />; smt(mem_fdom).
  rcondt{2} 8; 1: by auto=> />; smt(mem_fdom).
  auto=> />.
  move=> &h x0_nin_roa p1_gt_1 xp1_nin_roa good_size_p1 hinv eq_fdom key ? t ?.
  have good_size_0: good_size 0; 1: smt(good_size_leq plength_ge0).
  rewrite good_size_0 mem_set x0_nin_roa/=.
  split.
  - have/=:=cc_concat_inj 0 (plength p1{h}) n0{h} n0{h} good_size_0 good_size_p1.
    smt(plength_ge0).
  rewrite 2!fdom_set {2}eq_fdom /= => n ^ n_nin_nonces_n0.
  rewrite in_fsetU1 negb_or /= => [#] n_nin_nonces n_neq_n0 j j_good_size.
  rewrite in_fsetU1 negb_or mem_fdom.
  have/=:= hinv n n_nin_nonces_n0 j j_good_size.
  rewrite mem_fdom => -> /=.
  by have /=/#:=cc_concat_inj j (plength p1{h}) n n0{h} j_good_size good_size_p1.
while(={n0, i, p1, a0, c1, glob Poly, RP.ROa.RO.m, RP.ROb.RO.m, glob NR} /\
      cc_concat 0 n0{2} \notin RP.ROa.RO.m{1} /\
      (forall j, i{1} <= j <= plength p1{1} + 1 => 
        cc_concat j n0{2} \notin RP.ROa.RO.m{1}) /\ n0{1} \notin NR.nonces{1} /\
      good_size i{1} /\ good_size (plength p1{1} + 1) /\ 1 <= i{1} <= plength p1{1} /\
      inv_nonces (fdom NR.nonces{2} `|` fset1 n0{2}) (fdom RP.ROa.RO.m{2}) /\ 
      fdom RP.ROa.RO.m{1} = fdom RP.ROb.RO.m{1}).
+ rcondt{1} 4; 1: by auto; smt(mem_fdom).
  rcondt{2} 4; 1: by auto; smt(mem_fdom).
  rcondt{1} 8; 1: by auto; smt(mem_fdom).
  rcondt{2} 8; 1: by auto; smt(mem_fdom).
  auto=> />.
  move=> &h x0_nin_roa xj_nin_roa n0_nin_nonces gsi gsp1S i_ge1 h{h} hinv eq_fdom i_lt_p1 ? ? t ?.
  rewrite !fdom_set -eq_fdom /= mem_set x0_nin_roa /=.
  have gs0 : good_size 0 by smt(good_size_leq).
  have /=:= cc_concat_inj 0 i{h} n0{h} n0{h} gs0 gsi.
  move=> h; split; 1: smt(); move=> {h}.
  split.
  - move=> j j_gt_i j_leq_p1; rewrite mem_set.
    have-> /=:= xj_nin_roa j _ ; 1: smt().
    by have:=cc_concat_inj j i{h} n0{h} n0{h} _ _; smt(good_size_leq).
  split; 1: smt(good_size_leq).
  split; 1: smt().
  move=> n ^ n_nin_nonces_n0.
  rewrite in_fsetU1 mem_fdom negb_or=> [#] n_nin_nonces n_neq_n0 j gsj.
  rewrite in_fsetU1 mem_fdom negb_or.
  have/=:=hinv n n_nin_nonces_n0 j gsj; rewrite mem_fdom //= => -> /=.
  by have /# :=cc_concat_inj j i{h} n n0{h} gsj gsi.
by auto; smt(good_size_leq plength_ge0 mem_fdom cc_concat_inj in_fsetU1).
qed.


local module Rand (CC : FCC) = {
  var urf : (cckey * cct1) list
  proc keygen () = {
    var key;
    urf <- [];
    key <@ CC.keygen();
    return key;
  }
  proc enc (k : cckey, x : cct1) = {
    var y;
    urf <- rcons urf (k,x);
    y <@ CC.enc(k,x);
    return y;
  }
  proc all_enc () = {
    var i, kx;
    i <- 0;
    while (i < size urf) {
      kx <- nth witness urf i;
      CC.enc(kx);
      i <- i + 1;
    }
  }
}.


local module Game1 (A : CCA_Adv) (Poly : KRO) (CC : FCC) (CC2 : FCC) = {
  proc game () = {
    WrapForgery.success <- false;
    CC2.keygen();
    EncDec(A, Comp(Rand(CC), Poly)).game();
    Rand(CC2).all_enc();
    Comp(CC2,Poly).call_all_poly_dec();
  }
}.

op invar (set : cct1 fset) (m : (nonce, associated_data * plaintext * ciphertext * tag) fmap) = 
  forall n, n \notin m => forall i, good_size i => ! cc_concat i n \in set.


local module Invar (E : SKE) = {
  proc keygen = E.keygen
  proc enc (k : cckey, x : nonce * associated_data * plaintext) = {
    var y <- None;
    if (invar (oflist (map snd Rand.urf)) NR.nonces /\ oflist (map snd Rand.urf) = fdom URF.map) {
      y <@ E.enc(k,x);
    }
    return y;
  }
  proc dec = E.dec
}.


local module Game2 (A : CCA_Adv) (Poly : KRO) (CC : FCC) (CC2 : FCC) = {
  proc game () = {
    WrapForgery.success <- false;
    CC2.keygen();
    EncDec(A, Invar(Comp(Rand(CC), Poly))).game();
    Rand(CC2).all_enc();
    Comp(CC2,Poly).call_all_poly_dec();
  }
}.

local module Game3 (A : CCA_Adv) (Poly : KRO) (CC : FCC) = {
  proc game () = {
    WrapForgery.success <- false;
    Rand(CC).keygen();
    EncDec(A, Invar(Comp(Rand(CC), Poly))).game();
    Comp(CC,Poly).call_all_poly_dec();
  }
}.

local module Game4 (A : CCA_Adv) (Poly : KRO) (CC : FCC) = {
  proc game () = {
    WrapForgery.success <- false;
    Rand(CC).keygen();
    EncDec(A, Comp(Rand(CC), Poly)).game();
    Comp(CC,Poly).call_all_poly_dec();
  }
}.

local lemma step_0_poly_local_to_global 
    (A <: CCA_Adv { Order, Wrap, NR, WrapForgery, Comp, URF, Rand, Poly }) &m :
    Pr[Game1(A_nonce_respecting(A),Poly,Random,CC_URF).game() @ &m : WrapForgery.success] =
    Pr[Game2(A_nonce_respecting(A),Poly,Random,CC_URF).game() @ &m : WrapForgery.success].
proof.
byequiv=> //=; proc; inline*; sp; sim.
call(: ={glob NR, glob Wrap, glob Comp, glob Rand, glob Poly} /\ 
  invar (oflist (map snd Rand.urf)){1} NR.nonces{1}); auto; last first.
+ smt(mem_empty set0E in_fset0).
+ by proc; inline*; auto.
proc; inline*; sp; if; 1, 3: auto; sp.
rcondt{2} 1; 1: auto; sp.
rcondt{1} 21; 1: auto=> //=.
rcondt{1} 23; 1: auto=> //=.
rcondt{2} 22; 1: auto=> //=.
rcondt{2} 24; 1: auto=> //=.
wp=> //= />.
conseq(:_==> ={n0, a0, c1, t', s, p, glob Wrap, glob Comp, WrapForgery.success,
    Rand.urf, glob Poly, glob NR}
    /\ invar (oflist (map snd Rand.urf{1})) (NR.nonces.[n0 <- (a0, p, c1, t'+s)]){1})=> //=.
call(: true); auto=> /=.
case: (1 < plength p1{1}); last first.
+ rcondf{1} 6; 1: auto; rcondf{2} 6; auto=> />.
  move=> &h urf Hinvar n0_nin_nonces p1S_good_size p1_leq_1 c1 ? c2 ? r n.
  rewrite mem_set negb_or/= map_rcons -cats1/= oflist_cat -set1E => [][] n_nin_nonces n_neq_n0 j j_gs.
  rewrite in_fsetU1 negb_or/= map_rcons -cats1/= oflist_cat -set1E in_fsetU1/= negb_or.
  have/=:=cc_concat_inj j 0 n n0{h} j_gs _; 1: smt(plength_ge0 good_size_leq good_size_ge0).
  rewrite n_neq_n0 /= => ->/=.
  have/=:=cc_concat_inj j 1 n n0{h} j_gs _; 1: smt(plength_ge0 good_size_leq good_size_ge0).
  rewrite n_neq_n0 /= => ->/=.
  by apply Hinvar.
conseq(:_==> ={a0, c1, p1, n0, s, p, r, i, glob Wrap, glob Comp, glob Poly, 
  glob Rand, glob NR} /\ k{1} = k0{2} /\ i{2} = plength p1{1} /\
  invar (oflist (map snd Rand.urf{1})) (NR.nonces.[n0 <- (a0, p, c1, t'+s)]){1})=> //=.
+ move=> />. move=> &h urf Hinvar n0_nin_nonces p1S_good_size p1_gt_1 urf2 c s Hinvar2 c2 ? r n.
  rewrite mem_set negb_or => [][] r_nin_nonces r_neq_n0 j j_good_size.
  rewrite map_rcons /=-cats1 /=oflist_cat/=-set1E in_fsetU1 negb_or.
  have/=:=cc_concat_inj j (plength p1{h}) n n0{h} j_good_size _.
  - smt(good_size_leq plength_ge0).
  rewrite r_neq_n0 /= => ->/=.
  by have:=Hinvar2 n _ j j_good_size; 1: by rewrite mem_set negb_or //= r_nin_nonces r_neq_n0 /=.
while( ={a0, c1, p1, n0, s, p, r, i, glob Wrap, glob Comp, glob Poly, 
  glob Rand, glob NR} /\ k{1} = k0{2} /\ 1 <= i{2} <= plength p1{1} /\
  n0{1} \notin NR.nonces{1} /\ good_size (plength p1{1} + 1) /\
  invar (oflist (map snd Rand.urf{1})) (NR.nonces.[n0 <- (a0, p, c1, t'+s)]){1})=> //=.
+ auto=> />. move=> &l &r i_ge_1 p1_ge_i n0_nin_nonces p1S_good_size Hinvar p1_gt_i {p1_ge_i} y ?; split; 1: smt().
  move=> n.
  rewrite mem_set negb_or/= => [][] n_nin_nonces n_neq_n0 j j_good_size.
  rewrite map_rcons /=-cats1 /=oflist_cat/=-set1E in_fsetU1 negb_or.
  have/=:=cc_concat_inj j i{r} n n0{r} j_good_size _.
  - smt(good_size_leq plength_ge0).
  rewrite n_neq_n0 /==> ->/=.
  by have:=Hinvar n _ j j_good_size; 1: by rewrite mem_set negb_or //= r_nin_nonces r_neq_n0 /=.
auto=> />.
move=> &h urf Hinvar n0_nin_nonces p1S_good_size p1_gt_1 c ?; do !split; 1: smt().
+ move=> n; rewrite mem_set negb_or /= => [][] n_nin_nonces n_neq_n0 j j_good_size.
  rewrite map_rcons /=-cats1 /=oflist_cat/=-set1E in_fsetU1 negb_or.
  have/=:=cc_concat_inj j 0 n n0{h} j_good_size _.
  - smt(good_size_leq plength_ge0).
  rewrite n_neq_n0 /==> ->/=.
  by apply Hinvar.
smt().
qed.


local lemma step_1_poly_local_to_global 
    (A <: CCA_Adv { Order, Wrap, NR, WrapForgery, Comp, URF, Rand, Poly }) &m :
    Pr[ForgeryList(A_nonce_respecting(A),CC_URF,Poly).game() @ &m : WrapForgery.success] =
    Pr[Game4(A_nonce_respecting(A),Poly,CC_URF).game() @ &m : WrapForgery.success].
proof.
have->:Pr[ForgeryList(A_nonce_respecting(A),CC_URF,Poly).game() @ &m : WrapForgery.success] =
       Pr[ForgeryList(A_nonce_respecting(A),Rand(CC_URF),Poly).game() @ &m : WrapForgery.success].
+ byequiv=> //=; proc; inline*; sim; sp.
  call(: ={glob NR, glob Wrap, glob Comp, glob Poly, glob URF}); auto.
  - by proc; inline*; sim.
  by proc; inline*; sim.
byequiv=> //=; proc; sim.
seq 2 4 : (={WrapForgery.success, URF.map, glob Poly, Comp.order_dec}); last first.
+ inline*; sp.
  by while(={i, Comp.order_dec, WrapForgery.success, URF.map, glob Poly}); 2: auto; sim.
inline{2} 3; rcondf{2} 4; 1: by auto; inline*; auto; conseq(:_==> true); auto.
by swap{2} -1; sim; inline*; auto.
qed.

local lemma step_2_poly_local_to_global 
    (A <: CCA_Adv { Order, Wrap, NR, WrapForgery, Comp, URF, Rand, Poly }) &m :
    Pr[Game3(A_nonce_respecting(A),Poly,CC_URF).game() @ &m : WrapForgery.success] =
    Pr[Game4(A_nonce_respecting(A),Poly,CC_URF).game() @ &m : WrapForgery.success].
proof.
byequiv=> //=; proc; inline*; sp; sim.
call(: ={glob NR, glob Wrap, glob Comp, glob Rand, glob Poly, glob URF} /\ 
  (oflist (map snd Rand.urf)){1} = fdom URF.map{1} /\
  invar (oflist (map snd Rand.urf)){1} NR.nonces{1}); auto; last first.
+ by rcondf{1} 1; 1: auto; rcondf{2} 1; auto; smt(mem_empty set0E in_fset0 fdom0).
+ by proc; inline*; auto.
proc; sp; if; 1, 3: auto; sp.
inline{1} 1; inline{2} 1; sp.
inline{1} 1; inline{2} 1; sp.
rcondt{1} 1; 1: auto; sp.
inline{1} 1; sp.
inline Rand(CC_URF).enc.
auto=> />.
conseq(:_==> ={n0, a0, c1, t', s, p, glob NR, glob Wrap, glob Comp, glob Rand, 
    glob Poly, glob URF} /\ oflist (map snd Rand.urf{1}) = fdom URF.map{1} /\
    invar (oflist (map snd Rand.urf{1})) (NR.nonces.[n0 <- (a0, p, c1, t'+s)]){1})=> //=.
call(: true); auto=> /=.
conseq(:_==> ={n0, a0, c1, t', s, p, r, p1, glob NR, glob Wrap, glob Comp, 
    glob Rand, glob Poly, glob URF} /\ y3{1} = y2{2} /\
    oflist (map snd Rand.urf{1}) = fdom URF.map{1} /\
    (forall apct, invar (oflist (map snd Rand.urf{1})) (NR.nonces.[n0 <- apct]){1}))=> //=.
+ move=> />. 
  move=> &h eq_urf_map_h Hinvar n0_nin_nonces p1S_good_size urf map c s y.
  move=> eq_urf_map all_invar z n.
  rewrite mem_set negb_or /= => [][] n_nin_nonces n_neq_n0 j j_good_size.
  by have:=all_invar witness n _ j j_good_size; 1: by rewrite mem_set n_neq_n0 n_nin_nonces /=.
swap -1.
wp=> /=.
case: (1 <= plength p1{1}); last first.
+ rcondf{1} 8; 1: by auto; inline*; sp; if; auto; smt().
  rcondf{2} 8; 1: by auto; inline*; sp; if; auto; smt().
  sp 2 2.
  swap 7.
  swap [1..3] 3; wp; swap -2; sp; wp=> /=.
  conseq(:_==> ={URF.map} /\ y1{1} = y0{2} /\ y3{1} = y2{2} /\
      fdom URF.map{1} = 
        oflist (map snd
          (rcons (rcons Rand.urf{1} (k1{1},x1{1})) (k3{1},x3{1}))))=> />.
  - move=> &h eq Hinvar n0_nin_nonces p1S_good_size p1_lt_1 map eq1.
    rewrite eq1/==> //= t n.
    rewrite mem_set negb_or => [][] n_nin_nonces n_neq_n0 j j_good_size.
    rewrite 2!map_rcons -2!cats1 /= 2!oflist_cat -2!set1E 2!in_fsetU1 2!negb_or/=.
    have p1_eq_0: plength p1{h} = 0 by smt(good_size_leq plength_ge0).
    have->/= :=Hinvar n n_nin_nonces j j_good_size.
    have good_size_0 : good_size 0.
    + by have//=:=good_size_leq 0 1 _ _=> //=; have:=p1S_good_size; rewrite p1_eq_0 /=.
    have/=:=cc_concat_inj j 0 n n0{h} j_good_size _; 1: smt(cc_concat_inj good_size_leq plength_ge0).
    rewrite n_neq_n0/= => -> /=.
    by have/=:=cc_concat_inj j 1 n n0{h} j_good_size _; smt(cc_concat_inj good_size_leq plength_ge0).
  exists* k{1}, n{1}, p{1}; elim * => key nonce plain.
  call(: ={arg, URF.map} /\ arg{1} = (key, cc_concat 1 nonce) /\ 
      fdom URF.map{1} = oflist (map snd (rcons Rand.urf{2} (key, cc_concat 0 nonce))) ==>
      ={res, URF.map} /\ fdom URF.map{1} = 
        oflist (map snd (rcons (rcons Rand.urf{2} (key, cc_concat 0 nonce)) (key, cc_concat 1 nonce))))=> //=.
  + proc; inline*; sp; if; auto=> />.
    - move=> &h eq x_nin_urf y ?.
      by rewrite fdom_set map_rcons -cats1 /= set1E oflist_cat; congr.
    move=> &h eq x_in_urf.
    rewrite map_rcons -cats1 /= oflist_cat.
    rewrite fsetUC subset_fsetU_id //= => a. 
    by rewrite -set1E in_fset1 => -> //; rewrite -eq mem_fdom.
  conseq(:_==> ={URF.map} /\ y1{1} = y0{2} /\ 
      fdom URF.map{1} = oflist (map snd (rcons Rand.urf{1} (key, cc_concat 0 nonce))))=> //=.
  inline*; sp; if; auto=> />.
  - move=> &h eq Hinvar n0_nin_nonces p1S_good_size p1_lt_1 x_nin_urf y ?.
    by rewrite fdom_set map_rcons -cats1 /= set1E oflist_cat; congr; rewrite eq.
  move=> &h eq Hinvar n0_nin_nonces p1S_good_size p1_lt_1 x_in_urf.
  rewrite map_rcons -cats1 /= oflist_cat.
  rewrite eq fsetUC subset_fsetU_id //= => a. 
  by rewrite -set1E in_fset1 => -> //; rewrite mem_fdom.
exists* k{1}, n{1}, p{1}; elim * => key nonce plain.
call(: ={arg, glob URF} /\ arg{1} = (key, cc_concat (plength plain) nonce) /\ 
      fdom URF.map{1} = oflist (map snd Rand.urf{1}) ==> 
    ={res, glob URF} /\ fdom URF.map{1} = 
      oflist (map snd (rcons Rand.urf{1} (key, (cc_concat (plength plain) nonce))))).
+ proc; inline*; auto; sp; if; auto=> />.
  - move=> &l &r eq n0_nin_nonces y ?.
    by rewrite fdom_set map_rcons -cats1 oflist_cat -set1E /=; congr.
  move=> &l &r eq n0_in_urf.
  rewrite map_rcons -cats1 oflist_cat -set1E /= eq. 
  rewrite fsetUC subset_fsetU_id //= => a. 
  by rewrite in_fset1 => -> //; rewrite -eq mem_fdom n0_in_urf.
sp; auto=> /=.
conseq(:_==> ={i, c1, n0, a0, t', s, p, r, p1, glob NR, glob Wrap, glob Comp, 
      glob Rand, glob URF, glob Poly} /\ i{1} = plength p1{1} /\
      fdom URF.map{1} = oflist (map snd Rand.urf{1}) /\
      (forall apct, invar (oflist (map snd Rand.urf{1})) (NR.nonces.[n0 <- apct]){1}))=> //=.
+ move=> />.
  move=> &h urf eq Hinvar n0_nin_nonces p1S_good_size p1_ge_1 urf2 map2 eq2 Hinvar2 map3 eq3.
  rewrite eq3/= => t n .
  rewrite mem_set negb_or => [][] n_nin_nonces n_neq_n0 j j_good_size.
  rewrite map_rcons -cats1 oflist_cat -set1E /= in_fsetU1 negb_or/=. 
  have->/=:=Hinvar2 witness n _ j j_good_size; 1: by rewrite mem_set n_neq_n0 n_nin_nonces /=.
  by have/=:=cc_concat_inj j (plength p1{h}) n n0{h} j_good_size _; smt(good_size_leq plength_ge0).
move=> />.
while(={i, c1, n0, a0, t', s, p, r, p1, glob NR, glob Wrap, glob Comp, 
    glob Rand, glob Poly, glob URF} /\ 1 <= i{1} <= plength p1{1} /\
    n0{1} \notin NR.nonces{1} /\ good_size (plength p1{1} + 1) /\
    fdom URF.map{1} = oflist (map snd Rand.urf{1}) /\ k0{1} = k{2} /\
    (forall apct, invar (oflist (map snd Rand.urf{1})) NR.nonces{1}.[n0{1} <- apct])).
+ inline*; sp; if; auto=> />.
  - move=> &h urf i_ge_1 i_le_p1 n0_nin_nonces p1S_good_size eq all_invar.
    move=> i_lt_p1 {i_le_p1} x0_nin_map y ?; split; 1: smt().
    rewrite fdom_set map_rcons -cats1 oflist_cat -set1E eq/= => t n ^ HH.
    rewrite mem_set negb_or=> [][] n_nin_nonces n_neq_n0 j j_good_size.
    rewrite in_fsetU1 negb_or.
    have-> /=:=all_invar t n HH j j_good_size.
    by have:=cc_concat_inj j i{h} n n0{h} j_good_size _; smt(good_size_leq).
  move=> &h urf i_ge_1 i_le_p1 n0_nin_nonces p1S_good_size eq all_invar.
  move=> i_lt_p1 {i_le_p1} x0_nin_map; split; 1: smt().
  rewrite map_rcons -cats1 oflist_cat -set1E eq/=. 
  rewrite fsetUC subset_fsetU_id //= => a. 
  by rewrite in_fset1 => -> //; rewrite -eq mem_fdom.
inline*; sp; if; auto=> />.
+ move=> &h urf eq Hinvar n0_nin_nonces p1S_good_size p1_ge_1 x_nin_map y ?.
  rewrite fdom_set -eq.
  rewrite map_rcons -cats1 oflist_cat -set1E/=.
  split; 2: smt().
  move=> t n; rewrite mem_set negb_or=> [][] n_nin_nonces n_neq_n0 j j_good_size.
  rewrite in_fsetU1 negb_or.
  have->/=:=Hinvar n n_nin_nonces j j_good_size.
  by have:= cc_concat_inj j 0 n n0{h} j_good_size _; smt(good_size_leq).
move=> &h urf eq Hinvar n0_nin_nonces p1S_good_size p1_ge_1 x_nin_map.
rewrite map_rcons -cats1 oflist_cat -set1E/=; split; 2: smt().
rewrite eq fsetUC subset_fsetU_id //= => a.
- by rewrite in_fset1 => -> //; rewrite mem_fdom.
move=> n; rewrite mem_set negb_or -eq=> [][] n_nin_nonces n_neq_n0 j j_good_size.
by have->:=Hinvar n n_nin_nonces j j_good_size.
qed.



local equiv step_3_poly_local_to_global 
    (A <: CCA_Adv { Order, Wrap, NR, WrapForgery, Comp, URF, Rand, Poly }) :
    Game2(A_nonce_respecting(A),Poly,Random,CC_URF).game ~ 
    Game3(A_nonce_respecting(A),Poly,CC_URF).game :
    ={glob Poly, glob A} ==>
    ={glob NR, glob Wrap, glob Invar, glob Comp, glob URF, glob A, glob Poly}.
proof.
proc; sp.
inline{1} 1; inline{2} 1; sp.
inline{1} 1; inline{2} 1; sp.
inline{1} 1; inline{2} 1; sp.
inline{1} 1; inline{2} 1; sp.
rcondf{2} 1; 1: auto.
inline{1} 1; inline{2} 1; sp.
inline{1} 1; inline{2} 1; sp.
inline{1} 1; inline{2} 1; sp.
inline{1} 1; inline{2} 1; sp.
inline{1} 1; inline{2} 1; sp.
inline{2} 1; sp.
inline{2} 1; sp.
inline{2} 1; sp; sim.
swap{1} -1; sim.
replace{2} { all } by {
    Rand(CC_URF).all_enc();
    all;
  }
  (={glob NR, glob Wrap, glob Invar, glob Comp, glob URF, glob A, glob Poly} ==>
    ={glob NR, glob Wrap, glob Invar, glob Comp, glob URF, glob A, glob Poly})
  (={glob NR, glob Wrap, glob Invar, glob Comp, glob URF, glob A, glob Poly} /\
    Rand.urf{2} = []  ==>
    ={glob NR, glob Wrap, glob Invar, glob Comp, glob URF, glob A, glob Poly})
  => //=; 1: smt(); last first.
+ by sim; inline*; sp; rcondf{1} 1; auto.
symmetry; eager call(: ={glob Wrap, glob Comp, glob Rand, glob NR, glob URF, glob A, glob Poly} ==>
    ={res, glob Wrap, glob Comp, glob Rand, glob NR, glob URF, glob A, glob Poly}); auto.
eager proc(J : Rand(CC_URF).all_enc(); ~ Rand(CC_URF).all_enc(); :
    ={glob Wrap, glob Comp, glob Rand, glob NR, glob URF, glob Poly} ==>
    ={glob Wrap, glob Comp, glob Rand, glob NR, glob URF, glob Poly})
    (={glob Wrap, glob Comp, glob Rand, glob NR, glob URF, glob Poly})
  => //=; 1, 3, 5: sim.
+ by eager proc; swap{2} -4; sim.
eager proc.
swap{1} 2; swap{2} -1; sp; sim.
if{2}; last first.
+ by rcondf{1} 2; 2: sim; 1: by auto; conseq(:_==> true)=> //=.
rcondt{1} 2; 2: sim; 1: by auto; conseq(:_==> true)=> //=.
swap{2} -1; sim.
inline{1} 2; inline{2} 1.
swap{1} 1; swap{2} -2; sp; sim.
inline{1} 2; inline{2} 1.
swap{1} 3; sp; swap{2} -1; sim.
if{2}; last first.
+ by rcondf{1} 2; 2: sim; 1: by auto; conseq(:_==> true)=> //=.
rcondt{1} 2; 2: sim; 1: by auto; conseq(:_==> true)=> //=.
inline{1} 2; inline{2} 1.
swap{1} 5; sp.
swap{2} -6; sim=> />.

inline Rand(CC_URF).enc Rand(Random).enc CC_URF.enc.


qed.



local lemma step_2_poly_local_to_global 
    (A <: CCA_Adv { Order, Wrap, NR, WrapForgery, Comp, URF, Rand, Poly }) &m :
    Pr[ForgeryList(A_nonce_respecting(A),CC_URF,Poly).game() @ &m : WrapForgery.success] =
    Pr[Game1(A_nonce_respecting(A),Poly,Random,CC_URF).game() @ &m : WrapForgery.success].
proof.
rewrite (step_1_poly_local_to_global A &m).
rewrite (step_0_poly_local_to_global A &m).
have->:Pr[ForgeryList(A_nonce_respecting(A),CC_URF,Poly).game() @ &m : WrapForgery.success] =
       Pr[ForgeryList(A_nonce_respecting(A),Rand(CC_URF),Poly).game() @ &m : WrapForgery.success].
+ byequiv=> //=; proc; inline*; sim; sp.
  call(: ={glob NR, glob Wrap, glob Comp, glob Poly, glob URF}); auto.
  - by proc; inline*; sim.
  by proc; inline*; sim.


sp; inline{1} 1; inline{2} 1; sp. 
inline{1} 1; inline{2} 1; sp. 
inline{1} 1; inline{2} 1; sp. 
inline{1} 1; inline{2} 1; sp. 
inline{1} 1; inline{2} 1; sp. 
inline{1} 1; inline{2} 1; sp. 
inline{1} 1; inline{2} 1; sp. 
inline{1} 1; inline{2} 1; sp. 
inline{2} 1; sp. 
swap{2} -1; sim.
replace{1} { all } by {
    Rand(CC_URF).all_enc();
    all;
  }
  (={glob A, glob NR, glob Wrap, Comp.order_dec, glob Rand, glob URF, glob Poly, 
    WrapForgery.success} /\ Rand.urf{1} = [] ==>
    ={Comp.order_dec, glob URF, glob Poly, WrapForgery.success})
  (={glob A, glob NR, glob Wrap, Comp.order_dec, glob Rand, glob URF, glob Poly, 
    WrapForgery.success} ==>
    ={Comp.order_dec, glob URF, glob Poly, WrapForgery.success})=> //=; 1: smt().
+ by sim; inline*; sp; rcondf{2} 1; auto=> />.
eager call (: ={glob A, glob NR, glob Wrap, Comp.order_dec, glob URF, glob Poly,
      glob Rand, WrapForgery.success} ==> ={res, glob A, glob NR, glob Wrap,
      Comp.order_dec, glob URF, glob Poly, glob Rand, WrapForgery.success})=> //=.
eager proc (J : Rand(CC_URF).all_enc(); ~ Rand(CC_URF).all_enc(); :
    ={glob NR, glob Wrap, Comp.order_dec, glob URF, glob Poly, glob Rand,
      WrapForgery.success} ==> 
    ={glob NR, glob Wrap, Comp.order_dec, glob URF, glob Poly, glob Rand, 
      WrapForgery.success})
    (={glob NR, glob Wrap, Comp.order_dec, glob URF, glob Poly, glob Rand, 
      WrapForgery.success})=> //=; 1, 3, 5: sim=> />.
+ by eager proc; swap{2} -4; sim.
eager proc.
swap{1} 2; sp; if{2}; last first.
- rcondf{1} 2; 1: by auto; inline*; conseq(:_==> true); auto.
  by swap{2} -1; sim.
rcondt{1} 2; 1: by auto; inline*; conseq(:_==> true); auto.
swap{2} -2; sim.
inline{2} 1; inline{1} 2.
swap{2} -2; sim.
swap{1} 1; sp.
inline{2} 1; inline{1} 2.
swap{2} -6; sim.
swap{1} 1; sp.


qed.


local lemma URF_indist_random
  (A <: CCA_Adv { URF, Wrap, Chacha, Poly, NR }) &m :
  Pr[EncDec(Adv_Dec_None(A_nonce_respecting(A)),Composition(CC_URF,Poly)).game() @ &m : res ] =
  Pr[EncDec(Adv_Dec_None(A_nonce_respecting(A)),Composition(Random,Poly)).game() @ &m : res ].
proof. 
byequiv=> //=; proc; inline*; sp; sim.
call(: ={glob Poly, glob Wrap, glob NR} /\ invariant NR.nonces{2} URF.map{1}).
+ by proc; inline*; auto.
+ proc; inline*; sp; if; 1, 3: auto; sp.
  rcondt{1} 1; 1: by auto; smt(good_size_leq plength_ge0).
  rcondt{1} 19; 1: auto.
  - by conseq(:_==> true);auto.
  rcondt{1} 21; 1: auto.
  - by conseq(:_==> true);auto.
  rcondt{2} 16; 1: auto.
  - by conseq(:_==> true);auto.
  rcondt{2} 18; 1: auto.
  - by conseq(:_==> true);auto.
  wp=> />. 
  conseq(:_==> ={c1, t', s, glob Poly} /\
    invariant (NR.nonces.[n0 <- (a0, p1, c1, t' + s)]){2} URF.map{1})=>/>.
  call(: true); wp=> />; 1: smt().
  conseq(:_==> ={r, c1, s} /\ y2{2} = (oget URF.map{1}.[x5{1}]) /\
      forall result,
      invariant NR.nonces{2}.[n0{2} <- (a0{2}, p1{2}, cappend_last c1{2}
            (ptrunc_last p1{2} y2{2} ^+ plast_block p1{2}), result + s{2})] URF.map{1})=> />.
  rcondt{1} 10; 1: auto.
  - case: (1 < plength p1); last first.
    + rcondf 6; auto=> />. 
      move=> &h Hinv Hnin_nonces Hgood_size Hi y ?.
      rewrite mem_set negb_or.
      have//=H1:=good_size_leq 1 _ _ Hgood_size; 1:smt(plength_ge0).
      rewrite (Hinv n0{m0} Hnin_nonces 1 _)//=.
      have/=->//:=cc_concat_neq_i 1 0 n0{m0}.
      by have//=->//:=good_size_leq 0 1.
    conseq(:_==> cc_concat (plength p1) n0 \notin URF.map /\ i = plength p1)=>/>.
    while(cc_concat (plength p1) n0 \notin URF.map /\ good_size (plength p1) /\ 
              0 <= i <= plength p1).
    + sp; if; auto=> />.
      - move=> &h Hnin_map Hgoodsize Hi0 ? Hisize Hnini y ?.
        rewrite mem_set Hnin_map /=.
        by have->/=:=cc_concat_neq_i (plength p1{h}) i{h} n0{h} _ _ _; smt(good_size_leq).
      smt().
    auto=> /> &h Hinv Hnin_nonce Hgood_size Hgt1 y ?; split; 2: smt().
    split; 2: smt(good_size_leq).
    rewrite mem_set negb_or.
    smt(cc_concat_neq_i good_size_leq plength_ge0).
  auto=> /=.
  conseq(:_==> ={r, c1, s} /\ forall result y,
      invariant NR.nonces{2}.[n0{2} <-
        (a0{2}, p1{2}, cappend_last c1{2} (ptrunc_last p1{2} y ^+ plast_block p1{2}),
          result + s{2})] URF.map{1}.[cc_concat i{1} n0{1} <- y]).
  - smt(get_setE).
  alias {1} 1 urf = URF.map; sp.
  conseq(:_==> ={r, c1, s} /\ good_size i{1} /\
      invariant NR.nonces{2} urf{1} /\ n0{2} \notin NR.nonces{2} /\
      (forall nonce j, good_size j => cc_concat j nonce \in URF.map{1} => 
        cc_concat j nonce \in urf{1} \/ (0 <= j < i{1} /\ nonce = n0{1})) /\
      (forall nonce j, cc_concat j nonce \in urf{1} => 
        urf{1}.[cc_concat j nonce] = URF.map{1}.[cc_concat j nonce]) /\
      (forall j, 0 <= j < i{1} => cc_concat j n0{1} \in URF.map{1})).
  + move=> /> &l &r Hinv n0_nin_nonces pS_good_size 3? i_good_size H1 H2 H3 2?.
    rewrite mem_set negb_or/= => [#] n_nin_nonces n_neq_n0 j j_good_size.
    rewrite mem_set negb_or.
    split; 2: smt(domE cc_concat_neq_nonce).
    by have:=Hinv n n_nin_nonces j j_good_size; smt(). 
  case: (1 < plength p1{1}); last first.
  - rcondf{2} 5; 1: auto.
    rcondf{1} 6; auto=> />.
    move=> &l &r Hinv n0_nin_nonces pS_good_size p1_leq1 y h{h}.
    rewrite get_setE/= oget_some/=.
    have good_size_1//=:good_size 1 by smt(good_size_leq plength_ge0).
    by rewrite good_size_1/=; do!split; smt(mem_set cc_concat_inj good_size_leq get_setE).
  while(={i, p1, k, n0, c1} /\ 1 <= i{1} <= plength p1{1} /\ 
        good_size (plength p1{1} + 1) /\ n0{1} \notin NR.nonces{2} /\
        invariant NR.nonces{2} urf{1} /\
      (forall nonce j, good_size j => cc_concat j nonce \in URF.map{1} => 
        cc_concat j nonce \in urf{1} \/ (0 <= j < i{1} /\ nonce = n0{1})) /\
      (forall nonce j, cc_concat j nonce \in urf{1} => 
        urf{1}.[cc_concat j nonce] = URF.map{1}.[cc_concat j nonce]) /\
      (forall j, 0 <= j < i{1} => cc_concat j n0{1} \in URF.map{1})).
  - sp; rcondt{1} 1; auto=> />.
    + smt(good_size_leq).
    smt(get_setE mem_set cc_concat_neq_i cc_concat_neq_nonce good_size_leq domE cc_concat_inj).
  auto=> /> &l &r hinv n0_nin_nonces pS_good_size p_gt_1 y h{h}; do!split.
  - smt().
  - smt(mem_set cc_concat_inj good_size_leq get_setE).
  - smt(mem_set cc_concat_inj good_size_leq get_setE).
  - smt(mem_set cc_concat_inj good_size_leq get_setE).
  move=> map j i_ge1 h{h} i_leq_p j_leq_p H1 H2 H3.
  by rewrite get_setE/=oget_some/=; smt(good_size_leq).
by auto; smt(mem_empty).
qed.



local lemma poly_local_to_global
    (A <: CCA_Adv { Order, Wrap, NR, WrapForgery, Comp, URF, Rand, Poly }) &m :
    Pr[TestListPoly(OutputDecOrder(A_nonce_respecting(A),IdealSKE),Poly).game() @ &m : TestPoly.forgery] =
    Pr[ForgeryList(A_nonce_respecting(A),CC_URF,Poly).game() @ &m : WrapForgery.success].
proof.

byequiv=> //=; proc; sp.
inline{1} 1.
sim.
(** HOW TO DO :

*** do an accumlator of all the calls to URF, then switch to Random,
*** then get a while loop before the one about poly, then finally use
*** PROM to pospone those URF sampling to remove them at the end *)


qed.



local lemma step_5_chacha_poly_to_URF_and_forge
    (A <: CCA_Adv { URF, Wrap, Chacha, Poly, NR, WrapForgery, NR, Compo, Comp, EG.RO, EG.FRO }) &m :
  islossless Poly.mac => islossless Chacha.enc =>
  (forall (C <: CCA_SKE{A}), islossless C.dec => islossless C.enc => islossless A(C).guess) =>
  (equiv [ Swap_Poly(Poly).double_mac ~ Swap_Poly(Poly).double_reverse_mac :
      ={arg, glob Poly} ==> ={res, glob Poly} ]) =>
  `| Pr[EncDec(A_nonce_respecting(A), Composition(Chacha,Poly) ).game() @ &m : res]
   - Pr[EncDec(A_nonce_respecting(A), IdealSKE                 ).game() @ &m : res] |

    <= Pr[TestListPoly(OutputDecOrder(A_nonce_respecting(A),CC_URF),Poly).game() @ &m : TestPoly.forgery]

       + `| Pr[IndistCC(CCA_to_CC_indist(Poly,A_nonce_respecting(A)), Chacha ).game() @ &m : res]
          - Pr[IndistCC(CCA_to_CC_indist(Poly,A_nonce_respecting(A)), CC_URF ).game() @ &m : res] |.
proof.
move=> Poly_ll CC_ll A_ll swap_poly.
