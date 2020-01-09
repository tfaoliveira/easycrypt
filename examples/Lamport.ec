require import AllCore Distr DBool DInterval List.
from Jasmin require import JArray.
require (*  *) PlugAndPray.

abstract theory EUF_onetime.

type Sk.
type Pk.
type Sig.
type Msg.

module type Scheme = {
  proc keyGen () : Pk * Sk
  proc sign (m:Msg, sk:Sk) : Sig
  proc verify (m:Msg, sig:Sig, pk:Pk) : bool
}.

module type Forger = {
  proc choose(pk : Pk) : Msg
  proc forge(sig : Sig) : Msg * Sig
}.

module EUF(S:Scheme, F :Forger) ={
  proc main(): bool ={
    var sk:Sk;
    var pk:Pk;
    var msg,msg' : Msg;
    var sig,sig' : Sig;
    var valid : bool;

    (pk,sk)     <@ S.keyGen();
    msg         <@ F.choose(pk);
    sig         <@ S.sign(msg,sk);
    (msg',sig') <@ F.forge(sig);
    valid       <@ S.verify(msg',sig',pk);    
    return (msg <> msg' /\ valid);
  }
}.

end EUF_onetime.

type D.
type R.
type Sk = D * D.
type Pk = R * R.

type Sig = D.
type Msg = bool.
 
op H : D -> R.

op challenge : D distr.
axiom chal_ll : is_lossless challenge.
hint exact : chal_ll.

(* One wayness for H *)

module type Inverter = {
  proc invert(y : R) : D
}.

module OW(I :Inverter) ={
  proc main(): bool ={
    var x,x':D;
    var y : R;

    x       <$ challenge;
    y       <- H x;
    x'      <- I.invert(y);
    return (H x = H x');
  }
}.

(* One-Time Existential UF *)

clone import EUF_onetime as EUF1 with 
    type Sk  <- Sk,
    type Pk  <- Pk,
    type Sig <- Sig,
    type Msg <- Msg.

module Lamport : EUF1.Scheme = {

   proc keyGen() : Pk * Sk = {
      var sk0,sk1;
      sk0 <$ challenge;
      sk1 <$ challenge;
      return ((H sk0, H sk1), (sk0,sk1));
   }

   proc sign(m : Msg, sk : Sk) : Sig = {
      var sk0, sk1, sig;
      (sk0,sk1) <- sk;
      sig <- if m
             then sk1
             else sk0;
      return sig;
   }

   proc verify(m : Msg, sig : Sig, pk : Pk) : bool = {
      var pk0, pk1;
      (pk0,pk1) <- pk;
      return H sig = if m 
                     then pk1
                     else pk0; 
   }

}.

(* Reduction *)

module I(F : Forger) : Inverter = {

 proc invert(y : R) : D = {
    var sk:Sk;
    var pk:Pk;
    var b;
    var msg,msg' : Msg;
    var sig,sig' : Sig;

    (pk,sk)     <@ Lamport.keyGen();
    b           <$ {0,1};
    pk <- if b 
         then (fst pk, y)
         else (y, snd pk);
    msg         <@ F.choose(pk);
    sig         <@ Lamport.sign(msg,sk);
    (msg',sig') <@ F.forge(sig);
    return sig';
  }
}.

(* We modify the security game so that it
   has the same probability space as the
   inverter. *)

section PROOFS.

  declare module F: Forger.
  axiom forge_ll : islossless F.forge.

  local module EUF_guess ={
    var correct_guess : bool
    var msg : bool
  
    proc isolate() = {
      var sk:Sk;
      var pk:Pk;
      var msg' : Msg;
      var sig,sig' : Sig;
      var valid : bool;
  
      (pk,sk)     <@ Lamport.keyGen();
      msg         <@ F.choose(pk);
      sig         <@ Lamport.sign(msg,sk);
      (msg',sig') <@ F.forge(sig);
      valid       <@ Lamport.verify(msg',sig',pk);    
      return (msg <> msg' /\ valid);
    }

    proc main(): bool = {
      var r, b;
      r <@ isolate();
      b  <$ {0,1};
      correct_guess <- msg <> b;
      return r;
    }
  }.

  local lemma same_prob &mem :
    Pr [ EUF_guess.main() @ &mem : res ] =
    Pr [ EUF(Lamport, F).main()  @ &mem : res].
  proof.
    byequiv => />; proc.
    inline EUF_guess.isolate.
    wp; rnd {1}; wp.
    by sim : (={msg',valid} /\ EUF_guess.msg{1} = msg{2}).
  qed.

  local lemma lower_prob &mem :
     Pr [ EUF_guess.main() @ &mem : res /\ EUF_guess.correct_guess ] <=
      Pr [ OW(I(F)).main()  @ &mem : res ]. 
  proof.
    byequiv => />.
    proc.
    inline EUF_guess.isolate I(F).invert Lamport.verify.
    swap {1} 11 -10; swap {2} 5 -4.
    seq 1 1 : (={b, glob F}); 1: by sim.
    seq 1 5 : 
       (#pre /\ ={pk} /\ 
           (if b{1} then sk.`1{1} = sk.`1{2} else sk.`2{1} = sk.`2{2}) /\ 
           (if b{1} then pk{2}.`2 else pk{2}.`1) = H x{2}).
    + inline *; wp.
      case (b{1}).
      + by rnd{2}; swap {1} 2 -1; auto; smt(chal_ll).
      by swap {2} 5 -1; rnd{2}; auto; smt (chal_ll).
    wp; seq 1 1 : (#pre /\ EUF_guess.msg{1} = msg{2}); 1: by sim />.
    case (EUF_guess.msg{1} <> b{1}).
    (* correct guess*)
    + by inline *; call (_:true); auto => />; smt().
    (* incorrect guess *)
    conseq (:true) => />.
    by call{1} forge_ll; call{2} forge_ll; inline*; auto.
  qed.

  (* 1/2 loss *)

  local lemma prob_loss &mem :
     Pr [ EUF_guess.main() @ &mem : res /\ EUF_guess.correct_guess ]
       = 1%r / 2%r * Pr [ EUF_guess.main() @ &mem : res ].
  proof.
    byphoare (_: (glob F) = (glob F){mem} ==> res /\ EUF_guess.correct_guess) => //.
    proc; wp.
    seq 1 : r (Pr[EUF_guess.main() @ &mem : res]) (1%r/2%r) _ 0%r => //.
    + call (_: (glob F) = (glob F){mem}   ==> res).
      bypr => &m _.
      byequiv => //.
      proc; inline EUF_guess.isolate; wp; rnd{2}; wp. 
      by sim : (={EUF_guess.msg,msg',valid}).
    + by auto.
    + rnd (fun b => EUF_guess.msg <> b); auto => /> ??; smt(dboolE).
    by conseq (_ : _ ==> false) => />.
  qed.

  (* Theorem statement *)

  lemma lamport_euf &mem :
    Pr [ EUF(Lamport, F).main() @ &mem : res ] <= 2%r *  Pr [ OW(I(F)).main()  @ &mem : res].
  proof.
    rewrite -(same_prob &mem).
    have := prob_loss &mem; have := lower_prob &mem; smt().
  qed.

end section PROOFS.

(* Lamport for messages of size [size] *)

op n : {int | 0 < n } as gt0_n.

clone import PolyArray as Array with 
  op size <- n
  proof ge0_size by smt (gt0_n).

type Sk_n = D Array.t * D Array.t.
type Pk_n = R Array.t * R Array.t.

type Sig_n = D Array.t. 
type Msg_n = bool Array.t. 

clone import EUF_onetime as EUFn with 
    type Pk  <- Pk_n,
    type Sk  <- Sk_n,
    type Sig <- Sig_n,
    type Msg <- Msg_n.

module Lamport_n : EUFn.Scheme = {

   proc keyGen() : Pk_n * Sk_n = {
      var sk0, sk1;
      var i;
      i = 0;
      sk0 <- witness;
      sk1 <- witness;
      while (i < n) {
        sk0.[i] <$ challenge;
        sk1.[i] <$ challenge;
        i <- i + 1;
      }
      return ((Array.map H sk0, Array.map H sk1), (sk0,sk1));
   }

   proc sign(m : Msg_n, sk : Sk_n) : Sig_n = {
      var sk0, sk1, sig;
      (sk0,sk1) <- sk;
      sig <- Array.init (fun i => if m.[i] then sk1.[i] else sk0.[i]);
      return sig;
   }

   proc verify(m : Msg_n, sig : Sig_n, pk : Pk_n) : bool = {
      var pk0, pk1;
      (pk0,pk1) <- pk;
      return Array.map H sig = Array.init (fun i => if m.[i] then pk1.[i] else pk0.[i]);
   }

}.

module EUFn_1 (F:EUFn.Forger) : EUF1.Forger = {

  var k : int
  var sk : Sk_n
  var m : Msg_n

  proc choose(pk : Pk) : Msg = {
    var i, sk0, sk1, pk0, pk1;
    k <$ [0..n -1];
    i = 0;
    sk0 <- witness;
    sk1 <- witness;
    while (i < n) {
      if (i <> k) {
        sk0.[i] <$ challenge;
        sk1.[i] <$ challenge;
      }
      i <- i + 1;
    }
    sk <- (sk0, sk1);
    pk0 <- Array.init (fun i => if i = k then pk.`1 else H sk0.[i]);
    pk1 <- Array.init (fun i => if i = k then pk.`2 else H sk1.[i]);
    m <@ F.choose((pk0,pk1));
    return m.[k];  
  }
 
  proc forge(sig:Sig) : Msg * Sig = {
    var sk0, sk1, sign, sign';
    (sk0,sk1) <- sk;
    sign <- Array.init (fun i => if i = k then sig
                                else  if m.[i] then sk1.[i] else sk0.[i]);
    (m,sign') <@ F.forge(sign);
    return (m.[k], sign'.[k]);
  }

}.
    
section PROOFS_n.

  declare module F: EUFn.Forger {EUFn_1}.
  axiom forge_ll : islossless F.forge.

  local clone import PlugAndPray as PlugAndPray0 with 
    type tval <- int,
    op indices = range 0 n,
    type tin <- unit,
    type tres <- bool
    proof *.
  realize indices_not_nil.
  proof. smt (range_ltn gt0_n). qed.

  local module G:Game = {

    var msg  : Msg_n
    var msg' : Msg_n

    proc main(): bool ={
      var sk:Sk_n;
      var pk:Pk_n;
      var sig,sig' : Sig_n;
      var valid : bool;
    
      (pk,sk)     <@ Lamport_n.keyGen();
      msg         <@ F.choose(pk);
      sig         <@ Lamport_n.sign(msg,sk);
      (msg',sig') <@ F.forge(sig);
      valid       <@ Lamport_n.verify(msg',sig',pk);    
      return (msg <> msg' /\ valid);
    }

  }.

  op diff_msg (msg msg':Msg_n) = 
    List.find (fun i => msg.[i] <> msg'.[i]) (range 0 n).

  lemma card_n : card = n.
  proof. rewrite undup_id 1:range_uniq size_range; smt(gt0_n). qed.

  lemma diff_msg_has (msg msg':Msg_n) : 
    msg' <> msg =>
    has (fun (i : int) => msg'.[i] <> msg.[i]) (range 0 n).
  proof.
    rewrite hasP => hn.
    case : (exists (x : int), (x \in range 0 n) /\ (fun (i : int) => msg'.[i] <> msg.[i]) x) => //.
    rewrite negb_exists => h; apply hn.
    apply Array.tP => i /mem_range hi.
    by have := h i; rewrite /= hi. 
  qed.

  lemma diff_msg_bound msg msg' :
    msg' <> msg =>
    0 <= diff_msg msg' msg < n.
  proof.
    rewrite /diff_msg => hn.
    have {3}<-: size (range 0 n) = n.
    + by rewrite size_range; smt(gt0_n).
    by rewrite find_ge0 -has_find diff_msg_has. 
  qed.

  lemma diff_msg_in msg msg' :  
    msg' <> msg => diff_msg msg' msg \in indices.
  proof. by move=> hn; rewrite mem_range diff_msg_bound. qed.
 
  lemma diff_msg_neq msg msg' :  
    msg' <> msg => msg'.[diff_msg msg' msg] <> msg.[diff_msg msg' msg].
  proof.
    rewrite /diff_msg => hn. 
    have /= := nth_find witness (fun i => msg'.[i] <> msg.[i]) (range 0 n) _.
    + by apply diff_msg_has.
    by rewrite nth_range //=; apply diff_msg_bound. 
  qed.
 
  local lemma guess_euf1 &mem :
    let psi = fun (g:glob G) (b:bool) =>
      let (msg', msg, gF) = g in
      diff_msg msg msg' in
    let phi = fun (g:glob G) (b:bool) =>
      let (msg', msg, gF) = g in
      msg <> msg' /\ b in
    Pr[Guess(G).main() @ &mem : phi (glob G) res.`2 /\ res.`1 = psi (glob G) res.`2] <= 
    Pr[EUF1.EUF(Lamport, EUFn_1(F)).main () @ &mem : res].
  proof.
    move=> /=.
    byequiv => //;proc.
    inline G.main EUFn_1(F).forge  EUFn_1(F).choose.
    swap{1} 8 -7; swap{2} 3 -2.
    seq 3 10 : (={glob F} /\ pk{1} = (pk00, pk1){2} /\ i{1} = EUFn_1.k{2} /\
                 pk00{2}.[i{1}] = pk{2}.`1 /\
                 pk1{2}.[i{1}] = pk{2}.`2 /\
                 sk{2} = (sk.`1.[i], sk.`2.[i]){1} /\
                 (forall j, 0 <= j < n => j <> i{1} => sk.`1{1}.[j] = EUFn_1.sk{2}.`1.[j] /\
                                                       sk.`2{1}.[j] = EUFn_1.sk{2}.`2.[j])).
    + inline Lamport_n.keyGen.
      swap{2} 3 3; wp; swap{2} 2 1.
      splitwhile{1} 6 : (i0 < i).
      splitwhile{2} 7 : (i < EUFn_1.k).
      swap{2} 3 2. swap{2} [5..6] 1.
      seq 6 5 : (={glob F, sk0, sk1} /\ i0{1} = i{2} /\ i{1} = EUFn_1.k{2} /\ i{2} = i{1} /\ 0 <= i{1} < n).
      + while (={sk0, sk1} /\ i0{1} = i{2} /\ i{2} <= i{1} /\ i{1} = EUFn_1.k{2}).
        + by rcondt{2} ^if; auto => />; smt(). 
        by auto => />; smt (supp_dinter).
      rcondt{1} ^while; 1: by auto;smt().
      rcondt{2} ^while; 1: by auto; conseq (:true) => />; auto.
      rcondf{2} ^if; 1: by auto; conseq(:true) => />; auto.
      inline{2} Lamport.keyGen; swap{2} [3..4] 2; wp.
      while ((sk0.[i], sk1.[i]){1} = (sk01,sk11){2} /\ 0 <= i{2} /\ 
             i0{1} = i{2} /\ i{1} < i{2} <= n /\ i{1} = EUFn_1.k{2} /\
             (forall j, 0 <= j < i{2} => j <> i{1} => sk0{1}.[j] = sk0{2}.[j] /\
                                                      sk1{1}.[j] = sk1{2}.[j])).
      + by rcondt{2} ^if; auto; smt (Array.get_setE).
      by auto; smt (Array.get_setE Array.mapE Array.tP Array.initiE).
    move=> /=; inline *; wp.
    call (:true); wp; call(:true); skip => /> &1 &2 h1 h2 h ?; split.
    + by apply Array.tP => *;smt (Array.initiE).
    move=> heqi rL rR Fl Fr /> hn heq.
    rewrite (diff_msg_neq _ _ hn) /=.
    have <- := Array.mapiE H rR.`2 (diff_msg result_R rR.`1).
    + by apply diff_msg_bound.
    by rewrite heq  Array.initiE 1:diff_msg_bound //= h1 h2.
  qed.

  lemma lamport_n_euf &mem :
    Pr[EUFn.EUF(Lamport_n,F).main() @ &mem : res] <= 
      2%r * n%r * Pr[OW(I(EUFn_1(F))).main() @ &mem : res].
  proof.
    pose psi (g:glob G) (b:bool) :=
      let (msg', msg, gF) = g in
      diff_msg msg msg'. 
    pose phi (g:glob G) (b:bool) := 
      let (msg', msg, gF) = g in
      msg <> msg' /\ b.
    have -> : Pr[EUFn.EUF(Lamport_n,F).main() @ &mem : res] = 
              Pr[G.main() @ &mem : phi (glob G) res].
    + byequiv => //;proc.
      sim : (msg{1} = G.msg{2} /\ msg'{1} = G.msg'{2} /\ ={valid}) => />.
    have -> := PBound_mult G phi psi () &mem.
    + by rewrite /psi => -[msg msg' F] o [] /= hn ho; apply diff_msg_in.
    rewrite card_n.
    have /= := (guess_euf1 &mem).
    have := lamport_euf (EUFn_1(F)) _ &mem.
    + by islossless; apply forge_ll.
    have : 0%r < n%r; smt(gt0_n).   
  qed.

end section PROOFS_n.