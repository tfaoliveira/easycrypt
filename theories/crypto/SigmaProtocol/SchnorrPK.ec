(* --------------------------------------------------------------------
 * Copyright (c) - 2016--2017 - Roberto Metere (r.metere2@ncl.ac.uk)
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(*
 * A formal verification of the Schnorr proof of knowledge
 *)
require import Int.
require import Real.
require import Distr.
require import CyclicGroup.

require (*--*) SigmaProtocol.

(* Schnorr protocol types *)
type statement    = group.
type witness      = F.t.
type message      = group.
type challenge    = F.t.
type response     = F.t.

op R (h:statement) (w:witness) = h = g^w.
op challenges = FDistr.dt.

op verify (h: statement) (a: message) (e: challenge) (z: response) : bool = 
  a * h^e = g^z.

(* Instantiate the Sigma scheme with the above types *)
clone include SigmaProtocol.SP with
  type statement  <- statement,
  type witness    <- witness,
  type message    <- message,
  type challenge  <- challenge,
  type response   <- response,
  op   R          <- R,
  op   challenges <- challenges,
  op   verify     <- verify
  proof *.

module P : Prover = {
  proc gen () : statement * witness = {
    var w;
    w <$ challenges; 
    return (g^w, w);
  }

  var w_ : witness
  var r  : F.t
  
  proc init (x:statement, w:witness) : message = {
    w_ <- w;
    r  <$ challenges;
    return g^r;
  }

  proc respond (e: challenge) : response = {
    return r + e * w_;
  }
}.

module KE: KnowledgeExtractor = {
  proc extract(x: statement, a: message, e: challenge, z: response, e': challenge, z': response) : witness = {
    return  (z - z') / (e - e');
  }
}.

module S:Simulator = { 
  proc simulate(x: statement, e: challenge) : message * response = {
    var z;
    z  <$ FDistr.dt;
    return (g^z * x^(-e), z);
  }
}.

lemma Completeness : 
  phoare [Completeness(P).main : R x w ==> res] = 1%r.
proof.
  proc;inline * => /=.
  conseq (: true ==> true) (: R x w ==> verify x a e z) => //; last by islossless.
  by auto;rewrite /verify /R => /> *;algebra.
qed.

lemma SpecialSoundness :
  phoare [SpecialSoundness(KE).main : verify x a e z /\ verify x a e' z' /\ e <> e' ==> res] =  1%r.
proof.
  proc; inline *; auto; rewrite /verify /R => /> &m.
  rewrite !(log_bij, log_g, log_pow, log_mul) => h1 h2 he.
  by field h1 h2; apply /negP => h; apply he; ring h.
qed.

lemma sHVZK : 
  equiv [RealP(P).main ~ S.simulate : (R x w) {1} /\ ={x,e} ==> ={res}].
proof.
  proc; inline *; wp.
  rnd (fun r => r + log x{2} * e{2}) (fun r => r + log x{2} * -e{2}) .
  auto; rewrite /R => /> &1 &2; split; 1: by move=> *;ring.
  move=> h r hr;split => [ | _];2:split; algebra.
qed.

