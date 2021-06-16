require import AllCore List Distr DBool DInterval.
require (*--*) Oracle_PKE.


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

axiom encK (k : keyseed) (m : plaintext) (e : encseed) : 
  dec (enc(m,pkgen k,e),skgen k) = Some m.

module type ICCA = {
  proc init() : unit 
  proc enc (_ : plaintext) : ciphertext
  proc dec (_ : ciphertext)  : plaintext option
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
    c <- enc(witness,pk,e);
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

module type Adv (G : ICCA) = {
  proc main () : bool
}.

module Game (O : ICCA, A : Adv) = {
  
  proc main() = {
    var r;
    
    O.init();
    r <@ A(O).main();
    return r;
  }
}.

equiv Real_Real' (A <: Adv {Real, Real'}) : 
  Game(Real,A).main ~ Game(Real',A).main : true ==> ={res}.
