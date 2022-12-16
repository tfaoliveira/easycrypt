require import AllCore List.

module Mmatch = {
  var l : int list
  var x : int
  proc foo() = {
    match l with | [] => x <- 0; | h :: t => x <- h end;
  }
}.

module M1 = {
  var x : int

  proc foo() = {
    x <- 0;
  }
}.

module M2 = {
  proc foo() = {
    var x : int;
    x <- 0;
  }
}.

module M3 = {
  proc foo() = {
    x <- 0;
    var x : int;
  }
}.

module ML1 = {
  var x : int

  proc foo() = {
    @L;
  }
}.

module ML2 = {
  proc foo() = {
    var x : int;
    @L;
  }
}.

module ML3 = {
  proc foo() = {
    @L;
    var x : int;
  }
}.
