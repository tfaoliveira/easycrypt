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
