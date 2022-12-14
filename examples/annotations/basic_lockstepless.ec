module M = {
  var x, y : int

  proc foo() = {
    @L1foo;
    y <- 4 * x;
    @L2foo;
  }

  proc bar() = {
    @L2bar;
    x <- y %/ 4;
    @L1bar;
  }
}.

(*Relational assertions do not have to be in lockstep, and label names can differ.*)
equiv [M.f ~ M.g : 4 %| y{2} ==> true |
       { (L1foo, L1bar) --> ={x} } ==> { (L2foo, L2bar) --> ={y} }].
proof.
admitted.
