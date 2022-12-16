require import AllCore.

module M = {
  var x, y : int

  proc foo() = {
    x <- 0;
    @l;
    y <- 1;
  }

  proc bar() = {
    x <- y;
    @l;
    y <- x + 1;
  }
}.

(*After the usual equiv, we add the list of assumptions and the list of assertions.*)
lemma foobar : equiv[M.foo ~ M.bar : true ==> true | { } ==> { (l, l --> true) , (l, l --> true) } ].
proof.
admitted.

(*
equiv [M.f ~ M.g : y{2} = 0 ==> x{1} = x{2} |
       {} ==> { (l, l) --> ={x, y} }].
proof.
admitted.
*)
