module M = {
  var x, y : int

  proc foo() = {
    x <- 0;
    @L;
    y <- 1;
  }

  proc bar() = {
    x <- y;
    @L;
    y <- x + 1;
  }
}

(*After the usual equiv, we add the list of assumptions and the list of assertions.*)
equiv [M.f ~ M.g : y{2} = 0 ==> ={x, y} |
       {} ==> { (L, L) --> ={x, y} }].
proof.
admitted.
