module M = {
  var i, n, x : int

  proc foo() = {
    i = 0;
    while (i < n) {
      @L;
      x += i;
      i += 1;
    }
  }

  proc bar() = {
    i = 0;
    while (i < 10) {
      @L;
      x -= i;
      i += 1;
    }
  }
}

(*Relational assertions can be used in lockstep.*)
equiv [M.f ~ M.g : n{1} = 10 /\ x{1} + x{2} = 42 ==> x{1} + x{2} = 42 |
       {} ==> { (L, L) --> ={i} => x{1} + x{2} = 42 }].
proof.
admitted.
