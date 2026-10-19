(* [eval proc] and [check proc] run concrete procedures. *)
require import AllCore List IntDiv DBool.

module M = {
  var count : int

  proc fib(n : int) : int = {
    var a, b, t, i;

    a <- 0; b <- 1; i <- 0;
    while (i < n) {
      t <- a + b; a <- b; b <- t; i <- i + 1;
    }
    return a;
  }

  proc collatz(n : int) : int = {
    count <- 0;
    while (n <> 1) {
      if (n %% 2 = 0) { n <- n %/ 2; } else { n <- 3 * n + 1; }
      count <- count + 1;
    }
    return count;
  }

  proc twice(n : int) : int * int = {
    var x, y;

    x <@ fib(n);
    y <@ collatz(n);
    return (x, y);
  }

  proc nop() : unit = { }

  proc tick() : int = {
    count <- count + 1;
    return count;
  }

  proc flip() : bool = {
    var b;
    b <$ {0,1};
    return b;
  }
}.

module N = M.

check proc M.fib(10) = 55.
check proc M.fib(90) = 2880067194370816120.
check proc M.collatz(27) = 111.
check proc M.twice(27) = (196418, 111).
check proc N.fib(5) = 5.
eval proc M.nop().
check proc M.collatz(1) = 0.

fail check proc M.fib(10) = 56.
fail check proc M.tick() = 1.
fail eval proc M.flip().
