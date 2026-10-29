(* A closure built by an expression sees the program variables as they
   were when the expression was evaluated, not as they are when the
   closure is applied. *)
require import AllCore.

module M = {
  var g : int

  proc locals() : int = {
    var x, f;
    x <- 1;
    f <- fun (i : int) => x + i;
    x <- 5;
    return f 0;
  }

  proc globals() : int = {
    var f;
    g <- 1;
    f <- fun (i : int) => g + i;
    g <- 5;
    return f 0 + g;
  }
}.

check proc M.locals() = 1.
check proc M.globals() = 6.
