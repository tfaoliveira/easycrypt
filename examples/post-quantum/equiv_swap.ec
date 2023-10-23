require import AllCore.

module M = { 
  quantum var q_ : int
  var n, m : int

  proc c(x : int) = { n <- x; return x + 1;} 

  proc qu(x : int) { q r: int} = { 
    q_ <- 0;
    q_, q <* U[(q_, q + q_)];
    r <- 0;
    n <- x;
    return x + 1;
  } 

}.

import var M.

equiv e1 : M.qu ~ M.qu : true ==> true.
proof.
  proc.
  swap{1} 3 -2.
  swap{1} 1 2.
(* Fail *)
(*   swap{1}2 -1.  *)
  admit.
qed.
