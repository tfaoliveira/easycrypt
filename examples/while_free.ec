require import AllCore Int StdOrder.
import IntOrder.

module MAIN = {
  proc id_while (n : int) : int = {
    var i, one;
    i <- 0;
    one <- 1;
    while (i < n) {
      i <- i + one;
    }
    return i;
  }
}.

lemma double_while_double m :
  hoare [MAIN.id_while : (m = n) /\ (0 <= n) ==> res = m].
proof.
  proc; sp.
  while(i <= n).
  + by sp; skip => /> /#.
  by skip => /> /#.
qed.
