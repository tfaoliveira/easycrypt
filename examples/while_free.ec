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

lemma id_while_free m :
  hoare [MAIN.id_while : (n = m) /\ (0 <= n) ==> res = m].
proof.
  proc.
  sp.
  while(i <= n).
  + by sp; skip => /> /#.
  by skip => /> /#.
qed.
