require import AllCore Int StdOrder.
import IntOrder.

module MAIN = {
  proc id_while (n : int) : int = {
    var i;
    i <- 0;
    while (i < n) {
      i <- i + 1;
    }
    return i;
  }
}.

lemma id_while_free m :
  hoare [MAIN.nth_odd : m = 0 ==> m = 0].
proof.
  proc; sp.
  while ((0 <= i <= n) /\ (x = 2 * i + 1)).
  + by auto => /> /#.
  by auto => /> /#.
qed.

lemma nth_odd_spec_for m :
  hoare [MAIN.nth_odd : (n = m) /\ (0 <= n) ==> res = (2 * m + 1)].
proof.
  proc.
  for (fun i => (x = 2 * i + 1)) => /=.
  + by auto => /> /#.
  by auto => /> /#.
qed.
