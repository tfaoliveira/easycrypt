require import AllCore Int StdOrder.
import IntOrder.

module MAIN = {
  proc nth_odd (n : int) : int = {
    var x, i;
    x <- 1;
    i <- 0;
    while (i < n) {
      x <- x + 2;
      i <- i + 1;
    }
    return x;
  }
}.

lemma nth_odd_spec_while m :
  hoare [MAIN.nth_odd : (n = m) /\ (0 <= n) ==> res = (2 * m + 1)].
proof.
  proc.
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
