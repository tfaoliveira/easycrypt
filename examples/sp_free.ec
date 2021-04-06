require import AllCore Int StdOrder.
import IntOrder.

module MAIN = {
  proc incr (n : int) : int = {
    n <- n + 1;
    return n;
  }
  proc id_while (n : int) : int = {
    var i;
    i <- 0;
    while (i < n) {
      i <- i + 1;
    }
    return i;
  }
  proc id_call (n : int) : int = {
    var i;
    i <- id_while(n);
    return i;
  }
}.

lemma incr_free m :
  hoare [MAIN.incr : n = m ==> res = m + 1].
proof. by proc; sp; skip. qed.

lemma id_while_free m :
  hoare [MAIN.id_while : m = 0 ==> m = 0].
proof. by proc; sp; skip. qed.

lemma id_call_free m :
  hoare [MAIN.id_call : m = 0 ==> m = 0].
proof. by proc; sp; skip. qed.
