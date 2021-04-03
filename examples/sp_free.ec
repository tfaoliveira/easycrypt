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
  proc id_call (n : int) : int = {
    var i;
    i <- id_while(n);
    return i;
  }
}.

lemma id_while_free m :
  hoare [MAIN.id_while : m = 0 ==> m = 0].
proof. by proc; sp; skip. qed.

lemma id_call_free m :
  hoare [MAIN.id_call : m = 0 ==> m = 0].
proof. by proc; sp; skip. qed.

module FALSE = {
  proc incr (n : int) : unit = {
    n <- n + 1;
    return ();
  }
  proc incr_call (n : int) : int = {
    incr(n);
    return n;
  }
  proc infinite () : unit = {
    while(true) {}
    return ();
  }
}.

(*Interesting, does s_write unfold function calls?*)
lemma incr_call_free m :
  hoare [FALSE.incr_call : n = m ==> res = m].
proof. proc. sp. abort.

(*This is really bad.*)
lemma islossless_infinite_free :
  islossless FALSE.infinite.
proof. by proc; sp; skip. qed.
