require import AllCore Int.


type t.


op b_low : t -> bool.
op b     : bool -> bool.


module M = {
  var low : t
  var k, n, h, l : int

  proc while_() : unit = {
    while (b_low low) {
      k <- 2 ^ (n - 1);
      @l;
      if (b (k < h)) {
        h <- h - k;
        l <- l - l + k;
      } else {}
    }
  }
}.


lemma declassify :
  equiv
    [M.while_ ~ M.while_ :
     ={M.l, M.n} ==>
     ={M.l, M.n} /\ b (M.k{1} < M.h{1}) = b (M.k{2} < M.h{2}) |
     { (l, l -->    b (M.k{1} < M.h{1}) = b (M.k{2} < M.h{2}) ) } ==>
     { } ].
proof.
proc.
admit.
qed.

