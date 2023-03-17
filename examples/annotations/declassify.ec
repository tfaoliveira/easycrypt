require import AllCore Int List Real StdBigop.
        import Bigreal.BRA.

module A = {
  (*Low security variables*)
  var n : int
  var h : real
  (*High security variables*)
  var hs : real list

  proc average_salary() : unit = {
    @declassify;
    h <- (big predT idfun hs) / n%r;
  }
}.

lemma delimited_release_average :
  equiv
    [A.average_salary ~ A.average_salary :
     ={A.n, A.h} /\ 0 < A.n{1} ==>
     ={A.n, A.h} |
     { (declassify, declassify --> ((big predT idfun A.hs{1}) / A.n{1}%r) = ((big predT idfun A.hs{2}) / A.n{2}%r)) } ==>
     { } ].
proof.
proc.
wp.
label.
skip.
move=> &1 &2 |> lt0n.
pose x1 := big _ _ A.hs{1}.
pose y1 := big _ _ A.hs{1}.
(*TODO: somehow not instant win?*)
admit.
abort.


module W = {
  (*Low security variables*)
  var n, l: int
  (*High security variables*)
  var k, h : int

  proc wallet_attack() : unit = {
    l <- 0;
    while (0 <= n) {
      k <- 2 ^ (n - 1);
      @declassify;
      if (k <= h) {
        h <- h - k;
        l <- l + k;
      } else {}
      n <- n - 1;
    }
  }
}.



lemma delimited_release_wallet :
  equiv
    [W.wallet_attack ~ W.wallet_attack :
     ={W.n, W.l} ==>
     ={W.n, W.l} |
     { (declassify, declassify --> (W.k{1} <= W.h{1}) = (W.k{2} <= W.h{2})) } ==>
     { } ].
proof.
proc.
sp.

abort.


lemma declassify :
  equiv
    [M.while_ ~ M.while_ :
     ={M.l, M.n} /\ (b_low M.low{1} <=> b_low M.low{2}) ==>
     ={M.l, M.n} /\ b (M.k{1} < M.h{1}) = b (M.k{2} < M.h{2}) |
     { (l, l -->    b (M.k{1} < M.h{1}) = b (M.k{2} < M.h{2}) ) } ==>
     { } ].
proof.
proc.
lwhile
  (={M.l, M.n, M.k} /\
   (b_low M.low{1} <=> b_low M.low{2}) /\
   (0 < M.c{1} => b (M.k{1} < M.h{1}) = b (M.k{2} < M.h{2})) )
  (M.c{1}) (M.c{2}).
+ move=> z.
  sp.
  wp.
  label.
  skip.
  by move=> &1 &2 |> _; rewrite ltzE.
+ move=> z.
  sp.
  wp.
  label.
  skip.
  by move=> &1 &2 |> _; rewrite ltzE.
+ sp.
  wp.
  label.
  skip.
  by move=> &1 &2 |>.
+ sp.
  wp.
  label.
  skip.
  move=> &1 &2 |>. ? ? -> _ _ _ ->.
wp.
skip.
move=> &1 &2 |> ->.
admit.
qed.

