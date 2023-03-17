require import AllCore Int IntDiv.


module M = {
  var k, n, t : int

  proc while_left() : unit = {
    k <- 1;
    while (k < 2 ^ n) {
      @l;
      t <- t + k;
      k <- 2 * k;
    }
  }

  proc while_right() : unit = {
    k <- 1;
    while (k < 4 ^ n) {
      @l;
      t <- t + k;
      k <- 4 * k;
    }
  }
}.


lemma index_equiv :
  equiv
    [M.while_left ~ M.while_right :
     0 <= M.n{1} /\ ={M.n} ==>
     true |
     { } ==>
     { (l, l --> exists a , 0 <= a /\ M.k{1} = 2 ^ a /\ M.k{2} = 4 ^ a)  } ].
proof.
proc.
(*TODO: annotations: the type of a is not well defined or not well displayed.*)
lwhile
  (0 <= M.n{1} /\ ={M.n} /\ exists a, 0 <= a /\ M.k{1} = 2 ^ a /\ M.k{2} = 3 ^ a)
  (-M.k{1}) (-M.k{2}).
+ move=> z.
  (*TODO: annotations: this could be a hoare goal.*)
  wp.
  label.
  skip.
  move=> &1 _ //.
  admit.
+ admit.
+ wp.
  label.
  skip.
  move=> &1 &2 //= neq_.
  (*exists 0.*)
  admit.
+ wp.
  label.
  skip.
  move=> &1 &2 //=.
  admit.
wp.
skip.
move=> &1 &2 //=.
admit.
qed.

lemma value_equiv :
  equiv
    [M.while_left ~ M.while_right :
     0 <= M.n{1} /\ ={M.n} ==>
     3 * M.t{2} = (M.t{1} + 1) ^ 2 - 1  |
     { (l, l --> exists a , 0 <= a /\ M.k{1} = 2 ^ a /\ M.k{2} = 4 ^ a) } ==>
     { } ].
proof.
proc.
admit.
qed.

lemma full_equiv :
  equiv
    [M.while_left ~ M.while_right :
     0 <= M.n{1} /\ ={M.n} ==>
     3 * M.t{2} = (M.t{1} + 1) ^ 2 - 1  |
     { } ==> { } ].
proof.
proc.
admit.
qed.
