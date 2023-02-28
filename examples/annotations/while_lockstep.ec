require import Int IntDiv List Ring.
import IntID.

module M = {
  var i, n, x : int

  proc foo() = {
    i <- 0;
    while (i < n) {
      @l;
      x <- x + i;
      i <- i + 1;
    }
  }

  proc bar() = {
    i <- 0;
    while (i < 10) {
      @l;
      x <- x - i;
      i <- i + 1;
    }
  }
}.

(*Relational assertions can be used in lockstep.*)
lemma foobar :
  equiv [M.foo ~ M.bar : M.n{1} = 10 /\ M.x{1} + M.x{2} = 42 ==> M.x{1} + M.x{2} = 42 |
         { } ==> { (l, l --> ={M.i} => M.x{1} + M.x{2} = 42) }].
proof.
proc.
lwhile (M.n{1} = 10 /\ M.x{1} + M.x{2} = 42) (-M.i{1}) (-M.i{2}).
+ move=> z.
  wp.
  label.
  skip.
  move=> &1 _ /= [<<- _].
  by rewrite opprD ltzE.
+ move=> z.
  wp.
  label.
  skip.
  move=> _  &2 /= [<<- _].
  by rewrite opprD ltzE.
+ wp.
  label.
  skip.
  by move=> &1 &2 [_] []; rewrite Ring.IntID.eqr_opp => ->.
+ wp.
  label.
  skip.
  move=> &1 &2 |> eq_.
  rewrite Ring.IntID.eqr_opp => <<- le1 le2 /=.
  by rewrite -eq_; ring.
sp.
skip.
by move=> &1 &2 |>.
qed.
