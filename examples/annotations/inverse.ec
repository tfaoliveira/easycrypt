require import AllCore.

op f : int -> int.
op g : int -> int.

axiom can_fg : cancel f g.

axiom can_gf : cancel g f.

module M = {
  var x, y : int

  proc foo(x : int) = {
    @before;
    y <- f x;
    @after;
  }

  proc bar(x : int) = {
    @before;
    x <- g y;
    @after;
  }
}.


lemma cancel_foobar :
  equiv[ M.foo ~ M.bar : true ==> true |
         { (before, after --> ={M.x}) } ==>
         { (after, before --> ={M.y}) } ].
proof.
proc.
(*TODO: bug: the labels should be preserved here.*)
label.
fail.
qed.
