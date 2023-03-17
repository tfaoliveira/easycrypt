require import AllCore.

op f : int -> int.

axiom inj_f : injective f.

module M = {
  var x, y : int

  proc foo(x : int) = {
    @before;
    y <- f x;
    @after;
  }
}.


lemma inj_foo :
  equiv[ M.foo ~ M.foo : true ==> true |
         { (after, after --> ={M.y}) } ==>
         { (before, before --> ={M.x}) } ].
proof.
proc.
label.
simplify.
fail.
qed.
