require import AllCore Int IntDiv.


module M = {
  var x, y : int

  proc poly() : unit = {
    @l_past;
    y <- x ^ 3 - x;
    @l_future;
  }
}.


lemma kernel :
  equiv
    [M.poly ~ M.poly :
     true ==>
     true |
     { (l_future, l_future --> ={M.y}) } ==>
     { (l_past, l_past --> ={M.x}) } ].
proof.
proc.
(*TODO: annotations: currently, this is unprovable using the rules of the Hoare logic, *)
(*                   but true using the semantics.                                     *)
admit.
qed.

