require import AllCore Int.


type t.


op b_low    : t -> bool.
op b_high_a : t -> bool.
op b_high_b : t -> bool.


module M = {
  var t         : int
  var low, high : t

  proc foo() : unit = {}

  proc bar() : unit = {}

  proc if_() : unit = {
    if (b_low low) {
      @l_if;
      if (b_high_a high)
        {foo();} else {bar();}
    }
    else {
      @l_else;
      if (b_high_b high)
        {foo();} else {bar();}
    }
  }
}.


lemma if_ct :
  equiv
    [M.if_ ~ M.if_ :
     ={M.low} ==>
     ={M.t} |
     { } ==>
     { (l_if,   l_if   --> b_high_a M.low{1} = b_high_a M.low{2}),
       (l_else, l_else --> b_high_b M.low{1} = b_high_b M.low{2}) } ].
proof.
proc.
(*TODO: annotations: seq rule.*)
if.
+ by trivial.
+ admit.
admit.
qed.

