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

axiom foo_ct :
  equiv
    [M.foo ~ M.foo :
     ={M.t} ==>
     ={M.t} |
     { } ==> { }].

axiom bar_ct :
  equiv
    [M.bar ~ M.bar :
     ={M.t} ==>
     ={M.t} |
     { } ==> { }].

lemma if_ct :
  equiv
    [M.if_ ~ M.if_ :
     ={M.t, M.low} ==>
     ={M.t} |
     { } ==>
     { (l_if,   l_if   --> b_high_a M.low{1} = b_high_a M.low{2}),
       (l_else, l_else --> b_high_b M.low{1} = b_high_b M.low{2}) } ].
proof.
proc.
if.
+ by trivial.
+ seq 1 1 : (={M.t, M.low} /\ b_low M.low{1}).
  - label.
    skip.
    by trivial.
  if.
  - admit.
  - admit.
  admit.
admit.
qed.

