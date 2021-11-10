require import CoreXint.

(* -------------------------------------------------------------------- *)
op zero : cost.
op inf  : cost.

op scale : int -> cost -> cost.
op xscale (x : xint) (c : cost) =
  with x = N x => scale x c
  with x = Inf => inf.
    
op add : cost -> cost -> cost.
op opp : cost -> cost.

op lt : cost -> cost -> bool.
op le = fun x y => lt x y \/ x = y.

abbrev ([-]) = opp.
abbrev ( + ) = add.
abbrev ( - ) (x : cost) (y : cost) = add x (-y).
abbrev ( *  ) = scale.
abbrev ( ** ) = xscale.

(* sufficient condition to do backward reasoning over costs. *)
op subcond = fun x y => (x - y) + y = zero.
