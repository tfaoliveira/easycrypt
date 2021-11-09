require import CoreXint.

(* -------------------------------------------------------------------- *)
op zero : cost.
op inf  : cost.

op scale : int -> cost -> cost.
op xscale (x : xint) (c : cost) =
  with x = N x => scale x c
  with x = Inf => inf
    
op add : cost -> cost -> cost.
op opp : cost -> cost.

op lt : cost -> cost -> bool.
op le = fun x y => lt x y \/ x = y.

(* sufficient condition to do backward reasoning over costs. *)
op subcond = fun x y => (x - y) + y = zero
