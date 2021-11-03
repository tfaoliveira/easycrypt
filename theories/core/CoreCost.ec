require import CoreXint.

(* -------------------------------------------------------------------- *)
op zero : cost.
op inf  : cost.

op scale : int -> cost -> cost.
op xscale (x : xint) (c : cost) =
  with x = N x => scale x c
  with x = Inf => inf
    
op add : cost -> cost -> cost.
op lt  : cost -> cost -> bool.
op le  = fun x y => lt x y \/ x = y.

op opp : cost -> cost.
