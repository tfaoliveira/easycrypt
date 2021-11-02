op zero : cost.

op scale : int -> cost -> cost.
op add : cost -> cost -> cost.
op lt  : cost -> cost -> bool.
op le  = fun x y => lt x y \/ x = y.

op opp : cost -> cost.
