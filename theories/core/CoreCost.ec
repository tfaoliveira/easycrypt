require import CoreXint Int.

(* -------------------------------------------------------------------- *)
op zero : cost.

axiom zero_def : zero = `[: N 0].

hint simplify zero_def.

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

(* -------------------------------------------------------------------- *)
(* sufficient condition to do backward reasoning over costs. *)
op subcond = fun x y => (x - y) + y = x.

(* -------------------------------------------------------------------- *)
axiom scale0cost (x : cost): 0 * x = zero.
axiom scale1cost : left_id   1 scale.

hint simplify [reduce] scale0cost, scale1cost.

axiom scale_distr (i j : int) (x : cost) : 
  (i + j) * x = i * x + j * x.

(* -------------------------------------------------------------------- *)
axiom add0cost : left_id zero add.
axiom addcost0 : right_id zero add.

hint simplify [reduce] add0cost, addcost0.

axiom addcostA : associative add.

axiom addcostC : commutative add.
