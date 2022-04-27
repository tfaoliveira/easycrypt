require import CoreXint Int.

(* -------------------------------------------------------------------- *)
op zero : cost.

(* FIXME: remove after generalized expressions *)
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
abbrev ( <= ) = le.
abbrev ( <  ) = lt.

(* -------------------------------------------------------------------- *)
(* sufficient condition to do backward reasoning over costs. *)
op subcond = fun x y => (x - y) + y = x.

(* -------------------------------------------------------------------- *)
axiom scale0c (x : cost) : 0 * x = zero.
axiom scale1c (x : cost) : 1 * x = x.

hint simplify scale0c, scale1c.

axiom scale_distr (i j : int) (x : cost) : 
  (i + j) * x = i * x + j * x.

(* -------------------------------------------------------------------- *)
axiom add0c (x : cost) : zero + x = x.
axiom addc0 (x : cost) : x + zero = x.

hint simplify add0c, addc0.

axiom addcA : associative add.

axiom addcC : commutative add.

(* -------------------------------------------------------------------- *)
axiom c_le_inf (c : cost) : c <= inf.

hint simplify c_le_inf.

axiom c_le_inf0 (c : cost) : c <= `[: .., ..].

hint exact : c_le_inf0.

