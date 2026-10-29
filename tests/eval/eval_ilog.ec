(* [RealExp.ilog], defined with real logarithms, is computed on integers
   with the rule ilog_eval. *)
require import AllCore RealExp.

check ilog 2 1 = 0 /\ ilog 2 2 = 1 /\ ilog 2 3 = 1.
check ilog 2 1023 = 9 /\ ilog 2 1024 = 10 /\ ilog 2 1025 = 10.
check ilog 3 80 = 3 /\ ilog 3 81 = 4.
check ilog 10 (10 ^ 40 - 1) = 39 /\ ilog 10 (10 ^ 40) = 40.
fail check ilog 2 1024 = 9.
