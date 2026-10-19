(* Modular arithmetic: [exp] and [inv] are computed through the lemmas
   exp_modexp and inv_eval of ZModP. *)
require import AllCore IntDiv ZModP.

op p : int = 2^127 - 1.

clone import ZModField as Zp with op p <= p proof prime_p by admit.

check asint (inzmod 5 + inzmod (p - 1)) = 4.
check inv (inzmod 9) * inzmod 9 = one.
check inv zero = zero.
check asint (ZModpRing.exp (inzmod 3) (p - 1)) = 1.
check asint (ZModpRing.exp (inzmod 2) 127) = 1.
