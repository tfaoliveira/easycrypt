(* -------------------------------------------------------------------- *)
require import AllCore RealExtra RealSeq Ring StdRing StdOrder.
(*---*) import RField RealOrder.

(* -------------------------------------------------------------------- *)
op convergeto (f : real -> real) (x : real) (l : real) =
  forall e, 0%r < e => exists a, forall y, `|y - x| < a => `|l - f x| < e.

(* -------------------------------------------------------------------- *)
op diff (f : real -> real) (x : real) =
  lim x (fun y => (f y - f x) / (y - x)).
