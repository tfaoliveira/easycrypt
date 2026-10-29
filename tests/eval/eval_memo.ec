(* Functions given to abstract operators are memoised: an array defined
   from another one reads each of its elements once. Without memoisation,
   the check below makes about 3^30 calls. *)
require import AllCore.

type t.
op init : (int -> int) -> t.
op get : t -> int -> int.
axiom getE f i : get (init f) i = f i.

hint simplify in eval : getE.

op step (a : t) = init (fun i => get a i + get a (i + 1) + get a (i + 2)).

check get (iter 30 step (init (fun i => i))) 0 = 6176733962839470.
check get (iter 30 step (init (fun i => i))) 5 = 7206189623312715.
