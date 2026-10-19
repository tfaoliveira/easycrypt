(* Applications of operators defined by a body are memoised, with arrays
   (applications of abstract operators) compared by identity. Here, as in
   the sponges of SHA-3 specifications, the i-th output recomputes
   [iter i step s] from the same state [s]: quadratic without
   memoisation (EC_EVAL_NOMEMO), linear with it. *)
require import AllCore List IntDiv.

type state.
op init : (int -> int) -> state.
op get : state -> int -> int.
axiom getE f i : get (init f) i = f i.

hint simplify in eval : getE.

op step (a : state) : state =
  init (fun i => (get a i + get a ((i + 1) %% 4)) %% 1000003).

op st_i (s : state) (i : int) : state = iter i step s.

op squeeze (s : state) (n : int) : int list =
  map (fun i => get (st_i s i) 0) (iota_ 0 n).

op s0 : state = init (fun i => i + 1).

check nth 0 (squeeze s0 3000) 2999 = 408557.
check nth 0 (squeeze s0 3000) 1234 = 378934.
check foldr (fun x acc => (x + acc) %% 1000003) 0 (squeeze s0 3000) = 850772.
