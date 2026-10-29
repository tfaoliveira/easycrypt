(* Memoisation avoids recomputations: each check below is linear with
   memoisation and exponential (or quadratic) without it. The step budget
   turns a loss of sharing into a failure instead of a very long run. *)
require import AllCore List IntDiv.

pragma Eval:steps = 10000000.

(* ---------------------------------------------------------------- *)
(* 1. Trees with shared subtrees: [full n] has 2^n leaves, but only n
   distinct subtrees. Counting the leaves takes 2^60 calls without
   sharing, and n with it (keys are compared structurally, and the two
   children are even the same value). *)
type nat = [Z | S of nat].
type tree = [Leaf | Node of tree & tree].

op nat_of (n : int) : nat = iter n S Z.

op full (n : nat) : tree =
  with n = Z => Leaf
  with n = S m => Node (full m) (full m).

op count (t : tree) : int =
  with t = Leaf => 1
  with t = Node l r => count l + count r.

check count (full (nat_of 10)) = 1024.
check count (full (nat_of 60)) = 1152921504606846976.

(* ---------------------------------------------------------------- *)
(* Arrays given by [init] and [get], as in the Jasmin library *)
type state.
op init : (int -> int) -> state.
op get : state -> int -> int.
axiom getE f i : get (init f) i = f i.
hint simplify in eval : getE.

op combine (a b : state) : state = init (fun i => get a i + get b ((i + 1) %% 4)).

(* ---------------------------------------------------------------- *)
(* 2. A diamond: each level combines the previous array with itself.
   Sharing needs both memoisations: [g m] is computed once and is the
   same array (identifier) in both arguments, and each element of an
   array is computed once. 2^60 arrays without sharing. *)
op g (n : nat) : state =
  with n = Z => init (fun i => i + 1)
  with n = S m => combine (g m) (g m).

check get (g (nat_of 60)) 0 = 2882303762590859264.
check get (g (nat_of 60)) 3 = 2882303760443375616.

(* ---------------------------------------------------------------- *)
(* 3. A sponge that squeezes again from the start for each output, as
   the XOFs of the ML-DSA specification: [iter i step s] for each i. *)
op step (a : state) : state =
  init (fun i => (get a i + get a ((i + 1) %% 4)) %% 1000003).

op squeeze (s : state) (n : int) : int list =
  map (fun i => get (iter i step s) 0) (iota_ 0 n).

op s0 : state = init (fun i => i + 1).

(* 1000 outputs: about 10^6 steps with sharing, 3 * 10^7 without *)
check nth 0 (squeeze s0 1000) 999 = 138306.
check nth 0 (squeeze s0 1000) 123 = 531488.
check foldr (fun x acc => (x + acc) %% 1000003) 0 (squeeze s0 1000) = 323443.

(* ---------------------------------------------------------------- *)
(* 4. A procedure that calls an expensive operator on few distinct
   arguments: each value is computed once in the whole command. *)
op slow (x : int) : int = iter 2000 (fun acc => acc + x) 0.

module M = {
  proc loop() : int = {
    var i, s;
    i <- 0; s <- 0;
    while (i < 3000) {
      s <- s + slow (i %% 5 + 1);
      i <- i + 1;
    }
    return s;
  }
}.

check proc M.loop() = 18000000.

(* ---------------------------------------------------------------- *)
(* The budget itself: an evaluation that needs more steps fails. *)
pragma Eval:steps = 1000.

check iter 100 (fun x => x + 1) 0 = 100.
fail check iter 100000 (fun x => x + 1) 0 = 100000.

pragma Eval:steps = 0.

check iter 100000 (fun x => x + 1) 0 = 100000.
