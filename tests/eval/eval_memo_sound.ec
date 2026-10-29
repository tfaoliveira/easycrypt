(* Memoisation never changes the result of an evaluation. Each check below
   targets one way in which a memoised value could be wrongly reused; all
   of them also hold with EC_EVAL_NOMEMO set. *)
require import AllCore List IntDiv.

(* ---------------------------------------------------------------- *)
(* 1. An operator value is shared by all the instances of a polymorphic
   operator: keys must distinguish the constructors of different types
   that have the same index ([None] and [[]] are both constructor 0). *)
op idp ['a] (x : 'a) : 'a = x.

op isnil : int list -> bool.
axiom isnilE : isnil [] = true.
hint simplify in eval : isnilE.

check (idp None<:int> = None) /\ isnil (idp []).
check (idp (Some 0) = Some 0) /\ idp [0] = [0] /\ idp (0, 0) = (0, 0).

(* ---------------------------------------------------------------- *)
(* 2. Functions inside arguments: two different functions are never the
   same key, even with the same code and arguments. *)
op app_pair (p : (int -> int) * int) : int = p.`1 p.`2.

check app_pair ((fun x => x + 1), 1) = 2 /\ app_pair ((fun x => x * 10), 1) = 10.
check app_pair ((fun x => x + 1), 1) = 2 /\ app_pair ((fun x => x + 2), 1) = 3.

op appf (f : int -> int) (x : int) : int = f x.

check appf (fun x => x + 1) 1 = 2 /\ appf (fun x => x - 1) 1 = 0.

(* ---------------------------------------------------------------- *)
(* 3. Hash collisions: keys are hashed on their first nodes only. These
   300 lists share a prefix of 200 elements and differ in the last one. *)
op last0 (l : int list) : int = nth 0 l (size l - 1).

op keys : int list list = map (fun k => nseq 200 7 ++ [k]) (iota_ 0 300).

check foldr (fun l acc => last0 l + acc) 0 keys = 44850.
check map last0 keys = iota_ 0 300.

(* structurally equal keys built differently share their result *)
check last0 (iota_ 0 100) = 99 /\ last0 (rev (rev (iota_ 0 100))) = 99.

(* ---------------------------------------------------------------- *)
(* 4. Partial and over-application *)
op add3 (x y z : int) : int = x + y + z.
op adder (x : int) : int -> int = fun y => x + y.

check map (add3 1 2) [0; 10] = [3; 13] /\ add3 1 2 0 = 3 /\ (add3 1) 2 10 = 13.
check map (adder 1) [0; 10] = [1; 11] /\ adder 2 3 = 5 /\ adder 1 0 = 1.

(* ---------------------------------------------------------------- *)
(* 5. Operators computed by a conditional [eval] rule or by their
   definition, depending on the argument. *)
op g (x : int) : int = 0.
lemma gE x : 0 < x => g x = x.
proof. admit. qed.
hint simplify in eval : gE.

check g 5 = 5 /\ g (-1) = 0 /\ g 5 = 5 /\ g (-1) = 0.

(* ---------------------------------------------------------------- *)
(* 6. More keys than the capacity of a table (65536): the table is
   emptied, and the results stay correct. *)
op sq (x : int) : int = x * x.

check foldr (fun x acc => sq x + acc) 0 (iota_ 0 70000) + sq 3 = 114330883345009.

(* ---------------------------------------------------------------- *)
(* 7. Arrays: two arrays with the same contents are different keys, and
   an array returned from the memo is not affected by later updates. *)
type state.
op init : (int -> int) -> state.
op get : state -> int -> int.
op set : state -> int -> int -> state.
axiom getE f i : get (init f) i = f i.
axiom get_setE a i j x : get (set a i x) j = if i = j then x else get a j.
hint simplify in eval : getE, get_setE.

op mk (n : int) : state = init (fun i => i + n).
op first (a : state) : int = get a 0.

check first (mk 3) = 3 /\ first (init (fun i => i + 3)) = 3 /\ first (mk 4) = 4.
check get (set (mk 3) 0 99) 0 = 99 /\ get (mk 3) 0 = 3 /\ first (set (mk 3) 0 99) = 99.

(* ---------------------------------------------------------------- *)
(* 8. Procedures: the memoised operators see the values of the program
   variables, and closures built in a loop are all different. *)
module M = {
  var x : int

  proc loop() : int = {
    var i, a, s;
    i <- 0; s <- 0;
    while (i < 5) {
      x <- i;
      a <- init (fun j => j * x);       (* a new array at each iteration *)
      s <- s + get a 2 + sq x + first a;
      i <- i + 1;
    }
    return s;
  }
}.

(* sum of 2 i + i^2 + 0 for i < 5 *)
check proc M.loop() = 50.
