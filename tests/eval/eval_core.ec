(* [eval] and [check] on the core datatypes. *)
require import AllCore List IntDiv.
require Subtype.

(* integers *)
check 3 + 4 * 5 = 23.
check (-17) %/ 5 = -4 /\ (-17) %% 5 = 3.
check 7 %/ 0 = 0 /\ 7 %% 0 = 7.
check 2 ^ 100 = 1267650600228229401496703205376.
check 0 < 1 /\ !(1 <= 0) /\ `|-5| = 5.
check modexp 3 200 1000 = 1.
eval 2 ^ 64.

(* booleans: connectives are lazy *)
check !(false /\ (1 %/ 0 = witness)).
check true \/ (1 %/ 0 = witness).
check (false => (1 %/ 0 = witness)).
check (true <> false) && (true <=> true).

(* lists, options, tuples, let, match *)
check map (fun x => x * x) (iota_ 0 5) = [0; 1; 4; 9; 16].
check foldl (+) 0 (range 0 101) = 5050.
check rev [1; 2; 3] = [3; 2; 1].
check nth 0 [1; 2; 3] 7 = 0.
check head 0 [] = 0.
check mkseq (fun i => 2 * i) 3 = [0; 2; 4].
check sumz (iota_ 1 10) = 55.
check (let (x, y) = (1, 2) in x + y) = 3.
check (match Some 3 with None => 0 | Some x => x end) = 3.
check odflt 0 (ohead [5]) = 5.
check iter 10 (fun x => 2 * x) 1 = 1024.
check flatten [[1]; []; [2; 3]] = [1; 2; 3].
check undup [1; 1; 2] = [1; 2].
check sort (<=) [3; 1; 2] = [1; 2; 3].

(* user datatypes, records and recursive operators *)
type tree = [Leaf | Node of tree & int & tree].

op size_t (t : tree) : int =
  with t = Leaf => 0
  with t = Node l _ r => size_t l + 1 + size_t r.

op insert (x : int) (t : tree) : tree =
  with t = Leaf => Node Leaf x Leaf
  with t = Node l y r => if x < y then Node (insert x l) y r else Node l y (insert x r).

op elems (t : tree) : int list =
  with t = Leaf => []
  with t = Node l x r => elems l ++ x :: elems r.

check size_t (foldr insert Leaf [5; 2; 8; 1]) = 4.
check elems (foldr insert Leaf [5; 2; 8; 1]) = [1; 2; 5; 8].

type point = { px : int; py : int; }.

op mirror (p : point) = {| px = p.`py; py = p.`px; |}.

check (mirror {| px = 1; py = 2; |}).`px = 2.

(* subtypes evaluate on their representation *)
subtype nat as Nat = { x : int | 0 <= x }.
realize inhabited by exists 0.

check Nat.val (Nat.insubd 3) = 3.
check Nat.insub (-1) = None.

(* failures *)
op abs_op : int -> int.

fail check 1 + 1 = 3.
fail check false.
fail check abs_op 0 = 0.
fail check forall (x : int), x = x.
fail check witness<:int> = 0.
fail check (fun (x : int) => x) = (fun x => x).
