(* Lemmas of the [eval] database define abstract operators. *)
require import AllCore List IntDiv.

op f : int -> int.
axiom fE x : f x = x + 1.

fail check f 1 = 2.

hint simplify in eval : fE.

check f 1 = 2.
check map f [1; 2] = [2; 3].

(* rules with side conditions and nested patterns *)
op g : int list -> int.
axiom g_nil : g [] = 0.
axiom g_cons x s : 0 <= x => g (x :: s) = x + g s.

hint simplify in eval : g_nil, g_cons.

check g [1; 2; 3] = 6.
fail check g [-1] = -1.

(* rules replace inefficient definitions *)
op slow (n : int) = iter n (fun x => x + 1) 0.
lemma slowE n : slow n = max 0 n.
proof. admit. qed.

hint simplify in eval : slowE.

check slow (2 ^ 100) = 2 ^ 100.
