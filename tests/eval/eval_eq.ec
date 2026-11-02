(* Equality is type-directed: componentwise on tuples, and given by the
   rules of the [eval] database whose left-hand side is an equality at
   the type, e.g. for types whose values are closures. *)
require import AllCore List.

type t.
op init : (int -> int) -> t.
op get : t -> int -> int.
axiom getE f i : get (init f) i = f i.
op to_list (a : t) = map (get a) (iota_ 0 4).
axiom eqE (a b : t) : (a = b) <=> (to_list a = to_list b).

hint simplify in eval : getE.

fail check init (fun i => i) = init (fun i => 0 + i).

hint simplify in eval : eqE.

check init (fun i => i) = init (fun i => 0 + i).
check init (fun i => i) <> init (fun i => 1 + i).
check (init (fun i => i), 1) = (init (fun i => 0 + i), 1).
check ((init (fun i => i), 1) = (init (fun i => i + 1), 1)) = false.
