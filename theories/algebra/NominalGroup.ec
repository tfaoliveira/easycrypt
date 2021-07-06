(* -------------------------------------------------------------------- *)
require import AllCore List IntMin IntDiv.
require import FinType FSet.
require (*--*) Ring Number StdOrder ZModP.

import Ring.IntID StdOrder.IntOrder.

(* -------------------------------------------------------------------- *)

op injective_on (A : 'a fset) (f : 'a -> 'b) : bool = 
  forall (x y : 'a), x \in A => y \in A => f x = f y => x = y.

abstract theory NominalGroup.

type G.
type Z.

clone include FinType
  with type t <- G
  rename "card" as "order"
  rename "enum" as "elems".

op g     : G.
op ( ^ ) : G -> Z -> G.

op ( * ) : Z -> Z -> Z.
op inv   : Z -> Z.

op f : Z.
op exp(a,x) = a^(x*inv f).

op E : Z fset.
op dZ : Z distr.

axiom expM       : forall a x y, a^(x * y) = (a^x)^y. 
axiom exp_inv    : forall x, x \in E => g^(x * inv x) = g.
axiom exp_inv_f  : forall a, a^(f * inv f) = a.

axiom exp_inj    : injective_on E (exp g).
axiom exp_inj'   : forall x, injective_on E (fun z => exp g (x*z)).

axiom img_exp    : forall x, image (fun z => exp g (x*z)) E = image (exp g) E.

end NominalGroup.
