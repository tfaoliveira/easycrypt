require import AllCore Int.

type class comoid = {
  op ('0) : comoid
  op (+)  : comoid -> comoid -> comoid

  axiom add0m (x : comoid)     : '0 + x = x
  axiom addmC (x y : comoid)   : x + y = y + x
  axiom addmA (x y z : comoid) : (x + y) + z = x + (y + z)
}.

lemma addm0 ['a <: comoid] (x : 'a) : x + '0 = x.
proof. by rewrite addmC add0m. qed.

op zero = 0.

instance comoid with int
  op ('0) = Self.zero
  op (+)  = Int.(+).
realize add0m.

  proof add0m by (exact/add0m<:int>)
  proof addmC by exact/addzC
  proof addmA by exact/addzA.
