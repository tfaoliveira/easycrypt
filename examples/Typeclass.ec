require import Int.

print Int.(+).

type class comoid = {
  op ('0) : comoid
  op (+)  : comoid -> comoid -> comoid

  axiom add0m (x : comoid)     : '0 + x = x
  axiom addmC (x y : comoid)   : x + y = y + x
  axiom addmA (x y z : comoid) : (x + y) + z = x + (y + z)
}.

print ('0).
print (+).

print add0m.

lemma addm0 ['a <: comoid] (x : 'a) : x + '0 = x.
proof. by rewrite addmC add0m. qed.

op zero = 0.

instance comoid with int
  op ('0) = Self.zero
  op (+)  = Int.(+).
realize add0m. by exact/add0z.
realize addmC. by exact/addzC.
realize addmA. by exact/addzA.
