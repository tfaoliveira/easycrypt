require export CoreXint Int.

(* -------------------------------------------------------------------- *)
abbrev ('0) = N 0.
abbrev ('1) = N 1.

op xopp (x:xint) = 
  with x = N x => N (-x)
  with x = Inf => Inf.

op xadd (x y : xint) =
  with x = N x, y = N y => N (x + y)
  with x = N _, y = Inf => Inf
  with x = Inf, y = N _ => Inf
  with x = Inf, y = Inf => Inf.

op xmul (x : xint) (y : xint) =
  with x = N x, y = N y => N (x * y)
  with x = N x, y = Inf => if x = 0 then N 0 else Inf
  with x = Inf, y = N y => if y = 0 then N 0 else Inf
  with x = Inf, y = Inf => Inf.

abbrev ([-])  = xopp.
abbrev ( + )  = xadd.
abbrev ( - ) x y = xadd x (-y).
abbrev ( *  ) = xmul.
abbrev ( ** ) = fun (c : int) (x : xint) => N c * x.

op is_int (x:xint) = 
  with x = N _ => true
  with x = Inf => false.

op is_inf (x:xint) = 
  with x = N _ => false
  with x = Inf => true.

op xoget (x : xint) =
  with x = N i => i
  with x = Inf => 0.

(* -------------------------------------------------------------------- *)
lemma xmulz_l (c : xint) : '0 * c = '0 by case c.
lemma xmulz_r (c : xint) : c * '0 = '0 by case c.

hint rewrite xmulz : xmulz_l xmulz_r.
