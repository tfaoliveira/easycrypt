(* -------------------------------------------------------------------- *)
require import AllCore Real.

(* -------------------------------------------------------------------- *)
type ereal = [ PInf | NInf | Real of real ].

abbrev (%e) (x : real) = Real x.
abbrev (%i) (x : int)  = x%r%e.

abbrev #+oo = PInf.
abbrev #-oo = NInf.

abbrev (\0) = 0%i.
abbrev (\1) = 1%i.

(* -------------------------------------------------------------------- *)
type sign = [ Null | Pos | Neg ].

(* -------------------------------------------------------------------- *)
op select ['a] (s : sign) (z p n : 'a) =
  with s = Pos  => p
  with s = Neg  => n
  with s = Null => z.

(* -------------------------------------------------------------------- *)
op rsign (x : real) : sign =
  if x = 0%r then Null else if x < 0%r then Neg else Pos.

(* -------------------------------------------------------------------- *)
op sign (x : ereal) : sign =
  with x = PInf   => Pos
  with x = NInf   => Neg
  with x = Real x => rsign x.

(* -------------------------------------------------------------------- *)
op lee (x y : ereal) =
  with x = PInf  , y = PInf   => true
  with x = PInf  , y = NInf   => false
  with x = PInf  , y = Real _ => false
  with x = Real _, y = PInf   => true
  with x = Real x, y = Real y => x <= y
  with x = Real x, y = NInf   => false
  with x = NInf  , y = PInf   => false
  with x = NInf  , y = Real _ => false
  with x = NInf  , y = NInf   => true.

abbrev (<=) = lee.

(* -------------------------------------------------------------------- *)
op lte (x y : ereal) =
  with x = PInf  , y = PInf   => false
  with x = PInf  , y = NInf   => false
  with x = PInf  , y = Real _ => false
  with x = Real _, y = PInf   => true
  with x = Real x, y = Real y => x < y
  with x = Real x, y = NInf   => false
  with x = NInf  , y = PInf   => false
  with x = NInf  , y = Real _ => false
  with x = NInf  , y = NInf   => false.

abbrev (<) = lte.

(* -------------------------------------------------------------------- *)
op eopp (x : ereal) =
  with x = PInf   => #-oo
  with x = NInf   => #+oo
  with x = Real x => (-x)%e.

abbrev ([-]) = eopp.

(* -------------------------------------------------------------------- *)
op eadd (x y : ereal) =
  with x = PInf  , y = PInf   => #+oo
  with x = PInf  , y = NInf   => 0%i
  with x = NInf  , y = PInf   => 0%i
  with x = NInf  , y = NInf   => #-oo
  with x = Real x, y = Real y => (x + y)%e
  with x = Real _, y = PInf   => #+oo
  with x = Real _, y = NInf   => #-oo
  with x = PInf  , y = Real _ => #+oo
  with x = NInf  , y = Real _ => #-oo.

abbrev (+) = eadd.
abbrev (-) (x y : ereal) = x + (-y).

(* -------------------------------------------------------------------- *)
op emul (x y : ereal) =
  with x = PInf  , y = PInf   => #+oo
  with x = PInf  , y = NInf   => #-oo
  with x = NInf  , y = PInf   => #-oo
  with x = NInf  , y = NInf   => #+oo
  with x = Real x, y = Real y => (x * y)%e
  with x = Real x, y = PInf   => select (rsign x) (\0) #+oo #-oo
  with x = Real x, y = NInf   => select (rsign x) (\0) #-oo #+oo
  with x = PInf  , y = Real y => select (rsign y) (\0) #+oo #-oo
  with x = NInf  , y = Real y => select (rsign y) (\0) #-oo #+oo.

abbrev ( * ) = emul.
