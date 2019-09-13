require import AllCore.

pragma -oldip.
pragma +implicits.

(** A type for Z-modules over some type 'a **)
type 'a zmodule =
  [ PreZMod of ('a -> bool)     (* support *)
             & 'a               (* zero *)
             & ('a -> 'a -> 'a) (* operation *)
             & ('a -> 'a)       (* inverse *)
  ].

(** Notations **)
op (\in) (x : 'a) (m : 'a zmodule) =
  with m = PreZMod m _ _ _ => m x.

op e (m : 'a zmodule) =
  with m = PreZMod _ e _ _ => e.

op o (m : 'a zmodule) =
  with m = PreZMod _ _ o _ => o.

op n (m : 'a zmodule) =
  with m = PreZMod _ _ _ n => n.

(** Some of those are not Z-modules **)
inductive iszmodule (m : 'a zmodule) =
  | IsZMod of (e m \in m)
            & (forall x y, x \in m => y \in m => (o m) x y \in m)
            & (forall x, x \in m => (n m) x \in m)

            & (forall x, x \in m => (o m) (e m) x = x)
            & (forall x y, x \in m => y \in m => (o m) x y = (o m) y x)
            & (forall x y z, x \in m => y \in m => z \in m =>
                             (o m) x ((o m) y z) = (o m) ((o m) x y) z)

            & (forall x, x \in m => (o m) ((n m) x) x = e m).

(** But those that are enjoy great properties **)
lemma erM (m : 'a zmodule) :
  iszmodule m =>
  e m \in m.
proof. by case=> ->. qed.

lemma addrM (m : 'a zmodule) (x y : 'a) :
  iszmodule m =>
  x \in m => y \in m =>
  (o m) x y \in m.
proof. by case=> _ + _ _ _ _ _ x_in_m y_in_m - ->. qed.

lemma opprM (m : 'a zmodule) (x : 'a) :
  iszmodule m =>
  x \in m =>
  (n m) x \in m.
proof. by case=> _ _ h _ _ _ _ /h. qed.

lemma addrA (m : 'a zmodule) (x y z : 'a) :
  iszmodule m =>
  x \in m => y \in m => z \in m =>
  (o m) x ((o m) y z) = (o m) ((o m) x y) z.
proof. by case=> _ _ _ _ _ + _ x_in_m y_in_m z_in_m - ->. qed.

lemma addrC (m : 'a zmodule) (x y : 'a) :
  iszmodule m =>
  x \in m => y \in m =>
  (o m) x y = (o m) y x.
proof. by case=> _ _ _ _ + _ _ x_in_m y_in_m - ->. qed.

lemma add0r (m : 'a zmodule) (x : 'a) :
  iszmodule m =>
  x \in m =>
  (o m) (e m) x = x.
proof. by case=> _ _ _ + _ _ _ x_in_m - ->. qed.

lemma addNr (m : 'a zmodule) (x : 'a) :
  iszmodule m =>
  x \in m =>
  (o m) ((n m) x) x = e m.
proof. by case=> _ _ _ _ _ _ + x_in_m - ->. qed.

hint exact: erM addrM opprM addrA addrC add0r addNr.

(** And all derived properties **)
lemma addr0 (m : 'a zmodule) (x : 'a) :
  iszmodule m =>
  x \in m =>
  (o m) x (e m) = x.
proof. by move=> m_zmod x_in_m; rewrite addrC // add0r. qed.

lemma addrN (m : 'a zmodule) (x : 'a) :
  iszmodule m =>
  x \in m =>
  (o m) x ((n m) x) = e m.
proof. by move=> m_zmod x_in_m; rewrite addrC // addNr. qed.

lemma addrK (m : 'a zmodule) (x : 'a) (y : 'a) :
  iszmodule m =>
  x \in m => y \in m =>
  (o m) ((o m) x y) ((n m) y) = x.
proof.
by move=> m_zmod x_in_m y_in_m; rewrite -addrA // addrN // addr0.
qed.

lemma addIr (m : 'a zmodule) (y x x' : 'a) :
  iszmodule m =>
  x \in m => x' \in m => y \in m =>
  (o m) x y = (o m) x' y => x = x'.
proof.
move=> m_zmod x_in_m x'_in_m y_in_m h.
by rewrite -(@addrK m x' y) // -h addrK.
qed.

lemma opprK (m : 'a zmodule) (x : 'a) :
  iszmodule m =>
  x \in m =>
  (n m) ((n m) x) = x.
proof.
move=> m_zmod x_in_m; apply (@addIr m (n m x))=> //.
+ exact/opprM.
by rewrite addNr // addrN.
qed.

lemma oppr0 (m : 'a zmodule) :
  iszmodule m =>
  (n m) (e m) = e m.
proof.
move=> m_zmod.
by rewrite -(@addr0 m ((n m) (e m))) ?addNr ?opprM ?erM.
qed.

(** And some derived operations **)
op intmul (m : 'a zmodule) (x : 'a) (c : int) =
  if   c < 0
  then (n m) (iterop (-c) (o m) x (e m))
  else       (iterop   c  (o m) x (e m)).

lemma iterM (c : int) (m : 'a zmodule) (x : 'a) :
  iszmodule m =>
  x \in m =>
  0 <= c =>
  iter c (o m x) x \in m.
proof.
move=> m_zmod x_in_m; elim: c=> [|c ge0_c ih].
+ by rewrite iter0.
by rewrite iterS.
qed.

lemma iteropM (c : int) (m : 'a zmodule) (x z : 'a) :
  0 <= c =>
  iszmodule m =>
  x \in m => z \in m =>
  iterop c (o m) x z \in m.
proof.
move=> + m_zmod x_in_m z_in_m; case: c=> [|c ge0_c ih].
+ by rewrite iterop0.
by rewrite iteropS // iterM.
qed.

hint exact: iteropM.

lemma intmulpE (m : 'a zmodule) (x : 'a) (c : int) :
  0 <= c =>
  intmul m x c = iterop c (o m) x (e m).
proof. by rewrite /intmul lezNgt=> ->. qed.

lemma mulr0z (m : 'a zmodule) (x : 'a) :
  intmul m x 0 = e m.
proof. by rewrite /intmul /= iterop0. qed.

lemma mulrNz (m : 'a zmodule) (x : 'a) (c : int) :
  iszmodule m =>
  x \in m =>
  intmul m x (-c) = (n m) (intmul m x c).
proof.
move=> m_zmod x_in_m.
case: (c = 0)=> [->|nz_c]; first by rewrite oppz0 mulr0z oppr0.
rewrite /intmul oppz_lt0 oppzK ltz_def nz_c lezNgt /=.
case: (c < 0)=> // lt0_c.
rewrite ?opprK //; apply/iteropM=> //.
by rewrite oppz_ge0; exact/ltzW.
qed.
