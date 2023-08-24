require import AllCore List CHoareTactic StdBigop.
import Bigint.

lemma ltrue : true by done.

(* ------------------------------------------------ *)
lemma x_le_test0 : N (-3) <= Inf. proof. rewrite /= ltrue. qed. 
lemma x_le_test1 : N 0    <= Inf. proof. rewrite /= ltrue. qed. 
lemma x_le_test2 : N 3    <= Inf. proof. rewrite /= ltrue. qed. 

lemma x_le_test3 (x : xint) : x <= Inf. proof. rewrite /= ltrue. qed. 
lemma x_le_test4 (x : xint) : x <= x  . proof. rewrite /= ltrue. qed. 

(* fail *)
lemma x_le_test4 (x : xint) : Inf <= x.
proof. try rewrite /= ltrue. rewrite /=. abort. 

(* ------------------------------------------------ *)
lemma x_lt_test0 : N (-3) < Inf. proof. rewrite /= ltrue. qed. 
lemma x_lt_test1 : N 0    < Inf. proof. rewrite /= ltrue. qed. 
lemma x_lt_test2 : N 3    < Inf. proof. rewrite /= ltrue. qed. 

(* must fail *)
lemma x_lt_test3 (x : xint) : x < Inf. 
proof. try rewrite /= ltrue. rewrite /=. abort. 

(* must fail *)
lemma x_lt_test4 (x : xint) : x < x.
proof. try rewrite /= ltrue. rewrite /=. abort. 

(* must fail *)
lemma x_lt_test4 (x : xint) : Inf < x.
proof. try rewrite /= ltrue. rewrite /=. abort. 

(* ------------------------------------------------ *)
lemma cost_test0  [$u] :
`[: N 3, u.o : N 2] <= `[: Inf, u.o : Inf].
proof. rewrite /= ltrue. qed.

lemma cost_test1  [$u] :
`[: N 3, u.o : N 2] <= `[: Inf, u.o : Inf, ..].
proof. rewrite /= ltrue. qed.

lemma cost_test2 [$u] (x, y : xint) :
`[: x, u.o : y] <= `[: Inf, u.o : Inf]. 
proof. rewrite /= ltrue. qed.

lemma cost_test3 [$u] (x, y : xint) :
`[: x, u.o : y] <= `[: Inf, u.o : Inf, ..]. 
proof. rewrite /= ltrue. qed.

lemma cost_test4 [$u] (x, y : xint) :
`[: x, u.o : y] <= `[: x, u.o : y]. 
proof. rewrite /= ltrue. qed.

lemma cost_test5 [$u] (x, y : xint) :
`[: x, u.o : y] <= `[: x, u.o : y, ..]. 
proof. rewrite /= ltrue. qed.

(* must fail *)
lemma cost_test6 [$u] :
`[: N 3, u.o : N 2] <= `[: N 1, u.o : Inf].
proof. try rewrite /= ltrue. rewrite /=. abort.

(* must fail *)
lemma cost_test7 [$u] :
`[: N 3, u.o : N 2] <= `[: Inf, u.o : N 1].
proof. try rewrite /= ltrue. rewrite /=. abort.

(* must fail *)
lemma cost_test8 [$u] :
`[: N 3, u.o : N 2] <= `[: N 1, u.o : Inf, ..].
proof. try rewrite /= ltrue. rewrite /=. abort.

(* must fail *)
lemma cost_test9 [$u] :
`[: N 3, u.o : N 2] <= `[: Inf, u.o : N 1, ..].
proof. try rewrite /= ltrue. rewrite /=. abort.

(* must fail *)
lemma cost_test6 [$u] :
`[: N 3, u.o : N 2, ..] <= `[: Inf, u.o : Inf].
proof. try rewrite /= ltrue. rewrite /=. abort.

lemma cost_test7 [$u] :
`[: N 3, u.o : N 2] <= `[: .., ..].
proof. try rewrite /= ltrue. qed. 
