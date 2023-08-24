require import AllCore CHoareTactic Xint.

axiom foo0 [$ a] : false. print foo0.

(* -------------------------------------------------------------------- *)
module type U = { proc o () : unit }.

lemma test1 [$ x y] :
  `[: N 3, x.a : N 4,  x.b : N 5, y.a : N 10] <= 
  `[: N 3, x.a : N 10, x.b : Inf, y.a : N 20].
proof. 
  auto.
qed.

axiom test2 [$ x y] :           (* false axiom, because of last field *)
  `[: N 3, x.a : N 4,  x.b : N 5, y.a : N 20] <= 
  `[: N 3, x.a : N 10, x.b : Inf, y.a : N 10].

lemma bar1 ['a] [$ u v] : false.
proof.
  try have ? := test2.           (* cannot infer all placeholders *)
  try have ? := test2<$ v v>.    (* agent name is used twice *)
  try have ? := test2<$ u u>.    (* agent name is used twice *)
  have ? := test2<$ u v>.
  have ? := test2<$ v u>.
abort.

(* same as `test2` *)
lemma bar0 [$ u v] :
  `[: N 3, u.a : N 4,  u.b : N 5, v.a : N 20] <=
  `[: N 3, u.a : N 10, u.b : Inf, v.a : N 10].
proof.
  have A := test2<$ v u>. 
  rewrite /= in A.
  clear A.

  try apply (test1<$ u v>). 
  try apply (test1<$ v u>).
  try apply (test1<$ u u>).

  try apply (test2<$ u u>).
  try apply (test2<$ v v>).         (* agent name v is used twice *)
  try apply (test2<$ v u>).         (* does not apply to the goal *)
  apply (test2<$ u v>).
qed.

(* changed first value *)
lemma bar1 [$ u v] :  
  `[: N 10, u.a : N 4,  u.b : N 5, v.a : N 20] <= 
  `[: N 3 , u.a : N 10, u.b : Inf, v.a : N 10].
proof. 
  try apply (test1<$ u v>). 
  try apply (test1<$ v u>). 
  try apply (test1<$ u u>). 
  try apply (test1<$ v v>). 

  try apply (test2<$ u v>). 
  try apply (test2<$ v u>). 
  try apply (test2<$ u u>). 
  try apply (test2<$ v v>). 
  try by auto.
abort.

(* TODO: cost: v2: test below is broken *)
(* lemma test3 ['a] [$ x] (H <: $U) (H1 <: $U) : *)
(*   `[: N 3, H.o : N 2, H1.o : N 4 , x.a : N 4 ] <= *)
(*   `[: Inf, H.o : Inf, H1.o : N 10, x.a : N 10]. *)
(* proof. *)
(*   (* check that this correctly rebinds H into H2 *) *)
(*   move: H => H2. *)
(*   auto. *)
(* qed. *)
