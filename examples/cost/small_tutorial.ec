require import AllCore Xint Int List CHoareTactic StdBigop.
import Bigint.

module V = { var v : int }.

(*********************)
(* Expression's cost *)
(*********************)

(* Integer constants are free. *)
lemma free_int : cost(_:{})[true : 1] = N 0 by auto.

(* Variable lookups are free. *)
lemma free_var : cost(_:{x : int})[true : x] = N 0 by auto.

(* Same for global variables. *)
module A = { var x : int }.
lemma free_var_g : cost(_:{})[true : A.x] = N 0 by auto.

(* And logical variables. *)
lemma free_var_logical (a : int) : cost(_:{})[true : a] = N 0 by auto.


(* Everything else has a cost, that must be given by the user through 
   schemata. A schema allow to quantify over *expressions*, as in: *)
schema cost_plus `{P} {e e' : int}: 
  cost[P : e + e'] = cost[P : e] + cost[P : e'] + N 1.

schema cost_plus_true {e e' : int}: 
  cost[true : e + e'] = cost[true : e] + cost[true : e'] + N 1.

schema cost_times `{P} {e e' : int}: 
  cost[P : e * e'] = cost[P : e] + cost[P : e'] + N 1.

(* It can be instantiated manually with the [instantiate] tactic. *)
(* Syntax, where for every i, Pi can use memory mhm:
   instantiate intro_pat := 
   (sc_name memtype '(P1) ... '(Pn) expr1 ... exprm) *)
lemma foo_cost : cost(_:{})[true : 1 + 2] = N 1.
proof.
instantiate H  := (cost_plus_true {} 1 2).
instantiate H0 := (cost_plus      {} `(true) 1 2).
instantiate H2 := (cost_plus      {} `(_:true) 1 2).

(* We can also explicitely give the memory name, as follows: *)
instantiate H3 := (cost_plus      {} `(&mem: V.v = 2) 1 2). 
instantiate H4 := (cost_plus      {} `(&mem: V.v{mem} = 2) 1 2).

instantiate -> := (cost_plus      {} `(_:true) 1 2).
auto.
qed.

(* Instantiating manually can be avoided using simplification hints.  *)
hint simplify cost_plus.
hint simplify cost_times.

lemma foo_cost2 : cost(_:{})[true : 1 + 2] = N 1 by auto.

(* Schemata can have type variables, e.g. for lists. *)
require import List.
schema cost_cons ['a] {e : 'a} {l : 'a list} : 
    cost[true : e :: l] =   
    cost[true : e] + cost[true : l] + N 1.

schema cost_nil ['a] : cost[true : [<:'a>]] = N 1.

hint simplify cost_cons.
hint simplify cost_nil.
lemma foo_list : cost(_:{})[true: [1;2;3;4]] = N 5 by auto.


(****************************)
(* Modules and restrictions *)
(****************************)


module B = { 
  proc g (x : int, y : int) : int = {
    var r : int;
    r <- x + y;
    r <- r * x;
    return r * r;
  }

  proc f (x : int) : int = {
    var a : int;
    a <- x + 1;
    a <@ g(a,x);
  return a;
  }
}.

(* Assignements are free, only the variable evaluation has a cost. *)
lemma foo : choare[B.g : true ==> true] time `[:N 3].
proof. by proc; auto. qed.

(* Procedure calls are also free. *)
lemma foo3 : choare[B.f : true ==> true] time `[:N 4].
proof.
  by proc; call foo; auto. 
qed.

module C = { 
  proc f (x : int, y : int) : int = {
    var r : int;
    if (y < x) {
      r <- 1 + 1;
      r <- 1 + 1;
     } else {
      r <- 2 + 1;
      r <- 2 + 1;
    }
    return r;
  }
}.

schema cost_lt `{P} {e e' : int}: 
  cost[P : e < e'] = cost[P : e] + cost[P : e'] + N 1.
hint simplify cost_lt.

(* For if statements, the cost is the maximum of both branches, plus the cost of
   evaluating the if expression. *)
lemma foo4 : choare[C.f] time `[:N 3].
proof.
proc; auto.
qed.

module D = { 
  var g : int

  proc f (x : int, y : int) : int = {
    while (x < y) {
      x <- x + 1;
    }
    return x;
  }
}.

lemma foo5 (a : int) (b : int) :
  0 <= a <= b =>
  choare[D.f : x = a /\ y = b /\ x < y ==> true] 
    time `[:N (2 * (b - a) + 1)].
proof.
  move => [Ha Hb].
  proc => /=.
  (* The [while] tactic takes the following parameters:
     - invariant, 
     - deacreasing quantity qdec
     - number of loop iterations
     - cost of one loop body, when (qdec = k), given using a lambda. *)
  while (x <= y /\ y = b) (b - x) (b - a) time (fun _ => `[:N 1]).
  
  (* prove that the loop body preserves the invariant, and cost what
  was stated. *)
  by auto; smt ().
  
  (* prove that the if the invariant holds, and if the decreasing
     quantity is less or equal to zero, then we exit the loop. *)
  smt ().
  
  (* prove that either the wanted upper-bound is infinite, or the
    final cost is not infinite. *)
  by rewrite bigi_constC /subcond /#.
  
  (* prove that the invariant implies the post, that the decreasing
     quantity is initially smaller than the number of loop iterations,
     and that the cost of all iterations is smaller than the final
     cost. *)
  skip => * /=; split; 1: by smt().
  by rewrite big_constC !size_range /#.
qed.

(* Match example *)

module ExMatch = {
  proc gethead (l : int list) = {
    var x : int;
    match 1 :: 2 :: l with
    | [] => x <- 0;
    | a :: tail => x <- a + 1;
    end;
  }
}.

lemma test_match : choare[ExMatch.gethead] time `[:N 4].
proof.
  proc; match (::) 0 => //=.
   by skip=> /#.
   by auto.
qed.

(*********************)
(* Lemma application *)
(*********************)

module type H = { proc o () : unit }.

module type Adv (H0 : H) = { proc a () : unit }.

module (MyAdv : Adv) (H0 : H) = {
  proc a () = {
    var y;
    y <- 1 + 1 + 1 + 1;
    H0.o();
    H0.o();
  }
}.

lemma MyAdv_compl (H0 <: H) : 
  choare[MyAdv(H0).a] time `[:N 3, H0.o : N 2].
proof.
  by proc; do !(call(_: true)); auto. 
qed.

lemma MyAdv_compl_bis (k : cost) (H0 <: H [o : [k, ..]]) : 
  choare[MyAdv(H0).a] time `[:N 3, H0.o : 2].
proof.
  by proc; do !(call(_: true : [])); auto => /=. 
qed.

(* The same lemma, but in a section. *)
section.
  declare module H0 : H.
  
  lemma MyAdv_compl_loc : choare[MyAdv(H0).a] time [:N 3, H0.o : 2].
  proof. 
    by proc; do !(call(_: true : [])); auto. 
  qed.
end section.

module (MyH : H) = { 
  proc o () = {
    var z;
    z <- 1+1;
  }
}.

lemma MyH_compl : choare[MyH.o] time [:N 1] by proc; auto.

lemma advcompl_inst_bis : choare[MyAdv(MyH).a] time [:N 5].
proof.
 apply (MyAdv_compl_bis _ MyH MyH_compl). 
qed.

module Inv (Adv0 : Adv) (HI : H) = {
  module Adv1 = Adv0(HI)

  proc i () = {
    var z;
    z <- 1 + 1;
    Adv1.a();
  }
}.

(* Allow both formulations below: *)
(*     (Adv0 <: Adv [a : `{j, #H0.o : 0}])  *)
(*     (Adv0(H1) <: Adv [a : `{j, H1.o : 0}])  *)

lemma Inv_compl
    (j k : int)
    (Adv0 <: Adv [a : [j, #H0.o : k]]) 
    (H0   <: H) : 
    0 <= k =>
    choare[Inv(Adv0, H0).i] time [:N 1, Adv0.a : 1, H0.o : k ].
proof.
move => hk; proc.
call (_: true : []). 
move => i Hi /=; proc*; call(_: true : []); auto => /=.
by auto => /=; rewrite big_constz count_predT !size_range /#.
qed.

(* Alternative future syntax *)
(* lemma Inv_compl *)
(*     (Adv0 <: Adv[#])  *)
(*     (H0   <: H) :  *)
(*     0 <= k => *)
(*     choare[Inv(Adv0, H0).i] time [:N 1, Adv0.a : 1, H0.o : #Adv0.a[H0.o] ]. *)

lemma Inv_compl_inst (H1 <: H) :
  choare[Inv(MyAdv, H1).i] time [:N 4, H1.o : 2 ].
proof.
  by apply (Inv_compl _ _ MyAdv MyAdv_compl H1 _).
qed.


(**************************************************)
(* without self complexity *)
lemma Inv_compl_partial
    (k : int)
    (Adv0 <: Adv [a : [_, #H0.o : k]]) 
    (H0   <: H) : 
    0 <= k =>
    choare[Inv(Adv0, H0).i] time [: `_, Adv0.a : 1, H0.o : k]. 
proof.    
move => hk; proc.
call (_: true : []).
move => i Hi /=; proc*; call(_: true : []); auto => /=.
by auto => /=; rewrite big_constz count_predT !size_range /#.
qed.

lemma test_conseq :
  (forall (H0 <: H), choare[MyAdv(H0).a] time [: N 3, H0.o : 4]) =>
  forall (H0 <: H), choare[MyAdv(H0).a] time [: `_, H0.o : 5].
proof.
 move => Hyp H0.
 conseq (_: _ ==> _ : time [: N 3, H0.o : 4]).
 by apply (Hyp H0).
qed.

lemma Inv_compl_partial_inst (H1 <: H) :
  choare[Inv(MyAdv, H1).i] time [:`_, H1.o : 2 ].
proof.
  apply (Inv_compl_partial _ MyAdv _ H1) => //.
  move => H0.
  by conseq (MyAdv_compl H0). 
qed.

(**************************************************)
op kab : int.

module type AB (H0 : H) = {
  proc a () : unit [ kab, H0.o : 1 ]
}.

section.
 declare module H0 : H.
 declare module AB0 : AB.

 local module AB1 = AB0(H0).

 local module E = { 
   proc e () = {
     AB1.a();
   }
 }.

(**************************************************)
 module type MAB (H1 : H) (H2 : H)  = {
   proc a () : unit {H2.o}
 }.

 local module (MAB0 : MAB) (H1 : H) (H2 : H) = {
   proc a () = {
     H2.o();
     H0.o();
   }
 }.

 local module MAB1 = MAB0(H0).

 local module MAB2 = MAB0(H0, H0).

end section.

(**************************************************)
(* Bonus: expression's cost using a free operator *)
(**************************************************)

op free ['a] (x : 'a) : 'a.

axiom free_id ['a] (x : 'a) : free(x) = x.

schema free_id ['a] {e : 'a} : cost[true : free(e)] = N 0.

schema plus_cost_f {e e' : int}: cost[true : free(e) + free(e')] = N 1.

(* The schema below is valid for any operator with a call-by-value semantics. *)
schema plus_cost_e {e e' : int}: 
  cost[true : e + e'] = 
  cost[true : free(e) + free(e')] +
  cost[true : e] + cost[true : e'].

schema free_beta ['a, 'b] {f : 'a -> 'b} {k : 'a} :
  cost[true : (fun x => f x) k] = 
  cost[true : f (free k)] + cost[true : k] + N 1.

lemma foo_p_f : cost(_:{})[true : 1 + 2] = N 1.
proof.
instantiate -> := (plus_cost_e {} 1 2).
instantiate -> := (plus_cost_f {} 1 2) => //.
qed.

(* Remark: we cannot use hints there, because plus_cost_e is not terminating. *)

