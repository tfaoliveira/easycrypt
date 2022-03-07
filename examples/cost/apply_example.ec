require import AllCore Int CHoareTactic StdBigop.
import Bigint.

schema cost_plus `{P} {e e' : int}: 
  cost[P : e + e'] = cost[P : e] + cost[P : e'] + N 1.

schema cost_times `{P} {e e' : int}: 
  cost[P : e * e'] = cost[P : e] + cost[P : e'] + N 1.

hint simplify cost_plus, cost_times.

(*********************)
(* Lemma application *)
(*********************)

module type H = { 
  proc o1 () : unit
  proc o2 () : unit  
}.

module type Adv (H0 : H) (H1 : H) = { proc a () : unit }.

module (MyAdv : Adv) (H0 : H) (H1 : H) = {
  proc a () = {
    var y;
    y <- 1 + 1 + 1 + 1;
    H0.o1();
    H1.o2();
    H0.o2();
  }
}.

lemma MyAdv_compl (k01 k02 k11 k12 : cost)
    (H0 <: H [o1 : [k01], o2 : [k02]])
    (H1 <: H [o1 : [k11], o2 : [k12]]) : 
    choare[MyAdv(H0, H1).a] 
      time `[:N 3, H0.o1 : N 1, H0.o2 : N 1, H1.o2 : N 1].
proof.
  by proc; do !(call(_: true)); auto.
qed.

module (MyH : H) = { 
  proc o1 () = {
    var z;
    z <- 1 + 1;
  }

  proc o2 () = {
    var z;
    z <- 1 + 1 + 1;
  }
}.

lemma MyH_compl1 : choare[MyH.o1] time `[:N 1] by proc; auto.
lemma MyH_compl2 : choare[MyH.o2] time `[:N 2] by proc; auto.
lemma MyH_compl : choare[MyH.o1] time `[:N 1] /\ choare[MyH.o2] time `[:N 2] 
    by split; [apply MyH_compl1 | apply MyH_compl2].

lemma advcompl_inst:  choare[MyAdv(MyH, MyH).a] time `[:N 8].
proof. 
  (* TODO: bunch of partial applications. Keep them as sanity checks? *)
  have H0 := MyAdv_compl. 
  have H1 := (MyAdv_compl `[:N 1]).
  have H2 := (MyAdv_compl `[:N 1] `[:N 2] `[:N 1] `[:N 2]).
  have H3 := (MyAdv_compl `[:N 1] `[:N 2] `[:N 1] `[:N 2] MyH _ _);
  [1: by apply MyH_compl1 | 2: by apply MyH_compl2].
  have U := H3 MyH _ _; 
  [1: by apply MyH_compl1 | 2: by apply MyH_compl2].

  clear H0 H1 H2 H3 U.

  apply (MyAdv_compl `[:N 1] `[:N 2] `[:N 1] `[:N 2] MyH _ _ MyH);
  [1: by apply MyH_compl1 | 
   2: by apply MyH_compl2 | 
   3: by apply MyH_compl1 | 
   4: by apply MyH_compl2 ].
qed.
