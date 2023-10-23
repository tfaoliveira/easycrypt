require import AllCore.

module M = { 
  quantum var q_ : int
  var n, m : int

  proc c(x : int) = { n <- x; return x + 1;} 

  proc qu(x : int) { q r: int} = { 
    q_ <- 0;
    n <- x;
    return x + 1;
  } 

}.

import var M.

equiv e1 : M.c ~ M.c : ={x} ==> ={n}.
proof. admitted.

equiv e2 : M.c ~ M.c : 
  ={x} /\ m{1} = 1 /\ n{1} = 1 ==> ={n} /\ m{1} = 1.
proof.
  conseq e1.
  admit.
  admit.
qed.

equiv e2_1 : M.c ~ M.c : 
  ={x} /\ m{1} = 1 /\ n{1} = 1 ==> ={n} /\ m{1} = 1.
proof.
  conseq (: ={x} ==> ={n}).
  admit.
  admit.
  admit.
qed.

equiv e2_2 : M.c ~ M.c : 
  ={x} /\ m{1} = 1 /\ n{1} = 1 ==> ={n} /\ m{1} = 1.
proof.
  conseq (: ={x} ==>).
  admit.
  admit.
qed.

equiv e2_3 : M.c ~ M.c : 
  ={x} /\ m{1} = 1 /\ n{1} = 1 ==> ={n} /\ m{1} = 1.
proof.
  conseq (: ==> ={n}).
  admit.
  admit.
qed.

equiv e2_4 : M.c ~ M.c : 
  ={x} /\ m{1} = 1 /\ n{1} = 1 ==> ={n} /\ m{1} = 1.
proof.
  conseq (: ={n}).
  admit.
  admit.
qed.

equiv e2_5 : M.c ~ M.c : 
  ={x} /\ m{1} = 1 /\ n{1} = 1 ==> ={n} /\ m{1} = 1.
proof.
  conseq (: _).
  admit.
qed.

(* This fail *)
(*
equiv e2_fail : M.c ~ M.c : 
  ={x} /\ m{1} = 1 /\ n{1} = 1, ={global} ==> ={n} /\ m{1} = 1, ={global}.
proof.
  conseq e1.
*)

equiv e3 : M.qu ~ M.qu : ={x}, ={global,q,r} ==> ={n}, ={global,q,r}.
proof. admitted.

equiv e4 : M.qu ~ M.qu : 
  ={x} /\ m{1} = 1 /\ n{1} = 1, ={global,q,r} ==> ={n} /\ m{1} = 1, ={global,q,r}.
proof.
  conseq e3.
  admit.
  admit.
qed.

equiv e4_1 : M.qu ~ M.qu : 
  ={x} /\ m{1} = 1 /\ n{1} = 1, ={global,q,r} ==> ={n} /\ m{1} = 1, ={global,q,r}.
proof.
  conseq (: ={x} ==> ={n}).
  admit.
  admit.
  admit.
qed.

equiv e4_1_1 : M.qu ~ M.qu : 
  ={x} /\ m{1} = 1 /\ n{1} = 1, ={global,q,r} ==> ={n} /\ m{1} = 1, ={global,q,r}.
proof.
  conseq (: ={x} ==> ={n}, ={global,q,r}).
  admit.
  admit.
  admit.
qed.

(* FAIL *)
(*
equiv e4_1_fail : M.qu ~ M.qu : 
  ={x} /\ m{1} = 1 /\ n{1} = 1, ={global,q,r} ==> ={n} /\ m{1} = 1, ={global,q,r}.
proof.
  conseq (: ={x} ==> ={n}, ={global,q}).
qed.
*)

equiv e4_2 : M.qu ~ M.qu : 
  ={x} /\ m{1} = 1 /\ n{1} = 1, ={global,q,r} ==> ={n} /\ m{1} = 1, ={global,q,r}.
proof.
  conseq (: ={x} ==>).
  admit.
  admit.
qed.

equiv e4_3 : M.qu ~ M.qu : 
  ={x} /\ m{1} = 1 /\ n{1} = 1, ={global,q,r} ==> ={n} /\ m{1} = 1, ={global,q,r}.
proof.
  conseq (: ==> ={n}).
  admit.
  admit.
qed.

equiv e4_4 : M.qu ~ M.qu : 
  ={x} /\ m{1} = 1 /\ n{1} = 1, ={global,q,r} ==> ={n} /\ m{1} = 1, ={global,q,r}.
proof.
  conseq (: ={n}).
  admit.
  admit.
qed.

equiv e4_5 : M.qu ~ M.qu : 
  ={x} /\ m{1} = 1 /\ n{1} = 1, ={global,q,r} ==> ={n} /\ m{1} = 1, ={global,q,r}.
proof.
  conseq (: _).
  admit.
qed.


(* Same for statement *)
(* More work are needed, to have it *)

equiv e5_1 : M.qu ~ M.qu : 
  ={x} /\ m{1} = 1 /\ n{1} = 1, ={global,q,r} ==> ={n} /\ m{1} = 1, ={global,q,r}.
proof.
  proc.
  conseq (: ={x} ==> ={n}).
  admit.
  admit.
  admit.
qed.

equiv e5_1_1 : M.qu ~ M.qu : 
  ={x} /\ m{1} = 1 /\ n{1} = 1, ={global,q,r} ==> ={n} /\ m{1} = 1, ={global,q,r}.
proof.
  proc.
  conseq (: ={x} ==> ={n}, ={global,q,r}).
  admit.
  admit.
  admit.
qed.

(* FAIL *)
(*
equiv e5_1_fail : M.qu ~ M.qu : 
  ={x} /\ m{1} = 1 /\ n{1} = 1, ={global,q,r} ==> ={n} /\ m{1} = 1, ={global,q,r}.
proof.
  proc.  
  conseq (: ={x} ==> ={n}, ={global,q}).
qed.
*)

equiv e5_2 : M.qu ~ M.qu : 
  ={x} /\ m{1} = 1 /\ n{1} = 1, ={global,q,r} ==> ={n} /\ m{1} = 1, ={global,q,r}.
proof.
  proc.
  conseq (: ={x} ==>).
  admit.
  admit.
qed.

equiv e5_3 : M.qu ~ M.qu : 
  ={x} /\ m{1} = 1 /\ n{1} = 1, ={global,q,r} ==> ={n} /\ m{1} = 1, ={global,q,r}.
proof.
  proc.
  conseq (: ==> ={n}).
  admit.
  admit.
qed.

equiv e5_4 : M.qu ~ M.qu : 
  ={x} /\ m{1} = 1 /\ n{1} = 1, ={global,q,r} ==> ={n} /\ m{1} = 1, ={global,q,r}.
proof.
  proc.
  conseq (: ={n}).
  admit.
  admit.
qed.

equiv e5_5 : M.qu ~ M.qu : 
  ={x} /\ m{1} = 1 /\ n{1} = 1, ={global,q,r} ==> ={n} /\ m{1} = 1, ={global,q,r}.
proof.
  proc.
  conseq (: _).
  admit.
qed.


(* --------------------------------------------------------- *)

module N = { 
  quantum var x : int * int
  quantum var y : int * (int * int)

  proc f() = {}

}.

import var N.

equiv T : N.f ~ N.f : true, ={x,y} ==> true, ={x,y}.
conseq (: _, ={x.`1, x.`2, y.`2.`1, y.`1, y.`2.`2}).
conseq (: _, ={x.`1, x.`2, y.`2, y.`1}).
conseq (: _, ={y.`1, x, y.`2}).
(* FAIL *)
(* conseq (: _, ={x, y.`2}). *)
admitted.

