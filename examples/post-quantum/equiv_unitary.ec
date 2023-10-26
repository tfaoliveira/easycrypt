require import AllCore.

module M = {

  quantum var x : int

  proc f1 (y:int) {q r:int} = {
    (q, r) <* U[(q, q+r)];
    return y;
  } 

  proc f2 (y:int) {q r:int} = {
    (q, r) <* U[(q+r, r)];
    return y;
  } 

  proc f3 (y:int) {q r:int} = {
    (q, r) <* U[(q, q+r+1)];
    return y;
  } 

  proc g1 {x y:int} = {
    (x,y) <* U[(y,x)];
  }

  proc g2 {x y:int} = {
    (x,y) <* U[(x,y)];
  }

}.

equiv T : M.f1 ~ M.f1 : ={y}, ={M.x, q,r} ==> ={res}, ={q,M.x, r}.
proof.
  proc.
  U.
  rewrite /=.
  by skip => /> [].
qed.

(* This fail *)
(*
equiv T1 : M.f1 ~ M.f2 : ={y}, ={M.x, q/r,r/q} ==> ={res}, ={q/r,M.x, r/q}.
  proc.
  U.
*)

(* This fail *)
(*
equiv T2 : M.f1 ~ M.f3 : ={y}, ={M.x, q} ==> ={res}, ={q,M.x}.
  proc.
  U.
*)
 
(* This fail *)
(*
equiv T3 : M.g1 ~ M.g2 : true, ={x/y} ==> true, ={y}.
proof.
  proc.
  U.
*)

equiv T4 : M.g1 ~ M.g2 : true, ={x, y} ==> true, ={x,y}.
proof.
  proc.
  U.
  skip => /= -[??] /=.  
abort.

(* -------------------------- *)

module C = { 
  proc f () {x y: bool} = { 
    (x,y) <* U[(x, x ^ y)];
  } 

}.

(* This fail *)
(*
equiv C1 : C.f ~ C.f : true, ={x} ==> true, ={x}.
proof.
proc.
U.
*)

