require import AllCore.

(* FIXME :

OK:
module M = { 
  var f : int -> int
  var c : int

  proc o (q r) = {
    c <- c + 1;
    (q,r) <- (q, r + f q);
  } 

}.

FAIL: 
module M = { 
  var f : int -> int
  var c : int

  proc o {q r} = {
    c <- c + 1;
    (q,r) <* U[ fun qr => let (q,r) = qr in (q, r + f q)];
  } 

}.
*)

module M = { 
  var f : int -> bool
  var c : int

  proc o {q r:int} = {
    c <- c + 1;
    (q,r) <* U[ fun qr => let (q,r) = qr in (q, r && f q)];
  } 

}.

(* FIXME *)
(*
equiv o_o : M.o ~ M.o : true, ={qarg} ==> true,  ={qarg}.
*)

equiv o_o : M.o ~ M.o : true, ={qarg} ==> true,  ={global}.
proof.
  proc.


