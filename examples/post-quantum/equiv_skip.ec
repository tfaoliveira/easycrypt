require import AllCore.

module M = { 
  proc c(x : int) = { return x + 1;} 

  proc qu(x : int) { q r: int} = { return x + 1;} 

}.

equiv c_c : M.c ~ M.c : ={x} ==> ={res}.
proof.
  proc.
  skip.
  done.
qed.

equiv qu_qu : M.qu ~ M.qu : ={x}, ={global, q, r} ==> ={res}, ={global, q, r}.
proof.
  proc.
  skip.
  done.
qed.

equiv qu_qu1 : M.qu ~ M.qu : ={x}, ={global, q,r} ==> ={res}.
proof.
  proc.
  skip.
  done.
qed.

equiv qu_qu_fail : M.qu ~ M.qu : ={x}, ={global, q,r} ==> ={res}, ={global, q}.
proof.
  proc.
  (* This does not work, and should not work *)
  (* skip. *)
abort.


