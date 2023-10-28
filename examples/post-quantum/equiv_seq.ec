require import AllCore.


module M = { 
  proc f {q:int} = { 
    quantum var r:int;

    r <- 0;
    q,r <* U[(q+r, r)];
  }
}.

equiv T: M.f ~ M.f : true, ={q} ==> true, ={q}.
proof.
  proc. 
  seq 1 1 : (: ={r}, ={q,r}).
  qinit; skip => //.
  conseq (: ={r} , ={q,r}).
  U; skip => //.
qed.
