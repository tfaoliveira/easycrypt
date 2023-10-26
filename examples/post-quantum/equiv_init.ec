require import AllCore.

module M = {
  proc f1 {r:int} = {
    (* Can we really do that ? *)
    r <- 1;
  }

  proc f11 {q r:int} = {
    (* Can we really do that ? *)
    (q, r) <- (1,2);
  }

  proc f2 {r:int} = {
    quantum var q : int;
    q <- 1;
    q, r <* U [(q, r + q)];
  }
}.

equiv T11 : M.f1 ~ M.f1 : true, ={} ==> true, ={r}.
proof.
  proc.
  qinit.
  skip => //.
qed.

equiv T12 : M.f11 ~ M.f11 : true ==> ={q,r}.
proof.
  proc.
  qinit.
  skip => //.
qed.

equiv T12' : M.f11 ~ M.f11 : true, ={} ==> ={q}, ={r}.
proof.
  proc.
  qinit.
  skip => //.
qed.

equiv T : M.f2 ~ M.f2 : true, ={r} ==> true, ={r}.
proof.
  proc.
  conseq (: ={q}, ={q,r}).
  U => /=.
  qinit. 
  skip. move => /= -[??] [??] />.
qed.






