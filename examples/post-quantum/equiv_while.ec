require import AllCore.

module M = { 

  proc f(x:int) {qx qs: int} = { 
    quantum var qi;
    var i, s: int;
    s <- 0;
    i <- 0;
    qi <- 0;
    while (i < x) { 
      s <- s + x;
      (qx, qs) <* U[(qx, qs + qx)];
      i <- i + 1;
      qi <* U[qi + 1];
    }
    return s;
  } 

}.


equiv T x_ : M.f ~ M.f : 
  ={x} /\ (0 <= x /\ x_ = x /\ qx = x /\ qs=0){1}, ={qx,qs} ==> 
  ={res} /\ (res = x_ * x_ /\ qx = x_ /\ qs = res){1}, ={qx, qs}.
proof.
  proc.
  conseq (:  ={s,qi} /\ (s = x_ * x_ /\ qx = x_ /\ qs = s /\ qi = i){1},
             ={qx, qs, qi} ).
  + by move=> &1 &2 />. 
  while (={s, qi, i} /\ (s = i * x /\ qx = x /\ qs = s /\ qi = i /\ i <= x){1}).
  + U; wp; U; wp; skip => />. 
    admit.
  qinit; wp; skip => />.
  admit.
qed.

equiv T' x_ : M.f ~ M.f : 
  ={x} /\ (0 <= x /\ x_ = x /\ qx = x /\ qs=0){1}, ={qx,qs} ==> 
  ={res} /\ (res = x_ * x_ /\ qx = x_ /\ qs = res){1}, ={qx, qs}.
proof.
  proc.
  while (={s, qi, i} /\ (s = i * x /\ qx = x /\ qs = s /\ qi = i /\ i <= x){1}).
  + U{1}; U{2}; wp; U; wp; skip => />. 
    admit.
  qinit; wp; skip => />.
  admit.
qed.

