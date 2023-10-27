require import AllCore.

op swap_ ['a] (p : 'a * 'a) = (p.`2, p.`1).

module M = { 
  proc f1 (x:int) {q: int} = { 
    quantum var r : int;
    r <- 0;
    (q,r) <* U{swap_};
    (r,q) <* U{swap_};
    x <- x + 1;
    return x;
  }

  proc f2 (x:int) {q:int * int} = {
    var y : int;
    quantum var r : int;
    r <- 0;
    y <@ f1(x){q.`1};
    q <* U{swap_};
    x <@ f1(x){q.`2};
    (q.`2,r) <* U{swap_};
    return y;
  }

  proc f3(x:int){q:int, r:int} = { 
    var z;
    z <@ f2(x){q,r};
    return z;
  }
}.

equiv T : M.f3 ~ M.f2 : ={x}, ={(q,r)/q} ==> ={res}, ={(q,r)/q}.
proc.
inline{1} f2.
inline M.
abort. 

equiv T1 : M.f3 ~ M.f2 : ={x}, ={qarg} ==> ={res}, ={qarg}.
proc.
inline.
abort.



