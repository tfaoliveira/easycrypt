require import AllCore.

module M = { 
  quantum var q : int 

  proc c () = { 
    var x : int;
    var y, z;
    var w <- 3;

    y <- true;
    z <- 2;
  }

  proc f (x:bool) {z: int, z2: int} = { 
    return 3;
  }

  proc q () {a b : int, c : bool} = { 
    quantum var x : int;
            var x1 : int;
            var y : bool;
    quantum var z : int <- 3;
    quantum var w <- 3;
    quantum var l : (int * int) * int;
    
    (l.`1 as l1), (l.`2 as l2) <* U[((l1.`2, l1.`1), l2 + 1)];
    l <* U[l];
    l.`2 as v <* U[v + 1]; 
    x1 <- measure q, l.`1 as l1 with q + l1.`2;

    x1 <@ f(y){z, w};
    f(y){z, w};

    y <- true;
    z <- 2;
    x1 <- 2;
  }

  proc q1 {a b : int, c : bool} = { 
  }
}.

module M2 = { 
  var f : int -> int
  var c : int

  proc o {q r} = {
    c <- c + 1;
    (q, r) <* U[(q, r + f q)];
  } 

}.

lemma L : forall (x : int), equiv[M.q ~ M.q : ={a}, ={global,a} ==> true, ={a}].
proof.

lemma L : forall (x : int), equiv[M.q ~ M.q : ={a}, ={global,a} ==> true, ={a}].
proof.

print M.
