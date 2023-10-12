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

  proc f (x:bool) { z: int} = { 
    return 3;
  }

  proc q () {a b : int, c : bool} = { 
    quantum var (x,x1): int * int;  (* Why this is useful *)
    quantum var y, z;
    quantum var w <- 3; (* TODO: translate this to quantum init *)
    quantum var l;
    l <* U[3];
    l <* U[l];
    x <* U[3]; 
    x <- measure q with 3;

    x <@ f(y){(z,(y, x.`2)), x.`1}; 
    x <@ f(y){z};   
    f(y){z};

    y <- true;
    z <- 2;
  }

  proc q1 {a b : int, c : bool} = { 
  }

}.

