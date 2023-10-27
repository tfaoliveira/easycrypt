require import AllCore.

module M = { 
  proc f (x: int) {q:int} = { 
    var y : int;
    y <- x + 1;
    if (x = x) { 
      y <- 1;
    } else { 
      y <- 0;
    }
    return y;
  }
}. 

equiv T : M.f ~ M.f : true, ={q} ==> ={res}, ={q}.
proof.
  proc.
  rcondt{1} ^if.
  + by auto. 
  rcondt{2} ^if.
  + by auto. 
  by wp; skip.
qed.

module N = { 
  proc f (x: int) {q:int} = { 
    var y : int;
    y <- x + 1;
    while (x <> x) { 
      y <- 1;
    } 
    return y;
  }
}. 

equiv T1 : N.f ~ N.f : ={x}, ={q} ==> ={res}, ={q}.
proof.
  proc.
  rcondf{1} ^while.
  + auto.
  rcondf{2} ^while.
  + auto. 
  by wp; skip.
qed.



