require import AllCore.

module M = { 
  var f : int -> int
  var c : int

  proc o {q r} = {
    c <- c + 1;
    q,r <* U[ (q, r + f q)];
  } 

}.

equiv o_o : M.o ~ M.o : q{1} = 0 /\ q{2} = 1, ={qarg} ==> true, ={r}.
proof.
  proc.
abort.

equiv o_o : M.o ~ M.o : q{1} = 0 /\ q{2} = 1, ={global, q,r} ==> true, ={global, q,r}.
proof.
  proc.
abort.



