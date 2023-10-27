require import AllCore.

module M = { 

  quantum var r : int * int
  var y : int
  proc f(x:int) { q : int * int} = {
    return x;
  }

}.


equiv T &m : M.f ~ M.f : true ==> true.
proof.
  proc.
  case (x{1} = x{2}).
  case (x{1} = M.y{1}).
(* FAIL *)
(*  case (q.`1{1} = M.y{1}). *)
(* FAIL *)
(*  case (M.r.`1{1} = x{2}). *)
(* Is it ok ? *)
  case (x{1} = M.y{m}).
admitted.

equiv T1 &m : M.f ~ M.f : true ==> true.
proof.
  proc.
  exists * x{1}.
  elim * => z.
  exists * M.y{1}. 
  elim * => y_.
  exists * q{1}.
  (* does nothing, should we add a warning ? *)
  elim *. 
  exlim M.y{1}, x{2} => y__ x2_.
admitted.
