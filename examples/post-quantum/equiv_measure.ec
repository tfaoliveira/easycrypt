require import AllCore Distr.

module M = {
  proc f () = { 
    quantum var q : bool;
    var x : bool;
    q <- true;
    x <- measure q with !q;
    return x;
  } 
}.

equiv T : M.f ~ M.f : true ==> ={res}.
proof.
  proc.
  measure{1}.
  measure{2}.
  qinit{1}.
  qinit{2}.
  skip => //.
qed.

type t, u.
op (+) : u -> u -> u.
op u0 : u.
axiom add0u u : u0 + u = u.

op du : u distr.

clone MUniFinFun as FD with type t <= t.

module QRO = { 
   var fro : t -> u
   proc init () = { 
      fro <$ FD.dfun (fun _ => du);
   }
 
   proc qro {t : t, u : u} = { 
      (t, u) <* U[(t, u + fro t)];
   }

   proc ro1 (t : t) : u = { 
     return (fro t);
   } 
  
   proc ro2 (t : t) : u = { 
     quantum var t_ : t;
     quantum var u_ : u;
     var u : u;
     t_ <- t;
     u_ <- u0;
     (t_, u_) <* U[(t_, u_ + fro t_)];
     u <- measure u_ with u_;   (* FIXME QUANTUM: add a notation for measure u_ *)
     return u;
   }

   proc ro3 (t : t) : u = { 
     quantum var t_ : t;
     quantum var u_ : u;
     var u : u;
     t_ <- t;
     u_ <- u0;
     qro{t_, u_};
     u <- measure u_ with u_;   
     return u;
   }
}.

equiv ro1_ro2 : QRO.ro1 ~ QRO.ro2 : ={QRO.fro, t} ==> ={QRO.fro, res}.
proof.
  proc.
  (* FIXME QUANTUM: We should integrate this in the wp *)
  measure{2}; U{2}; qinit{2}; qinit{2}.
  by skip => /> &m; rewrite add0u.
qed.

equiv ro2_ro3 : QRO.ro2 ~ QRO.ro3 : ={QRO.fro, t} ==> ={QRO.fro, res}.
proof.
  proc.
  (* FIXME QUANTUM: inline *) 
admitted.
(*
  inline QRO.qro.  
  measure{1}; U{1}; qinit{1}; qinit{1}.
  measure{2}; U{2}; qinit{2}; qinit{2}.
  by skip => /> &m.
qed.
*)

equiv qro_qro : QRO.qro ~ QRO.qro : ={QRO.fro}, ={t, u} ==> ={QRO.fro}, ={t,u}.
proof.
  proc.
  U.
  skip => />.
qed.

equiv qro_qro_glob : QRO.qro ~ QRO.qro : ={QRO.fro}, ={global, t, u} ==> ={QRO.fro}, ={global, t,u}.
proof.
  proc.
  U.
  skip => />.
qed.








   
  
  
