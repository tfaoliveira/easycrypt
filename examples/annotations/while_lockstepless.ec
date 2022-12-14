module M = {
  var i, x0, x1, x2, x3 : real
  var x : real Array4.t

  proc foo() = {
    @L0;
    x0 = x0 + x1;
    x1 = x0 - 2%r * x1;
    @L1;
    x2 = x2 + x3;
    x3 = x2 - 2%r * x3;
    @L2;
  }

  proc bar() = {
    i = 0;
    while (i < 2) {
      @L;
      x.[2 * i] = (x.[2 * i] - x.[2 * i + 1]) / 2;
      x.[2 * i + 1] = x.[2 * i] + x.[2 * i + 1];
      i += 1;
    }
    @Le;
  }
}.

(*Or not be.*)
equiv [M.f ~ M.g : true ==> true |
       { (L0, Le) -->            x0{1} = x{2}.[0] /\
                                 x0{1} = x{2}.[1] /\
                                 x0{1} = x{2}.[2] /\
                                 x0{1} = x{2}.[3] } ==>
       { (L1, L) --> i{2} = 1 => x0{1} = x{2}.[0] /\
                                 x0{1} = x{2}.[1] /\
                                 x0{1} = x{2}.[2] /\
                                 x0{1} = x{2}.[3]     ;
         (L2, L) --> i{2} = 0 => x0{1} = x{2}.[0] /\
                                 x0{1} = x{2}.[1] /\
                                 x0{1} = x{2}.[2] /\
                                 x0{1} = x{2}.[3]}  ].
proof.
admitted.
