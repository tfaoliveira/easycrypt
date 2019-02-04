require import AllCore DBool.


module Test = {
  proc t () : int = { return 5; }
  proc toto () = {
    var a,b,c,d,e,f;
    a <- 1;
    b <- 2;
    c <- 3;
    d <$ {0,1};
    e <@ t();
    if (d) {
      f <- a + (b - c + 4) * e;
    } else {
      f <- a * 7 - c + 3 * b;
    }
    return f;
  }
}.


lemma adv : equiv [ Test.toto ~ Test.toto : true ==> ={res} ].
proof.
proc.
test { _ } .
test { #name }.
test { ? }.
test { <- }.
test { <@ }.
test { while }.
test { {2}if }.
test { {-2}if }.
test { {5}<- }.
test { [{1}if:{4}while] }.
test { [{1}if:{4}while]{<+1:-2>} }.
test { x <- 3 ; <- }.
test { if ; while (true) _ ; <- ; while ; if }.
test { if (false) }. (* match a if (false) with no condition on its branches *)
test { if (false) _ }. 
test { if (false) else { <-; _ } }. (* match in else branch *)
test { if (false) { <-; _ } }. (* match in true branch *)
test { [:if] }.
test { [:if]{2} }.
test { s1 ; s2 }.
test { s1 ;; s2 }.
test { [while:] as name }.
test { { if ; <@ ; <- ; <$ ; while } as name }.
test { if* }.
test { <-+ }.
test { { <- | <$ } * }.
test { <@? }.
test { <$ *! }.
test { { <$ ; <$ ; <@ } {1:3}! }.
test { {5}{ _ <- #expression } }.
test { (_,#x) <$ _ }.
test { _ <@ #f(_) }.  (* matches also A.guess(g^x,g^y,g^z) *)
test { (_,_) as toto <- _ }.
test { #y <@ #G(#A,P)._ (_,_,_) }.
test { #C.counter <- _.counter + 1 }. (* matches a global variable that is named counter, but the module may be anything *)
test { _.counter <- _.counter + 1 }. (* matches a global variable that is named counter, but the module may be anything *)
test { _ <@ _.#procname(#args1,#args2) }.
test { if (_ <= _ as cond) _ else _ }.
test { if (#cond) #strue else #sfalse }.
test { if (#cond) #strue }.
test { if (#cond) else #sfalse }.
test { if _ #strue }.
test { if (#cond) _ else #sfalse }.
test { if _ #strue }.
test { if _ else #sfalse }.
admitted.
