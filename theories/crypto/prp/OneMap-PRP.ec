require import AllCore.
require import Distr SmtMap Dexcepted.

type D.

op dD: D -> D distr.
axiom dD_ll  x: is_lossless (dD x).

module RP = {
  var m  : (D, D) fmap
  var mi : (D, D) fmap

  proc init() = {
    m  <- empty;
    mi <- empty;
  }

  proc o(x : D): D = {
    var y;

    if (x \notin m) {
      y <$ (dD x) \ (rng m);
      m.[x]  <- y;
      mi.[y] <- x;
    }
    return oget m.[x];
  }

  proc oi(y : D) : D = {
    var x;

    if (y \notin mi) {
      x <$ (dD y) \ (rng mi);
      m.[x]  <- y;
      mi.[y] <- x;
    }
    return oget mi.[y];
  }
}.

op PermInv (m: ('a, 'a) fmap) (mi : ('a, 'a) fmap) =
  forall x y, m.[x] = Some y <=> mi.[y] = Some x.

module RP' = {
  var m : (D, D) fmap

  proc init() = {
    m <- empty;
  }

  proc o(x : D): D = {
    var y;

    if (x \notin m) {
      y     <$ (dD x) \ (rng m);
      m.[x] <- y;
    }
    return oget m.[x];
  }

  proc oi(y : D): D = {
    var x;

    if (!rng m y) {
      x     <$ (dD y) \ (dom m);
      m.[x] <- y;
    }
    return oget (find (fun _=> pred1 y) m);
  }
}.

lemma PermInv_sym (m mi : ('a, 'a) fmap):
  PermInv m mi => PermInv mi m.
proof. by move=> pi @/PermInv x y; rewrite pi. qed.

lemma PI_dom_rng (m : ('a, 'a) fmap) (mi : ('a, 'a) fmap):
  PermInv m mi => rng m = dom mi.
proof.
move=> pi; apply/fun_ext=> y; rewrite rngE eq_iff /= domE.
split=>[[x] /pi M_y_x|y_in_Mi].
+ by rewrite M_y_x.
by exists (oget mi.[y]); rewrite pi; apply/get_some/domE.
qed.

lemma PI_rng_dom (m : ('a, 'a) fmap) (mi : ('a, 'a) fmap):
  PermInv m mi => rng mi = dom m.
proof. by move=> /PermInv_sym; exact/PI_dom_rng. qed.

hoare PermInv_RP_o: RP.o:
  PermInv RP.m RP.mi
  ==> PermInv RP.m RP.mi.
proof.
proc; if=> //=.
auto=> /> &m ih; rewrite domE=> /= M_x y.
rewrite supp_dexcepted (PI_dom_rng _ _ ih) domE=> /> _ Mi_y.
rewrite /PermInv=> x' y'; rewrite !get_setE; case: (x' = x{m})=> //= [<<-|].
+ rewrite eq_sym; case: (y' = y)=> //= _.
  by move: (ih x' y')=> <-; rewrite M_x.
by rewrite eq_sym ih; case: (y' = y)=> //= ->>; rewrite Mi_y.
qed.

equiv RP_RP'_o:
  RP.o ~ RP'.o:
       ={arg}
    /\ RP.m{1} = RP'.m{2}
    /\ PermInv RP.m{1} RP.mi{1}
    ==>    ={res}
        /\ RP.m{1} = RP'.m{2}
        /\ PermInv RP.m{1} RP.mi{1}.
proof.
conseq (: _ ==> ={res} /\ ={m}(RP,RP'))
       PermInv_RP_o=> //=.
by sim.
qed.

hoare PermInv_RP_oi: RP.oi:
  PermInv RP.m RP.mi
  ==> PermInv RP.m RP.mi.
proof.
proc; if=> //=.
auto=> /> &m ih; rewrite domE=> /= Mi_y x.
rewrite supp_dexcepted /= (PI_rng_dom _ _ ih) domE=> /> _ M_x.
rewrite /PermInv=> x' y'; rewrite !get_setE; case: (x' = x)=> //= [<<-|].
+ rewrite eq_sym; case: (y' = y{m})=> //= _.
  by move: (ih x' y')=> <-; rewrite M_x.
by rewrite eq_sym ih; case: (y' = y{m})=> //= ->>; rewrite Mi_y.
qed.

equiv RP_RP'_oi:
  RP.oi ~ RP'.oi:
       ={arg}
    /\ RP.m{1} = RP'.m{2}
    /\ PermInv RP.m{1} RP.mi{1}
    ==>    ={res}
        /\ RP.m{1} = RP'.m{2}
        /\ PermInv RP.m{1} RP.mi{1}.
proof.
conseq (: _ ==> ={res} /\ ={m}(RP,RP'))
       PermInv_RP_oi=> //=.
proc; if=> //=.
+ move=> &1 &2 />; rewrite domE=> inv; split.
  + case: {-1}(RP.mi{1}.[y{2}]) (eq_refl (RP.mi{1}.[y{2}]))=> //= x.
    by rewrite (PI_dom_rng _ _ inv) domE=> ->.
  by rewrite (PI_dom_rng _ _ inv) domE.
+ auto=> /> &1 &2 inv; rewrite !domE=> /= Mi_y; split=> [x|_ x].
  + by rewrite (PI_rng_dom _ _ inv).
  rewrite (PI_rng_dom _ _ inv)=> -> //=.
  rewrite get_set_sameE oget_some.
  case: (findP (fun _=> pred1 y{2}) RP'.m.[x <- y]{2})=> /=.
  + move=> _ /(_ x _) @/pred1.
    + by rewrite mem_set.
    by rewrite get_set_sameE oget_some.
  move=> x' y' -> @/pred1 + <<-; rewrite oget_some (eq_sym x x').
  case: (x' = x)=> [->>|x'_neq_x] //=; rewrite get_set_neqE // -negP.
  by rewrite inv Mi_y.
auto=> /> &1 &2 inv; rewrite domE.
case: {-1}(RP.mi{1}.[y{2}]) (eq_refl (RP.mi{1}.[y{2}]))=> //= x Mi_y.
rewrite oget_some /pred1.
have -> //: find (fun _ x0=> x0 = y{2}) RP'.m{2} = Some x.
case: (findP (fun _ x0=> x0 = y{2}) RP'.m{2})=> //=.
+ move=> -> /=; rewrite negb_forall /=; exists x.
  rewrite negb_imply /= domE.
  by move: Mi_y; rewrite -(inv x y{2})=> ->.
move=> x' y' h + <<-.
move: (find_some_unique x x' (fun _ x=> x = y') RP'.m{2} _ h)=> /= => [/> x0|<<- //].
by rewrite inv Mi_y.
qed.
