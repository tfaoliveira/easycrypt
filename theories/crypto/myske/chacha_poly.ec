require import AllCore List Int IntDiv Real SmtMap Distr DBool DList DProd FSet PROM SplitRO FelTactic.

require (****) Subtype Ske RndProd Indistinguishability Monoid.
import StdOrder IntOrder RealOrder.

(* TODO: this come from eclib/JUtil.ec *)
op map2 ['a, 'b, 'c] (f:'a -> 'b -> 'c) (s:'a list) (t:'b list) = 
  with s = "[]"   , t = "[]" => []
  with s = _ :: _ , t = "[]" => []
  with s = "[]"   , t = _ :: _ => []
  with s = x :: s', t = y :: t' => f x y :: map2 f s' t'.

lemma map2_zip (f:'a -> 'b -> 'c) s t : 
  map2 f s t = map (fun (p:'a * 'b) => f p.`1 p.`2) (zip s t).
proof.
  by elim: s t => [ | s1 s hrec] [ | t1 t] //=;rewrite hrec.
qed.

lemma size_map2 (f:'a -> 'b -> 'c) (l1:'a list) l2 : size (map2 f l1 l2) = min (size l1) (size l2).
proof. by rewrite map2_zip size_map size_zip. qed.

lemma nth_map2 dfla dflb dflc (f:'a -> 'b -> 'c) (l1:'a list) l2 i: 
  0 <= i < min (size l1) (size l2) => 
  nth dflc (map2 f l1 l2) i = f (nth dfla l1 i) (nth dflb l2 i).
proof.
  elim: l1 l2 i => [ | a l1 hrec] [ | b l2] i /=; 1..3:smt(size_ge0).
  case: (i=0) => [->> // | hi ?].
  apply hrec;smt().
qed.

(* -------------------------------------------------------------------------- *)

theory Byte.
  type byte.

  clone include MFinite with 
    type t <- byte
    rename "dunifin" as "dbyte".
   
  op zero : byte.
  op (+^) : byte -> byte -> byte.

  clone import Monoid as MB with 
    type t <- byte,
    op idm <- zero,
    op (+) <- (+^).

  axiom addK b : b +^ b = zero.

  lemma xorK1 b1 b2 : b1 = b1 +^ b2 +^ b2.
  proof. by rewrite -addmA addK addm0. qed.

end Byte.
import Byte.

type bytes = byte list.

(* -------------------------------------------------------------------------- *)
theory Key.
  type key.     (* chacha key *)
  clone include MFinite with 
    type t <- key
    rename "dunifin" as "dkey".
end Key.
import Key.

theory Nonce.
  type nonce.     (* chacha nonce *)
  clone MFinite with 
    type t = nonce
    rename "dunifin" as "dnonce".
end Nonce.
import Nonce.

(* -------------------------------------------------------------------------- *)
theory C.

  op max_counter : int.

  axiom gt0_max_counter : 0 < max_counter.

  clone include Subtype with 
    type T <- int,
    pred P <- fun (i:int) => 0 <= i < max_counter + 1
    rename [type] "sT" as "counter"
           [op] "insubd" as "ofint".

  clone FinType.FinType with 
    type t = counter,
    op enum = List.map ofint (iota_ 0 (max_counter + 1)),
    op card = max_counter
    proof *.
  realize enum_spec.  
  proof.
    move=> c; rewrite count_uniq_mem.
    + apply map_inj_in_uniq; last by apply iota_uniq.
      move=> x y /mema_iota hx /mema_iota hy heq.
      by rewrite -(insubdK x) 1:// -(insubdK y) 1:// heq.
    have -> // : c \in enum.  
    rewrite /enum mapP; exists (val c).
    by rewrite mema_iota /= valP valKd.
  qed.

end C.

clone FinType.FinProdType as NonceCount with
  type t1 <- nonce, type t2 <- C.counter,
  theory FT1 <- Nonce.MFinite.Support, theory FT2 <- C.FinType.

(* -------------------------------------------------------------------------- *)

abstract theory GenBlock.
  type block.
  op block_size : int.
  axiom ge0_block_size : 0 <= block_size.

  clone include Subtype with
    type T <- bytes, 
    type sT <- block,
    pred P <- fun (l:bytes) => size l = block_size
    rename [op] "val" as "bytes_of_block".

  op dblock =  dmap (dlist dbyte block_size) insubd.

  lemma dblock_ll : is_lossless dblock.
  proof. apply dmap_ll; apply dlist_ll; apply dbyte_ll. qed.
  
  lemma dblock_uni: is_uniform dblock.
  proof. 
    apply dmap_uni_in_inj.
    + move=> x y hx hy heq.
      rewrite -(insubdK x) 1:(supp_dlist_size _ _ _ ge0_block_size hx) //.
      by rewrite -(insubdK y) 1:(supp_dlist_size _ _ _ ge0_block_size hy) // heq.
    by apply dlist_uni; apply dbyte_uni.
  qed.

  lemma dblock_fu: is_full dblock.
  proof.
   move=> x; rewrite supp_dmap; exists (bytes_of_block x).
   rewrite valKd /= -(valP x); apply dlist_fu => ??; apply dbyte_fu.
  qed.
 
  lemma dblock_funi: is_funiform dblock.
  proof. apply is_full_funiform; [apply dblock_fu | apply dblock_uni]. qed.

  op zero = insubd (mkseq (fun _ => Byte.zero) block_size).

  op (+^) (b1 b2:block) =
     insubd (map2 (+^) (bytes_of_block b1) (bytes_of_block b2)).
 
  lemma nth_xor x y i :
     0 <= i < block_size =>
     nth Byte.zero (bytes_of_block (x +^ y)) i =
     nth Byte.zero (bytes_of_block x) i +^ nth Byte.zero (bytes_of_block y) i.
  proof. 
    move=> hi; rewrite /(+^) !insubdK ?size_map2 ?valP //.
    rewrite !(nth_map2 Byte.zero Byte.zero) ?valP //.
  qed.

  lemma nth_zero i : nth Byte.zero (bytes_of_block zero) i = Byte.zero. 
  proof.
    rewrite /zero insubdK ?size_mkseq; 1:smt (ge0_block_size).
    smt (nth_mkseq nth_neg nth_default size_mkseq).
  qed.

  clone import Monoid as MB with 
    type t <- block,
    op idm <- zero,
    op (+) <- (+^)
    proof *.
  realize Axioms.addmA.
  proof.
    move=> x y z; apply val_inj; apply (eq_from_nth Byte.zero); rewrite !valP //.
    by move=> i hi; rewrite !nth_xor // Byte.MB.addmA. 
  qed.
  realize Axioms.addmC.
  proof.
    move=> x y; apply val_inj; apply (eq_from_nth Byte.zero); rewrite !valP //.
    by move=> i hi; rewrite !nth_xor // Byte.MB.addmC.
  qed.
  realize Axioms.add0m.
  proof.
    move=> x; apply val_inj; apply (eq_from_nth Byte.zero); rewrite !valP //.
    by move=> i hi; rewrite !nth_xor // nth_zero Byte.MB.add0m.
  qed.

  lemma addK b : b +^ b = zero.
  proof.
    apply val_inj; apply (eq_from_nth Byte.zero); rewrite !valP //.
    by move=> i hi; rewrite nth_xor // Byte.addK nth_zero.
  qed.

  lemma xorK1 b1 b2 : b1 = b1 +^ b2 +^ b2.
  proof. by rewrite -addmA addK addm0. qed.

end GenBlock.

(* block : [poly_tin; poly_tout; extra_block] *)
clone import GenBlock as Poly_in 
  rename "block" as "poly_in".
hint solve 0 random : dpoly_in_ll dpoly_in_funi dpoly_in_fu. 

clone import GenBlock as Poly_out 
  rename "block" as "poly_out".
hint solve 0 random : dpoly_out_ll dpoly_out_funi dpoly_out_fu. 

clone import GenBlock as TPoly with 
  op block_size = poly_in_size + poly_out_size 
  proof ge0_block_size by smt (ge0_poly_in_size ge0_poly_out_size) 
  rename "block" as "poly".
hint solve 0 random : dpoly_ll dpoly_funi dpoly_fu. 

clone import GenBlock as Extra_block
  rename "block" as "extra_block".
hint solve 0 random : dextra_block_ll dextra_block_funi dextra_block_fu. 
 
clone import GenBlock as Block
  with op block_size = poly_in_size + poly_out_size + extra_block_size
  proof ge0_block_size by smt (ge0_poly_in_size ge0_poly_out_size ge0_extra_block_size).
hint solve 0 random : dblock_ll dblock_funi dblock_fu. 

axiom gt0_block_size : 0 < block_size.

op extend (bs:bytes) : block = 
  Block.insubd (take block_size bs ++ mkseq (fun _ => Byte.zero) (block_size - size bs)).

lemma nth_extend m i : 0 <= i < block_size => 
  nth Byte.zero (bytes_of_block (extend m)) i = 
    if i < size m then  nth Byte.zero m i else Byte.zero.
proof.
  move=> [h0i hi]; rewrite /extend Block.insubdK.
  + by rewrite size_cat size_mkseq size_take 1:ge0_block_size /#.
  rewrite nth_cat size_take 1:ge0_block_size; smt (nth_take nth_mkseq).
qed.

(* -------------------------------------------------------------------------- *)
op chacha20_block : key -> nonce -> C.counter -> block.

(* -------------------------------------------------------------------------- *)
(* Functional definition of chacha20                                          *)

op gen_ctr_round (merge: bytes -> block -> bytes) genblock (k:key) (n:nonce) (round_st : bytes * bytes * int) =
  let (cph,m,c) = round_st in
  let stream = genblock k n (C.ofint c) in
  (cph ++ merge m stream, drop block_size m, c + 1).

op gen_CTR_encrypt_bytes merge genblock key nonce counter m =
  let len = size m in
  let rounds = (len %/ block_size) + b2i (len %% block_size <> 0) in 
  (iter rounds (gen_ctr_round merge genblock key nonce) ([], m, counter)).`1.

op take_xor (m:bytes) (stream : block) = 
  take (size m) (bytes_of_block (extend m +^ stream)).

op map2_xor (m:bytes) (stream : block) = 
  map2 Byte.(+^) m (bytes_of_block stream).

(* This correspond exactly to the definition used in the functional correctness proof *)

op chacha20_CTR_encrypt_bytes key nonce counter m =
  gen_CTR_encrypt_bytes map2_xor chacha20_block key nonce counter m.

lemma take_xor_map2_xor m str: map2_xor m str = take_xor m str.
proof.
  apply (eq_from_nth Byte.zero).
  + by rewrite size_map2 Block.valP size_take 1:size_ge0 Block.valP.
  rewrite size_map2 Block.valP => j hj.
  rewrite (nth_map2 Byte.zero Byte.zero) ?Block.valP 1://.
  rewrite nth_take 1:size_ge0 1:/# Block.nth_xor 1:/#; congr.
  smt (nth_extend).
qed.

lemma iter_gen_ctr_round_nil_cat merge genblock k n c m i j : 
  let round = gen_ctr_round merge genblock k n in
  iter i round (c, m, j) = 
     let (c', m', j') = iter i round ([], m, j) in
     (c ++ c', m', j').
proof.
  move=> round.
  elim /natind : i j m c => [i hi| i hi hrec] j m c; 1: by rewrite !iter0 //= cats0.
  rewrite !iterS //= {1 2}/round /gen_ctr_round hrec. 
  by case : (iter _ _ _) => /= c' p' j'; rewrite catA.
qed.

lemma iter_gen_ctr_round_S merge genblock k n c m i j: 
  let round = gen_ctr_round merge genblock k n in
  0 <= i =>
  iter (i + 1) round (c, m, j) = 
    let (c', m', j') = iter i round ([], drop block_size m, j + 1) in 
    (c ++ merge m (genblock k n (C.ofint j)) ++ c', m', j').
proof.  
  by move=> round hi; rewrite iterSr // {2}/round /gen_ctr_round /= iter_gen_ctr_round_nil_cat.
qed.

lemma iter_gen_ctr_round_nil merge genblock k n i j:
  (forall str, merge [] str = []) =>
  let round = gen_ctr_round merge genblock k n in
  iter i round ([], [],j) = ([], [], max j (j + i)).
proof.
  move=> hm round; elim /natind: i j => [i hi| i hi hrec] j; 1: by rewrite iter0 // /#.
  rewrite iter_gen_ctr_round_S // drop_oversize 1:[smt(gt0_block_size)].
  rewrite hrec /= hm /#.
qed.

lemma gen_CTR_encrypt_bytes0 merge genblock k n c :
  (forall str, merge [] str = []) =>
  gen_CTR_encrypt_bytes merge genblock k n c [] = [].
proof.
  by move=> hm; rewrite /gen_CTR_encrypt_bytes /= iter_gen_ctr_round_nil.
qed.

lemma gen_CTR_encrypt_bytes_cons merge genblock k n c m:
  (forall str, merge [] str = []) =>
  gen_CTR_encrypt_bytes merge genblock k n c m = 
  merge m (genblock k n (C.ofint c)) ++ 
    gen_CTR_encrypt_bytes merge genblock k n (c+1) (drop block_size m).
proof.
  move=> hm; rewrite /gen_CTR_encrypt_bytes /=; have h0s := size_ge0 m.
  case : (size m < block_size) => hs.
  + have hb : 0 <= size m < `|block_size| by smt().
    rewrite divz_small 1:// modz_small //= size_eq0.
    case: (m = []) => [->> | hne] @/b2i /=;1: by rewrite !iter0 // hm.
    rewrite (iter_gen_ctr_round_S _ _ _ _ _ _ 0) // iter0 //=.
    by rewrite drop_oversize 1:/# /= iter0.
  have -> : size m = block_size + size (drop block_size m).
  + by rewrite -{1}(cat_take_drop block_size m) size_cat size_take 1:ge0_block_size /#.
  have /= -> := divzMDl 1; 1: smt(gt0_block_size).
  rewrite modzDl -addzA addzC iter_gen_ctr_round_S; 1: smt (size_ge0 gt0_block_size).
  by case: (iter _ _ _) => />.
qed.

(* -------------------------------------------------------------------------- *)
(* Functional definition of poly1305                                          *) 

type polynomial.

op topol : bytes -> bytes -> polynomial.
op max_ad_size : int.
op max_cipher_size : int.
axiom max_cipher_size_ok : max_cipher_size <= C.max_counter * block_size.

op valid_topol (a:bytes) (c:bytes) = 
  size a <= max_ad_size /\ size c <= max_cipher_size.

axiom topol_inj a1 c1 a2 c2:
  valid_topol a1 c1 => valid_topol a2 c2 =>
  topol a1 c1 = topol a2 c2 => a1 = a2 /\ c1 = c2.

op poly1305_eval : poly_in -> polynomial -> poly_out.

op (+) : poly_out -> poly_out -> poly_out.
op (-) : poly_out -> poly_out -> poly_out.

op poly1305 (r:poly_in) (s:poly_out) (p:polynomial) = s + poly1305_eval r p.

op mk_rs (b:block) = 
  let b = take (poly_in_size + poly_out_size) (bytes_of_block b) in
  (Poly_in.insubd (take poly_in_size b), Poly_out.insubd (drop poly_in_size b)).

op genpoly1305 genblock (k:key) (n:nonce) (p:polynomial) = 
  let (r,s) = mk_rs (genblock k n (C.ofint 0)) in
  poly1305 r s p.
  
axiom poly_out_sub_add (p1 p2: poly_out) : p1 = p1 - p2 + p2.
axiom poly_out_add_sub (p1 p2: poly_out) : p1 = p1 + p2 - p2.
axiom poly_out_add_sub' (p1 p2: poly_out) : p1 = p1 + (p2 - p2).
axiom poly_out_swap (t p1 p2:poly_out) : t - p1 + p2 = t + (p2 - p1).

(* -------------------------------------------------------------------------- *)
type message = bytes.
type associated_data = bytes.
type tag = poly_out.

type plaintext = nonce * associated_data * message.
type ciphertext = nonce * associated_data * message * tag.

clone import Ske.SKE_RND with
  type key <- key,
  type plaintext <- plaintext,
  type ciphertext <- ciphertext.

module ChaChaPoly = {
  proc init() = {}
  
  proc kg () = { var k; k <$ dkey; return k; }
  
  proc enc (k : key, nap : nonce * associated_data * message) : 
     nonce * associated_data * message * tag = {
    var n, a, p, c, t;
    (n,a,p) <- nap;
    c <- gen_CTR_encrypt_bytes take_xor chacha20_block k n 1 p;
    t <- genpoly1305  chacha20_block k n (topol a c);
    return (n,a,c,t);
  }
  
  proc dec(k : key, nact : nonce * associated_data * message * tag) :
    (nonce * associated_data * message) option = {
    var n, a, c, p, t, t', result;
    result <- None;
    (n,a,c,t) <- nact;
    t' <- genpoly1305 chacha20_block k n (topol a c);
    if (t = t') {
      p <- gen_CTR_encrypt_bytes take_xor chacha20_block k n 1 c;
      result <- Some (n,a,p);
    }
    return result;
  }

}.

(* --------------------------------------------------------------------------- *)

module type CC = {
  proc cc (k:key, n:nonce, c: C.counter) : block
}.

module type FCC = {
  proc * init () : unit
  include CC
}.

module ChaCha(CC:CC) = {
  proc enc(k:key, n:nonce, p:message) : bytes = {
    var i, z, c;
    c     <- [];
    i     <- 1;
    while (p <> []) {
      z <@ CC.cc(k, n, C.ofint i);
      c <- c ++ take (size p) (bytes_of_block (extend p +^ z));
      p <- drop block_size p;
      i <- i + 1;
    }
    return c;
  }
}.

module Poly(CC:CC) = {
  proc mac(k:key, n: nonce, a: associated_data, c: message) : tag = {
    var b, r, s;
    b     <@ CC.cc(k, n, C.ofint 0);
    (r,s) <- mk_rs b; 
    return poly1305 r s (topol a c);
  }
}.

module GenChaChaPoly(CC:FCC) : SKE = {
  include CC[init]
  include ChaChaPoly[kg]
  
  proc enc (k : key, nap : nonce * associated_data * message) : 
    nonce * associated_data * message * tag = {
    var n, a, p, c, t;
    (n,a,p) <- nap;
    c <@ ChaCha(CC).enc(k,n,p);
    t <@ Poly(CC).mac(k,n,a,c);
    return (n,a,c,t);
  }

  proc dec(k : key, nact : nonce * associated_data * message * tag) :
    (nonce * associated_data * message) option = {
    var n, a, c, p, t, t', result;
    result <- None;
    (n,a,c,t) <- nact;
    t' <@ Poly(CC).mac(k,n,a,c);
    if (t = t') {
      p <@ ChaCha(CC).enc(k,n,c);
      result <- Some (n,a,p);
    }
    return result;
  }
}.

(* --------------------------------------------------------------------- *)
(* We want to bound :
   `| Pr[CCA_game(A, Real_Oracles(ChaChaPoly(CCperm))).main() : res] 
      - Pr[CCA_game(A, Ideal_Oracles).main() : res] |

   We process as follow: 
    `| Pr[CCA_game(A, Real_Oracles(ChaChaPoly(CCperm))).main() : res] 
        - Pr[CCA_game(A, Ideal_Oracles).main() : res] | <= 
Step 1 indistinguishability from a random oracle:
    `| Pr[CCA_game(A, Real_Oracles(ChaChaPoly(CCperm))).main() : res] 
        - Pr[CCA_game(A, Real_Oracles(ChaChaPoly(RO))).main() : res] + 
    `| Pr[CCA_game(A, Real_Oracles(ChaChaPoly(RO))).main() : res] 
        - Pr[CCA_game(A, Ideal_Oracles).main() : res] | 

Step 2 : CCA <= CPA + UFCMA + extra stuff on RO
    
Step 3 : enc return random 
         => CPA ~ Ideal

Step 4 : UFCMA with random enc
   
*)

abstract theory OpCC.
  type globS.
  op cc : globS -> key -> nonce -> C.counter -> block.

  module type Init = {
    proc init () : globS
  }.

  module OCC (I:Init) : FCC = {
    var gs : globS

    proc init () : unit = {
      gs <@ I.init();
    }
    
    proc kg () : key = {
      var k;
      k <$ dkey;
      return k;
    }

    proc cc (k:key, n:nonce, c:C.counter) = {
      return cc gs k n c;
    }
  }.

  module OChaChaPoly (I:Init) = {
    include OCC(I) [init, kg]

    proc enc (k : key, nap : nonce * associated_data * message) : 
       nonce * associated_data * message * tag = {
      var n, a, p, c, t;
      (n,a,p) <- nap;
      c <- gen_CTR_encrypt_bytes take_xor (cc OCC.gs) k n 1 p;
      t <- genpoly1305  (cc OCC.gs) k n (topol a c);
      return (n,a,c,t);
    }

    proc dec(k : key, nact : nonce * associated_data * message * tag) :
      (nonce * associated_data * message) option = {
      var n, a, c, p, t, t', result;
      result <- None;
      (n,a,c,t) <- nact;
      t' <- genpoly1305 (cc OCC.gs) k n (topol a c);
      if (t = t') {
        p <- gen_CTR_encrypt_bytes take_xor (cc OCC.gs) k n 1 c;
        result <- Some (n,a,p);
      }
      return result;
    }
  }.
    
  module type Adv (S:SKE) = { 
    proc main () : bool 
  }.

  section PROOFS.
  
    declare module I: Init { OCC }.
    declare module A: Adv { OCC, I}.
   
    phoare chacha_spec k0 n0 p0 gs0 : 
      [ChaCha(OCC(I)).enc : 
        k = k0 /\ n = n0 /\ p = p0 /\ OCC.gs = gs0 ==>
        res = gen_CTR_encrypt_bytes take_xor (cc gs0) k0 n0 1 p0] = 1%r.
    proof.
      proc.
      rewrite /gen_CTR_encrypt_bytes /=.
      pose r := 
        iter (size p0 %/ block_size + b2i (size p0 %% block_size <> 0)) 
             (gen_ctr_round take_xor (cc gs0) k0 n0) ([], p0, 1).
      while (r = iter (size p %/ block_size + b2i (size p %% block_size <> 0))
                       (gen_ctr_round take_xor (cc OCC.gs) k n) (c, p, i)) 
            (size p).
      + move=> z; inline *; auto => /> &m.
        move: (p{m}) => p hp.
        have hd := StdOrder.IntOrder.lt0r_neq0 _ gt0_block_size.
        have -> : size p %/ block_size + b2i (size p %% block_size <> 0) = 
            (size (drop block_size p) %/ block_size + b2i (size (drop block_size p) %% block_size <> 0)) + 1.
        + case (block_size <= size p) => h.
          + have -> : size p = block_size + size (drop block_size p).
            + by rewrite size_drop 1:ge0_block_size /#.
            by rewrite (divzMDl 1 _ _ hd) (modzMDl 1 _ block_size); ring.
          have hm : 0 <= size p < `|block_size| by smt (size_ge0).
          by rewrite modz_small 1:hm divz_small 1:hm drop_oversize 1:/# /= size_eq0 hp.
        rewrite iterSr 1:[smt (size_ge0 gt0_block_size)]; split => //.
        smt (size_drop size_ge0 size_eq0 ge0_block_size).
      auto;rewrite /r => {r} /> &hr c i' p'; split;1: smt (size_eq0 size_ge0).  
      by rewrite /b2i /= (iter0 0) 1:// => ->.    
    qed.

    phoare poly_spec k0 n0 a0 c0 gs0 :
      [Poly(OCC(I)).mac : 
        k = k0 /\ n = n0 /\ a = a0 /\ c = c0 /\ OCC.gs = gs0 ==>
        res = genpoly1305 (cc gs0) k0 n0 (topol a0 c0)] = 1%r.
    proof. proc; inline *; auto. qed.

    equiv CCP_OCCP : A(GenChaChaPoly(OCC(I))).main ~ A(OChaChaPoly(I)).main : 
       ={glob A, glob I, glob OCC, arg} ==> ={res, glob A, glob I, glob OCC}.
    proof.
      proc (={glob I, glob OCC}) => //; 1,2: by sim.
      + proc.
        ecall{1} (poly_spec k{1} n{1} a{1} c{1} OCC.gs{1}).
        by ecall{1} (chacha_spec k{1} n{1} p{1} OCC.gs{1}); wp.
      proc.
      seq 3 3 : (={glob I, glob OCC, result, n, a, c, t, t',k}).
      + by ecall{1} (poly_spec k{1} n{1} a{1} c{1} OCC.gs{1});wp.
      by if;auto; ecall{1} (chacha_spec k{1} n{1} c{1} OCC.gs{1}).
    qed.
  
    lemma pr_CCP_OCCP &m : 
      Pr[A(GenChaChaPoly(OCC(I))).main() @ &m : res] = 
      Pr[A(OChaChaPoly(I)).main() @ &m : res].
    proof. by byequiv CCP_OCCP. qed.

  end section PROOFS.

end OpCC.
  
clone import FinGenEager as FiniteRO with
  type from <- (nonce*C.counter),
  type to   <- block, 
  type input <- unit,
  type output <- bool,
  op sampleto <- fun _ => dblock,
  theory FinFrom <- NonceCount
  proof *.
  realize sampleto_ll by apply dblock_ll.

module IndBlock = {
  var k: key
  proc init () = { k <$ dkey; }
  proc f (n:nonce, c:C.counter) = {
    return chacha20_block k n c;
  }
}.

module IndRO = {
  proc init = RO.init
  proc f = RO.get
}.

clone Indistinguishability as Indist with 
  type t_in <- nonce * C.counter,
  type t_out <- block.
  
module D(A:CCA_Adv, RO: Indist.Oracle) = {
  module O = {
    proc init () = {}
    
    module ChaCha = {
      proc enc(n:nonce, p:message) : bytes = {
        var i, z, c;
        c     <- [];
        i     <- 1;
        while (p <> []) {
          z <@ RO.f(n, C.ofint i);
          c <- c ++ take (size p) (bytes_of_block (extend p +^ z));
          p <- drop block_size p;
          i <- i + 1;
        }
        return c;
      }
    }

    module Poly = {
      proc mac(n: nonce, a: associated_data, c: message) : tag = {
        var b, r, s;
        b     <@ RO.f(n, C.ofint 0);
        (r,s) <- mk_rs b; 
        return poly1305 r s (topol a c);
      }
    }

    proc enc (nap : nonce * associated_data * message) : 
      nonce * associated_data * message * tag = {
      var n, a, p, c, t;
      (n,a,p) <- nap;
      c <@ ChaCha.enc(n,p);
      t <@ Poly.mac(n,a,c);
      return (n,a,c,t);
    }
  
    proc dec(nact : nonce * associated_data * message * tag) :
      (nonce * associated_data * message) option = {
      var n, a, c, p, t, t', result;
      result <- None;
      (n,a,c,t) <- nact;
      t' <@ Poly.mac(n,a,c);
      if (t = t') {
        p <@ ChaCha.enc(n,c);
        result <- Some (n,a,p);
      }
      return result;
    }
  }
  
  proc guess = CCA_game(A,O).main

}.

module CCRO(RO:RO) = {
  proc init = RO.init 
  proc cc(k : key, n : nonce, c : C.counter) : block = {
    var result;
    result <@ RO.get (n,c);
    return result;
  }
}.

op test_poly (n:nonce) (lc:ciphertext list) r s = 
  let pts = map (fun (c:ciphertext) => (topol c.`2 c.`3, c.`4))
                (List.filter (fun (c:ciphertext) => c.`1 = n) lc) in
  List.has (fun (pt:polynomial*tag) => pt.`2 = poly1305 r s pt.`1) pts.

module UFCMA_poly(A:CCA_Adv, RO:RO) = {
  proc main () = {
    var ns, forged, i, n, bl, r, s;
    CPA_game(CCA_CPA_Adv(A), RealOrcls(GenChaChaPoly(CCRO(RO)))).main();
    ns <- undup (List.map (fun (p:ciphertext) => p.`1) Mem.lc);
    forged <- false;
    i <- 0;
    while (i < size ns) {
      n  <- List.nth witness ns i;
      bl <@ RO.get(n,C.ofint 0);
      (r,s) <- mk_rs bl; 
      forged <- forged || test_poly n Mem.lc r s;
      i <- i + 1;
    }
    return forged;
  }
}.
       
abstract theory Step1_2.

clone import OpCC as OpCCinit with 
  type globS <- unit,
  op cc <- fun _ => chacha20_block.
 
module I_stateless = {
  proc init () = {}
}.

clone import OpCC as OpCCRO with 
  type globS = (nonce * C.counter, block) fmap,
  op cc m k n c <- oget m.[(n,c)].
 
module IFinRO = {
  proc init () = { 
    FinRO.init();
    return RO.m;
  }
}.

op get (gs:OpCCRO.globS) (k:key) n c = oget gs.[(n,c)].

clone import CCA_CPA_UFCMA as CCA_UFCMA with 
  type globS <- OpCCRO.globS,
  op enc gs k (nap:plaintext) =  
    let (n,a,p) = nap in
    let c = gen_CTR_encrypt_bytes take_xor (get gs) k n 1 p in
    let t = genpoly1305 (get gs) k n (topol a c) in
    (n,a,c,t), 
  op dec gs k (nact:ciphertext) = 
    let (n,a,c,t) = nact in
    let t' = genpoly1305 (get gs) k n (topol a c) in
    if (t = t') then
      Some (n,a, gen_CTR_encrypt_bytes take_xor (get gs) k n 1 c)
    else None, 
  op valid_key <- fun _ => true
  proof *.
realize dec_enc.
proof.
  move=> k _ gs [n a p]; rewrite /dec /enc /=.
  have htake_xor : forall str, take_xor [] str = [].
  + by move=> ?;rewrite take0.
  have : forall j, 0 <= j => forall p c, j = size p =>
    gen_CTR_encrypt_bytes take_xor (get gs) k n c (gen_CTR_encrypt_bytes take_xor (get gs) k n c p) = p;
   2: by move=> /(_ (size p)) -> //;apply size_ge0.
  elim /sintind.
  move=> {p} i hi hrec p c ->>.
  case: (size p = 0).
  + by rewrite size_eq0 => ->>; rewrite !gen_CTR_encrypt_bytes0.
  move=> hs; rewrite (gen_CTR_encrypt_bytes_cons _ _ _ _ _ p) 1:// gen_CTR_encrypt_bytes_cons 1://.
  case: (size p < block_size) => hsz.
  + rewrite drop_oversize 1:/# gen_CTR_encrypt_bytes0 1:// cats0 drop_oversize.
    + by rewrite size_take // Block.valP /#.
    rewrite gen_CTR_encrypt_bytes0 1:// cats0. 
    rewrite -!take_xor_map2_xor; apply (eq_from_nth Byte.zero).
    + by rewrite !size_map2 Block.valP /#.
    move=> j; rewrite !size_map2 Block.valP => hj.
    by rewrite !(nth_map2 Byte.zero Byte.zero) ?size_map2 ?Block.valP 1,2:/# -Byte.xorK1.
  rewrite drop_size_cat;1: by rewrite size_take 1:// Block.valP /#.
  rewrite (hrec (size (drop block_size p))) 2://; 1: smt(size_drop gt0_block_size).
  rewrite -{4}(cat_take_drop block_size p); congr.
  rewrite -!take_xor_map2_xor; apply (eq_from_nth Byte.zero).
  + smt (size_map2 Block.valP size_cat size_take gt0_block_size size_ge0).
  move=> j hj.
  have [hj1 hj2] : j < block_size /\ j < size p.
  + smt (size_map2 Block.valP size_cat size_take gt0_block_size size_ge0).
  rewrite (nth_map2 Byte.zero Byte.zero) ?(size_cat, size_map2, Block.valP) 1:[smt(size_ge0)].
  rewrite nth_cat ?(size_cat, size_map2, Block.valP) /min hsz /= hj1.
  by rewrite (nth_map2 Byte.zero Byte.zero) ?Block.valP 1:/# /= -Byte.xorK1 nth_take 1:ge0_block_size.
qed.

module St = {
  proc init () = { 
    FinRO.init();
    return RO.m;
  }
  proc kg = ChaChaPoly.kg
}.

clone Split as Split0 with 
  type from   <- nonce * C.counter,
  type to     <- block,
  type input  <- unit,
  type output <- bool,
  op sampleto <- fun _ => dblock
  proof *.

clone import Split0.SplitDom as SplitD with
  op test = fun p:nonce * C.counter => C.val p.`2 = 0.

clone import Split0.SplitCodom as SplitC1 with
  type to1 <- poly,
  type to2 <- extra_block,
  op topair = fun (b:block) => 
     let bs = bytes_of_block b in
     (TPoly.insubd (take poly_size bs), Extra_block.insubd (drop poly_size bs)),
  op ofpair = fun (p:poly * extra_block) =>
     Block.insubd (bytes_of_poly p.`1 ++ bytes_of_extra_block p.`2),
  op sampleto1 <- fun _ => dpoly,
  op sampleto2 <- fun _ => dextra_block
  proof *.
realize topairK.
proof.
  move=> x; rewrite /topair /ofpair /=.
  rewrite -{3}(Block.valKd x); congr.
  rewrite TPoly.insubdK. 
  + rewrite size_take 1:ge0_poly_size Block.valP.
    smt (ge0_poly_in_size ge0_poly_out_size ge0_extra_block_size).
  rewrite Extra_block.insubdK 2:cat_take_drop 2://.
  rewrite size_drop 1:ge0_poly_size Block.valP.
  smt (ge0_poly_in_size ge0_poly_out_size ge0_extra_block_size).
qed.

realize ofpairK.
proof.
  move=> [x1 x2]; rewrite /topair /ofpair /=.
  rewrite Block.insubdK.
  + by rewrite size_cat TPoly.valP Extra_block.valP.
  by rewrite take_size_cat 1:TPoly.valP 1:// drop_size_cat 1:TPoly.valP 1://
     TPoly.valKd Extra_block.valKd.
qed.

realize sample_spec.
proof.
  move=> _; rewrite /dblock; apply eq_distr => b.
  rewrite !dmap1E.
  apply (eq_trans _ (mu1 (dpoly `*` dextra_block) ((topair b).`1, (topair b).`2))); last first.
  + congr; apply fun_ext; smt (topairK ofpairK).
  rewrite dprod1E (_:block_size = poly_size + extra_block_size) //.
  rewrite dlist_add 1:ge0_poly_size 1:ge0_extra_block_size dmapE.
  rewrite !dmap1E /(\o) -dprodE &(mu_eq_support) => -[l1 l2] /supp_dprod /= [h1 h2].
  have s1 := supp_dlist_size dbyte _ _ ge0_poly_size h1.
  have s2 := supp_dlist_size dbyte _ _ ge0_extra_block_size h2.
  smt (ofpairK topairK size_cat drop_size_cat take_size_cat insubdK).
qed.

clone Split as Split1 with 
  type from   <- nonce * C.counter,
  type to     <- poly,
  type input  <- unit,
  type output <- bool,
  op sampleto <- fun _ => dpoly
  proof *.

(* TODO: share more stuff with the previous clone *)
clone import Split1.SplitCodom as SplitC2 with
  type to1 <- poly_in,
  type to2 <- poly_out,
  op topair = fun (b:poly) => 
     let bs = bytes_of_poly b in
     (Poly_in.insubd (take poly_in_size bs), Poly_out.insubd (drop poly_in_size bs)),
  op ofpair = fun (p:poly_in * poly_out) =>
     TPoly.insubd (bytes_of_poly_in p.`1 ++ bytes_of_poly_out p.`2),
  op sampleto1 <- fun _ => dpoly_in,
  op sampleto2 <- fun _ => dpoly_out
  proof *.
realize topairK.
proof.
  move=> x; rewrite /topair /ofpair /=.
  rewrite -{3}(TPoly.valKd x); congr.
  rewrite Poly_in.insubdK. 
  + rewrite size_take 1:ge0_poly_in_size TPoly.valP.
    smt (ge0_poly_in_size ge0_poly_out_size).
  rewrite Poly_out.insubdK 2:cat_take_drop 2://.
  rewrite size_drop 1:ge0_poly_in_size TPoly.valP.
  smt (ge0_poly_in_size ge0_poly_out_size).
qed.

realize ofpairK.
proof.
  move=> [x1 x2]; rewrite /topair /ofpair /=.
  rewrite TPoly.insubdK.
  + by rewrite size_cat Poly_in.valP Poly_out.valP.
  by rewrite take_size_cat 1:Poly_in.valP 1:// drop_size_cat 1:Poly_in.valP 1://
     Poly_in.valKd Poly_out.valKd.
qed.

realize sample_spec.
proof.
  move=> _; rewrite /dpoly; apply eq_distr => b.
  rewrite !dmap1E.
  apply (eq_trans _ (mu1 (dpoly_in `*` dpoly_out) ((topair b).`1, (topair b).`2))); last first.
  + congr; apply fun_ext; smt (topairK ofpairK).
  rewrite dprod1E (_:poly_size = poly_in_size + poly_out_size) //.
  rewrite dlist_add 1:ge0_poly_in_size 1:ge0_poly_out_size dmapE.
  rewrite !dmap1E /(\o) -dprodE &(mu_eq_support) => -[l1 l2] /supp_dprod /= [h1 h2].
  have s1 := supp_dlist_size dbyte _ _ ge0_poly_in_size h1.
  have s2 := supp_dlist_size dbyte _ _ ge0_poly_out_size h2.
  smt (ofpairK topairK size_cat drop_size_cat take_size_cat TPoly.insubdK).
qed.

module G4 (A:CCA_Adv, RO:RO) = {
  proc distinguish () = {
    var b;
    Mem.k <@ GenChaChaPoly(CCRO(RO)).kg();
    b <@ CCA_CPA_Adv(A, RealOrcls(GenChaChaPoly(CCRO(RO)))).main();
    return b;
  }
}.

module G5_end(RO:RO) = {
  proc main() = {
    var ns, forged, i, n, bl, r,s ;
    ns <- undup (List.map (fun (p:ciphertext) => p.`1) Mem.lc);
    forged <- false;
    i <- 0;
    while (i < size ns) {
      n  <- List.nth witness ns i;
      bl <@ RO.get(n,C.ofint 0);
      (r,s) <- mk_rs bl; 
      forged <- forged || test_poly n Mem.lc r s;
      i <- i + 1;
    }
    return forged;
  }
}.

module G5 (A:CCA_Adv, RO:RO) = {
  proc distinguish () = {
    var b, forged;
    b <@ G4(A, RO).distinguish();
    forged <@ G5_end(RO).main();
    return forged;
  }
}.

module G6 (A:CCA_Adv, ROT:Split0.IdealAll.RO) = {
  proc distinguish () = {
    var b;
    ROF.RO.init();
    b <@ G4(A, RO_DOM(ROT, ROF.RO)).distinguish();
    return b;
  }
}.

module G7 (A:CCA_Adv, ROT:Split0.IdealAll.RO) = {
  proc distinguish () = {
    var b;
    ROF.RO.init();
    b <@ G5(A, RO_DOM(ROT, ROF.RO)).distinguish();
    return b;
  }
}.

module G8 (A:CCA_Adv, RO1:SplitC1.I1.RO) = {
  proc distinguish() = {
    var b;
    SplitC1.I2.RO.init();
    b <@ G6(A, SplitC1.RO_Pair(RO1,SplitC1.I2.RO)).distinguish();
    return b;
  }
}.

module G9 (A:CCA_Adv, RO1:SplitC1.I1.RO) = {
  proc distinguish() = {
    var b;
    SplitC1.I2.RO.init();
    b <@ G7(A, SplitC1.RO_Pair(RO1,SplitC1.I2.RO)).distinguish();
    return b;
  }
}.

section PROOFS.

  declare module A : CCA_Adv { RO, FRO, OpCCinit.OCC, OpCCRO.OCC, IndBlock, Mem, StLSke,
                               Split0.IdealAll.RO, ROT.RO, ROF.RO, SplitC1.I1.RO, SplitC1.I2.RO,
                               Split1.IdealAll.RO, SplitC2.I1.RO, SplitC2.I2.RO }.

  axiom A_ll : forall (O <: CCA_Oracles{A}), islossless O.enc => islossless O.dec => islossless A(O).main.

  local module G1 (S:SKE) = CCA_game(A, RealOrcls(S)).

  local equiv poly_mac1 : 
    Poly(OpCCinit.OCC(I_stateless)).mac ~ D(A, IndBlock).O.Poly.mac : k{1} = IndBlock.k{2} /\ ={n,a,c} ==> ={res}.
  proof. proc; inline *;auto. qed.

  local equiv chacha_enc1: 
    ChaCha(OpCCinit.OCC(I_stateless)).enc ~ D(A, IndBlock).O.ChaCha.enc : 
      k{1} = IndBlock.k{2} /\ ={n,p} ==> ={res}.
  proof. proc; inline *; wp; sim. qed.

  local module G2(RO:RO) = {
    module CCRO = {
      proc f = RO.get
    }
    proc distinguish = D(A,CCRO).guess
  }.

  local equiv poly_mac2 : 
    Poly(OCC(IFinRO)).mac ~ D(A, G2(FinRO).CCRO).O.Poly.mac : OCC.gs{1} = RO.m{2} /\ ={n,a,c} ==> ={res}.
  proof. proc; inline *;auto. qed.

  local equiv chacha_enc2: 
    ChaCha(OCC(IFinRO)).enc ~ D(A, G2(FinRO).CCRO).O.ChaCha.enc : OCC.gs{1} = RO.m{2} /\ ={n,p} ==> ={res}.
  proof. 
    proc; inline *; wp.
    by while (={p, c, n, i} /\ OCC.gs{1} = RO.m{2}); auto.
  qed.

  local lemma step1 &m: 
     Pr[CCA_game(A, RealOrcls(ChaChaPoly)).main() @ &m : res] -
      Pr[CCA_game(A,RealOrcls(OChaChaPoly(IFinRO))).main() @ &m : res] =
     Pr[Indist.Distinguish(D(A), IndBlock).game() @ &m : res] -
       Pr[Indist.Distinguish(D(A), IndRO).game() @ &m : res].
  proof.
    congr.
    + have -> :
        Pr[CCA_game(A, RealOrcls(ChaChaPoly)).main() @ &m : res] =
        Pr[CCA_game(A, RealOrcls(OpCCinit.OChaChaPoly(I_stateless))).main() @ &m : res].
      + by byequiv => //; proc; inline *; wp; call (_: ={Mem.k}); sim />. 
      rewrite -(OpCCinit.pr_CCP_OCCP I_stateless G1 &m).
      byequiv => //; proc; inline *; wp; call (_: Mem.k{1} = IndBlock.k{2}); last by auto.
      + proc; inline GenChaChaPoly(OpCCinit.OCC(I_stateless)).enc; wp.
        by call poly_mac1; call chacha_enc1; auto.
      proc; inline GenChaChaPoly(OpCCinit.OCC(I_stateless)).dec; wp; conseq />.
      seq 5 3 : (={n,a,t,result,t'} /\ c0{1} = c{2} /\ k{1} = Mem.k{1} /\ Mem.k{1} = IndBlock.k{2}). 
      + by call poly_mac1; auto.
      by if => //; wp; call chacha_enc1.
    congr.
    have -> : 
      Pr[Indist.Distinguish(D(A), IndRO).game() @ &m : res] = 
      Pr[MainD(G2,RO).distinguish() @ &m : res].
    + by byequiv => //; proc; inline *; sim.
    rewrite (pr_RO_FinRO_D G2 &m () (fun x => x)) /=.
    rewrite -(pr_CCP_OCCP IFinRO G1 &m).
    byequiv => //; proc; inline G2(FinRO).distinguish; wp.
    call (_: OCC.gs{1} = RO.m{2}). 
    + proc; inline GenChaChaPoly(OCC(IFinRO)).enc; wp.
      by call poly_mac2; call chacha_enc2; auto.
    + proc; inline GenChaChaPoly(OCC(IFinRO)).dec; wp; conseq />.
      seq 5 3 : (={n,a,t,result,t'} /\ c0{1} = c{2} /\  OCC.gs{1} = RO.m{2}). 
      + by call poly_mac2; auto.
      by if => //; wp; call chacha_enc2.
    inline D(A, G2(FinRO).CCRO).O.init RealOrcls(GenChaChaPoly(OCC(IFinRO))).init 
     GenChaChaPoly(OCC(IFinRO)).kg; auto.
    conseq (_: ={glob A} /\ OCC.gs{1} = RO.m{2}) => />. 
    by inline GenChaChaPoly(OCC(IFinRO)).init IFinRO.init;sim.
  qed.

  local lemma step2_1 &m :
    Pr[CCA_game(A,RealOrcls(OChaChaPoly(IFinRO))).main() @ &m : res] <=
    Pr[CPA_game(CCA_CPA_Adv(A), RealOrcls(StLSke(St))).main() @ &m : res] + 
     Pr[UFCMA(A, St).main() @ &m : (exists c, c \in Mem.lc /\ dec StLSke.gs Mem.k c <> None)].
  proof.
    have -> : 
      Pr[CCA_game(A,RealOrcls(OChaChaPoly(IFinRO))).main() @ &m : res] =
      Pr[CCA_game(A,RealOrcls(StLSke(St))).main() @ &m : res].
    + byequiv => //;proc; call (_: OCC.gs{1} = StLSke.gs{2} /\ ={Mem.k}); last by sim />.
      + by proc; inline *; auto => /> &2; case: (p{2}).
      proc; inline *; auto => /> &2; case: (c{2}) => /> n a c t.
      by rewrite /dec /get /= => ->. 
    by apply (CCA_CPA_UFCMA St A _ _ &m) => //; apply A_ll.
  qed.

  local module G3 (S:SKE) = CPA_game(CCA_CPA_Adv(A), RealOrcls(S)).

  local equiv UFCMA_genCC :
    UFCMA(A, St).main ~ CPA_game(CCA_CPA_Adv(A), RealOrcls(GenChaChaPoly(CCRO(FinRO)))).main :
    ={glob A} ==> ={res, Mem.lc} /\ StLSke.gs{1} = RO.m{2}.
  proof.
    proc *.
    transitivity*{1} { r <@ G3(StLSke(St)).main(); } => //; 1:smt(); 1: by sim.
    transitivity* {2} { r <@ G3(OChaChaPoly(IFinRO)).main(); } => //; 1:smt().
    + inline *; wp.
      call (_: StLSke.gs{1} = OCC.gs{2} /\ ={Mem.k, Mem.log, Mem.lc}).
      + by proc; inline *; auto => /> &2; case: (p{2}).
      + by proc; auto.
      by auto; conseq (_: ={RO.m}) => //; sim.
    transitivity*{1} { r <@ G3(GenChaChaPoly(OCC(IFinRO))).main(); } => //;1:smt().
    + by symmetry; call (CCP_OCCP IFinRO G3).
    inline *; sim (_: ={Mem.lc, Mem.log, Mem.k} /\ OCC.gs{1} = RO.m{2}).
    proc; inline *;auto.
  qed.

  local lemma step2_2 &m : 
    Pr[CPA_game(CCA_CPA_Adv(A), RealOrcls(StLSke(St))).main() @ &m : res] + 
    Pr[UFCMA(A, St).main() @ &m : (exists c, c \in Mem.lc /\ dec StLSke.gs Mem.k c <> None)] <=
    Pr[CPA_game(CCA_CPA_Adv(A), RealOrcls(GenChaChaPoly(CCRO(FinRO)))).main() @ &m : res] +
    Pr[UFCMA_poly(A, FinRO).main() @ &m : res].
  proof.
    apply StdOrder.RealOrder.ler_add; 1: byequiv UFCMA_genCC => //.
    byequiv => //; proc *; inline UFCMA_poly(A, FinRO).main.
    seq 1 1: (={Mem.lc} /\ StLSke.gs{1} = RO.m{2}); 1 : by call UFCMA_genCC.
    wp;while{2} (0 <= i <= size ns /\ 
              forged = exists j, 0 <= j < i /\
                        let n = nth witness ns j in
                        let bl = oget RO.m.[(n,C.ofint 0)] in
                        let (r,s) = mk_rs bl in
                        test_poly n Mem.lc r s){2} (size ns - i){2}.
    + by move=> _ z; inline *; auto => /> /#.
    auto => /> &1 &2; rewrite size_ge0 /=; split; 1:smt().
    move=> i; split; 1:smt().
    move=> h1 h2 h3 [n a c t] hin hdec.
    have ->> {h1 h2 h3}: i = size (undup (map (fun (p : ciphertext) => p.`1) Mem.lc{2})) by smt().
    pose ns := (undup (map (fun (p : ciphertext) => p.`1) Mem.lc{2})).
    exists (index n ns); rewrite index_ge0 index_mem. 
    have in_ns : n \in ns.
    + by rewrite mem_undup; apply (map_f _ _ (n,a,c,t)).
    move: hdec; rewrite in_ns /dec /genpoly1305 /test_poly /= /get nth_index 1://.
    case: (mk_rs (oget RO.m{2}.[(n, C.ofint 0)])) => r s /=.
    case: (t = poly1305 r s (topol a c)) => // heq _.
    apply hasP; exists (topol a c, t) => /=;split; 2:by rewrite heq.
    by apply mapP; exists (n, a, c, t) => /=; apply mem_filter.
  qed.

  local lemma step2_3 &m : 
    Pr[CPA_game(CCA_CPA_Adv(A), RealOrcls(GenChaChaPoly(CCRO(FinRO)))).main() @ &m : res] +
    Pr[UFCMA_poly(A, FinRO).main() @ &m : res] = 
    Pr[Split1.IdealAll.MainD(G8(A), SplitC2.RO_Pair(SplitC2.I1.RO, SplitC2.I2.RO)).distinguish() @ &m : res] + 
    Pr[Split1.IdealAll.MainD(G9(A), SplitC2.RO_Pair(SplitC2.I1.RO, SplitC2.I2.RO)).distinguish() @ &m : res]. 
  proof.
    apply (eq_trans _ (Pr[MainD(G4(A), RO).distinguish() @ &m : res] + 
                       Pr[MainD(G5(A), RO).distinguish() @ &m : res])).
    + congr.
      + apply (eq_trans _ Pr[MainD(G4(A), FinRO).distinguish() @ &m : res]).
        + by byequiv => //; proc; inline *;sim.
        by rewrite -(pr_RO_FinRO_D (G4(A)) &m () (fun x => x)).
      apply (eq_trans _ Pr[MainD(G5(A), FinRO).distinguish() @ &m : res]).
      + by byequiv => //; proc; inline *; sim.
      by rewrite -(pr_RO_FinRO_D (G5(A)) &m () (fun x => x)).
    apply (eq_trans _ (Pr[Split0.IdealAll.MainD(G4(A), Split0.IdealAll.RO).distinguish() @ &m : res] +
                       Pr[Split0.IdealAll.MainD(G5(A), Split0.IdealAll.RO).distinguish() @ &m : res])).
    + by congr; byequiv => //; sim.
    rewrite (SplitD.pr_RO_split (G4(A)) (fun _ r => r) &m ()) (SplitD.pr_RO_split (G5(A)) (fun _ r => r) &m ()) /=.
    apply (eq_trans _ (Pr[Split0.IdealAll.MainD(G6(A), Split0.IdealAll.RO).distinguish() @ &m : res] +
                       Pr[Split0.IdealAll.MainD(G7(A), Split0.IdealAll.RO).distinguish() @ &m : res])).
    + by congr;byequiv => //; proc; inline *; sim.
    rewrite (SplitC1.pr_RO_split (G6(A)) (fun _ r => r) &m ()) (SplitC1.pr_RO_split (G7(A)) (fun _ r => r) &m ()) /=.
    rewrite -(SplitC2.pr_RO_split (G8(A)) (fun _ r => r) &m ()) -(SplitC2.pr_RO_split (G9(A)) (fun _ r => r) &m ()) /=.
    by congr; byequiv => //; proc; inline *; sim.
  qed.

  lemma step2 &m : 
    Pr[CCA_game(A, RealOrcls(ChaChaPoly)).main() @ &m : res] <=
     Pr[Split1.IdealAll.MainD(G8(A), SplitC2.RO_Pair(SplitC2.I1.RO, SplitC2.I2.RO)).distinguish() @ &m : res] + 
     Pr[Split1.IdealAll.MainD(G9(A), SplitC2.RO_Pair(SplitC2.I1.RO, SplitC2.I2.RO)).distinguish() @ &m : res] + 
     (Pr[Indist.Distinguish(D(A), IndBlock).game() @ &m : res] - Pr[Indist.Distinguish(D(A), IndRO).game() @ &m : res]).
  proof. move: (step1 &m) (step2_1 &m) (step2_2 &m) (step2_3 &m) => /#. qed.

end section PROOFS.

end Step1_2.

(* -------------------------------------------------------------------------- *)
(* We now restrict the adversary to be :                                      *)
(* - nonce respective                                                         *)
(* - for encryption end decryption :                                          *)
(*   * the size of additionnal is bounded by [max_ad_size]                    *)
(*   * the size of message is bounded by max_cipher_size                      *)
(* - number of call to                                                        *)
(*   * enc is bounded by qenc                                                 *)
(*   * dec is bounded by qdec                                                 *)

op qenc : int.
axiom ge0_qenc : 0 <= qenc.

op qdec : int.
axiom ge0_qdec : 0 <= qdec.

op dec_bytes : int.
axiom ge0_dec_bytes : 0 <= dec_bytes. 

op pr1_poly_out = mu1 dpoly_out witness.

op pr_zeropol : real.
axiom ge0_pr_zeropol : 0%r <= pr_zeropol.

axiom pr_zeropol_spec ad1 ad2 m1 m2 t1 t2 : 
   valid_topol ad1 m1 =>
   valid_topol ad2 m2 =>
   let p1 = topol ad1 m1 in
   let p2 = topol ad2 m2 in
   p2 <> p1 => 
   mu dpoly_in (fun r => t2 = t1 + (poly1305_eval r p2 - poly1305_eval r p1)) <= pr_zeropol.
  
op test_poly_in (n : nonce) (lc : ciphertext list) (r : poly_in)
       (amt: associated_data * message * tag) = 
    let (a,m,t) = amt in
    let p = topol a m in
    let pts = 
       map (fun (c : ciphertext) => (topol c.`2 c.`3, c.`4))
           (filter (fun (c : ciphertext) => c.`1 = n /\ valid_topol c.`2 c.`3) lc) in
     valid_topol a m /\
     has (fun (pt : polynomial * tag) => 
            pt.`1 <> p /\ pt.`2 = t + (poly1305_eval r pt.`1 - poly1305_eval r p)) pts.

lemma pr_TPI_ok n (lc:ciphertext list) (amt : associated_data * message * tag) : 
  size lc <= qdec => 
  mu dpoly_in (fun r => test_poly_in n lc r amt) <= qdec%r * pr_zeropol.
proof.
  move => hlc; rewrite /test_poly_in; case: amt => a m t /=.
  case: (valid_topol a m) => hv /=;last by rewrite mu0; smt (ge0_qdec ge0_pr_zeropol).
  pose lc' := List.map _ _; apply (ler_trans ((size lc')%r*pr_zeropol));
   last by rewrite size_map size_filter; smt (count_size size_ge0 ge0_pr_zeropol).
  apply mu_has_leM => /= ? /mapP [] [n' a' m' t'] /> /mem_filter |> ??.
  case: (topol a' m' <> topol a m) => ? /=; last by rewrite mu0; smt (ge0_pr_zeropol).
  by apply pr_zeropol_spec.
qed.

op check_plaintext (lenc:nonce list) (p:plaintext) = 
  let (n, a, m) = p in
  ! n \in lenc /\ 
  valid_topol a m /\
  size lenc < qenc.

op check_cipher (ndec:int) (c:ciphertext) =
  let (n, a, m, t) = c in
  valid_topol a m /\
  ndec < qdec.

(* Bounded and Nonce Respecting *)
module BNR (O:CCA_Oracles) = {
  var lenc : nonce list
  var ndec : int 

  proc init () = { lenc <- []; ndec <- 0; }

  proc enc (p:plaintext) = {
    var c;
    c <- witness;
    if (check_plaintext lenc p) {
      c <@ O.enc(p);
      lenc <- p.`1 :: lenc;
    }
    return c;
  }

  proc dec (c:ciphertext) = {
    var p;
    p <- None;
    if (check_cipher ndec c) {
      p <@ O.dec(c);
      ndec <- ndec + 1;
    }
    return p;
  }
}.

module BNR_Adv(A:CCA_Adv, O:CCA_Oracles) = {
  proc main() = {
    var b;
    BNR(O).init();
    b <@ A(BNR(O)).main();
    return b;
  }
}.

module EncRnd = {

  proc init () = {}

  proc cc(n:nonce, p:message) : bytes = {
    var i, z, c;
    p     <- List.map (fun _ => witness<:byte>) p; 
    c     <- [];
    i     <- 1;
    while (p <> []) {
      z <$ dblock; 
      c <- c ++ take (size p) (bytes_of_block  z);
      p <- drop block_size p;
      i <- i + 1;
    }
    return c;
  }

  proc enc (nap : nonce * associated_data * message) : 
       nonce * associated_data * message * tag = {
    var n, a, p, c, t;
    (n,a,p) <- nap;
    c <@ cc(n,p);
    t <$ dpoly_out; 
    return (n,a,c,t);
  }
  
  proc dec (nact: nonce * associated_data * message * tag) : 
    (nonce * associated_data * message) option = {
    return None;
  }
   
}.

section PROOFS.
  declare module A : CCA_Adv { BNR, Mem, IndBlock, RO, FRO}.

  axiom A_ll : forall (O <: CCA_Oracles{A}), islossless O.enc => islossless O.dec => islossless A(O).main.

  local clone import Step1_2 as Step1_2'.

  local module ROin  = SplitC2.I1.RO.
  local module ROout = SplitC2.I2.RO.
  local module ROF   = SplitD.ROF.RO.

  lemma mk_rs_ofpair r s e : 
    mk_rs (SplitC1.ofpair (SplitC2.ofpair (r, s), e)) = (r, s).
  proof.
    rewrite /mk_rs /SplitC1.ofpair /SplitC2.ofpair /= insubdK.
    + by rewrite size_cat TPoly.valP Extra_block.valP.
    have h1 : size (bytes_of_poly_in r ++ bytes_of_poly_out s) = poly_size.
    + by rewrite size_cat Poly_in.valP Poly_out.valP.
    rewrite TPoly.insubdK 1:// take_size_cat 1:// take_size_cat 2:drop_size_cat ?Poly_in.valP //.
    by rewrite Poly_in.valKd Poly_out.valKd.
  qed.

  op inv_cpa (mr1 : (nonce*C.counter, poly_in) fmap) 
         (ms1 : (nonce*C.counter, poly_out) fmap)
         (log1 log2: (ciphertext, plaintext) fmap)
         (lc1 lc2 : ciphertext list) 
         (lenc1 lenc2: nonce list)
         (ndec1 ndec2 :int) =
     log1 = log2 /\ lenc1 = lenc2 /\ lc1 = lc2 /\ ndec1 = ndec2 /\
     (forall n c, (n,c) \in mr1 => n \in lenc1) /\
     (forall n c, (n,c) \in ms1 => n \in lenc1).

  local equiv equ_cc n0 mr0 ms0:
     ChaCha(CCRO(SplitD.RO_DOM(SplitC1.RO_Pair(SplitC2.RO_Pair(ROin, ROout), SplitC1.I2.RO), ROF))).enc
     ~
     EncRnd.cc : 
       arg{2} = (arg.`2, arg.`3){1} /\ arg{2}.`1 = n0 /\
       size arg{1}.`3 <= max_cipher_size /\
       !n0 \in BNR.lenc{1} /\
       (forall n c, (n,c) \in ROF.m => n \in BNR.lenc){1} /\
       mr0 = ROin.m{1} /\ ms0 = ROout.m{1} 
       ==>
       ={res} /\ size res{1} <= max_cipher_size /\ mr0 = ROin.m{1} /\ ms0 = ROout.m{1} /\ 
       (forall n c, (n,c) \in ROF.m => n \in n0 :: BNR.lenc){1}.
  proof.
    proc; wp.
    exlim (size p{1}) => sz.
    while (={i, c, n} /\ 
           size c{1} + size p{1} = sz /\
           size p{1} = size p{2} /\ 1 <= i{1} /\
           size p{1} <= (C.max_counter - (i{1} - 1)) * block_size /\
           mr0 = ROin.m{1} /\ ms0 = ROout.m{1}  /\
           (forall n' c, (n',c) \in ROF.m => 
                  if n{2} = n' then 1 <= C.val c < i else n' \in BNR.lenc){1}).
    + inline{1} 1; inline{1} 4; wp.
      conseq (_ : (={i, c, n} /\ size c{1} + size p{1} = sz /\
                  size p{1} = size p{2} /\
                  1 <= i{1} /\
                  size p{1} <= (C.max_counter - (i{1} - 1)) * block_size /\
                  mr0 = ROin.m{1} /\ ms0 = ROout.m{1}  /\
                  (forall (n' : nonce) (c1 : C.counter),
                    (n', c1) \in ROF.m{1} => 
                    if n{2} = n' then 1 <= C.val c1 < i{1} else n' \in BNR.lenc{1})) /\
                  p{1} <> [] /\ p{2} <> [] /\
                  i{1} <= C.max_counter ==> _) => //.
      + move=> /> &1 &2 -> *.
        have h1 : 0 < size p{2} by smt (size_ge0 size_eq0).
        have : 0 < (C.max_counter - (i{2} - 1)) * block_size by smt().
        by rewrite (StdOrder.IntOrder.pmulr_lgt0 _ _ gt0_block_size) /#.
      rcondf{1} ^if; 1: by auto; smt (C.insubdK).
      inline{1} 5; rcondt{1} ^if; 1: by auto; smt (C.insubdK).
      wp; rnd (fun z => z +^ extend p{1}); auto => &1 &2 [#] 3!-> heq hs /= *;split.
      + move=> ??;apply xorK1.
      move=> h1 b ?; rewrite -h1 //= get_setE /= Block.MB.addmC /=.
      rewrite -!size_eq0 !size_drop 1,2:ge0_block_size hs /= 
        size_cat size_take 1:size_ge0 -heq Block.valP; split;1: smt(); split; 1: smt().
      split; 2: smt(mem_set C.insubdK).
      have := StdOrder.IntOrder.mulr_ge0 (C.max_counter - i{2}) block_size.
      smt (ge0_block_size).
    wp; skip=> &1 &2 [#] //= 4!->> h1 h2 h3 2!<<- //=.
    rewrite size_map //=; do!split; smt (max_cipher_size_ok).
  qed.

  local lemma step3 &m:  
    Pr[Split1.IdealAll.MainD(G8(BNR_Adv(A)), SplitC2.RO_Pair(ROin, ROout)).distinguish() @ &m : res] =
    Pr[CPA_game(CCA_CPA_Adv(BNR_Adv(A)), EncRnd).main() @ &m : res].
  proof.
    byequiv => //; proc; inline *; wp.
    call (_: 
       (forall n c, (n,c) \in ROF.m => n \in BNR.lenc){1} /\
       inv_cpa ROin.m{1} ROout.m{1} 
           Mem.log{1} Mem.log{2} Mem.lc{1} Mem.lc{2} 
           BNR.lenc{1} BNR.lenc{2} BNR.ndec{1} BNR.ndec{2}).
    + rewrite /inv_cpa;proc => /=; sp 1 1; if; 1:done; 2: by auto.
      wp; inline{1} 1; inline{2} 1; wp.
      inline{1} 2; inline{1} 3; inline{1} 7; inline{2} 2.
      seq 6 4:
        ( ={c, p, n, a, p0} /\ (p = p0 /\ p = (n, a, p2)){1} /\
           p2{1} = p1{2} /\ c2{1} = c1{2} /\
           (forall n' c, (n',c) \in ROF.m => n' \in n::BNR.lenc){1} /\
           inv_cpa ROin.m{1} ROout.m{1} 
               Mem.log{1} Mem.log{2} Mem.lc{1} Mem.lc{2} 
               BNR.lenc{1} BNR.lenc{2} BNR.ndec{1} BNR.ndec{2} /\
           check_plaintext BNR.lenc{1} p{1} ).
      + by ecall (equ_cc n{1} ROin.m{1} ROout.m{1}); rewrite /check_plaintext; auto => /> /#.
      move=> {&m};inline{1} 5; inline{1} 8.
      rcondt{1} ^if.
      + move=> &m; auto => />; rewrite /SplitD.test /= C.insubdK //=.
        smt(C.gt0_max_counter).
      inline{1} 9; wp.
      call{1} (_: true ==> true); 1: by islossless; apply dextra_block_ll.
      inline{1} 10; inline{1} 12; inline{1} 11.
      rcondt{1} ^if{1}; 1: by move=> &m; auto => /> /#.
      rcondt{1} ^if; 1: by move=> &m; auto => /> /#.
      swap{1} 12 -11; swap{1} 16 -14; wp.
      rnd (fun s => s + poly1305_eval r4{1} (topol a{2} c1{2}))
          (fun s => s - poly1305_eval r4{1} (topol a{2} c1{2})); rnd{1}; skip.
      smt (dpoly_in_ll poly_out_sub_add poly_out_add_sub get_setE mk_rs_ofpair mem_set).
    + by proc;inline *; sim /> => />.
    by auto => />; smt (dkey_ll mem_empty).
  qed.
          
  local module UFCMA (ROin:SplitC2.I1.RO) = {
  
    var log : (nonce, associated_data * message * tag)fmap
    var bad1 : bool
    var cbad1 : int   
    var bad2 : bool
    var cbad2 : int   
 
    proc set_bad1 (lt:tag list) : poly_out = {
      var t;
      t <$ dpoly_out;
      if (cbad1 < qenc /\ size lt <= qdec) { 
         bad1 <- bad1 || t \in lt;
         cbad1 <- cbad1 + 1;
      }
      return t;
    } 

    proc set_bad2 (lt:tag list) : poly_out = {
      var t;
      t <$ dpoly_out;
      (* if (cbad2 < qdec /\ size lt <= qdec) {  *)
         bad2 <- bad2 || t \in lt;
         cbad2 <- cbad2 + 1;
      (* } *)
      return t;
    } 

    module O = {
      proc init () = {
        log <- empty;
        ROin.init(); ROout.init(); ROF.init();
      }
    
      proc enc (nap : nonce * associated_data * message) : 
          nonce * associated_data * message * tag = {
        var n, a, p, c, t;
        (n,a,p) <- nap;
        c <@ EncRnd.cc(n,p);   
        (* t <$ dp *)
        t <@ set_bad1(map (fun c:ciphertext => c.`4) (filter (fun (c:ciphertext) => c.`1 = n) Mem.lc));
        ROin.sample(n,C.ofint 0);
        ROout.set((n,C.ofint 0), witness); 
        log.[n] <- (a,c,t);
        return (n,a,c,t);
      }
  
      proc dec (nact: nonce * associated_data * message * tag) : 
        (nonce * associated_data * message) option = {
        return None;
      }
   
    }
    
    proc distinguish () = {
      var b, ns, forged, i, n, r, t;

      bad1 <- false; cbad1 <- 0;
      bad2 <- false; cbad2 <- 0;

      b <@ CPA_game(CCA_CPA_Adv(BNR_Adv(A)), O).main(); 

      forged <- false;
      if (size Mem.lc <= qdec) {
        ns <- undup (List.map (fun (p:ciphertext) => p.`1) Mem.lc);
        i <- 0;
        while (i < size ns) {
          n  <- List.nth witness ns i;
          if ((n,C.ofint 0) \in ROout.m) {
            r <@ ROin.get(n,C.ofint 0);
            forged <- forged || test_poly_in n Mem.lc r (oget log.[n]);
          } else { 
            r <@ ROin.get(n,C.ofint 0);
            t <@ set_bad2((map 
                (fun c:ciphertext => c.`4 - poly1305_eval r (topol c.`2 c.`3)) 
                (filter (fun c:ciphertext => c.`1 = n) Mem.lc)));
            ROout.set((n,C.ofint 0), witness); 
          }
          i <- i + 1;
        }
      }
      return forged;
    }

  }.

  local clone import GenEager as ROIN with
     type from <- (nonce*C.counter),
     type to   <- poly_in, 
     type input <- unit,
     type output <- bool,
     op sampleto <- fun _ => dpoly_in
     proof *.
  realize sampleto_ll by apply dpoly_in_ll.

  op inv (mr1 mr2 : (nonce*C.counter, poly_in) fmap) 
         (ms1 ms2 : (nonce*C.counter, poly_out) fmap)
         (log1 log2: (ciphertext, plaintext) fmap)
         (lc1 lc2 : ciphertext list) 
         (lenc1 lenc2: nonce list)
         (ndec1 ndec2 :int)
         (nlog : (nonce, associated_data * message * tag) fmap) = 
     inv_cpa mr1 ms1 log1 log2 lc1 lc2 lenc1 lenc2 ndec1 ndec2 /\
     mr1 = mr2 /\ 
     (forall s, s \in ms1 = s \in ms2) /\
     (forall s, s \in ms1 = s \in mr1) /\
     size lenc1 <= qenc /\ ndec1 <= qdec /\
     (forall n, n \in nlog = n \in lenc1) /\ size lc1 <= ndec1 /\
     (forall n, n \in lenc1 => let (a,c,t) = oget nlog.[n] in (n,a,c,t) \in log1) /\
     (forall n a c t, (n,a,c,t) \in lc1 => valid_topol a c) /\
     (forall n, n \in nlog => let (a,c,t) = oget nlog.[n] in valid_topol a c) /\
     (forall n a c t, (n,a,c,t) \in lc1 => n \in nlog => nlog.[n] <> Some (a, c, t)) /\
     (forall n, n \in lenc1 => 
        let (a,c,t) = oget nlog.[n] in
        let r = oget mr1.[(n,C.ofint 0)] in
        let s = oget ms1.[(n,C.ofint 0)] in
        s = t - poly1305_eval r (topol a c)).

  local lemma step4_1 &m:
    Pr[Split1.IdealAll.MainD(G9(BNR_Adv(A)), SplitC2.RO_Pair(ROin, ROout)).distinguish() @ &m : res] <=
     Pr[UFCMA(ROIN.RO).distinguish() @ &m : res \/ UFCMA.bad2] + Pr[UFCMA(ROIN.RO).distinguish() @ &m : UFCMA.bad1].
  proof. 
    apply (ler_trans
             Pr[UFCMA(ROIN.RO).distinguish() @ &m : (res \/ UFCMA.bad2) \/ UFCMA.bad1]); last first.
    + by rewrite Pr [mu_or]; smt(mu_bounded).
    byequiv (_: ={glob A} ==> !(UFCMA.bad1 \/ UFCMA.bad2){2} => ={res}) => //; last by smt().
    move=> {&m}; proc.
    inline{1} 2; inline{1} 4; inline{1} 5.
    seq 5 5:
      (!(UFCMA.bad1 \/ UFCMA.bad2){2} => 
        b1{1} = b{2} /\ UFCMA.cbad1{2} <= size BNR.lenc{1} /\
        UFCMA.cbad2{2} = 0 /\
        inv ROin.m{1} ROIN.RO.m{2} ROout.m{1} ROout.m{2} 
        Mem.log{1} Mem.log{2} Mem.lc{1} Mem.lc{2} 
           BNR.lenc{1} BNR.lenc{2} BNR.ndec{1} BNR.ndec{2}
           UFCMA.log{2}).
    + inline*;wp;
      call (_: UFCMA.bad1 \/ UFCMA.bad2, 
             UFCMA.cbad1{2} <= size BNR.lenc{1} /\
             UFCMA.cbad2{2} = 0 /\
             inv ROin.m{1} ROIN.RO.m{2} ROout.m{1} ROout.m{2} 
                 Mem.log{1} Mem.log{2} Mem.lc{1} Mem.lc{2} 
                 BNR.lenc{1} BNR.lenc{2} BNR.ndec{1} BNR.ndec{2}
                 UFCMA.log{2} /\
             (forall n c, (n,c) \in ROF.m => n \in BNR.lenc){1}).
      + by apply A_ll. 
      + proc => /=. sp 1 1; if; 1: (by move=> />); 2: by auto.
        wp; inline{1} 1; inline{2} 1; wp.
        inline{1} 2; inline{1} 3; inline{1} 7; inline{2} 2.
        seq 6 4:
          ( !(UFCMA.bad1 \/ UFCMA.bad2){2} /\
            ={c, p, n, a, p0} /\ (p = p0 /\ p = (n, a, p2)){1} /\
             p2{1} = p1{2} /\ c2{1} = c1{2} /\ size c2{1} <= max_cipher_size /\
             UFCMA.cbad1{2} <= size BNR.lenc{1} /\ UFCMA.cbad2{2} = 0 /\
             (forall n' c, (n',c) \in ROF.m => n' \in n::BNR.lenc){1} /\
              inv ROin.m{1} ROIN.RO.m{2} ROout.m{1} ROout.m{2} 
                  Mem.log{1} Mem.log{2} Mem.lc{1} Mem.lc{2} 
                  BNR.lenc{1} BNR.lenc{2} BNR.ndec{1} BNR.ndec{2}
                  UFCMA.log{2} /\
             check_plaintext BNR.lenc{1} p{1} ).
        + by ecall (equ_cc n{1} ROin.m{1} ROout.m{1}); rewrite /check_plaintext; auto => /> /#.
        inline{1} 5; inline{1} 8.
        rcondt{1} ^if.
        + by move=> &m; auto => />; rewrite /SplitD.test /= C.insubdK //=; smt(C.gt0_max_counter).
        inline{1} 9; wp.
        call{1} (_: true ==> true); 1: by islossless; apply dextra_block_ll.
        inline *.
        rcondt{1} ^if{1}; 1: by move=> &m; auto => /> /#.
        rcondt{1} ^if; 1: by move=> &m; auto => /> /#.
        rcondt{2} ^if{1}; 1: by auto => /> *; smt (size_map size_filter count_size ge0_qdec).
        rcondt{2} ^if; 1: by move=> &m; auto => /> /#.
        swap{1} 12 -11; swap{1} 16 -14; swap{2} 8 -7; swap{2} 3 -1 ;wp.
        rnd (fun s => s + poly1305_eval r{2} (topol a{2} c1{2}))
            (fun s => s - poly1305_eval r{2} (topol a{2} c1{2})); rnd; skip => /> *.
        have hh : forall c1 c2 c3 c4, 
          (c1, c2, c3, c4) \in Mem.lc{2} =>
          c4 \in map (fun (c : ciphertext) => c.`4) (filter (fun (c : ciphertext) => c.`1 = c1) Mem.lc{2}).
        + by move=> c1 c2 c3 c4 h;rewrite mapP; exists (c1,c2,c3,c4); rewrite mem_filter.
        progress; 1..14, 16:
          smt (size_map size_filter count_size mapP dpoly_in_ll poly_out_sub_add 
                  poly_out_add_sub get_setE mk_rs_ofpair mem_set). 
        apply/negP; rewrite get_setE; case : (n2 = n{2}). 
        + by move=> <<- [] 3!<<-; apply H24; rewrite (hh _ _ _ _ H25).
        smt (size_map size_filter count_size mapP get_setE mem_set). 
      + move=> &2 _; islossless.
        while true (size p).
        + move=> z; wp; conseq (_: true) => />; 2: by islossless.
          smt (size_drop size_eq0 gt0_block_size).
        by auto; smt (size_ge0 size_eq0).         
      + move=> _; proc; inline *; sp; if => //.
        swap 13 9; wp; conseq (_: true) => />; 1: smt(); islossless.
        while true (size p2).
        + move=> z; wp; conseq (_: true) => //=; 2: by islossless.
          move=> &h.
          smt (size_drop size_eq0 gt0_block_size).
        by auto; smt (size_ge0 size_eq0 dpoly_out_ll). 
      + by proc; inline *; sp 1 1; if; auto => /> *; smt(get_setE mem_set).
      + by move=> &2 _; islossless.
      + by move=> _; conseq />; islossless.
      by auto => />; smt (dkey_ll mem_empty ge0_qenc ge0_qdec).
    inline{1} 1;wp; sp 0 1.
    case: ((UFCMA.bad1\/UFCMA.bad2){2}).
    + while{1} true (size ns - i){1}.
      + by move=> _ z; wp; conseq (_: true) => //; 1:smt(); islossless.
      if{2}.
      + while{2} ((UFCMA.bad1\/UFCMA.bad2){2}) (size ns - i){2}.
        + move=> _ z; sp; wp; if.
          + by conseq (_: true) => //; 1:smt(); islossless.
          by inline *; wp; conseq (_: true) => //; 1:smt(); islossless. 
        by auto => /> /#.
      by auto => /> /#. 
    rcondt{2} 1; 1: by auto => /> /#.
    while ( ={i, ns, Mem.lc} /\ uniq ns{1} /\ 0 <= i{1} /\
            UFCMA.cbad1{2} <= qenc /\ UFCMA.cbad2{2} <= i{1} /\ size ns{1} <= qdec /\
            ROin.m{1} = ROIN.RO.m{2} /\ size Mem.lc{1} <= qdec /\
            forged0{1} = (forged{2} \/ UFCMA.bad1{2} \/ UFCMA.bad2{2}) /\
            (forall n a c t, (n, a, c, t) \in Mem.lc{1} => valid_topol a c) /\
            (forall s, s \in ROout.m{1} = s \in ROout.m{2}) /\  
            (forall s, s \in ROout.m{1} = s \in ROin.m{1}) /\  
            (forall j, 
              i{1} <= j < size ns{1} =>
              let n = nth witness ns{1} j in
              (n, C.ofint 0) \in ROout.m{1} =>
              let (a, c, t) = oget UFCMA.log{2}.[n] in
              !(n,a,c,t) \in Mem.lc{1} /\ valid_topol a c /\
              let r = oget ROin.m{1}.[(n, C.ofint 0)] in 
              let s = oget ROout.m{1}.[(n, C.ofint 0)] in 
              s = t - poly1305_eval r (topol a c))); last first.
    + by auto => />; smt (undup_uniq size_undup size_map).
    inline{1} 2; rcondt{1} 3. 
    + by move=> *;auto => />;rewrite /test /= C.insubdK; smt (C.gt0_max_counter).
    inline{1} 3; inline{1} 4; sp 0 1; wp.
    call{1} (_: true ==> true); 1: by islossless.
    wp; inline *; if{2}.
    + rcondf{2} ^if; 1: by auto => /#.
      do 2! (rcondf{1} ^if{1}; 1: by auto => /#).
      auto; rnd{1}; auto => /> &1 &2 h1 hi hcbad hcbad2 hns h2 h3 h4 h5 h6 h7 h8 r _ s _ e.
      rewrite mk_rs_ofpair /=.
      pose t1 := test_poly _ _ _ _; pose t2 := test_poly_in _ _ _ _.
      have /# : t1 = t2; rewrite /t1 /t2 /test_poly /test_poly_in => {t1 t2} /=.
      have := h6 i{2} h7; rewrite h4 => /(_ h8).
      case (oget UFCMA.log{2}.[_]) => a c t /= [# h9 hv ->].
      rewrite hv /= !has_map !has_filter /predI /=.
      apply/eq_iff/eq_in_has => @/preim -[] /=.
      smt (poly_out_add_sub' topol_inj mem_filter poly_out_swap).
    rcondt{2} ^if; 1: by auto => /#.
    (* rcondt{2} ^if; 1: by auto=> /> *; smt (size_map size_filter count_size size_ge0). *)
    do 2! (rcondt{1} ^if{1}; 1: by auto => /#).
    swap{1} 6 -5; swap{1} 10 -8; swap{2} 2 -1; swap{2} 6 -4.
    auto => /> *; rewrite mk_rs_ofpair /=; rewrite !get_setE /=.
    split; 1:smt(); split; 1:smt();split.
    + case: (forged{2}) => //; case: ((UFCMA.bad1\/UFCMA.bad2){2}) => //= ??.
      - have[|]->//=:=H13.
      have:=H13; rewrite negb_or => /> *.
      rewrite /test_poly /= /poly1305 /= /test_bad.
      pose f := fun (c : ciphertext) => c.`4 - poly1305_eval r3L (topol c.`2 c.`3).
      pose m := List.filter _ _.
      rewrite  hasP /=.
      case: (r4L \in map f m); rewrite mapP. 
      - rewrite eqT=> [][]c [].
        smt (poly_out_add_sub poly_out_sub_add hasP mapP).
      apply contraNF. 
      smt (poly_out_add_sub poly_out_sub_add hasP mapP).
    smt(mem_set index_uniq get_setE).
  qed.

  import StdBigop.Bigreal.

  local lemma step4_bad1 &m :
    Pr[UFCMA(ROIN.RO).distinguish() @ &m : UFCMA.bad1] <= qenc%r * (qdec%r * pr1_poly_out).
  proof.
    have <- : Pr[UFCMA(ROIN.RO).distinguish() @ &m : UFCMA.bad1 /\ UFCMA.cbad1 <= qenc] =
              Pr[UFCMA(ROIN.RO).distinguish() @ &m : UFCMA.bad1].
    + byequiv (_ : ={glob A} ==> ={UFCMA.bad1} /\ (UFCMA.cbad1{1} <= qenc)) => //.
      proc. sp 2 2.
      inline{1} 3; inline{1} 4; inline{1} 5.
      inline{2} 3; inline{2} 4; inline{2} 5.
      sim (_: ={RO.m, UFCMA.log, UFCMA.bad1, UFCMA.cbad1, SplitC2.I2.RO.m, 
                SplitD.ROF.RO.m, BNR.ndec, BNR.lenc, Mem.lc, Mem.log}) 
          /(UFCMA.cbad1{1} <= qenc) : (={UFCMA.bad1}).
      + proc; auto => /#.
      auto; smt(ge0_qenc ge0_qdec).

    fel 2 UFCMA.cbad1                     (* the query counter *)
        (fun i=> (qdec%r * pr1_poly_out)) (* probability of bad first occurring during ith query *)
        (qenc)                            (* the bound on the counter (after which we stop caring) *)
        UFCMA.bad1                        (* the bad event *)
        [UFCMA(RO).set_bad1 : (UFCMA.cbad1 < qenc /\ size lt <= qdec)] 
                                          (* condition(s) under which the oracle(s) do not respond *)
        true; auto.                       (* general unconditional invariants *)
    + by rewrite sumr_const count_predT size_range; smt(ge0_qenc ge0_qdec).
    + proc; rcondt ^if; 1: by auto.
      wp; conseq (_: t \in lt) => />; rnd; auto => /> *.
      apply (StdOrder.RealOrder.ler_trans ((size lt{hr})%r * pr1_poly_out)).
      + by apply mu_mem_le_mu1 => ?; rewrite (dpoly_out_funi x witness).
      smt (mu_bounded).
    + by move=> c;proc; auto => /> /#.
    by move=> b c; proc; auto => />.
  qed.

  require IterProc.

  clone import IterProc as IPNonce with
    type t <- nonce
    proof *.

  (* print IPNonce.iter_perm. *)

  op sub_map (m1 : (nonce * C.counter, 'a) fmap) (m2 : (nonce * C.counter, 'a) fmap) i l =
    (forall n, (n, C.ofint 0) \in m2 => (n,C.ofint 0) \in m1) /\
    (forall n, (n, C.ofint 0) \in m2 => m1.[(n,C.ofint 0)] = m2.[(n,C.ofint 0)]) /\
    (forall j, 0 <= j < i => (nth witness l j, C.ofint 0) \in m1) /\
    (forall n, (n, C.ofint 0) \in m1 => (n, C.ofint 0) \in m2 \/ exists j, 0 <= j < i /\ n = nth witness l j).


  local module UF = {
    var forged : bool
  }.

  local module Orcl : Orcl = {
    proc f (n : nonce) : unit = {
      var r, t;
      if ((n,C.ofint 0) \in ROout.m) {
        r <@ ROIN.RO.get(n,C.ofint 0);
        UF.forged <- UF.forged || test_poly_in n Mem.lc r (oget UFCMA.log.[n]);
      } else { 
        r <@ ROIN.RO.get(n,C.ofint 0);
        t <@ UFCMA(ROIN.RO).set_bad2((map 
                (fun c:ciphertext => c.`4 - poly1305_eval r (topol c.`2 c.`3)) 
                (filter (fun c:ciphertext => c.`1 = n) Mem.lc)));
        ROout.set((n,C.ofint 0), witness); 
      }
    }
  }.

  local module UFCMA2 (ROin:SplitC2.I1.RO) = {

    proc set_bad1 = UFCMA(ROin).set_bad1

    proc set_bad2  = UFCMA(ROin).set_bad2

    module O = {
      proc init () = {
        UFCMA.log <- empty;
        ROin.init(); ROout.init(); ROF.init();
      }
    
      proc enc (nap : nonce * associated_data * message) : 
          nonce * associated_data * message * tag = {
        var n, a, p, c, t;
        (n,a,p) <- nap;
        c <@ EncRnd.cc(n,p);   
        (* t <$ dp *)
        t <@ set_bad1(map (fun c:ciphertext => c.`4) Mem.lc);
        ROin.sample(n,C.ofint 0);
        ROout.set((n,C.ofint 0), witness); 
        UFCMA.log.[n] <- (a,c,t);
        return (n,a,c,t);
      }
  
      proc dec (nact: nonce * associated_data * message * tag) : 
        (nonce * associated_data * message) option = {
        return None;
      }
   
    }
    
    proc distinguish () = {
      var b, ns, ns1, ns2;

      UFCMA.bad1 <- false; UFCMA.cbad1 <- 0;
      UFCMA.bad2 <- false; UFCMA.cbad2 <- 0;

      b <@ CPA_game(CCA_CPA_Adv(BNR_Adv(A)), O).main(); 

      UF.forged <- false;
      if (size Mem.lc <= qdec) {
        ns <- undup (List.map (fun (p:ciphertext) => p.`1) Mem.lc);
        ns1 <- filter (fun n => (n,C.ofint 0) \in ROout.m) ns;
        ns2 <- filter (fun n => (n,C.ofint 0) \notin ROout.m) ns;
        Iter(Orcl).iter(ns1++ns2);
      }
      return UF.forged;
    }

  }.

  local module UFCMA3 (ROin:SplitC2.I1.RO) = {

    proc set_bad1 = UFCMA(ROin).set_bad1

    proc set_bad2  = UFCMA(ROin).set_bad2

    module O = {
      proc init () = {
        UFCMA.log <- empty;
        ROin.init(); ROout.init(); ROF.init();
      }
    
      proc enc (nap : nonce * associated_data * message) : 
          nonce * associated_data * message * tag = {
        var n, a, p, c, t;
        (n,a,p) <- nap;
        c <@ EncRnd.cc(n,p);   
        (* t <$ dp *)
        t <@ set_bad1(map (fun c:ciphertext => c.`4) Mem.lc);
        ROin.sample(n,C.ofint 0);
        ROout.set((n,C.ofint 0), witness); 
        UFCMA.log.[n] <- (a,c,t);
        return (n,a,c,t);
      }
  
      proc dec (nact: nonce * associated_data * message * tag) : 
        (nonce * associated_data * message) option = {
        return None;
      }
   
    }
    
    proc distinguish () = {
      var b, ns, ns1, ns2, i, n, r, t;

      UFCMA.bad1 <- false; UFCMA.cbad1 <- 0;
      UFCMA.bad2 <- false; UFCMA.cbad2 <- 0;

      b <@ CPA_game(CCA_CPA_Adv(BNR_Adv(A)), O).main(); 

      UF.forged <- false;
      if (size Mem.lc <= qdec) {
        ns <- undup (List.map (fun (p:ciphertext) => p.`1) Mem.lc);
        ns1 <- filter (fun n => (n,C.ofint 0) \in ROout.m) ns;
        ns2 <- filter (fun n => (n,C.ofint 0) \notin ROout.m) ns;
        i <- 0;
        while (i < size ns1) {
          n <- nth witness ns1 i;
          r <@ ROIN.RO.get(n,C.ofint 0);
          UF.forged <- UF.forged || test_poly_in n Mem.lc r (oget UFCMA.log.[n]);
          i <- i + 1;
        }
        i <- 0;
        while (i < size ns2) {
          n <- nth witness ns2 i;
          r <@ ROIN.RO.get(n,C.ofint 0);
          t <@ UFCMA(ROIN.RO).set_bad2((map 
                (fun c:ciphertext => c.`4 - poly1305_eval r (topol c.`2 c.`3)) 
                (filter (fun c:ciphertext => c.`1 = n) Mem.lc)));
          i <- i + 1;
        }
      }
      return UF.forged;
    }

  }.


  local equiv equiv_step4 :
    UFCMA(ROIN.RO).distinguish ~ UFCMA3(ROIN.RO).distinguish :
    ={glob A} ==> ={res, UFCMA.bad2}.
  proof.
  transitivity UFCMA2(RO).distinguish (={glob A} ==> ={res, UFCMA.bad2}) (={glob A} ==> ={res, UFCMA.bad2})=> //=.
  + smt().
  + proc; sim; sp.
    seq 2 2 : (={glob UFCMA, glob RO} /\ forged{1} = UF.forged{2})=> /=; 1: sim.
    if; 1, 3: by auto.
    transitivity{1} {
            UF.forged <- forged;
            ns <- undup (map (fun (p:ciphertext) => p.`1) Mem.lc);
            Iter(Orcl).iter(ns);
            forged <- UF.forged;
          }
          (={glob UFCMA, glob RO, forged} ==> ={UFCMA.bad2, forged})
          (={glob UFCMA, glob RO} /\ forged{1} = UF.forged{2} ==> ={UFCMA.bad2} /\ forged{1} = UF.forged{2})=> //=; 1: smt().
    + inline*.
      sp; wp.
      while(={ns, glob UFCMA, RO.m} /\ forged{1} = UF.forged{2} /\ l{2} = drop i{1} ns{1} /\ 0 <= i{1}).
      - sp; if; 1: smt(nth0_head nth_drop).
        + wp 5 5=> />. 
          by conseq(:_==> ={RO.m, UFCMA.log,Mem.lc} /\ forged{1} = UF.forged{2})=> />; 2: sim; 
            smt(nth0_head nth_drop size_drop size_eq0 drop_nth drop0).
        by wp 8 8=>/>; conseq(:_==> ={UFCMA.bad2, UFCMA.cbad2, RO.m}); 2: sim;
          smt(nth0_head nth_drop size_drop size_eq0 drop_nth drop0).
      by auto; smt(drop0 size_ge0 size_eq0).
      sp 1 0; wp=> />.
    call (iter_perm Orcl _); auto.
    - proc=> /=; inline*.
      case: (t1{1} = t2{1}).
      - rcondt{1} 4; 2: rcondt{2} 4; 1,2: auto=> />.
        + sp; if; auto=> />; smt(mem_set).
        + sp; if; auto=> />; smt(mem_set).
        by sim.
      sp; if{2}.
      + rcondt{1} 3=> />; 1: by auto=> />; if; auto=> />; smt(mem_set).
        if{1}.
        - rcondt{2} 7; 1: by auto=> />; auto.
          sp; swap 7 -6; swap{1} 1.
          wp; conseq(:_==> (r1,r3){1} = (r3,r1){2}); auto.
          move=> /> *.
          rewrite !mem_set !get_setE/= !oget_some/=. 
          rewrite (eq_sym t2{2}) H /= => />; do ! split=> /> *; -1: smt().
          by rewrite set_setE /=  (eq_sym t2{2}) H /=; smt().
        rcondf{2} 7; 1: by auto=> />; auto.
        sp; swap{1} 5 -3; swap{2} 11 -9; swap{1} 14 -12; swap{2} 8 -6; swap{1} 1.
        swap{1} [6..12] 5; sim.
        swap{2} 6 4; sim.
        wp; rnd; rnd; rnd; skip=> /> *.
        rewrite !mem_set /= !get_setE /= !oget_some /=.
        have h: t1{2} <> t2{2} by smt().
        by rewrite (eq_sym t2{2}) h /= => /> *; rewrite set_setE //=; smt().
      rcondf{1} 3=> />; 1: auto=> />.
      - if; auto; smt(mem_set).
      if{1}.
      - rcondt{2} 14; 1: by auto=> />; auto; smt(mem_set).
        sp.
        swap{1} 7 -5; swap{1} 11 -8; swap{2} 5 -3; swap{2} 14 -13.
        swap{1} 6 10; sim.
        swap{2} [13..17] -7; sim.
        wp; rnd; rnd; rnd; skip=> /> *.        
        rewrite !mem_set /= !get_setE /= !oget_some /=.
        have h: t1{2} <> t2{2} by smt().
        by rewrite (eq_sym t2{2}) h /= => /> *; rewrite set_setE //=; smt().
      rcondf{2} 14; 1: by auto=> />; auto; smt(mem_set).
      sp.
      swap 5 -3; swap 14 -11; swap 18 -14.
      swap{1} 3; swap{1} 1 3.
      wp; auto=> /> *.
      rewrite !mem_set /= !get_setE /= !oget_some /=.
      have h: t1{2} <> t2{2} by smt().
      rewrite (eq_sym t2{2}) h /= => /> *. 
      rewrite set_setE //= (eq_sym t2{2}) h /= => /> *. 
      by rewrite set_setE //= (eq_sym t2{2}) h /= => /> *; smt().
    move=> /> *; pose l := undup _.
    by have:=perm_filterC (fun n => (n,C.ofint 0) \in ROout.m{2}) l; rewrite /predC perm_eq_sym.
  proc; sp.
  seq 2 2 : (={glob UFCMA2,RO.m}); 1: by sim.
  inline*; if; auto; sp.
  splitwhile {1} 1 : size ns2 < size l.
  seq 1 1 : (={glob UFCMA2,RO.m,ns,ns1,ns2} /\
               l{1} = ns2{2} /\
               ns{2} = undup (map (fun (p : ciphertext) => p.`1) Mem.lc{2}) /\
               ns1{2} = filter (fun (n0 : nonce) => (n0, C.ofint 0) \in ROout.m{2}) ns{2} /\
               ns2{2} = filter (fun (n0 : nonce) => (n0, C.ofint 0) \notin ROout.m{2}) ns{2}).
  + move=> />.
    while(={glob UFCMA2, RO.m, ns, ns1, ns2} /\
        ns{2} = undup (map (fun (p : ciphertext) => p.`1) Mem.lc{2}) /\
        ns1{2} = filter (fun (n0 : nonce) => (n0, (C.ofint 0)%C) \in ROout.m{2}) ns{2} /\
        ns2{2} = filter (fun (n0 : nonce) => (n0, (C.ofint 0)%C) \notin ROout.m{2}) ns{2} /\
        l{1} = drop i{2} ns1{2} ++ ns2{2} /\ 0 <= i{2});
      2: by auto=>/>; smt(drop0 size_eq0 size_ge0 size_cat drop_oversize).    
    sp=> />.
    conseq(: n{2} = nth witness ns1{2} i{2} /\ x{2} = (n{2}, (C.ofint 0)%C) /\
             n{1} = head witness l{1} /\
             (((UF.forged{1}, UFCMA.bad2{1}, UFCMA.cbad2{1}, UFCMA.bad1{1}, UFCMA.cbad1{1}, RO.m{1}, UFCMA.log{1}, SplitC2.I2.RO.m{1},
                SplitD.ROF.RO.m{1}, BNR.ndec{1}, BNR.lenc{1}, Mem.lc{1}, Mem.log{1}, (glob A){1}) =
               (UF.forged{2}, UFCMA.bad2{2}, UFCMA.cbad2{2}, UFCMA.bad1{2},
                UFCMA.cbad1{2}, RO.m{2}, UFCMA.log{2}, SplitC2.I2.RO.m{2},
                SplitD.ROF.RO.m{2}, BNR.ndec{2}, BNR.lenc{2}, Mem.lc{2}, Mem.log{2},
                (glob A){2}) /\
             ={RO.m, ns, ns1, ns2}) /\
             ns{2} = undup (map (fun (p : ciphertext) => p.`1) Mem.lc{2}) /\
             ns1{2} = filter (fun (n0 : nonce) => (n0, (C.ofint 0)%C) \in ROout.m{2}) ns{2} /\
             ns2{2} = filter (fun (n0 : nonce) => (n0, (C.ofint 0)%C) \notin ROout.m{2}) ns{2} /\
             l{1} = drop i{2} ns1{2} ++ ns2{2} /\ 0 <= i{2}) /\
             (l{1} <> [] /\ size ns2{1} < size l{1}) /\ i{2} < size ns1{2} /\
             ={n} /\ (forall j, 0 <= j < size ns1{2} => (nth witness ns1{2} j, C.ofint 0) \in ROout.m{2}) ==> _).
    - move=> /> &2.
      pose l := undup _; pose l1 := List.filter _ _; pose l2 := List.filter _ _.
      move=> *.
      have:= H1; rewrite size_cat ltz_addr => h. 
      rewrite -nth0_head  nth_cat //= h /= nth_drop //= => *.
      have:=allP (fun (n0 : nonce) => (n0, (C.ofint 0)%C) \in SplitC2.I2.RO.m{2}) l1.
      have->//=->//=:=filter_all (fun (n0 : nonce) => (n0, (C.ofint 0)%C) \in SplitC2.I2.RO.m{2}) l.
      by apply mem_nth.
    rcondt{1} 1; 1: by auto=> /#.
    wp 5 4.
    conseq(:_==> ={UF.forged, RO.m}) => />; 2: by sim; auto.
    move=> /> &2.
    pose l := undup _; pose l1 := List.filter _ _; pose l2 := List.filter _ _.
    rewrite size_cat //= ltz_addr => *.
    by rewrite (drop_nth witness i{2}) //= drop0 //=; smt(size_drop size_eq0 size_ge0 size_cat).

  sp.
  while(={UF.forged,UFCMA.bad2,UFCMA.cbad2,UFCMA.log,Mem.lc,Mem.log,RO.m,ns,ns1,ns2} /\
        l{1} = drop i{2} ns2{2} /\ 0 <= i{2} /\
        ns{2} = undup (map (fun (p : ciphertext) => p.`1) Mem.lc{2}) /\
        ns1{2} = filter (fun (n0 : nonce) => (n0, C.ofint 0) \in ROout.m{2}) ns{2} /\
        ns2{2} = filter (fun (n0 : nonce) => (n0, C.ofint 0) \notin ROout.m{2}) ns{2} /\
        sub_map ROout.m{1} ROout.m{2} i{2} ns2{2}); 2: by auto; smt(drop0 size_eq0 size_ge0).
  sp.
  conseq(: n{2} = nth witness ns2{2} i{2} /\ x0{2} = (n{2}, C.ofint 0) /\
      n{1} = head witness l{1} /\
      (={UF.forged, UFCMA.bad2, UFCMA.cbad2, UFCMA.log, Mem.lc, Mem.log, RO.m, ns, ns1, ns2} /\
      l{1} = drop i{2} ns2{2} /\ 0 <= i{2} /\ ns{2} = undup (map (fun (p : ciphertext) => p.`1) Mem.lc{2}) /\
      ns1{2} = filter (fun (n0 : nonce) => (n0, (C.ofint 0)%C) \in ROout.m{2}) ns{2} /\
      ns2{2} = filter (fun (n0 : nonce) => (n0, (C.ofint 0)%C) \notin ROout.m{2}) ns{2} /\
      sub_map ROout.m{1} ROout.m{2} i{2} ns2{2}) /\ l{1} <> [] /\ i{2} < size ns2{2} /\ ={n} ==> _).
  + by move=> /> *; rewrite (drop_nth witness) //=.
  rcondf{1} 1; 1: auto=> />.
  + move=> *.
    rewrite -nth0_head nth_drop //=.
    pose l:= undup _.
    pose l2 := List.filter _ _ .
    have/=:=H3 (nth witness l2 i{m}).
    apply absurd=> /= -> /=.
    rewrite negb_or negb_exists/=; split=> /> *.
    - have:=allP (fun (n0 : nonce) => (n0, C.ofint 0) \notin SplitC2.I2.RO.m{m}) l2.
      have-> /= -> //=:=filter_all (fun (n0 : nonce) => (n0, C.ofint 0) \notin SplitC2.I2.RO.m{m}) l.
      by rewrite mem_nth //=.
    case: (0 <= a < i{m})=> //= [#]*.
    have := before_index witness (nth witness l2 i{m}) l2 a.
    have huniq:uniq l2 by rewrite filter_uniq undup_uniq.
    by rewrite index_uniq //=; smt().
  wp 9 8; conseq(:_==> ={UFCMA.bad2, UFCMA.cbad2, t, RO.m})=> />; 2: by sim; auto.
  move=> /> &1 &2.
  pose l := undup _.
  pose l2 := List.filter _ _.
  move=> *.
  have h1: forall j, 0 <= j < size l2 => (nth witness l2 j, C.ofint 0) \notin ROout.m{2}.
  + move=> j [#] *.
    - have:=allP (fun (n0 : nonce) => (n0, C.ofint 0) \notin ROout.m{2}) l2.
      have-> /= -> //=:=filter_all (fun (n0 : nonce) => (n0, C.ofint 0) \notin SplitC2.I2.RO.m{2}) l.
      by rewrite mem_nth //=.
  rewrite (drop_nth witness i{2} l2) //= drop0 //=; do ! split=> /> *.
  + smt().
  + smt(mem_set).
  + rewrite get_set_neqE /=; smt(mem_nth).
  + smt(mem_set).
  + smt(mem_set).
  + smt(mem_set size_drop size_ge0 size_eq0).
  + smt(mem_set size_drop size_ge0 size_eq0).
  qed.


  local lemma step4_bad2 &m :
    Pr[UFCMA(ROIN.RO).distinguish() @ &m : UFCMA.bad2] <= qdec%r * pr1_poly_out.
  proof.
    
 
  local lemma step4_bad &m : 
    Pr[UFCMA(ROIN.RO).distinguish() @ &m : UFCMA.bad] <= (qenc + qdec)%r * (qdec%r * pr1_poly_out) .
  proof.
    have <- : Pr[UFCMA(ROIN.RO).distinguish() @ &m : UFCMA.bad /\ UFCMA.cbad <= qenc + qdec] =
              Pr[UFCMA(ROIN.RO).distinguish() @ &m : UFCMA.bad].
    + byequiv (_ : ={glob A} ==> ={UFCMA.bad} /\ (UFCMA.cbad{1} <= qenc + qdec)) => //.
      proc. 
      inline{1} 3; inline{1} 4; inline{1} 5.
      inline{2} 3; inline{2} 4; inline{2} 5.
      sim (_: ={RO.m, UFCMA.log, UFCMA.bad, UFCMA.cbad, SplitC2.I2.RO.m, 
                SplitD.ROF.RO.m, BNR.ndec, BNR.lenc, Mem.lc, Mem.log}) 
          /(UFCMA.cbad{1} <= qenc + qdec) : (={UFCMA.bad}).
      + proc; auto => /#.
      auto; smt(ge0_qenc ge0_qdec).

    fel 2 UFCMA.cbad                      (* the query counter *)
        (fun i=> (qdec%r * pr1_poly_out)) (* probability of bad first occurring during ith query *)
        (qenc + qdec)                     (* the bound on the counter (after which we stop caring) *)
        UFCMA.bad                         (* the bad event *)
        [UFCMA(RO).set_bad : (UFCMA.cbad < qenc + qdec /\ size lt <= qdec)] 
                                          (* condition(s) under which the oracle(s) do not respond *)
        true; auto.                       (* general unconditional invariants *)
    + by rewrite sumr_const count_predT size_range; smt(ge0_qenc ge0_qdec).
    + proc; rcondt ^if; 1: by auto.
      wp; conseq (_: t \in lt) => />; rnd; auto => /> *.
      apply (StdOrder.RealOrder.ler_trans ((size lt{hr})%r * pr1_poly_out)).
      + by apply mu_mem_le_mu1 => ?; rewrite (dpoly_out_funi x witness).
      smt (mu_bounded).
    + by move=> c;proc; auto => /> /#.
    by move=> b c; proc; auto => />.
  qed.
  
  local module UFCMA_f = {
    var bad : bool
    var cbad : int   
     
    proc set_bad (n: nonce) = {
      var r;
      r <$ dpoly_in;
      if (cbad < qdec /\ size Mem.lc <= qdec) { 
         bad <- bad || test_poly_in n Mem.lc r (oget UFCMA.log.[n]);
         cbad <- cbad + 1;
      }
    } 

    proc main () = {
      var b, ns, i, n;

      bad <- false; cbad <- 0;

      b <@ CPA_game(CCA_CPA_Adv(BNR_Adv(A)), UFCMA(LRO).O).main(); 
      if (size Mem.lc <= qdec) {
        ns <- undup (List.map (fun (p:ciphertext) => p.`1) Mem.lc);
        i <- 0;
        while (i < size ns) {
          n  <- List.nth witness ns i;
          if ((n,C.ofint 0) \in ROout.m) set_bad(n);
          else SplitC2.I2.RO.set((n, C.ofint 0), witness);
          i <- i + 1;
        }
      }
    }
  }.

  local lemma step4_forged &m : 
    Pr[UFCMA(ROIN.RO).distinguish() @ &m : res ] <= qdec%r * qdec%r * pr_zeropol.
  proof.
    have -> : Pr[UFCMA(ROIN.RO).distinguish() @ &m : res ] = 
              Pr[UFCMA(ROIN.LRO).distinguish() @ &m : res ].
    + byequiv (ROIN.RO_LRO_D UFCMA) => //.
    have -> : Pr[UFCMA(ROIN.LRO).distinguish() @ &m : res ] =
              Pr[UFCMA_f.main() @ &m : UFCMA_f.bad /\ UFCMA_f.cbad <= qdec].
    + byequiv (_: ={glob A} ==> res{1} = UFCMA_f.bad{2} /\ UFCMA_f.cbad{2} <= qdec) => //. 
      proc.
      seq 3 3 : (={Mem.lc, RO.m, ROout.m, UFCMA.log} /\ 
                 UFCMA_f.bad{2} = false /\ UFCMA_f.cbad{2} = 0 /\ 
                 RO.m{2} = empty).
      + by sp 2 2; inline *; wp; sp; sim />.
      sp; if => //; last by auto => />; rewrite ge0_qdec.
      while ( ={i, ns, ROout.m, Mem.lc, UFCMA.log} /\ uniq ns{1} /\ 0 <= i{1} <= size ns{1}/\
              forged{1} = UFCMA_f.bad{2} /\ UFCMA_f.cbad{2} <= i{2} /\
              size ns{1} <= qdec /\ size Mem.lc{1} <= qdec /\
              (forall j, i{1} <= j < size ns{2} => ! (nth witness ns{1} j, C.ofint 0) \in RO.m{1})).
      + sp; if; 1: done.
        + inline *; rcondt{2} ^if; 1: auto => /> * /#.
          rcondt{1} ^if; auto => /> *; 1: smt().
          smt(get_setE mem_set index_uniq).
        wp; call (_: ={ROout.m}); 1: by auto.
        call{1} (_: true ==> true); 1: by islossless.
        inline *; rcondt{1} ^if; auto => /> *; 1: smt().
        smt(dpoly_in_ll mem_set index_uniq).
      auto => /> *; smt (undup_uniq size_undup size_map mem_empty size_ge0).
    
    fel 2 UFCMA_f.cbad                      
        (fun i=> qdec%r * pr_zeropol)
        qdec
        UFCMA_f.bad
        [UFCMA_f.set_bad : (UFCMA_f.cbad < qdec /\ size Mem.lc <= qdec)] 
        true; auto.              
    + by rewrite sumr_const count_predT size_range; smt(ge0_qenc ge0_qdec).
    + proc; rcondt ^if; 1: by auto.
      wp; conseq (_: test_poly_in n Mem.lc r (oget UFCMA.log.[n])) => />; rnd; auto => /> *.
      by apply pr_TPI_ok.
    + by move=> c;proc; auto => /> /#.
    by move=> b c; proc; auto => />.
  qed.

  lemma conclusion &m : 
    Pr[CCA_game(BNR_Adv(A), RealOrcls(ChaChaPoly)).main() @ &m : res] <=
      Pr[CCA_game(CCA_CPA_Adv(BNR_Adv(A)), EncRnd).main() @ &m : res] +
      (Pr[Indist.Distinguish(D(BNR_Adv(A)), IndBlock).game() @ &m : res] -
       Pr[Indist.Distinguish(D(BNR_Adv(A)), IndRO).game() @ &m : res]) + 
       (qdec%r)^2 * pr_zeropol +
       (qenc + qdec)%r * (qdec%r * pr1_poly_out).
   proof. 
     have := step2 (BNR_Adv(A)) _ &m.
     + by move=> *;islossless;apply (A_ll (BNR(O)));islossless.
     have := step3 &m.
     have := step4_1 &m. have := step4_bad &m. have := step4_forged &m.
     have -> /#: (qdec%r)^2 = qdec%r * qdec%r by ring.
   qed.

end section PROOFS.

