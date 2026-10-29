(* The number-theoretic transform of ML-KEM (FIPS 203), over Z_3329:
   the mathematical definition (as a sum, with negative exponents for the
   inverse), and Algorithms 9 and 10 of FIPS 203 as procedures. They are
   checked against each other, against the constants of FIPS 203, and on
   the multiplication theorem. Exponentiation and inversion are computed
   with the [eval] rules of ZModP (exp_modexp, exp_neg_eval, inv_eval). *)
require import AllCore List IntDiv ZModP BitEncoding.
import BS2Int.

clone import ZModField as Zq with op p <= 3329 proof prime_p by admit.

abbrev exp = ZModpRing.exp.

op zt = inzmod 17.

op br7 (i : int) : int = bs2int (rev (int2bs 7 i)).

op sum (f : int -> zmod) (n : int) : zmod =
  foldr (fun j acc => f j + acc) zero (iota_ 0 n).

(* NTT and inverse, as in the definitions of FIPS 203 (4.3) *)
op ntt (f : zmod list) : zmod list =
  mkseq (fun i => sum (fun j =>
    nth zero f (2 * j + i %% 2) * exp zt ((2 * br7 (i %/ 2) + 1) * j)) 128) 256.

op invntt (f : zmod list) : zmod list =
  mkseq (fun i => sum (fun j =>
    inv (inzmod 128) * nth zero f (2 * j + i %% 2)
    * exp zt (- ((2 * br7 j + 1) * (i %/ 2)))) 128) 256.

(* Algorithms 11 and 12: multiplication in the NTT domain *)
op basemul (a b : zmod list) : zmod list =
  flatten (mkseq (fun i =>
    let g  = exp zt (2 * br7 i + 1) in
    let a0 = nth zero a (2 * i) in let a1 = nth zero a (2 * i + 1) in
    let b0 = nth zero b (2 * i) in let b1 = nth zero b (2 * i + 1) in
    [a0 * b0 + a1 * b1 * g; a0 * b1 + a1 * b0]) 128).

(* Schoolbook multiplication in Z_q[X]/(X^256 + 1) *)
op schoolbook (a b : zmod list) : zmod list =
  mkseq (fun k => sum (fun i =>
    if i <= k then nth zero a i * nth zero b (k - i)
    else - (nth zero a i * nth zero b (k - i + 256))) 256) 256.

module NTT = {
  (* FIPS 203, Algorithm 9 *)
  proc ntt(f : zmod list) : zmod list = {
    var i, len, start, j, z, t;
    i <- 1; len <- 128;
    while (2 <= len) {
      start <- 0;
      while (start < 256) {
        z <- exp zt (br7 i); i <- i + 1;
        j <- start;
        while (j < start + len) {
          t <- z * nth zero f (j + len);
          f <- put f (j + len) (nth zero f j - t);
          f <- put f j (nth zero f j + t);
          j <- j + 1;
        }
        start <- start + 2 * len;
      }
      len <- len %/ 2;
    }
    return f;
  }

  (* FIPS 203, Algorithm 10 *)
  proc invntt(f : zmod list) : zmod list = {
    var i, len, start, j, z, t;
    i <- 127; len <- 2;
    while (len <= 128) {
      start <- 0;
      while (start < 256) {
        z <- exp zt (br7 i); i <- i - 1;
        j <- start;
        while (j < start + len) {
          t <- nth zero f j;
          f <- put f j (t + nth zero f (j + len));
          f <- put f (j + len) (z * (nth zero f (j + len) - t));
          j <- j + 1;
        }
        start <- start + 2 * len;
      }
      len <- len * 2;
    }
    return map (fun x => x * inzmod 3303) f;
  }
}.

op pa = mkseq (fun i => inzmod (i * i * 31 + 7 * i + 1)) 256.
op pb = mkseq (fun i => inzmod (5 * i * i + 3)) 256.

(* ---------------------------------------------------------------- *)
(* Constants of FIPS 203 *)

(* 17 is a primitive 256-th root of unity modulo q *)
check exp zt 128 = - one.
check exp zt 256 = one.

(* 3303 = 128^-1 mod q (Algorithm 10) *)
check inv (inzmod 128) = inzmod 3303.

(* Appendix A: the first and last values of zeta^BitRev7(i) *)
check map (fun i => asint (exp zt (br7 i))) (iota_ 0 8)
  = [1; 1729; 2580; 3289; 2642; 630; 1897; 848].
check asint (exp zt (br7 127)) = 2154.

(* ---------------------------------------------------------------- *)
(* Exponentiation and inversion: corner cases *)
check exp zt (-1) * zt = one.
check exp zt (-128) = - one.
check exp zt (-256) = one.
check exp zt 0 = one /\ exp zero 0 = one.
check exp zero (-1) = zero.              (* inv zero = zero *)
check inv (- one) = - one.
check exp (inzmod 3328) (-3) = - one.    (* 3328 = -1 *)

(* ---------------------------------------------------------------- *)
(* The transforms *)

(* Algorithm 9 computes the NTT of the definition *)
check proc NTT.ntt(pa) = ntt pa.
check take 4 (ntt pa) = map inzmod [816; 772; 546; 1008].

(* the inverses: definition and Algorithm 10 *)
check invntt (ntt pa) = pa.
check proc NTT.invntt(ntt pa) = pa.

(* the NTT of 1 and of X *)
check ntt (one :: nseq 255 zero) = flatten (nseq 128 [one; zero]).
check ntt (zero :: one :: nseq 254 zero) = flatten (nseq 128 [zero; one]).

(* multiplication theorem: NTT^-1 (NTT a o NTT b) = a * b mod X^256 + 1 *)
check invntt (basemul (ntt pa) (ntt pb)) = schoolbook pa pb.
check take 4 (schoolbook pa pb) = map inzmod [521; 3138; 2789; 566].

(* X^128 * X^128 = X^256 = -1: the negacyclic wrap-around *)
check schoolbook (nseq 128 zero ++ one :: nseq 127 zero)
                 (nseq 128 zero ++ one :: nseq 127 zero)
  = (- one) :: nseq 255 zero.

(* a wrong expected value is detected *)
fail check proc NTT.ntt(pa) = pa.
