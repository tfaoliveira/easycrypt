(* Large exponents. Powers too large to compute are evaluation errors (no
   anomaly), and 2 ^ n is not computed when only its value modulo 2 ^ w is
   needed ([W.of_int (x * 2 ^ n)], [(x * 2 ^ n) %% 2 ^ w]) or when the
   quotient [x %/ 2 ^ n] is 0: e.g. the shifts of the words of the Jasmin
   library, x `<<<` n = of_int (to_uint x * 2 ^ n), with a count n of 64
   bits (VPSLLV_4u64). *)
require import AllCore List IntDiv QFABV.

(* -------------------------------------------------------------------- *)
(* powers *)
check 2 ^ 100 = 1267650600228229401496703205376.
check 1 ^ (2 ^ 70) = 1.
check 0 ^ (2 ^ 70) = 0 /\ 0 ^ 0 = 1.
check (-1) ^ (2 ^ 70) = 1 /\ (-1) ^ (2 ^ 70 + 1) = -1.

(* exponent >= 2^62: was "exponent too large" *)
expect fail "tests/eval/eval_bigpow.ec: line 18 (5-17): evaluation failed: exponent too large: 2 ^ 9223372036854775808 has more than 4294967296 bits"
eval 2 ^ (2 ^ 63).
(* exponent < 2^62: was an anomaly (Z.pow: risk of overflow in mpz type) *)
expect fail "tests/eval/eval_bigpow.ec: line 21 (5-26): evaluation failed: exponent too large: 2 ^ 72340172838076673 has more than 4294967296 bits"
eval 2 ^ 72340172838076673.
expect fail "tests/eval/eval_bigpow.ec: line 23 (5-17): evaluation failed: exponent too large: 3 ^ 1099511627776 has more than 4294967296 bits"
eval 3 ^ (2 ^ 40).

(* modexp with a modulus 0 is a power *)
check modexp 3 200 0 = 3 ^ 200.
expect fail "tests/eval/eval_bigpow.ec: line 28 (5-33): evaluation failed: exponent too large: 2 ^ 72340172838076673 has more than 4294967296 bits"
eval modexp 2 72340172838076673 0.
check modexp 2 72340172838076673 1000 = 392.

(* a negative number of iterations below min_int: was an anomaly (Z.Overflow) *)
check iter (- 2 ^ 100) (fun x => x + 1) 0 = 0.

(* -------------------------------------------------------------------- *)
(* quotients and remainders by powers of 2 *)
check 12345 %/ 2 ^ (2 ^ 63) = 0 /\ 12345 %% 2 ^ (2 ^ 63) = 12345.
check 0 %/ 2 ^ (2 ^ 63) = 0 /\ 0 %% 2 ^ (2 ^ 63) = 0.
check 12345 %/ 3 ^ 72340172838076673 = 0.
check 12345 %/ 2 ^ 3 = 1543 /\ 12345 %% 2 ^ 3 = 1.
check 12345 %/ 2 ^ 14 = 0 /\ 12345 %/ 2 ^ 13 = 1.
check (-12345) %/ 2 ^ 3 = -1544 /\ (-12345) %% 2 ^ 3 = 7.
check (-12345) %/ 2 ^ 100 = -1.
(* the remainder is 2 ^ (2 ^ 63) - 12345: not computed *)
expect fail "tests/eval/eval_bigpow.ec: line 45 (5-29): evaluation failed: exponent too large: 2 ^ 9223372036854775808 has more than 4294967296 bits"
eval (-12345) %% 2 ^ (2 ^ 63).
check 12345 %/ 2 ^ 0 = 12345.
check 12345 %/ (-2) ^ 3 = -1543.

check (12345 * 2 ^ (2 ^ 63)) %% 2 ^ 64 = 0.
check (12345 * 2 ^ 72340172838076673) %% 2 ^ 64 = 0.
check (12345 * 2 ^ 60) %% 2 ^ 64 = (12345 * 1152921504606846976) %% 18446744073709551616.
check (- 12345 * 2 ^ 60 + 7) %% 2 ^ 64 = (- 12345 * 1152921504606846976 + 7) %% 18446744073709551616.
check (3 ^ 72340172838076673) %% 2 ^ 64 = modexp 3 72340172838076673 (2 ^ 64).
check (2 ^ 3 * 5) %% 2 ^ 4 = 8.

(* -------------------------------------------------------------------- *)
(* words, as in the Jasmin library *)
type W64.

op w2bits : W64 -> bool list.
op bits2w : bool list -> W64.
op of_int : int -> W64.
op to_uint : W64 -> int.
op to_sint : W64 -> int.

bind bitstring w2bits bits2w to_uint to_sint of_int W64 64.
realize gt0_size by admit.
realize tolistP by admit.
realize oflistP by admit.
realize touintP by admit.
realize tosintP by admit.
realize ofintP by admit.
realize size_tolist by admit.

op (`<<<`) : W64 -> int -> W64.
op (`>>>`) : W64 -> int -> W64.

(* the [eval] rules of the shifts in the Jasmin tests (JWord_exec.ec) *)
axiom shl_eval (w : W64) i : 0 <= i => w `<<<` i = of_int (to_uint w * 2 ^ i).
axiom shr_eval (w : W64) i : 0 <= i => w `>>>` i = of_int (to_uint w %/ 2 ^ i).

hint simplify in eval : shl_eval, shr_eval.

op ones = of_int (-1).

check ones `<<<` 0 = ones /\ ones `>>>` 0 = ones.
check ones `<<<` 4 = of_int 18446744073709551600.
check ones `>>>` 60 = of_int 15.
check ones `<<<` 63 = of_int (2 ^ 63) /\ ones `>>>` 63 = of_int 1.
check ones `<<<` 64 = of_int 0 /\ ones `>>>` 64 = of_int 0.
check ones `<<<` 100 = of_int 0 /\ ones `>>>` 100 = of_int 0.
(* counts of VPSLLV_4u64 / VPSRLV_4u64 that failed: 2^63 ("exponent too large") *)
check ones `<<<` (2 ^ 63) = of_int 0 /\ ones `>>>` (2 ^ 63) = of_int 0.
check ones `<<<` (2 ^ 64 - 1) = of_int 0 /\ ones `>>>` (2 ^ 64 - 1) = of_int 0.
(* and 0x0101010101010101 (anomaly) *)
check ones `<<<` 72340172838076673 = of_int 0.
check ones `>>>` 72340172838076673 = of_int 0.
check of_int 0 `<<<` 72340172838076673 = of_int 0.

(* the shifts of the lanes of a 256-bit word, as in VPSLLV_4u64 *)
op vpsllv (x c : W64 list) = map (fun (p : W64 * W64) => p.`1 `<<<` to_uint p.`2) (zip x c).
op vpsrlv (x c : W64 list) = map (fun (p : W64 * W64) => p.`1 `>>>` to_uint p.`2) (zip x c).

check vpsllv [ones; ones; ones; ones] [of_int 1; of_int 64; of_int (2 ^ 63); of_int 72340172838076673]
    = [of_int (2 ^ 64 - 2); of_int 0; of_int 0; of_int 0].
check vpsrlv [ones; ones; ones; ones] [of_int 1; of_int 64; of_int (2 ^ 63); of_int 72340172838076673]
    = [of_int (2 ^ 63 - 1); of_int 0; of_int 0; of_int 0].

(* [of_int] of an expression with a power: computed modulo 2 ^ 64 *)
check of_int (3 ^ 72340172838076673) = of_int (modexp 3 72340172838076673 (2 ^ 64)).
check of_int (- 2 ^ 72340172838076673 + 5) = of_int 5.
check of_int (2 ^ 63 + 2 ^ 63) = of_int 0.
check to_uint (of_int (2 ^ 64 + 2 ^ 3 * 3)) = 24.
expect fail "tests/eval/eval_bigpow.ec: line 115 (5-22): evaluation failed: negative exponent"
eval of_int (2 ^ (-1)).
