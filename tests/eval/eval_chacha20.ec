(* ChaCha20 (RFC 8439), on integers: a functional specification and an
   imperative block function, checked against the test vectors of the RFC
   and against each other. Words are integers in [0, 2^32); bitwise
   operations go through the (native) bit encodings of BS2Int. *)
require import AllCore List IntDiv BitEncoding.
import BS2Int.

(* [hex n x]: the n bytes of x, most significant first. *)
op hex (n x : int) : int list = mkseq (fun i => x %/ 256 ^ (n - 1 - i) %% 256) n.

op xor (n a b : int) : int =
  let xa = int2bs n a in
  let xb = int2bs n b in
  bs2int (mkseq (fun i => nth false xa i <> nth false xb i) n).

op add32 (a b : int) = (a + b) %% 2 ^ 32.
op rotl32 (x n : int) = (x * 2 ^ n) %% 2 ^ 32 + x %/ 2 ^ (32 - n).

(* RFC 8439, 2.1 *)
op qr (a b c d : int) : int * int * int * int =
  let a = add32 a b in let d = rotl32 (xor 32 d a) 16 in
  let c = add32 c d in let b = rotl32 (xor 32 b c) 12 in
  let a = add32 a b in let d = rotl32 (xor 32 d a) 8 in
  let c = add32 c d in let b = rotl32 (xor 32 b c) 7 in
  (a, b, c, d).

op qr_at (s : int list) (a b c d : int) : int list =
  let r = qr (nth 0 s a) (nth 0 s b) (nth 0 s c) (nth 0 s d) in
  put (put (put (put s a r.`1) b r.`2) c r.`3) d r.`4.

op dround (s : int list) : int list =
  let s = qr_at s 0 4  8 12 in let s = qr_at s 1 5  9 13 in
  let s = qr_at s 2 6 10 14 in let s = qr_at s 3 7 11 15 in
  let s = qr_at s 0 5 10 15 in let s = qr_at s 1 6 11 12 in
  let s = qr_at s 2 7  8 13 in qr_at s 3 4  9 14.

(* little-endian words and bytes *)
op word_at (bs : int list) (i : int) : int =
  nth 0 bs (4 * i) + 2 ^ 8 * nth 0 bs (4 * i + 1)
  + 2 ^ 16 * nth 0 bs (4 * i + 2) + 2 ^ 24 * nth 0 bs (4 * i + 3).

op le_bytes (ws : int list) : int list =
  flatten (map (fun w => mkseq (fun j => w %/ 2 ^ (8 * j) %% 256) 4) ws).

(* RFC 8439, 2.3: the counter is taken modulo 2^32 *)
op init_state (key : int list) (ctr : int) (nonce : int list) : int list =
  [0x61707865; 0x3320646e; 0x79622d32; 0x6b206574]
  ++ mkseq (word_at key) 8 ++ [ctr %% 2 ^ 32] ++ mkseq (word_at nonce) 3.

op block (key : int list) (ctr : int) (nonce : int list) : int list =
  let s0 = init_state key ctr nonce in
  le_bytes (map (fun (p : int * int) => add32 p.`1 p.`2) (zip (iter 10 dround s0) s0)).

(* RFC 8439, 2.4 *)
op encrypt (key : int list) (ctr : int) (nonce : int list) (m : int list) : int list =
  flatten (mkseq (fun j =>
    map (fun (p : int * int) => xor 8 p.`1 p.`2)
        (zip (take 64 (drop (64 * j) m)) (block key (ctr + j) nonce)))
    ((size m + 63) %/ 64)).

(* An imperative block function, in the style of an implementation. *)
module ChaCha = {
  proc block(key : int list, ctr : int, nonce : int list) : int list = {
    var s0, s, i, out;
    s0 <- init_state key ctr nonce;
    s <- s0;
    i <- 0;
    while (i < 10) {
      s <- qr_at s 0 4  8 12; s <- qr_at s 1 5  9 13;
      s <- qr_at s 2 6 10 14; s <- qr_at s 3 7 11 15;
      s <- qr_at s 0 5 10 15; s <- qr_at s 1 6 11 12;
      s <- qr_at s 2 7  8 13; s <- qr_at s 3 4  9 14;
      i <- i + 1;
    }
    out <- [];
    i <- 0;
    while (i < 16) {
      out <- out ++ le_bytes [add32 (nth 0 s i) (nth 0 s0 i)];
      i <- i + 1;
    }
    return out;
  }
}.

(* ---------------------------------------------------------------- *)
(* RFC 8439 test vectors *)

(* 2.1.1: the quarter round *)
check qr 0x11111111 0x01020304 0x9b8d6f43 0x01234567
  = (0xea2a92f4, 0xcb1cf8ce, 0x4581472e, 0x5881c4bb).

(* 2.3.2: the block function, functional and imperative *)
check block (iota_ 0 32) 1 (hex 12 0x000000090000004a00000000) =
  (hex 64 0x10f1e7e4d13b5915500fdd1fa32071c4c7d1f4c733c068030422aa9ac3d46c4ed2826446079faa0914c2d705d98b02a2b5129cd1de164eb9cbd083e8a2503c4e).
check proc ChaCha.block(iota_ 0 32, 1, (hex 12 0x000000090000004a00000000)) =
  (hex 64 0x10f1e7e4d13b5915500fdd1fa32071c4c7d1f4c733c068030422aa9ac3d46c4ed2826446079faa0914c2d705d98b02a2b5129cd1de164eb9cbd083e8a2503c4e).

(* 2.4.2: encryption of the "sunscreen" plaintext (114 bytes, 2 blocks) *)
check encrypt (iota_ 0 32) 1 (hex 12 0x000000000000004a00000000)
  (hex 114 0x4c616469657320616e642047656e746c656d656e206f662074686520636c617373206f66202739393a204966204920636f756c64206f6666657220796f75206f6e6c79206f6e652074697020666f7220746865206675747572652c2073756e73637265656e20776f756c642062652069742e) =
  (hex 114 0x6e2e359a2568f98041ba0728dd0d6981e97e7aec1d4360c20a27afccfd9fae0bf91b65c5524733ab8f593dabcd62b3571639d624e65152ab8f530c359f0861d807ca0dbf500d6a6156a38e088a22b65e52bc514d16ccf806818ce91ab77937365af90bbf74a35be6b40b8eedf2785e42874d).

(* A.1, test vector #1: all-zero key, nonce and counter *)
check block (nseq 32 0) 0 (nseq 12 0) =
  (hex 64 0x76b8e0ada0f13d90405d6ae55386bd28bdd219b8a08ded1aa836efcc8b770dc7da41597c5157488d7724e03fb8d84a376a43b8f41518a11cc387b669b2ee6586).

(* ---------------------------------------------------------------- *)
(* Corner cases (expected values from an independent implementation) *)

(* the bitwise helpers on extreme words *)
check xor 32 0xffffffff 0x0f0f0f0f = 0xf0f0f0f0.
check rotl32 0x80000001 1 = 0x00000003.
check add32 0xffffffff 1 = 0.

(* the functional and imperative blocks agree on the all-ones key *)
check proc ChaCha.block(nseq 32 255, 0xffffffff, nseq 12 255) =
  block (nseq 32 255) 0xffffffff (nseq 12 255).

(* the counter wraps around modulo 2^32: a 65-byte message from counter
   2^32 - 1 uses the blocks 2^32 - 1 and 0 *)
check block (iota_ 0 32) (2 ^ 32) (hex 12 0x000000000000004a00000000) = block (iota_ 0 32) 0 (hex 12 0x000000000000004a00000000).
check encrypt (iota_ 0 32) 0xffffffff (hex 12 0x000000000000004a00000000)
  (hex 65 0x000306090c0f1215181b1e2124272a2d303336393c3f4245484b4e5154575a5d606366696c6f7275787b7e8184878a8d909396999c9fa2a5a8abaeb1b4b7babdc0) =
  (hex 65 0x6d2adc52dd65553c08f3de9c9059f5e579af041bf029cf72693f3193e6453c84913fe5509d6047386eb7e50f95093b0f2f161a7ced100642cb2244ff01bd2ec86f).

(* empty message; decryption is encryption *)
check encrypt (iota_ 0 32) 1 (hex 12 0x000000000000004a00000000) [] = [].
check encrypt (iota_ 0 32) 7 (hex 12 0x000000000000004a00000000) (encrypt (iota_ 0 32) 7 (hex 12 0x000000000000004a00000000) (hex 114 0x4c616469657320616e642047656e746c656d656e206f662074686520636c617373206f66202739393a204966204920636f756c64206f6666657220796f75206f6e6c79206f6e652074697020666f7220746865206675747572652c2073756e73637265656e20776f756c642062652069742e)) =
  (hex 114 0x4c616469657320616e642047656e746c656d656e206f662074686520636c617373206f66202739393a204966204920636f756c64206f6666657220796f75206f6e6c79206f6e652074697020666f7220746865206675747572652c2073756e73637265656e20776f756c642062652069742e).

(* a wrong expected value is detected *)
fail check block (nseq 32 0) 0 (nseq 12 0) = (hex 64 0x77b8e0ada0f13d90405d6ae55386bd28bdd219b8a08ded1aa836efcc8b770dc7da41597c5157488d7724e03fb8d84a376a43b8f41518a11cc387b669b2ee6586).
