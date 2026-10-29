(* X25519 (RFC 7748) on integers modulo 2^255 - 19: the Montgomery
   ladder as a procedure, checked against the test vectors of the RFC and
   on corner cases (small-order and non-canonical points, clamping).
   The final inversion uses the native [modexp]. *)
require import AllCore List IntDiv.

op hex (n x : int) : int list = mkseq (fun i => x %/ 256 ^ (n - 1 - i) %% 256) n.

op p : int = 2 ^ 255 - 19.
op a24 : int = 121665.

(* little-endian encodings (RFC 7748, 5) *)
op le_int (bs : int list) : int = foldr (fun b acc => b + 256 * acc) 0 bs.
op le_bytes (x : int) : int list = mkseq (fun i => x %/ 256 ^ i %% 256) 32.

op clamp (k : int) : int =
  let k = k %/ 8 * 8 %% 2 ^ 255 in
  if k %/ 2 ^ 254 %% 2 = 1 then k else k + 2 ^ 254.

op decode_u (u : int list) : int = le_int u %% 2 ^ 255 %% p.

module X25519 = {
  proc ladder(k u : int) : int = {
    var x1, x2, z2, x3, z3, sw, t, kt, a, aa, b, bb, e, c, d, da, cb;
    x1 <- u; x2 <- 1; z2 <- 0; x3 <- u; z3 <- 1; sw <- 0;
    t <- 254;
    while (0 <= t) {
      kt <- k %/ 2 ^ t %% 2;
      sw <- (sw + kt) %% 2;
      if (sw = 1) { (x2, x3) <- (x3, x2); (z2, z3) <- (z3, z2); }
      sw <- kt;
      a  <- (x2 + z2) %% p; aa <- a * a %% p;
      b  <- (x2 - z2) %% p; bb <- b * b %% p;
      e  <- (aa - bb) %% p;
      c  <- (x3 + z3) %% p; d <- (x3 - z3) %% p;
      da <- d * a %% p; cb <- c * b %% p;
      x3 <- (da + cb) ^ 2 %% p;
      z3 <- x1 * (da - cb) ^ 2 %% p;
      x2 <- aa * bb %% p;
      z2 <- e * (aa + a24 * e) %% p;
      t  <- t - 1;
    }
    if (sw = 1) { (x2, x3) <- (x3, x2); (z2, z3) <- (z3, z2); }
    return x2 * modexp z2 (p - 2) p %% p;
  }

  proc x25519(k u : int list) : int list = {
    var r;
    r <@ ladder(clamp (le_int k), decode_u u);
    return le_bytes r;
  }

  (* RFC 7748, 5.2: k, u <- X25519(k, u), k, n times from k = u = 9 *)
  proc iterate(n : int) : int list = {
    var k, u, r, i;
    k <- le_bytes 9; u <- le_bytes 9; i <- 0;
    while (i < n) { r <@ x25519(k, u); u <- k; k <- r; i <- i + 1; }
    return k;
  }
}.

(* ---------------------------------------------------------------- *)
(* RFC 7748 test vectors *)

(* 5.2: the two single-call vectors; in the second one the top bit of
   the u-coordinate is set and must be ignored *)
check proc X25519.x25519((hex 32 0xa546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4), (hex 32 0xe6db6867583030db3594c1a424b15f7c726624ec26b3353b10a903a6d0ab1c4c)) = (hex 32 0xc3da55379de9c6908e94ea4df28d084f32eccf03491c71f754b4075577a28552).
check proc X25519.x25519((hex 32 0x4b66e9d4d1b4673c5ad22691957d6af5c11b6421e0ea01d42ca4169e7918ba0d), (hex 32 0xe5210f12786811d3f4b7959d0538ae2c31dbe7106fc03c3efc4cd549c715a493)) = (hex 32 0x95cbde9476e8907d7aade45cb4b873f88b595a68799fa152e6f8f7647aac7957).

(* 5.2: one and 1000 iterations *)
check proc X25519.iterate(1) = (hex 32 0x422c8e7a6227d7bca1350b3e2bb7279f7897b87bb6854b783c60e80311ae3079).
check proc X25519.iterate(1000) = (hex 32 0x684cf59ba83309552800ef566f2f4d3c1c3887c49360e3875f2eb94d99532c51).

(* 6.1: Diffie-Hellman *)
check proc X25519.x25519((hex 32 0x77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a), le_bytes 9) = (hex 32 0x8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a).
check proc X25519.x25519((hex 32 0x5dab087e624a8a4b79e17f8b83800ee66f3bb1292618b6fd1c2f8b27ff88e0eb), le_bytes 9) = (hex 32 0xde9edb7d7b7dc1b4d35b61c2ece435373f8343c85b78674dadfc7e146f882b4f).
check proc X25519.x25519((hex 32 0x77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a), (hex 32 0xde9edb7d7b7dc1b4d35b61c2ece435373f8343c85b78674dadfc7e146f882b4f)) = (hex 32 0x4a5d9d5ba4ce2de1728e3bf480350f25e07e21c947d19e3376f09b3c1e161742).
check proc X25519.x25519((hex 32 0x5dab087e624a8a4b79e17f8b83800ee66f3bb1292618b6fd1c2f8b27ff88e0eb), (hex 32 0x8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a)) = (hex 32 0x4a5d9d5ba4ce2de1728e3bf480350f25e07e21c947d19e3376f09b3c1e161742).

(* ---------------------------------------------------------------- *)
(* Corner cases *)

(* points of small order give the all-zero output *)
check proc X25519.x25519((hex 32 0x77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a), le_bytes 0) = nseq 32 0.
check proc X25519.x25519((hex 32 0x77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a), le_bytes 1) = nseq 32 0.
check proc X25519.x25519((hex 32 0x77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a), le_bytes (p - 1)) = nseq 32 0.

(* non-canonical u-coordinates are reduced modulo p *)
check proc X25519.x25519((hex 32 0x77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a), le_bytes p) = nseq 32 0.
check proc X25519.x25519((hex 32 0x77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a), le_bytes (p + 9)) = (hex 32 0x8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a).

(* clamping: the three low bits and the two high bits of the scalar
   are irrelevant *)
check proc X25519.x25519((hex 32 0x70076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92cea), le_bytes 9) = (hex 32 0x8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a).
check clamp (2 ^ 256 - 1) = 2 ^ 255 - 8 /\ clamp 0 = 2 ^ 254.

(* a wrong expected value is detected *)
fail check proc X25519.x25519((hex 32 0x5dab087e624a8a4b79e17f8b83800ee66f3bb1292618b6fd1c2f8b27ff88e0eb), (hex 32 0x8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a)) = (hex 32 0x8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a).
