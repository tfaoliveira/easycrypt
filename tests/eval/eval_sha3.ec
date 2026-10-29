(* Keccak-f[1600] and SHA3-256 (FIPS 202) on 64-bit lanes represented by
   integers. The state is an abstract array type given by [init] and
   [_.[_]], as the arrays of the Jasmin library: each step builds a new
   array from the previous one, so evaluation relies on the memoisation
   of the functions given to [init], and equality on an [eval] rule. The
   round constants and the rotation offsets are computed from the
   algorithms of FIPS 202. *)
require import AllCore List IntDiv BitEncoding.
import BS2Int.

op hex (n x : int) : int list = mkseq (fun i => x %/ 256 ^ (n - 1 - i) %% 256) n.

(* ---------------------------------------------------------------- *)
(* Arrays of 25 lanes. A model of the axioms: lists of size 25, with
   [init f = mkseq f 25] and [a.[i] = nth 0 a i]. *)
type state.

op init : (int -> int) -> state.
op "_.[_]" : state -> int -> int.

axiom getE f i : 0 <= i < 25 => (init f).[i] = f i.

op to_list (a : state) = mkseq (fun i => a.[i]) 25.

axiom eqE (a b : state) : (a = b) <=> (to_list a = to_list b).

hint simplify in eval : getE, eqE.

(* ---------------------------------------------------------------- *)
(* Bitwise operations on n-bit integers *)
op xor (n a b : int) : int =
  let xa = int2bs n a in
  let xb = int2bs n b in
  bs2int (mkseq (fun i => nth false xa i <> nth false xb i) n).

op andn (n a b : int) : int =               (* (not a) and b *)
  let xa = int2bs n a in
  let xb = int2bs n b in
  bs2int (mkseq (fun i => !nth false xa i /\ nth false xb i) n).

op rotl64 (x n : int) = (x * 2 ^ n) %% 2 ^ 64 + x %/ 2 ^ (64 - n).

(* ---------------------------------------------------------------- *)
(* FIPS 202, Algorithms 5 and 6: the round constants *)
op lfsr (r : int) : int =
  let r = 2 * r in if 256 <= r then xor 9 r 0x171 else r.

op rc (t : int) : bool = iter (t %% 255) lfsr 1 %% 2 = 1.

op RC (ir : int) : int =
  foldr (fun j acc => if rc (j + 7 * ir) then acc + 2 ^ (2 ^ j - 1) else acc)
    0 (iota_ 0 7).

(* FIPS 202, Algorithm 2: the rotation offsets, indexed by x + 5 y *)
op offsets : int list =
  (foldl (fun (acc : (int * int) * int list) t =>
     let (xy, offs) = acc in
     ((xy.`2, (2 * xy.`1 + 3 * xy.`2) %% 5),
      put offs (xy.`1 + 5 * xy.`2) ((t + 1) * (t + 2) %/ 2 %% 64)))
   ((1, 0), nseq 25 0) (iota_ 0 24)).`2.

(* FIPS 202, 3.2: the step mappings, A[x, y] = a.[x + 5 y] *)
op theta (a : state) : state =
  let c = mkseq (fun x =>
    xor 64 a.[x] (xor 64 a.[x + 5] (xor 64 a.[x + 10] (xor 64 a.[x + 15] a.[x + 20])))) 5 in
  let d = mkseq (fun x =>
    xor 64 (nth 0 c ((x + 4) %% 5)) (rotl64 (nth 0 c ((x + 1) %% 5)) 1)) 5 in
  init (fun i => xor 64 a.[i] (nth 0 d (i %% 5))).

op rho (a : state) : state = init (fun i => rotl64 a.[i] (nth 0 offsets i)).

op pi (a : state) : state =
  init (fun i => a.[(i %% 5 + 3 * (i %/ 5)) %% 5 + 5 * (i %% 5)]).

op chi (a : state) : state =
  init (fun i =>
    let x = i %% 5 in let y = i %/ 5 in
    xor 64 a.[i] (andn 64 a.[(x + 1) %% 5 + 5 * y] a.[(x + 2) %% 5 + 5 * y])).

op iota_step (ir : int) (a : state) : state =
  init (fun i => if i = 0 then xor 64 a.[0] (RC ir) else a.[i]).

op keccak_f (a : state) : state =
  foldl (fun a ir => iota_step ir (chi (pi (rho (theta a))))) a (iota_ 0 24).

(* ---------------------------------------------------------------- *)
(* SHA3-256: rate 136 bytes, domain separation and padding 0x06 ... 0x80
   (0x86 when a single byte of padding is needed) *)
op zero_state : state = init (fun _ => 0).

op pad (m : int list) : int list =
  let n = 135 - size m %% 136 in
  if n = 0 then m ++ [0x86] else m ++ [0x06] ++ nseq (n - 1) 0 ++ [0x80].

op lanes (bs : int list) : int list =
  mkseq (fun i => foldr (fun j acc => nth 0 bs (8 * i + j) + 256 * acc) 0 (iota_ 0 8)) 17.

op absorb (a : state) (blk : int list) : state =
  let l = lanes blk in
  keccak_f (init (fun i => if i < 17 then xor 64 a.[i] (nth 0 l i) else a.[i])).

op sha3_256 (m : int list) : int list =
  let p = pad m in
  let a = foldl absorb zero_state (mkseq (fun k => take 136 (drop (136 * k) p)) (size p %/ 136)) in
  take 32 (flatten (map (fun w => mkseq (fun j => w %/ 2 ^ (8 * j) %% 256) 8) (to_list a))).

(* ---------------------------------------------------------------- *)
(* Constants of FIPS 202 *)
check map RC (iota_ 0 24) =
  [0x1; 0x8082; 0x800000000000808a; 0x8000000080008000; 0x808b; 0x80000001; 0x8000000080008081; 0x8000000000008009; 0x8a; 0x88; 0x80008009; 0x8000000a; 0x8000808b; 0x800000000000008b; 0x8000000000008089; 0x8000000000008003; 0x8000000000008002; 0x8000000000000080; 0x800a; 0x800000008000000a; 0x8000000080008081; 0x8000000000008080; 0x80000001; 0x8000000080008008].
check offsets =
  [0; 1; 62; 28; 27; 36; 44; 6; 55; 20; 3; 10; 43; 25; 39; 41; 45; 15; 21; 8; 18; 2; 61; 56; 14].

(* Keccak-f[1600] on the all-zero state (Keccak team's reference values);
   the equality of states goes through the rule eqE *)
check keccak_f zero_state = init (fun i => nth 0
  [0xf1258f7940e1dde7; 0x84d5ccf933c0478a; 0xd598261ea65aa9ee; 0xbd1547306f80494d; 0x8b284e056253d057; 0xff97a42d7f8e6fd4; 0x90fee5a0a44647c4; 0x8c5bda0cd6192e76; 0xad30a6f71b19059c; 0x30935ab7d08ffc64; 0xeb5aa93f2317d635; 0xa9a6e6260d712103; 0x81a57c16dbcf555f; 0x43b831cd0347c826; 0x1f22f1a11a5569f; 0x5e5635a21d9ae61; 0x64befef28cc970f2; 0x613670957bc46611; 0xb87c5a554fd00ecb; 0x8c3ee88a1ccf32c8; 0x940c7922ae3a2614; 0x1841f924a2c509e4; 0x16f53526e70465c2; 0x75f644e97f30a13b; 0xeaf1ff7b5ceca249] i).

(* FIPS 202 examples (SHA3-256 of "" and "abc") *)
check sha3_256 [] = (hex 32 0xa7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a).
check sha3_256 (hex 3 0x616263) = (hex 32 0x3a985da74fe225b2045c172d6bd390bd855f086e3e9d525b46bfe24511431532).

(* ---------------------------------------------------------------- *)
(* Padding corner cases, against Python's hashlib *)

(* 135 bytes: a single padding byte, 0x86 *)
check sha3_256 (hex 135 0x01080f161d242b323940474e555c636a71787f868d949ba2a9b0b7bec5ccd3dae1e8eff6fd040b121920272e353c434a51585f666d747b828990979ea5acb3bac1c8cfd6dde4ebf2f900070e151c232a31383f464d545b626970777e858c939aa1a8afb6bdc4cbd2d9e0e7eef5fc030a11181f262d343b424950575e656c737a81888f969da4ab) =
  (hex 32 0x64ccd300c1cf3d3846046bd588a1613e5ba619c09d45d4b7cc9afa093af29e19).

(* 136 bytes: a full block, then a block of padding only *)
check sha3_256 (hex 136 0x01080f161d242b323940474e555c636a71787f868d949ba2a9b0b7bec5ccd3dae1e8eff6fd040b121920272e353c434a51585f666d747b828990979ea5acb3bac1c8cfd6dde4ebf2f900070e151c232a31383f464d545b626970777e858c939aa1a8afb6bdc4cbd2d9e0e7eef5fc030a11181f262d343b424950575e656c737a81888f969da4abb2) =
  (hex 32 0xf106d1024a855c6a20d300bb53ec5472a1bae126fa630fee78219b51add7d768).

(* ---------------------------------------------------------------- *)
(* The rule eqE decides disequalities as well *)
check keccak_f zero_state <> zero_state.
check (keccak_f zero_state = zero_state) = false.

(* a wrong expected value is detected *)
fail check sha3_256 [] = (hex 32 0xa6ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a).
