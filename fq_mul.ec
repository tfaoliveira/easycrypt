require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel.
from Jasmin require import JWord.

op rshift_w32_int (a: W32.t) (b: int) =
  a `|>>` (W8.of_int b).

op eq_mod (a: int) (b: int) (q: int list) : bool.

(* assumes no overflow *)
op smull (a: W32.t) (b: W32.t) =
 (W32.of_int ((to_uint a) * (to_uint b))).

module M = {
  proc __fqmul (a:W16.t, b:W16.t, q: int) : W16.t = {

    var r:W16.t;
    var ad:W32.t;
    var bd:W32.t;
    var c:W32.t;
    var u:W32.t;
    var t:W32.t;

    ad <- (sigextu32 a);
  bd <- (sigextu32 b);
    (* only low order bits should matter here V*)
  c <- (smull ad bd); (* target for red *)
    (* STEP 1 of algorithm *)
    u <- (c * (W32.of_int (62209 `<<` 16)));
  u <- (rshift_w32_int u 16);
  (* LEFT + RIGHT shift = FAST MODULO Beta
  so u = m here *)
  (* probably doesnt have overflow, check change here *)
    (* calculate -q*m congr to q*(beta - m) *)
  t <- (smull u (W32.of_int (- q)));
    (* a + (beta - m)*q  *)
  t <- (t + c);
    (* (a + (beta-m)*q)/beta *)
  t <- (rshift_w32_int t 16);
    (* r = t (mod beta) *)
  r <- (truncateu16 t);

  (* return r = r' + q ,
  where r' is such that a*b = m*q + r'*beta
  so r' congr to a*(beta^-1) mod q *)
    return (r);
  }
}.

hoare fqmul_contr (a: W16.t) (b: W16.t) (q: int) : M.__fqmul : true ==> eq_mod (W16.to_uint(a*b)) (W16.to_uint res) [4294967296; q].
proof.
  zify.
admit.
qed.

    (* This works with the sigext factored out,
    doesn't work if we do left shift then right shift
    limitation of the proof technique? *)
module M2 = {
  proc __fqmul_part1 (a:W16.t, b:W16.t, q: int) : W32.t = {

  var r:W16.t;
  var ad:W32.t;
  var bd: W32.t;
  var c:W32.t;
  var u:W32.t;

  ad <- sigextu32 a;
  bd <- sigextu32 b;
    
  (* only low order bits should matter here V*)
  c <- (ad * bd); (* target for red *)
  (* STEP 1 of algorithm *)
  u <- (c * (W32.of_int (62209)));   
  return (u);
  }

  proc __fqmul_part2 (a: W16.t, b: W16.t, u: W32.t, q: int) =
  {
    var ad: W32.t;
    var bd: W32.t;
    var c: W32.t;
    var t: W32.t;
    var r: W16.t;
    
    ad <- sigextu32 a;
    bd <- sigextu32 b;
    c <- smull ad bd;

    t <- (smull u (W32.of_int (- q)));
    (* a + (beta - m)*q  *)
  t <- (t + c);
    (* (a + (beta-m)*q)/beta *)
  t <- (rshift_w32_int t 16);
    (* r = t (mod beta) *)
    r <- (truncateu16 t);
    return (r);
  }
}.

hoare fqmul_part1_contr (a: W16.t) (b: W16.t) (q: int) : M2.__fqmul_part1 : true ==> eq_mod (W16.to_uint(a*b)) (W32.to_uint res * 3329) [65536].
proof.
  zify.
  admit.
qed.

module Ms = {
  proc __fqmul_symb (a:W16.t, b:W16.t, q: int, qinv: int, R: int, Rinv: int) : W16.t = {

    var r:W16.t;
    var ad:W32.t;
    var bd:W32.t;
    var c:W32.t;
    var u:W32.t;
    var t:W32.t;

    ad <- (sigextu32 a);
  bd <- (sigextu32 b);
    (* only low order bits should matter here V*)
  c <- (smull ad bd); (* target for red *)
    (* STEP 1 of algorithm *)
    u <- (c * (W32.of_int (R * qinv)));
  u <- u * (W32.of_int Rinv);
  (* LEFT + RIGHT shift = FAST MODULO Beta
  so u = m here *)
  (* probably doesnt have overflow, check change here *)
    (* calculate -q*m congr to q*(beta - m) *)
  t <- (smull u (W32.of_int (- q)));
    (* a + (beta - m)*q  *)
  t <- (t + c);
    (* (a + (beta-m)*q)/beta *)
  t <- t * (W32.of_int Rinv);
  (* r = t (mod beta) *)
    
  r <- (truncateu16 t);

    return (r);
  }
}.

print (/\).

hoare fqmul_symb_contr (a: W16.t) (b: W16.t) (q: int) (qinv: int) (R: int) (Rinv: int) : Ms.__fqmul_symb : eq_mod (q*qinv) 1 [R] /\ eq_mod (R*Rinv) 1 [q] ==> eq_mod (W16.to_uint (a*b)) (W16.to_uint (res) * Rinv) [R*R; q].
proof.
zify.


(*
inline fn __fqmul_cas(reg u16 a b q) -> reg u16
requires #[prover=smt]{q == KYBER_Q}
requires #[prover=smt] {(-32768)*KYBER_Q <=64s se_16_64(a)*se_16_64(b)  &&  se_16_64(a)*se_16_64(b) < 64s 32768*KYBER_Q}
ensures #[prover=smt] {(-1)*KYBER_Q <=64s se_16_64(result.0)  &&  se_16_64(result.0) < 64s KYBER_Q}
ensures #[prover=cas] {eqmod((int)result.0,(int)a * (int)b * 169,pair((int) q,65536))}
{
  reg u32 ad;
  reg u32 bd;
  reg u32 c;
  reg u32 t;
  reg u16 r;
  reg u32 test;
  reg u32 u;

  test = (32s)q;

  ad = (32s)a;
  bd = (32s)b;

  c = ad * bd;

  u = c * QINV;
  #[tran=cas] u <<= 16;
  //u = #SAR_32(u, 16);
  #[tran=cas] u >>s= 16;
  t = u * test;
  #[tran=cas] t = c - t;
  //t = #SAR_32(t, 16);
  #[tran=cas] t >>s= 16;
  r = t;
  return r;
} 
 *)
