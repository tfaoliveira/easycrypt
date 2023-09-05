(* -------------------------------------------------------------------- *)
require import AllCore Ring Finite.

(* -------------------------------------------------------------------- *)
abstract theory Multivariate.
  clone IDomain as Coeffs.      (* the integral domain of coeffcients *)

  type vars.                    (* the set of variables *)

  theory Monomials.
    type premonom = vars -> int.

    type monom.

    inductive ismonom (m : premonom) =
    | IsMonom of
          (forall i, 0 <= m i)
        & (is_finite (fun i => m i <> 0)).

    op tomonom : premonom -> monom.

    op ofmonom : monom -> premonom.

    axiom ofmonomK (m : monom) :
      tomonom (ofmonom m) = m.

    axiom tomonomK (m : premonom) :
      ismonom m => ofmonom (tomonom m) = m.
    
    axiom ismonom_monom (m : monom) : ismonom (ofmonom m).

    abbrev "_.[_]" (m : monom) (i : vars) =
      (ofmonom m) i.
  end Monomials.

  import Monomials.

  type prempoly = monom -> Coeffs.t.

  type mpoly.

  inductive ismpoly (p : prempoly) =
  | IsMpoly of (is_finite (fun m => p m <> Coeffs.zeror)).

  op tompoly : prempoly -> mpoly.

  op ofmpoly : mpoly -> prempoly.

  axiom ofmpolyK (p : mpoly) :
    tompoly (ofmpoly p) = p.

  axiom tompolyK (p : prempoly) :
    ismpoly p => ofmpoly (tompoly p) = p.

  axiom ismpoly_mpoly (p : mpoly) :
    ismpoly (ofmpoly p).
end Multivariate.
