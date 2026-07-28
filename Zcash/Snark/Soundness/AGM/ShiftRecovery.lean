import Zcash.Snark.Soundness.GoodChallenge

/-!
# Recovering the unshifted multiopen value

The IPA opens the aggregate to `v + z⁻¹·(pU + ξ·sU) - ξ·<s,b>`, not to `v`.  `S` is absorbed
before `ξ` and `z`, so a raw-value error survives only on two linear root sets — an additive
`2 / |Fp|` loss.
-/

namespace Zcash.Snark

open Polynomial
open scoped ENNReal

/-- The exceptional `ξ` polynomial.  Its value is the coefficient of `z` after clearing the IPA
value shift denominator. -/
noncomputable def ipaShiftXiPolynomial (delta sEval : Fp) : Polynomial Fp :=
  Polynomial.C delta + Polynomial.C sEval * Polynomial.X

/-- For a fixed good `ξ`, the shifted IPA equality makes `z` a root of this linear polynomial. -/
noncomputable def ipaShiftZPolynomial
    (delta pU sU sEval xi : Fp) : Polynomial Fp :=
  Polynomial.C (-(pU + xi * sU)) +
    Polynomial.C (delta + xi * sEval) * Polynomial.X

@[simp] theorem ipaShiftXiPolynomial_eval (delta sEval xi : Fp) :
    (ipaShiftXiPolynomial delta sEval).eval xi = delta + xi * sEval := by
  simp [ipaShiftXiPolynomial]
  ring

@[simp] theorem ipaShiftZPolynomial_eval (delta pU sU sEval xi z : Fp) :
    (ipaShiftZPolynomial delta pU sU sEval xi).eval z =
      z * (delta + xi * sEval) - (pU + xi * sU) := by
  simp [ipaShiftZPolynomial]
  ring

theorem ipaShiftXiPolynomial_ne_zero {delta sEval : Fp} (hdelta : delta ≠ 0) :
    ipaShiftXiPolynomial delta sEval ≠ 0 := by
  intro hzero
  have hcoeff := congrArg (Polynomial.coeff · 0) hzero
  simp [ipaShiftXiPolynomial] at hcoeff
  exact hdelta hcoeff

theorem ipaShiftZPolynomial_ne_zero {delta pU sU sEval xi : Fp}
    (hslope : delta + xi * sEval ≠ 0) :
    ipaShiftZPolynomial delta pU sU sEval xi ≠ 0 := by
  intro hzero
  have hcoeff := congrArg (Polynomial.coeff · 1) hzero
  simp [ipaShiftZPolynomial] at hcoeff
  exact hslope hcoeff

/-- Two fresh good challenges remove the IPA's `U`/`S` value shift.  This is the scalar core needed
to turn the recursive extractor's shifted aggregate opening into the raw aggregate-value premise
consumed by algebraic multiopen unbatching. -/
theorem rawValue_of_shiftedValue_of_good
    (aggregateEval value pU sU sEval xi z : Fp) (hz : z ≠ 0)
    (hshifted : aggregateEval =
      value + z⁻¹ * (pU + xi * sU) - xi * sEval)
    (hgoodXi : xi ∉ szBadSet
      (ipaShiftXiPolynomial (aggregateEval - value) sEval))
    (hgoodZ : z ∉ szBadSet
      (ipaShiftZPolynomial (aggregateEval - value) pU sU sEval xi)) :
    aggregateEval = value := by
  by_contra hne
  have hdelta : aggregateEval - value ≠ 0 := sub_ne_zero.mpr hne
  have hxiNonzero := ipaShiftXiPolynomial_ne_zero (sEval := sEval) hdelta
  have hslope : aggregateEval - value + xi * sEval ≠ 0 := by
    have heval := (not_mem_szBadSet.mp hgoodXi) hxiNonzero
    simpa using heval
  have hzPolyNonzero := ipaShiftZPolynomial_ne_zero
    (pU := pU) (sU := sU) hslope
  apply hgoodZ
  rw [mem_szBadSet]
  refine ⟨hzPolyNonzero, ?_⟩
  rw [ipaShiftZPolynomial_eval]
  calc
    z * (aggregateEval - value + xi * sEval) - (pU + xi * sU)
        = z * (z⁻¹ * (pU + xi * sU)) - (pU + xi * sU) := by
            rw [hshifted]
            ring
    _ = 0 := by rw [← mul_assoc, mul_inv_cancel₀ hz, one_mul, sub_self]

theorem ipaShiftXiPolynomial_natDegree_le (delta sEval : Fp) :
    (ipaShiftXiPolynomial delta sEval).natDegree ≤ 1 := by
  change (Polynomial.C delta + Polynomial.C sEval * Polynomial.X).natDegree ≤ 1
  refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
  · exact (Polynomial.natDegree_C delta).le.trans (by omega)
  · exact Polynomial.natDegree_mul_le.trans
      (Nat.add_le_add (Polynomial.natDegree_C sEval).le Polynomial.natDegree_X_le)

theorem ipaShiftZPolynomial_natDegree_le (delta pU sU sEval xi : Fp) :
    (ipaShiftZPolynomial delta pU sU sEval xi).natDegree ≤ 1 := by
  change (Polynomial.C (-(pU + xi * sU)) +
    Polynomial.C (delta + xi * sEval) * Polynomial.X).natDegree ≤ 1
  refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
  · exact (Polynomial.natDegree_C (-(pU + xi * sU))).le.trans (by omega)
  · exact Polynomial.natDegree_mul_le.trans
      (Nat.add_le_add (Polynomial.natDegree_C (delta + xi * sEval)).le
        Polynomial.natDegree_X_le)

/-- Each of the two sequential exceptional sets costs at most one field element. -/
theorem ipaShiftXi_badSet_measure_le (delta sEval : Fp) :
    uniformChallenge.toOuterMeasure (szBadSet (ipaShiftXiPolynomial delta sEval)) ≤
      1 / (Fintype.card Fp : ℝ≥0∞) := by
  exact le_trans (uniformChallenge_szBadSet _) <| ENNReal.div_le_div_right
    (by exact_mod_cast ipaShiftXiPolynomial_natDegree_le delta sEval) _

theorem ipaShiftZ_badSet_measure_le (delta pU sU sEval xi : Fp) :
    uniformChallenge.toOuterMeasure
        (szBadSet (ipaShiftZPolynomial delta pU sU sEval xi)) ≤
      1 / (Fintype.card Fp : ℝ≥0∞) := by
  exact le_trans (uniformChallenge_szBadSet _) <| ENNReal.div_le_div_right
    (by exact_mod_cast ipaShiftZPolynomial_natDegree_le delta pU sU sEval xi) _

end Zcash.Snark
