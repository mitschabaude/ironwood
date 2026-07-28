import Zcash.Snark.Soundness.AGM.AlgebraicUnbatch
import Zcash.Snark.Soundness.Multiopen.NodeBinding

/-!
# Rewind-free value unbatching for multiopen

Once AGM fixes the relevant polynomials before their challenges, one accepting transcript is
enough: any failed coefficient identity makes the actual challenge a root of one explicit
polynomial.  Transcript pinning stays outside these lemmas; callers establish it before using the
uniform root-set bounds.
-/

namespace Zcash.Snark

open Polynomial
open Classical

/-! ## A generic power-sum error polynomial -/

/-- The polynomial whose coefficient at `i` is `c i`. -/
noncomputable def powerErrorPolynomial {n : Nat} (c : Fin n -> Fp) : Polynomial Fp :=
  ∑ i : Fin n, Polynomial.C (c i) * Polynomial.X ^ (i : Nat)

@[simp] theorem powerErrorPolynomial_eval {n : Nat} (c : Fin n -> Fp) (x : Fp) :
    (powerErrorPolynomial c).eval x = ∑ i : Fin n, x ^ (i : Nat) * c i := by
  rw [powerErrorPolynomial, Polynomial.eval_finsetSum]
  exact Finset.sum_congr rfl fun i _ => by
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    ring

theorem powerErrorPolynomial_coeff {n : Nat} (c : Fin n -> Fp) (i : Fin n) :
    (powerErrorPolynomial c).coeff (i : Nat) = c i := by
  rw [powerErrorPolynomial, Polynomial.finsetSum_coeff, Finset.sum_eq_single i]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
  · intro j _ hji
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      if_neg (fun h => hji (Fin.ext h.symm)), mul_zero]
  · intro hni
    exact absurd (Finset.mem_univ i) hni

/-- A deliberately loose degree bound that also covers the empty power sum. -/
theorem powerErrorPolynomial_natDegree_le {n : Nat} (c : Fin n -> Fp) :
    (powerErrorPolynomial c).natDegree <= n := by
  rw [powerErrorPolynomial, Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro m hm
  rw [Polynomial.finsetSum_coeff]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega), mul_zero]

/-- If `x` is a root but is outside the nonzero-polynomial root set, every coefficient vanishes. -/
theorem powerErrorCoefficients_eq_zero_of_good_root {n : Nat} (c : Fin n -> Fp) (x : Fp)
    (hroot : (powerErrorPolynomial c).eval x = 0)
    (hgood : x ∉ szBadSet (powerErrorPolynomial c)) : forall i, c i = 0 := by
  have hzero : powerErrorPolynomial c = 0 := by
    by_contra hne
    exact hgood (mem_szBadSet.mpr ⟨hne, hroot⟩)
  intro i
  have hcoeff := congrArg (fun P : Polynomial Fp => P.coeff (i : Nat)) hzero
  simpa [powerErrorPolynomial_coeff] using hcoeff

/-- Uniform pricing for a power-sum mismatch. -/
theorem powerErrorPolynomial_badSet_measure_le {n : Nat} (c : Fin n -> Fp) :
    uniformChallenge.toOuterMeasure (szBadSet (powerErrorPolynomial c)) <=
      (n : ENNReal) / (Fintype.card Fp : ENNReal) := by
  exact le_trans (uniformChallenge_szBadSet _) <| ENNReal.div_le_div_right
    (by exact_mod_cast powerErrorPolynomial_natDegree_le c) _

/-! ## The fixed-`qPrime` `x3` identity -/

/-- The denominator-cleared quotient mismatch checked at `x3`. -/
noncomputable def clearedQuotientErrorPolynomial {numSets : Nat}
    (allPts : Finset Fp) (pts : Fin numSets -> Finset Fp)
    (col r : Fin numSets -> Polynomial Fp) (a : Fin numSets -> Fp)
    (qCol : Polynomial Fp) : Polynomial Fp :=
  qCol * vanishingProd allPts -
    ∑ j : Fin numSets, Polynomial.C (a j) * ((col j - r j) * coProd allPts (pts j))

/-- Degree of the single cleared-quotient error polynomial. -/
theorem clearedQuotientErrorPolynomial_natDegree_le {numSets N : Nat}
    (allPts : Finset Fp) (pts : Fin numSets -> Finset Fp)
    (col r : Fin numSets -> Polynomial Fp) (a : Fin numSets -> Fp)
    (qCol : Polynomial Fp) (hq : qCol.natDegree <= N)
    (hcr : forall j, (col j - r j).natDegree <= N) :
    (clearedQuotientErrorPolynomial allPts pts col r a qCol).natDegree <=
      N + allPts.card := by
  refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
  · exact le_trans Polynomial.natDegree_mul_le
      (Nat.add_le_add hq (vanishingProd_natDegree_le _))
  · refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun j _ => ?_)
    calc
      (Polynomial.C (a j) * ((col j - r j) * coProd allPts (pts j))).natDegree
          <= ((col j - r j) * coProd allPts (pts j)).natDegree :=
        Polynomial.natDegree_C_mul_le _ _
      _ <= (col j - r j).natDegree + (coProd allPts (pts j)).natDegree :=
        Polynomial.natDegree_mul_le
      _ <= N + allPts.card :=
        Nat.add_le_add (hcr j) (coProd_natDegree_le _ _)

/-- One accepted multiopen value equation makes the current `x3` a root of the cleared mismatch. -/
theorem clearedQuotientErrorPolynomial_eval_eq_zero {numSets : Nat}
    (allPts : Finset Fp) (pts : Fin numSets -> Finset Fp) (hsub : forall j, pts j ⊆ allPts)
    (col r : Fin numSets -> Polynomial Fp) (a : Fin numSets -> Fp)
    (qCol : Polynomial Fp) (x3 : Fp)
    (hnode : forall j, (vanishingProd (pts j)).eval x3 ≠ 0)
    (hsamp : qCol.eval x3 =
      ∑ j : Fin numSets, a j * (col j - r j).eval x3 *
        (∏ p ∈ pts j, (x3 - p))⁻¹) :
    (clearedQuotientErrorPolynomial allPts pts col r a qCol).eval x3 = 0 := by
  rw [clearedQuotientErrorPolynomial, Polynomial.eval_sub, sub_eq_zero,
    Polynomial.eval_mul, hsamp, Polynomial.eval_finsetSum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hclear := clear_denom_eval (hsub j) (hnode j) (x := x3)
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_mul, <- hclear]
  ring

/-- Outside the explicit `x3` root set, one accepted value equation proves the full cleared
quotient polynomial identity. -/
theorem clearedQuotientIdentity_of_good_x3 {numSets : Nat}
    (allPts : Finset Fp) (pts : Fin numSets -> Finset Fp) (hsub : forall j, pts j ⊆ allPts)
    (col r : Fin numSets -> Polynomial Fp) (a : Fin numSets -> Fp)
    (qCol : Polynomial Fp) (x3 : Fp)
    (hnode : forall j, (vanishingProd (pts j)).eval x3 ≠ 0)
    (hsamp : qCol.eval x3 =
      ∑ j : Fin numSets, a j * (col j - r j).eval x3 *
        (∏ p ∈ pts j, (x3 - p))⁻¹)
    (hgood : x3 ∉ szBadSet (clearedQuotientErrorPolynomial allPts pts col r a qCol)) :
    qCol * vanishingProd allPts =
      ∑ j : Fin numSets, Polynomial.C (a j) *
        ((col j - r j) * coProd allPts (pts j)) := by
  have hroot := clearedQuotientErrorPolynomial_eval_eq_zero
    allPts pts hsub col r a qCol x3 hnode hsamp
  have hzero : clearedQuotientErrorPolynomial allPts pts col r a qCol = 0 := by
    by_contra hne
    exact hgood (mem_szBadSet.mpr ⟨hne, hroot⟩)
  exact sub_eq_zero.mp hzero

/-- Pricing of the `x3` mismatch from any explicit degree bound. -/
theorem clearedQuotientErrorPolynomial_badSet_measure_le {numSets d : Nat}
    (allPts : Finset Fp) (pts : Fin numSets -> Finset Fp)
    (col r : Fin numSets -> Polynomial Fp) (a : Fin numSets -> Fp)
    (qCol : Polynomial Fp)
    (hdeg : (clearedQuotientErrorPolynomial allPts pts col r a qCol).natDegree <= d) :
    uniformChallenge.toOuterMeasure
        (szBadSet (clearedQuotientErrorPolynomial allPts pts col r a qCol)) <=
      (d : ENNReal) / (Fintype.card Fp : ENNReal) := by
  exact le_trans (uniformChallenge_szBadSet _) <| ENNReal.div_le_div_right
    (by exact_mod_cast hdeg) _

/-! ## `x2` set separation at a node -/

/-- At a fixed node, the coefficient of `X^j` is set `j`'s cleared value mismatch. -/
noncomputable def nodeBindingErrorPolynomial {numSets : Nat}
    (allPts : Finset Fp) (pts : Fin numSets -> Finset Fp)
    (col r : Fin numSets -> Polynomial Fp) (node : Fp) : Polynomial Fp :=
  powerErrorPolynomial fun j =>
    (col j - r j).eval node * (coProd allPts (pts j)).eval node

/-- A cleared quotient identity at the current `x2` makes `x2` a root of the node error
polynomial. -/
theorem nodeBindingErrorPolynomial_eval_eq_zero {numSets : Nat}
    (allPts : Finset Fp) (pts : Fin numSets -> Finset Fp)
    (col r : Fin numSets -> Polynomial Fp) (qCol : Polynomial Fp) (x2 node : Fp)
    (hnodeAll : node ∈ allPts)
    (hid : qCol * vanishingProd allPts =
      ∑ j : Fin numSets, Polynomial.C (x2 ^ (j : Nat)) *
        ((col j - r j) * coProd allPts (pts j))) :
    (nodeBindingErrorPolynomial allPts pts col r node).eval x2 = 0 := by
  rw [nodeBindingErrorPolynomial, powerErrorPolynomial_eval]
  calc
    (∑ j : Fin numSets,
        x2 ^ (j : Nat) * ((col j - r j).eval node * (coProd allPts (pts j)).eval node)) =
        (∑ j : Fin numSets, Polynomial.C (x2 ^ (j : Nat)) *
          ((col j - r j) * coProd allPts (pts j))).eval node := by
            rw [Polynomial.eval_finsetSum]
            exact Finset.sum_congr rfl fun j _ => by
              rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_mul]
    _ = (qCol * vanishingProd allPts).eval node := congrArg _ hid.symm
    _ = 0 := by
      rw [Polynomial.eval_mul, vanishingProd_eval_mem hnodeAll, mul_zero]

/-- Outside the `x2` root set at a node of set `j0`, the aggregate identity separates set `j0`
and binds its polynomial to its claimed interpolant at that node. -/
theorem nodeBinding_of_good_x2 {numSets : Nat}
    (allPts : Finset Fp) (pts : Fin numSets -> Finset Fp)
    (col r : Fin numSets -> Polynomial Fp) (qCol : Polynomial Fp) (x2 : Fp)
    (hid : qCol * vanishingProd allPts =
      ∑ j : Fin numSets, Polynomial.C (x2 ^ (j : Nat)) *
        ((col j - r j) * coProd allPts (pts j)))
    (j0 : Fin numSets) {node : Fp} (hnode : node ∈ pts j0) (hnodeAll : node ∈ allPts)
    (hgood : x2 ∉ szBadSet (nodeBindingErrorPolynomial allPts pts col r node)) :
    (col j0).eval node = (r j0).eval node := by
  have hroot := nodeBindingErrorPolynomial_eval_eq_zero
    allPts pts col r qCol x2 node hnodeAll hid
  have hcoeff := powerErrorCoefficients_eq_zero_of_good_root
    (fun j : Fin numSets =>
      (col j - r j).eval node * (coProd allPts (pts j)).eval node)
    x2 hroot hgood j0
  have hWne : (coProd allPts (pts j0)).eval node ≠ 0 :=
    vanishingProd_eval_ne (by simp [Finset.mem_sdiff, hnode])
  have hdiff : (col j0 - r j0).eval node = 0 :=
    (mul_eq_zero.mp hcoeff).resolve_right hWne
  exact sub_eq_zero.mp (by simpa using hdiff)

theorem nodeBindingErrorPolynomial_badSet_measure_le {numSets : Nat}
    (allPts : Finset Fp) (pts : Fin numSets -> Finset Fp)
    (col r : Fin numSets -> Polynomial Fp) (node : Fp) :
    uniformChallenge.toOuterMeasure
        (szBadSet (nodeBindingErrorPolynomial allPts pts col r node)) <=
      (numSets : ENNReal) / (Fintype.card Fp : ENNReal) :=
  powerErrorPolynomial_badSet_measure_le _

/-! ## `x1` member separation -/

/-- At a fixed node, the coefficient of `X^m` is member `m`'s claimed-value mismatch. -/
noncomputable def memberBindingErrorPolynomial {numMem : Nat}
    (mem : Fin numMem -> Polynomial Fp) (claimed : Fin numMem -> Fp)
    (node : Fp) : Polynomial Fp :=
  powerErrorPolynomial fun m => (mem m).eval node - claimed m

theorem memberBindingErrorPolynomial_eval_eq_zero {numMem : Nat}
    (mem : Fin numMem -> Polynomial Fp) (claimed : Fin numMem -> Fp)
    (node x1 : Fp)
    (hagg : (∑ m : Fin numMem, x1 ^ (m : Nat) * (mem m).eval node) =
      ∑ m : Fin numMem, x1 ^ (m : Nat) * claimed m) :
    (memberBindingErrorPolynomial mem claimed node).eval x1 = 0 := by
  rw [memberBindingErrorPolynomial, powerErrorPolynomial_eval]
  calc
    (∑ m : Fin numMem, x1 ^ (m : Nat) * ((mem m).eval node - claimed m)) =
        (∑ m : Fin numMem, x1 ^ (m : Nat) * (mem m).eval node) -
          ∑ m : Fin numMem, x1 ^ (m : Nat) * claimed m := by
            rw [<- Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl fun m _ => by ring
    _ = 0 := sub_eq_zero.mpr hagg

/-- Outside the `x1` root set, the single aggregate equality binds every represented member at
the node. -/
theorem memberBinding_of_good_x1 {numMem : Nat}
    (mem : Fin numMem -> Polynomial Fp) (claimed : Fin numMem -> Fp)
    (node x1 : Fp)
    (hagg : (∑ m : Fin numMem, x1 ^ (m : Nat) * (mem m).eval node) =
      ∑ m : Fin numMem, x1 ^ (m : Nat) * claimed m)
    (hgood : x1 ∉ szBadSet (memberBindingErrorPolynomial mem claimed node)) :
    forall m, (mem m).eval node = claimed m := by
  have hroot := memberBindingErrorPolynomial_eval_eq_zero mem claimed node x1 hagg
  intro m
  exact sub_eq_zero.mp (powerErrorCoefficients_eq_zero_of_good_root
    (fun j : Fin numMem => (mem j).eval node - claimed j) x1 hroot hgood m)

theorem memberBindingErrorPolynomial_badSet_measure_le {numMem : Nat}
    (mem : Fin numMem -> Polynomial Fp) (claimed : Fin numMem -> Fp) (node : Fp) :
    uniformChallenge.toOuterMeasure
        (szBadSet (memberBindingErrorPolynomial mem claimed node)) <=
      (numMem : ENNReal) / (Fintype.card Fp : ENNReal) :=
  powerErrorPolynomial_badSet_measure_le _

end Zcash.Snark
