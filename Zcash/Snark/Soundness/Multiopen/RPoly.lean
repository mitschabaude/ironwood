import Mathlib
import Zcash.Snark.Soundness.Main
import Zcash.Snark.Soundness.Multiopen.Deployed

/-!
# The r-polynomial core: interpolants, node values, and identity-from-samples

The claimed-evaluation binding recovers polynomial identities from per-run scalar identities: each
`x₃`-rewound run's decode values substitute into the verifier's combined evaluation
(`multiopenEval`), and enough runs force the identity as polynomials. This module supplies the
generic pieces:

* `poly_eq_of_agree_on_family` — **identity from samples.** Two polynomials whose difference has
  degree at most `d` and which agree on `d + 1` pairwise-distinct points are equal — the counting
  core in the direction the rewinding uses (samples force identity), the polynomial-level twin of
  `exists_injective_accepting_of_measure`.
* `lagrangePoly` — the interpolant of a point/value list as a `Polynomial`, with its node values
  (`lagrangePoly_eval_node`): at each node it takes the claimed value. This is the `r`-polynomial
  of one point set.
* `lagrangePoly_eval` — the deployed fold `lagrangeEval` (`Verifier/Checks.lean`) *is* the
  interpolant's evaluation, so identities about the deployed combined value transfer to the
  polynomial.
-/

namespace Zcash.Snark

open Polynomial

/-- **Identity from samples.** Two polynomials whose difference has degree at most `d` and which
agree at `d + 1` pairwise-distinct points are equal. -/
theorem poly_eq_of_agree_on_family {d : ℕ} {P Q : Polynomial Fp}
    (hdeg : (P - Q).natDegree ≤ d)
    (ξ : Fin (d + 1) → Fp) (hξ : Function.Injective ξ)
    (heval : ∀ r, P.eval (ξ r) = Q.eval (ξ r)) : P = Q := by
  have h0 : P - Q = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hξ
    · intro r
      simp [heval r]
    · simpa using Nat.lt_succ_of_le hdeg
  exact sub_eq_zero.mp h0

/-- The `foldl`-accumulated sum over `List.range` is the finite sum — the outer fold of the
deployed combined evaluation. -/
theorem foldl_range_add_eq_sum (f : ℕ → Fp) (n : ℕ) :
    (List.range n).foldl (fun acc i => acc + f i) 0 = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        Finset.sum_range_succ, ih]

/-- The guarded `foldl` product over `List.range` is the guarded finite product — the inner
(basis) fold of the deployed combined evaluation, the skipped index carrying `1`. -/
theorem foldl_range_guardProd_eq_prod (g : ℕ → Fp) (i n : ℕ) :
    (List.range n).foldl (fun p j => if j = i then p else p * g j) 1
      = ∏ j ∈ Finset.range n, if j = i then 1 else g j := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        Finset.prod_range_succ, ih]
      by_cases hn : n = i <;> simp [hn]

/-- A guarded product over the full range is the product over the erased set. -/
theorem guardProd_eq_prod_erase {n : ℕ} (h : Fin n → Fp) (i : Fin n) :
    (∏ j : Fin n, if j = i then 1 else h j) = ∏ j ∈ Finset.univ.erase i, h j := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), if_pos rfl, one_mul]
  exact Finset.prod_congr rfl fun j hj => if_neg (Finset.ne_of_mem_erase hj)

/-- The interpolant of a point/value list: the `r`-polynomial of one point set. Indexed by the
point list's positions; values read by `getD` to match the deployed fold. -/
noncomputable def lagrangePoly (points evals : List Fp) : Polynomial Fp :=
  Lagrange.interpolate Finset.univ (fun i : Fin points.length => points[i])
    (fun i : Fin points.length => evals.getD (i : ℕ) 0)

/-- The interpolant takes the claimed value at each node (pairwise-distinct nodes). -/
theorem lagrangePoly_eval_node {points evals : List Fp}
    (hdist : Function.Injective (fun i : Fin points.length => points[i]))
    (i : Fin points.length) :
    (lagrangePoly points evals).eval points[i] = evals.getD (i : ℕ) 0 :=
  Lagrange.eval_interpolate_at_node _ hdist.injOn (Finset.mem_univ i)

/-- The deployed combined-evaluation fold (`lagrangeEval`, `Verifier/Checks.lean`) is the
interpolant's evaluation at `x`, for pairwise-distinct nodes. Stepped through in the body: the
outer fold is the basis-weighted sum, each inner guarded fold the evaluated Lagrange basis. -/
theorem lagrangePoly_eval {points evals : List Fp}
    (hdist : Function.Injective (fun i : Fin points.length => points[i])) (x : Fp) :
    (lagrangePoly points evals).eval x = lagrangeEval x points evals := by
  classical
  -- The deployed fold, as a range-indexed sum of guarded products.
  have houter : lagrangeEval x points evals
      = ∑ i ∈ Finset.range points.length, evals.getD i 0
          * ∏ j ∈ Finset.range points.length,
              if j = i then 1
              else (x - points.getD j 0) / (points.getD i 0 - points.getD j 0) := by
    show (List.range points.length).foldl (fun acc i =>
        acc + evals.getD i 0 * ((List.range points.length).foldl (fun p j =>
          if j = i then p else p * (x - points.getD j 0)
            / (points.getD i 0 - points.getD j 0)) 1)) 0 = _
    rw [foldl_range_add_eq_sum (fun i => evals.getD i 0
      * ((List.range points.length).foldl (fun p j =>
          if j = i then p else p * (x - points.getD j 0)
            / (points.getD i 0 - points.getD j 0)) 1)) points.length]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    have hstep : (fun (p : Fp) j => if j = i then p
        else p * (x - points.getD j 0) / (points.getD i 0 - points.getD j 0))
        = fun (p : Fp) j => if j = i then p
        else p * ((x - points.getD j 0) / (points.getD i 0 - points.getD j 0)) := by
      funext p j
      rw [mul_div_assoc]
    rw [hstep]
    exact foldl_range_guardProd_eq_prod
      (fun j => (x - points.getD j 0) / (points.getD i 0 - points.getD j 0)) i points.length
  rw [houter, ← Fin.sum_univ_eq_sum_range (fun i => evals.getD i 0
    * ∏ j ∈ Finset.range points.length,
        if j = i then 1 else (x - points.getD j 0) / (points.getD i 0 - points.getD j 0))]
  rw [lagrangePoly, Lagrange.interpolate_apply, eval_finset_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [eval_mul, eval_C]
  congr 1
  rw [Lagrange.basis, eval_prod,
    ← guardProd_eq_prod_erase
      (fun j => eval x (Lagrange.basisDivisor points[i] points[j])) i,
    ← Fin.prod_univ_eq_prod_range (fun j =>
      if j = (i : ℕ) then 1
      else (x - points.getD j 0) / (points.getD (i : ℕ) 0 - points.getD j 0))]
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases hj : j = i
  · simp [hj]
  · rw [if_neg hj, if_neg (fun h => hj (Fin.val_inj.mp h)),
      List.getD_eq_getElem points 0 j.isLt, List.getD_eq_getElem points 0 i.isLt,
      Lagrange.basisDivisor, eval_mul, eval_C, eval_sub, eval_X, eval_C, div_eq_mul_inv,
      mul_comm]
    rfl

/-! ## The combined evaluation in closed form

The deployed `multiopenEval` folds per-set contributions by `x₂` and clears each set's
denominators pointwise; the closed forms below expose the `x₂`-power sum and the cleared
per-set term, the shapes the sample-identity substitution consumes. -/

/-- The per-set contribution's denominator fold in closed form: starting value times the product
of the inverses. -/
theorem foldl_mul_inv_eq_prod (x3 : Fp) (points : List Fp) (e : Fp) :
    points.foldl (fun e point => e * (x3 - point)⁻¹) e
      = e * ∏ j ∈ Finset.range points.length, (x3 - points.getD j 0)⁻¹ := by
  induction points generalizing e with
  | nil => simp
  | cons p l ih =>
      rw [List.foldl_cons, ih, List.length_cons, Finset.prod_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      ring

/-- The `x₂` fold of `multiopenEval` in closed power form: ascending `x₂`-powers carry the per-set
cleared contributions in reverse fold order (the initial `0` kills the top term). -/
theorem multiopenEval_powerForm (x2 x3 : Fp) (sets : List (List Fp × List Fp × Fp)) :
    multiopenEval x2 x3 sets
      = ∑ j ∈ Finset.range sets.length,
          x2 ^ j * (((sets.reverse.getD j ([], [], 0)).2.2
              - lagrangeEval x3 (sets.reverse.getD j ([], [], 0)).1
                  (sets.reverse.getD j ([], [], 0)).2.1)
            * ∏ m ∈ Finset.range (sets.reverse.getD j ([], [], 0)).1.length,
                (x3 - (sets.reverse.getD j ([], [], 0)).1.getD m 0)⁻¹) := by
  have hfg : (fun (msmEval : Fp) (s : List Fp × List Fp × Fp) =>
      msmEval * x2 + s.1.foldl (fun e point => e * (x3 - point)⁻¹)
        (s.2.2 - lagrangeEval x3 s.1 s.2.1))
      = fun acc s => x2 • acc + (s.2.2 - lagrangeEval x3 s.1 s.2.1)
          * ∏ m ∈ Finset.range s.1.length, (x3 - s.1.getD m 0)⁻¹ := by
    funext acc s
    rw [foldl_mul_inv_eq_prod, smul_eq_mul, mul_comm x2 acc]
  show sets.foldl (fun msmEval s =>
      msmEval * x2 + s.1.foldl (fun e point => e * (x3 - point)⁻¹)
        (s.2.2 - lagrangeEval x3 s.1 s.2.1)) 0 = _
  rw [hfg, foldl_smul_add_powerForm x2
    (fun s : List Fp × List Fp × Fp => (s.2.2 - lagrangeEval x3 s.1 s.2.1)
      * ∏ m ∈ Finset.range s.1.length, (x3 - s.1.getD m 0)⁻¹) ([], [], 0) sets 0,
    smul_zero, zero_add]
  simp only [smul_eq_mul]

/-- **Coefficients from a vanishing power sum.** A power sum `∑_{j<n} ξ^j · c j` is the evaluation
at `ξ` of the degree-`<n` polynomial `∑_{j<n} C(c j)·Xʲ`; if it vanishes at `n` pairwise-distinct
`ξ`, that polynomial is zero, so every coefficient `c i` (`i < n`) is zero. -/
theorem coeffs_zero_of_power_sum_vanishes {n : ℕ} (c : ℕ → Fp)
    (ξ : Fin n → Fp) (hξ : Function.Injective ξ)
    (hvanish : ∀ r, ∑ j ∈ Finset.range n, ξ r ^ j * c j = 0) (i : Fin n) :
    c i = 0 := by
  classical
  have hn : 0 < n := i.pos
  have hcast : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos hn
  set P : Polynomial Fp := ∑ j ∈ Finset.range n, Polynomial.C (c j) * Polynomial.X ^ j with hPdef
  have hdeg : P.natDegree ≤ n - 1 := by
    rw [hPdef, Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro m hm
    rw [Polynomial.finset_sum_coeff]
    refine Finset.sum_eq_zero (fun j hj => ?_)
    simp only [Finset.mem_range] at hj
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega), mul_zero]
  have hP0 : P = 0 := by
    refine poly_eq_of_agree_on_family (d := n - 1) (Q := 0) (by rw [sub_zero]; exact hdeg)
      (fun r => ξ (Fin.cast hcast r)) (hξ.comp (Fin.cast_injective hcast)) (fun r => ?_)
    rw [Polynomial.eval_zero, hPdef, Polynomial.eval_finset_sum]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    rw [← hvanish (Fin.cast hcast r)]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hcoeff : P.coeff i = c i := by
    rw [hPdef, Polynomial.finset_sum_coeff, Finset.sum_eq_single (i : ℕ)]
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
    · intro j _ hji
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (fun h => hji h.symm), mul_zero]
    · intro hni; exact absurd (Finset.mem_range.mpr i.isLt) hni
  rw [hP0, Polynomial.coeff_zero] at hcoeff
  exact hcoeff.symm

/-- **The `x₂` value-separation floor.** The multiopen combined evaluation is, by
`multiopenEval_powerForm`, a polynomial of degree `< |sets|` in the set-separation challenge `x₂`,
its `j`-th coefficient set `j`'s cleared contribution `(qⱼ − r(x₃)) · ∏(x₃−node)⁻¹`. Vanishing at
`|sets|` pairwise-distinct `x₂` — the `reprogramX2` rewinds resampling `x₂` while the sets and their
claimed evaluations stay fixed (absorbed before `x₂`) — forces every set's contribution to zero.
This is the set-separation analogue of `col_eq_lagrangePoly_of_samples`'s `x₃` interpolation: it
un-batches the deployed value check into the per-set claimed-combined-evaluation binding. -/
theorem multiopenEval_perSet_zero_of_samples {x3 : Fp} {sets : List (List Fp × List Fp × Fp)}
    (ξ : Fin sets.length → Fp) (hξ : Function.Injective ξ)
    (hvanish : ∀ r, multiopenEval (ξ r) x3 sets = 0) (j : Fin sets.length) :
    ((sets.reverse.getD j ([], [], 0)).2.2
        - lagrangeEval x3 (sets.reverse.getD j ([], [], 0)).1 (sets.reverse.getD j ([], [], 0)).2.1)
      * ∏ m ∈ Finset.range (sets.reverse.getD j ([], [], 0)).1.length,
          (x3 - (sets.reverse.getD j ([], [], 0)).1.getD m 0)⁻¹ = 0 :=
  coeffs_zero_of_power_sum_vanishes
    (fun j => ((sets.reverse.getD j ([], [], 0)).2.2
        - lagrangeEval x3 (sets.reverse.getD j ([], [], 0)).1 (sets.reverse.getD j ([], [], 0)).2.1)
      * ∏ m ∈ Finset.range (sets.reverse.getD j ([], [], 0)).1.length,
          (x3 - (sets.reverse.getD j ([], [], 0)).1.getD m 0)⁻¹)
    ξ hξ (fun r => by rw [← multiopenEval_powerForm (ξ r) x3 sets]; exact hvanish r) j

/-! ## Claimed-evaluation binding: the decoded column is the `r`-polynomial

The verifier's per-set contribution reads the claimed per-point evaluations through
`lagrangeEval x₃ points evals` — the `r`-polynomial's value at the interpolation challenge
(`lagrangePoly_eval`). Rewinding `x₃` (`X3Run`, `Soundness.Multiopen.Deployed`) resamples that
challenge while the point set and its claimed evaluations stay fixed (absorbed before `x₃`). So a
decoded column of degree `< |points|` that reproduces the deployed `r`-value at enough distinct
`x₃` samples must *be* the `r`-polynomial — and then its value at each node is exactly the proof
string's claimed evaluation. This is the sample-forces-identity direction the claimed-eval binding
rests on; producing the `x₃`-sample family from deployed accepts mirrors the `x₄` opened chain
(`Soundness.Multiopen.Opened`) and consumes the same rewinding floor. -/

/-- The `r`-polynomial of a point set has degree below the number of nodes. -/
theorem lagrangePoly_natDegree_lt {points evals : List Fp} (hlen : 0 < points.length)
    (hnode : Function.Injective (fun i : Fin points.length => points[i])) :
    (lagrangePoly points evals).natDegree < points.length := by
  have hd : (lagrangePoly points evals).degree < (points.length : ℕ) := by
    have h := Lagrange.degree_interpolate_lt
      (s := (Finset.univ : Finset (Fin points.length)))
      (v := fun i : Fin points.length => points[i])
      (r := fun i : Fin points.length => evals.getD (i : ℕ) 0) hnode.injOn
    simpa [lagrangePoly, Finset.card_univ, Fintype.card_fin] using h
  by_cases h0 : lagrangePoly points evals = 0
  · rw [h0, Polynomial.natDegree_zero]; exact hlen
  · exact (Polynomial.natDegree_lt_iff_degree_lt h0).mpr hd

/-- **Claimed-evaluation binding from `x₃` samples.** A polynomial `col` of degree `< |points|`
that reproduces the deployed combined evaluation `lagrangeEval · points evals` at `|points|`
pairwise-distinct interpolation challenges *is* the `r`-polynomial `lagrangePoly points evals`. -/
theorem col_eq_lagrangePoly_of_samples {points evals : List Fp} {col : Polynomial Fp}
    (hlen : 0 < points.length)
    (hnode : Function.Injective (fun i : Fin points.length => points[i]))
    (hdeg : col.natDegree < points.length)
    (ξ : Fin points.length → Fp) (hξ : Function.Injective ξ)
    (hmatch : ∀ r, col.eval (ξ r) = lagrangeEval (ξ r) points evals) :
    col = lagrangePoly points evals := by
  have hn : points.length - 1 + 1 = points.length := Nat.succ_pred_eq_of_pos hlen
  have hrdeg := lagrangePoly_natDegree_lt (evals := evals) hlen hnode
  have hdiff : (col - lagrangePoly points evals).natDegree ≤ points.length - 1 := by
    refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_) <;> omega
  exact poly_eq_of_agree_on_family hdiff (fun r => ξ (Fin.cast hn r))
    (hξ.comp (Fin.cast_injective hn))
    (fun r => (hmatch (Fin.cast hn r)).trans (lagrangePoly_eval hnode _).symm)

/-- **The decoded column's node values are the claimed evaluations.** Composing
`col_eq_lagrangePoly_of_samples` with `lagrangePoly_eval_node`: at each rotated query point
`points[i]` — the `ωⁱ·x` the verifier opens — the sample-bound decoded column takes the proof
string's claimed evaluation `evals[i]`. This is the per-member claimed-eval binding, delegated to
the fingerprint before this development. -/
theorem col_eval_node_eq_claimed {points evals : List Fp} {col : Polynomial Fp}
    (hlen : 0 < points.length)
    (hnode : Function.Injective (fun i : Fin points.length => points[i]))
    (hdeg : col.natDegree < points.length)
    (ξ : Fin points.length → Fp) (hξ : Function.Injective ξ)
    (hmatch : ∀ r, col.eval (ξ r) = lagrangeEval (ξ r) points evals)
    (i : Fin points.length) :
    col.eval points[i] = evals.getD (i : ℕ) 0 := by
  rw [col_eq_lagrangePoly_of_samples hlen hnode hdeg ξ hξ hmatch]
  exact lagrangePoly_eval_node hnode i

end Zcash.Snark
