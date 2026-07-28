import Mathlib
import Zcash.Snark.Soundness.Multiopen.RPoly

/-!
# The multiopen value check, derived: per-set node binding

Un-batches the verifier's opening into the per-set claimed-evaluation consistency that
`Claimed.claimedEval_of_x3Prob` consumes, by commitment binding over two nested rewinds: the
quotient column is fixed across `x₃`-rewinds, enough `x₃`-samples make the cleared quotient
identity hold as polynomials, and evaluating it at any point kills every set not containing that
point — leaving an `x₂`-power sum with fixed coefficients, so the `x₂`-rewind family forces the
node binding `colⱼ(p) = rⱼ(p)` (`node_binding_of_samples`).
-/

namespace Zcash.Snark

open Polynomial

/-- The vanishing polynomial of a finite point set, `∏_{p ∈ pts} (X − p)`. -/
noncomputable def vanishingProd (pts : Finset Fp) : Polynomial Fp :=
  ∏ p ∈ pts, (X - C p)

@[simp] theorem vanishingProd_eval (pts : Finset Fp) (x : Fp) :
    (vanishingProd pts).eval x = ∏ p ∈ pts, (x - p) := by
  simp [vanishingProd, eval_prod]

/-- The vanishing polynomial vanishes at each of its points. -/
theorem vanishingProd_eval_mem {pts : Finset Fp} {p : Fp} (hp : p ∈ pts) :
    (vanishingProd pts).eval p = 0 := by
  rw [vanishingProd_eval]
  exact Finset.prod_eq_zero hp (by ring)

/-- Off its point set the vanishing polynomial is nonzero. -/
theorem vanishingProd_eval_ne {pts : Finset Fp} {p : Fp} (hp : p ∉ pts) :
    (vanishingProd pts).eval p ≠ 0 := by
  rw [vanishingProd_eval]
  refine Finset.prod_ne_zero_iff.mpr (fun q hq => ?_)
  exact sub_ne_zero.mpr (by rintro rfl; exact hp hq)

/-- The complementary product `Wⱼ = ∏_{p ∈ all \ pts} (X − p)`. -/
noncomputable def coProd (all pts : Finset Fp) : Polynomial Fp :=
  vanishingProd (all \ pts)

/-- The full vanishing polynomial splits as `D = Wⱼ · ∏(pts j)` when `pts j ⊆ all`. -/
theorem vanishingProd_split {all pts : Finset Fp} (hsub : pts ⊆ all) :
    vanishingProd all = coProd all pts * vanishingProd pts := by
  simp only [coProd, vanishingProd]
  rw [← Finset.prod_sdiff hsub]

/-- **Denominator clearing.** Off `pts`' nodes, `D(x) · (∏_{pts}(x − p))⁻¹ = Wⱼ(x)` — the identity
that turns the multiopen fold's `∏(x₃ − node)⁻¹` into the polynomial `Wⱼ`. -/
theorem clear_denom_eval {all pts : Finset Fp} (hsub : pts ⊆ all) {x : Fp}
    (hx : (vanishingProd pts).eval x ≠ 0) :
    (vanishingProd all).eval x * (∏ p ∈ pts, (x - p))⁻¹ = (coProd all pts).eval x := by
  rw [vanishingProd_split hsub, eval_mul, vanishingProd_eval, mul_assoc,
    mul_inv_cancel₀ (by rw [← vanishingProd_eval]; exact hx), mul_one]

/-- **Per-set node binding, from the cleared quotient identities over the `x₂` family.** Given fixed
per-set columns `col`, interpolants `r`, and point sets `pts` (all inside `allPts`), together with a
family of `x₂`-values `ζ : Fin numSets → Fp` (pairwise distinct) for each of which the cleared
quotient identity holds as polynomials, every point `p` of every set `j₀` satisfies
`(col j₀).eval p = (r j₀).eval p`. This is the un-batched value check: the decoded column agrees with
the interpolant of the claimed evaluations at every node of its set. -/
theorem node_binding_of_cleared_identities {numSets : ℕ}
    (allPts : Finset Fp) (pts : Fin numSets → Finset Fp)
    (col r : Fin numSets → Polynomial Fp)
    (qCol : Fin numSets → Polynomial Fp)
    (ζ : Fin numSets → Fp) (hζ : Function.Injective ζ)
    (hid : ∀ s : Fin numSets,
      qCol s * vanishingProd allPts
        = ∑ j : Fin numSets, C (ζ s ^ (j : ℕ)) * ((col j - r j) * coProd allPts (pts j)))
    (j₀ : Fin numSets) {p : Fp} (hp : p ∈ pts j₀) (hpall : p ∈ allPts) :
    (col j₀).eval p = (r j₀).eval p := by
  classical
  set c : ℕ → Fp := fun j => if h : j < numSets
      then (col ⟨j, h⟩ - r ⟨j, h⟩).eval p * (coProd allPts (pts ⟨j, h⟩)).eval p else 0 with hc
  -- Each identity, evaluated at `p`, is a vanishing power sum in `ζ s`.
  have hsum : ∀ s : Fin numSets, ∑ j ∈ Finset.range numSets, ζ s ^ j * c j = 0 := by
    intro s
    have h := congrArg (Polynomial.eval p) (hid s)
    rw [eval_mul, vanishingProd_eval_mem hpall, mul_zero, eval_finsetSum] at h
    have key : (∑ j : Fin numSets, ζ s ^ (j : ℕ) * c (j : ℕ)) = 0 := by
      rw [h]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [eval_mul, eval_C, eval_mul]
      simp only [hc, dif_pos j.isLt, Fin.eta]
    rw [← Fin.sum_univ_eq_sum_range (fun j => ζ s ^ j * c j) numSets]
    exact key
  -- The counting core forces every coefficient to zero.
  have hcj₀ : c (j₀ : ℕ) = 0 := coeffs_zero_of_power_sum_vanishes c ζ hζ hsum j₀
  rw [hc] at hcj₀
  simp only [dif_pos j₀.isLt, Fin.eta] at hcj₀
  have hWne : (coProd allPts (pts j₀)).eval p ≠ 0 :=
    vanishingProd_eval_ne (by simp [Finset.mem_sdiff, hp])
  have hdiff : (col j₀ - r j₀).eval p = 0 :=
    (mul_eq_zero.mp hcj₀).resolve_right hWne
  rw [eval_sub, sub_eq_zero] at hdiff
  exact hdiff

/-- **Cleared quotient identity from `x₃`-samples (one `x₂`-value).** If the quotient column `qCol`
reproduces the multiopen fold `∑ⱼ aⱼ·(colⱼ − rⱼ)(χ)·∏(χ − node)⁻¹` at `d+1` distinct non-node
samples `χ` and the difference has degree `≤ d`, the cleared identity `qCol·D = Σⱼ C(aⱼ)(colⱼ − rⱼ)Wⱼ`
holds as polynomials. -/
theorem cleared_identity_of_samples {numSets : ℕ}
    (allPts : Finset Fp) (pts : Fin numSets → Finset Fp) (hsub : ∀ j, pts j ⊆ allPts)
    (col r : Fin numSets → Polynomial Fp) (a : Fin numSets → Fp)
    (qCol : Polynomial Fp) (d : ℕ)
    (hdeg : (qCol * vanishingProd allPts
        - ∑ j : Fin numSets, C (a j) * ((col j - r j) * coProd allPts (pts j))).natDegree ≤ d)
    (χ : Fin (d + 1) → Fp) (hχinj : Function.Injective χ)
    (hnode : ∀ t j, (vanishingProd (pts j)).eval (χ t) ≠ 0)
    (hsamp : ∀ t, qCol.eval (χ t)
        = ∑ j : Fin numSets, a j * (col j - r j).eval (χ t) * (∏ p ∈ pts j, (χ t - p))⁻¹) :
    qCol * vanishingProd allPts
      = ∑ j : Fin numSets, C (a j) * ((col j - r j) * coProd allPts (pts j)) := by
  refine poly_eq_of_agree_on_family hdeg χ hχinj (fun t => ?_)
  rw [eval_mul, hsamp t, eval_finsetSum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hcd := clear_denom_eval (hsub j) (hnode t j) (x := χ t)
  rw [eval_mul, eval_C, eval_mul, ← hcd]
  ring

/-- **Per-set node binding from `x₃`-sample identities over the `x₂` family.** Composes
`cleared_identity_of_samples` (each `x₂`-value) with `node_binding_of_cleared_identities`: the
decoded column of every set agrees with the interpolant of the claimed evaluations at every node.
This is the deployed multiopen value check, stated purely over the fixed committed data and the two
rewind sample families. -/
theorem node_binding_of_samples {numSets : ℕ}
    (allPts : Finset Fp) (pts : Fin numSets → Finset Fp) (hsub : ∀ j, pts j ⊆ allPts)
    (col r : Fin numSets → Polynomial Fp) (qCol : Fin numSets → Polynomial Fp)
    (ζ : Fin numSets → Fp) (hζ : Function.Injective ζ) (d : ℕ)
    (hdeg : ∀ s, (qCol s * vanishingProd allPts
        - ∑ j : Fin numSets, C (ζ s ^ (j : ℕ)) *
            ((col j - r j) * coProd allPts (pts j))).natDegree ≤ d)
    (χ : Fin numSets → Fin (d + 1) → Fp) (hχinj : ∀ s, Function.Injective (χ s))
    (hnode : ∀ s t j, (vanishingProd (pts j)).eval (χ s t) ≠ 0)
    (hsamp : ∀ s t, (qCol s).eval (χ s t)
        = ∑ j : Fin numSets, ζ s ^ (j : ℕ) * (col j - r j).eval (χ s t)
            * (∏ p ∈ pts j, (χ s t - p))⁻¹)
    (j₀ : Fin numSets) {p : Fp} (hp : p ∈ pts j₀) (hpall : p ∈ allPts) :
    (col j₀).eval p = (r j₀).eval p :=
  node_binding_of_cleared_identities allPts pts col r qCol ζ hζ
    (fun s => cleared_identity_of_samples allPts pts hsub col r (fun j => ζ s ^ (j : ℕ))
      (qCol s) d (hdeg s) (χ s) (hχinj s) (fun t j => hnode s t j) (fun t => hsamp s t))
    j₀ hp hpall

/-- **The `x₁` un-batch: aggregate node binding ⟹ per-member node binding.** A point set's aggregate
column is the `x₁`-power fold of its member columns, and its claimed compressed evaluation at a node
is the `x₁`-power fold of the members' claimed evaluations. If the aggregate binding
`∑ₘ x₁ᵐ · memₘ(node) = ∑ₘ x₁ᵐ · claimedₘ` holds across `numMem` distinct `x₁` values (the `x₁`-rewind
family), then each member column takes its claimed evaluation at the node: `memₘ₀(node) = claimedₘ₀`.
The members and claimed values are fixed before `x₁`, so this is again `coeffs_zero_of_power_sum_vanishes`
— the `x₁`-Vandermonde separating the members. -/
theorem member_binding_of_x1_samples {numMem : ℕ}
    (mem : Fin numMem → Polynomial Fp) (claimed : Fin numMem → Fp) (node : Fp)
    (x1 : Fin numMem → Fp) (hx1 : Function.Injective x1)
    (hagg : ∀ s : Fin numMem,
      ∑ m : Fin numMem, x1 s ^ (m : ℕ) * (mem m).eval node
        = ∑ m : Fin numMem, x1 s ^ (m : ℕ) * claimed m)
    (m₀ : Fin numMem) : (mem m₀).eval node = claimed m₀ := by
  classical
  set c : ℕ → Fp := fun m => if h : m < numMem
      then (mem ⟨m, h⟩).eval node - claimed ⟨m, h⟩ else 0 with hc
  have hsum : ∀ s : Fin numMem, ∑ m ∈ Finset.range numMem, x1 s ^ m * c m = 0 := by
    intro s
    rw [← Fin.sum_univ_eq_sum_range (fun m => x1 s ^ m * c m) numMem]
    have h := hagg s
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at h
    rw [← h]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    simp only [hc, dif_pos m.isLt, Fin.eta]
    ring
  have hcm₀ : c (m₀ : ℕ) = 0 := coeffs_zero_of_power_sum_vanishes c x1 hx1 hsum m₀
  rw [hc] at hcm₀
  simp only [dif_pos m₀.isLt, Fin.eta] at hcm₀
  exact sub_eq_zero.mp hcm₀

end Zcash.Snark
