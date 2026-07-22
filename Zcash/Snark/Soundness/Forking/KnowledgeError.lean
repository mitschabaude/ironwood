import Zcash.Snark.Soundness.Forking.Tree

/-!
# Closed form of the fork-tree knowledge error

`Tree.kerr` is defined by the recursion `kerr N 0 = 0`, `kerr N (d+1) = 3·Nᵈ + N·kerr N d`. Its
docstring records the intended reading of the threshold fraction `kerr N d / Nᵈ` as `3d/N`, but that
closed form was only asserted in prose. This module proves it, so the abstract knowledge-error
threshold can be replaced by a concrete quantity in the deployed parameters (`Deployed.ConcreteBounds`
specialises `d = 11`, `N = |F_p|`).

* `kerr_mul_card` — the exact natural-number identity `kerr N d · N = 3·d·Nᵈ`, stated multiplied
  through by `N` so it needs neither `1 ≤ N` nor truncated subtraction.
* `kerr_eq` — the divided form `kerr N d = 3·d·Nᵈ⁻¹` (for `0 < N`).
* `kerr_div_card` — the probability form: the threshold `extractable_of_prob` compares against,
  `(kerr N d)/Nᵈ` with `Nᵈ = |Fin d → α|`, is exactly `3d/N` in `ℝ≥0∞`.
-/

namespace Zcash.Snark

variable {α : Type*}

/-- The exact natural-number closed form of the knowledge-error count: `kerr N d · N = 3·d·Nᵈ`.

This is `kerr N d = 3·d·Nᵈ⁻¹` cleared of the truncated exponent; the induction is immediate from the
defining recursion `kerr N (d+1) = 3·Nᵈ + N·kerr N d`. -/
theorem kerr_mul_card (N d : ℕ) : kerr N d * N = 3 * d * N ^ d := by
  induction d with
  | zero => simp [kerr]
  | succ d ih =>
      simp only [kerr]
      rw [add_mul, mul_assoc N (kerr N d) N, ih]
      ring

/-- The divided closed form `kerr N d = 3·d·Nᵈ⁻¹`, valid once `N` is nonzero (so `N` cancels). At
`d = 0` both sides are `0`; for `d ≥ 1` this is `kerr_mul_card` divided by `N`. -/
theorem kerr_eq {N : ℕ} (hN : 0 < N) (d : ℕ) : kerr N d = 3 * d * N ^ (d - 1) := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd; simp [kerr]
  · apply Nat.eq_of_mul_eq_mul_right hN
    rw [kerr_mul_card, mul_assoc (3 * d), ← pow_succ, Nat.sub_add_cancel hd]

open scoped ENNReal in
/-- **The fork-tree knowledge error is exactly `3d/N`.** The threshold `extractable_of_prob` (and
every capstone `hprob`) compares the accept probability against is `(kerr N d)/|Fin d → α|`; since
`|Fin d → α| = Nᵈ` for `N = |α|`, this equals `3·d/N` in `ℝ≥0∞`. Turning the recursive `kerr` into
this concrete fraction is what lets the deployed soundness floor be read off directly. -/
theorem kerr_div_card [Fintype α] [Nonempty α] (d : ℕ) :
    (kerr (Fintype.card α) d : ℝ≥0∞) / Fintype.card (Fin d → α)
      = 3 * d / Fintype.card α := by
  classical
  have hcard : Fintype.card (Fin d → α) = Fintype.card α ^ d := by
    rw [Fintype.card_fun, Fintype.card_fin]
  have hpos : 0 < Fintype.card α := Fintype.card_pos
  have hNe : (Fintype.card α : ℝ≥0∞) ≠ 0 := by exact_mod_cast hpos.ne'
  have hNt : (Fintype.card α : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  have hPe : ((Fintype.card α ^ d : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast (pow_pos hpos d).ne'
  have hPt : ((Fintype.card α ^ d : ℕ) : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  rw [hcard, ENNReal.div_eq_div_iff hNe hNt hPe hPt]
  have h : (kerr (Fintype.card α) d : ℝ≥0∞) * Fintype.card α
      = 3 * d * (Fintype.card α : ℝ≥0∞) ^ d := by exact_mod_cast kerr_mul_card (Fintype.card α) d
  push_cast
  rw [mul_comm (Fintype.card α : ℝ≥0∞) (kerr (Fintype.card α) d : ℝ≥0∞), h]
  ring

end Zcash.Snark
