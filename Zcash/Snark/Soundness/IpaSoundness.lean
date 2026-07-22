import Mathlib
import Zcash.Snark.Soundness.CommitFold
import Zcash.Snark.Soundness.Consistency

/-!
# IPA special-soundness extraction

This module derives an IPA opening witness from a ternary accepting transcript tree.

One IPA round is 3-special-sound for the commitment. Three sub-openings at distinct nonzero challenges
determine a parent witness through a Vandermonde combination. Two challenges do not fully pin the
parent commitment.

The extraction uses only module algebra. Binding is needed later for uniqueness.

* `vandermonde3` — the three-point functional reading off a degree-≤2 polynomial's linear
  coefficient from its samples.
* `ipa_round_commit_sound` — the round fold as a lemma: three sub-openings at distinct nonzero
  challenges pin the parent commitment. Pure module linear algebra, no binding.
-/

namespace Zcash.Snark

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- Compute coefficients that extract the linear term of a quadratic from three distinct samples. -/
def vandermonde3 (u₁ u₂ u₃ : F) (h12 : u₁ ≠ u₂) (h13 : u₁ ≠ u₃) (h23 : u₂ ≠ u₃) :
    Σ' (l₁ l₂ l₃ : F), (l₁ + l₂ + l₃ = 0) ∧ (l₁ * u₁ + l₂ * u₂ + l₃ * u₃ = 1)
      ∧ (l₁ * u₁ ^ 2 + l₂ * u₂ ^ 2 + l₃ * u₃ ^ 2 = 0) := by
  have d12 : u₁ - u₂ ≠ 0 := sub_ne_zero.mpr h12
  have d13 : u₁ - u₃ ≠ 0 := sub_ne_zero.mpr h13
  have d23 : u₂ - u₃ ≠ 0 := sub_ne_zero.mpr h23
  have d21 : u₂ - u₁ ≠ 0 := sub_ne_zero.mpr h12.symm
  have d31 : u₃ - u₁ ≠ 0 := sub_ne_zero.mpr h13.symm
  have d32 : u₃ - u₂ ≠ 0 := sub_ne_zero.mpr h23.symm
  refine ⟨-(u₂ + u₃) / ((u₁ - u₂) * (u₁ - u₃)), -(u₁ + u₃) / ((u₂ - u₁) * (u₂ - u₃)),
    -(u₁ + u₂) / ((u₃ - u₁) * (u₃ - u₂)), ?_, ?_, ?_⟩ <;> field_simp <;> ring

/-- Combine three sub-opening witnesses into an explicit parent witness. -/
theorem ipa_round_commit_with_coeffs {m : ℕ} (g_lo g_hi : Fin m → G) (P L R : G)
    (c₁ c₂ c₃ : Fin m → F) (u₁ u₂ u₃ l₁ l₂ l₃ : F)
    (hl0 : l₁ + l₂ + l₃ = 0) (hl1 : l₁ * u₁ + l₂ * u₂ + l₃ * u₃ = 1)
    (hl2 : l₁ * u₁ ^ 2 + l₂ * u₂ ^ 2 + l₃ * u₃ ^ 2 = 0)
    (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0) (hu₃ : u₃ ≠ 0)
    (e₁ : commitGen (g_lo + u₁⁻¹ • g_hi) c₁ = P + u₁⁻¹ • L + u₁ • R)
    (e₂ : commitGen (g_lo + u₂⁻¹ • g_hi) c₂ = P + u₂⁻¹ • L + u₂ • R)
    (e₃ : commitGen (g_lo + u₃⁻¹ • g_hi) c₃ = P + u₃⁻¹ • L + u₃ • R) :
    commitGen g_lo (l₁ • (u₁ • c₁) + l₂ • (u₂ • c₂) + l₃ • (u₃ • c₃))
      + commitGen g_hi (l₁ • c₁ + l₂ • c₂ + l₃ • c₃) = P := by
  rw [commitGen_add_gen, commitGen_smul_gen] at e₁ e₂ e₃
  have s₁ : u₁ • commitGen g_lo c₁ + commitGen g_hi c₁ = u₁ • P + L + (u₁ * u₁) • R := by
    have h := congrArg (u₁ • ·) e₁
    simp only [smul_add, smul_smul, mul_inv_cancel₀ hu₁, one_smul] at h; exact h
  have s₂ : u₂ • commitGen g_lo c₂ + commitGen g_hi c₂ = u₂ • P + L + (u₂ * u₂) • R := by
    have h := congrArg (u₂ • ·) e₂
    simp only [smul_add, smul_smul, mul_inv_cancel₀ hu₂, one_smul] at h; exact h
  have s₃ : u₃ • commitGen g_lo c₃ + commitGen g_hi c₃ = u₃ • P + L + (u₃ * u₃) • R := by
    have h := congrArg (u₃ • ·) e₃
    simp only [smul_add, smul_smul, mul_inv_cancel₀ hu₃, one_smul] at h; exact h
  have hB₁ : commitGen g_hi c₁ = u₁ • P + L + (u₁ * u₁) • R - u₁ • commitGen g_lo c₁ := by
    rw [← s₁]; abel
  have hB₂ : commitGen g_hi c₂ = u₂ • P + L + (u₂ * u₂) • R - u₂ • commitGen g_lo c₂ := by
    rw [← s₂]; abel
  have hB₃ : commitGen g_hi c₃ = u₃ • P + L + (u₃ * u₃) • R - u₃ • commitGen g_lo c₃ := by
    rw [← s₃]; abel
  simp only [commitGen_add_left, commitGen_smul_left, hB₁, hB₂, hB₃]
  match_scalars <;>
    first
      | linear_combination hl1
      | linear_combination hl0
      | linear_combination hl2
      | ring

/-- Three distinct nonzero challenge openings determine a parent commitment opening. -/
theorem ipa_round_commit_sound {m : ℕ} (g_lo g_hi : Fin m → G) (P L R : G)
    (c₁ c₂ c₃ : Fin m → F) (u₁ u₂ u₃ : F)
    (h12 : u₁ ≠ u₂) (h13 : u₁ ≠ u₃) (h23 : u₂ ≠ u₃)
    (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0) (hu₃ : u₃ ≠ 0)
    (e₁ : commitGen (g_lo + u₁⁻¹ • g_hi) c₁ = P + u₁⁻¹ • L + u₁ • R)
    (e₂ : commitGen (g_lo + u₂⁻¹ • g_hi) c₂ = P + u₂⁻¹ • L + u₂ • R)
    (e₃ : commitGen (g_lo + u₃⁻¹ • g_hi) c₃ = P + u₃⁻¹ • L + u₃ • R) :
    ∃ a_lo a_hi : Fin m → F, commitGen g_lo a_lo + commitGen g_hi a_hi = P := by
  obtain ⟨l₁, l₂, l₃, hl0, hl1, hl2⟩ := vandermonde3 u₁ u₂ u₃ h12 h13 h23
  exact ⟨_, _, ipa_round_commit_with_coeffs g_lo g_hi P L R c₁ c₂ c₃ u₁ u₂ u₃ l₁ l₂ l₃
    hl0 hl1 hl2 hu₁ hu₂ hu₃ e₁ e₂ e₃⟩

/-- Split a commitment over the lower and upper halves of its vectors. -/
theorem commitGen_split {k : ℕ} (g : Fin (2 ^ (k + 1)) → G) (a : Fin (2 ^ (k + 1)) → F) :
    commitGen g a = commitGen (loHalf g) (loHalf a) + commitGen (hiHalf g) (hiHalf a) := by
  have e : 2 ^ k + 2 ^ k = 2 ^ (k + 1) := by rw [pow_succ]; ring
  let φ : Fin (2 ^ k) ⊕ Fin (2 ^ k) ≃ Fin (2 ^ (k + 1)) := finSumFinEquiv.trans (finCongr e)
  simp only [commitGen]
  rw [← φ.sum_comp (fun j => a j • g j), Fintype.sum_sum_type]
  congr 1

/-- The lower half of an `append` is the lower part. -/
theorem loHalf_append {α : Type*} {k : ℕ} (lo hi : Fin (2 ^ k) → α) : loHalf (append lo hi) = lo := by
  funext i; simp only [loHalf, append, dif_pos i.isLt]

/-- The upper half of an `append` is the upper part. -/
theorem hiHalf_append {α : Type*} {k : ℕ} (lo hi : Fin (2 ^ k) → α) : hiHalf (append lo hi) = hi := by
  funext i
  have h : ¬ (2 ^ k + i.val < 2 ^ k) := by omega
  simp only [hiHalf, append, dif_neg h]
  congr 1; apply Fin.ext; simp

/-- A commitment to `append a_lo a_hi` splits into commitments to both halves. -/
theorem commitGen_append {k : ℕ} (g : Fin (2 ^ (k + 1)) → G) (a_lo a_hi : Fin (2 ^ k) → F) :
    commitGen g (append a_lo a_hi) = commitGen (loHalf g) a_lo + commitGen (hiHalf g) a_hi := by
  rw [commitGen_split, loHalf_append, hiHalf_append]

/-! ## The IPA soundness recursion -/

/-- A ternary IPA transcript tree with three challenge continuations at each round. -/
inductive IpaTree (F G : Type*) : ℕ → Type _ where
  | leaf : F → IpaTree F G 0
  | node {d : ℕ} : G → G → F → F → F →
      IpaTree F G d → IpaTree F G d → IpaTree F G d → IpaTree F G (d + 1)

/-- Recursive acceptance for a ternary IPA transcript tree. -/
def IpaAccept : {d : ℕ} → (Fin (2 ^ d) → G) → G → IpaTree F G d → Prop
  | 0, g, P, .leaf c => P = commitGen g (fun _ => c)
  | _ + 1, g, P, .node L R u₁ u₂ u₃ t₁ t₂ t₃ =>
      u₁ ≠ u₂ ∧ u₁ ≠ u₃ ∧ u₂ ≠ u₃ ∧ u₁ ≠ 0 ∧ u₂ ≠ 0 ∧ u₃ ≠ 0 ∧
        IpaAccept (foldGens g u₁) (P + u₁⁻¹ • L + u₁ • R) t₁ ∧
        IpaAccept (foldGens g u₂) (P + u₂⁻¹ • L + u₂ • R) t₂ ∧
        IpaAccept (foldGens g u₃) (P + u₃⁻¹ • L + u₃ • R) t₃

/-- An accepting transcript tree yields a coefficient vector opening `P`. -/
theorem ipa_sound : {d : ℕ} → (g : Fin (2 ^ d) → G) → (P : G) → (t : IpaTree F G d) →
    IpaAccept g P t → ∃ a : Fin (2 ^ d) → F, commitGen g a = P
  | 0, g, P, .leaf c, h => ⟨fun _ => c, h.symm⟩
  | _ + 1, g, P, .node L R u₁ u₂ u₃ t₁ t₂ t₃, h => by
      obtain ⟨h12, h13, h23, hu₁, hu₂, hu₃, ha₁, ha₂, ha₃⟩ := h
      obtain ⟨c₁, hc₁⟩ := ipa_sound (foldGens g u₁) _ t₁ ha₁
      obtain ⟨c₂, hc₂⟩ := ipa_sound (foldGens g u₂) _ t₂ ha₂
      obtain ⟨c₃, hc₃⟩ := ipa_sound (foldGens g u₃) _ t₃ ha₃
      obtain ⟨a_lo, a_hi, hP⟩ := ipa_round_commit_sound (loHalf g) (hiHalf g) P L R c₁ c₂ c₃
        u₁ u₂ u₃ h12 h13 h23 hu₁ hu₂ hu₃ hc₁ hc₂ hc₃
      exact ⟨append a_lo a_hi, by rw [commitGen_append]; exact hP⟩

/-! ## The full opening relation (commitment + inner product)

The same extraction applied to `b` proves the inner-product equation. `IpaTreeV` carries both sets of
round terms so one witness satisfies both equations.
-/

/-- A ternary IPA tree carrying commitment and inner-product round terms. -/
inductive IpaTreeV (F G : Type*) : ℕ → Type _ where
  | leaf : F → IpaTreeV F G 0
  | node {d : ℕ} : G → G → F → F → F → F → F →
      IpaTreeV F G d → IpaTreeV F G d → IpaTreeV F G d → IpaTreeV F G (d + 1)

/-- Recursive acceptance for both the commitment and inner-product equations. -/
def IpaAcceptV : {d : ℕ} → (Fin (2 ^ d) → G) → (Fin (2 ^ d) → F) → G → F → IpaTreeV F G d → Prop
  | 0, g, b, P, v, .leaf c => P = commitGen g (fun _ => c) ∧ v = commitGen b (fun _ => c)
  | _ + 1, g, b, P, v, .node L R Lv Rv u₁ u₂ u₃ t₁ t₂ t₃ =>
      u₁ ≠ u₂ ∧ u₁ ≠ u₃ ∧ u₂ ≠ u₃ ∧ u₁ ≠ 0 ∧ u₂ ≠ 0 ∧ u₃ ≠ 0 ∧
        IpaAcceptV (foldGens g u₁) (foldGens b u₁) (P + u₁⁻¹ • L + u₁ • R) (v + u₁⁻¹ • Lv + u₁ • Rv) t₁ ∧
        IpaAcceptV (foldGens g u₂) (foldGens b u₂) (P + u₂⁻¹ • L + u₂ • R) (v + u₂⁻¹ • Lv + u₂ • Rv) t₂ ∧
        IpaAcceptV (foldGens g u₃) (foldGens b u₃) (P + u₃⁻¹ • L + u₃ • R) (v + u₃⁻¹ • Lv + u₃ • Rv) t₃

/-- Compute an explicit opening witness and both of its equations from an accepting full IPA tree. -/
def ipa_extractV : {d : ℕ} → (g : Fin (2 ^ d) → G) → (b : Fin (2 ^ d) → F) → (P : G) → (v : F) →
    (t : IpaTreeV F G d) → IpaAcceptV g b P v t →
    Σ' a : Fin (2 ^ d) → F, commitGen g a = P ∧ commitGen b a = v
  | 0, g, b, P, v, .leaf c, h => ⟨fun _ => c, h.1.symm, h.2.symm⟩
  | _ + 1, g, b, P, v, .node L R Lv Rv u₁ u₂ u₃ t₁ t₂ t₃, h => by
      obtain ⟨h12, h13, h23, hu₁, hu₂, hu₃, ha₁, ha₂, ha₃⟩ := h
      obtain ⟨c₁, hP₁, hv₁⟩ := ipa_extractV (foldGens g u₁) (foldGens b u₁) _ _ t₁ ha₁
      obtain ⟨c₂, hP₂, hv₂⟩ := ipa_extractV (foldGens g u₂) (foldGens b u₂) _ _ t₂ ha₂
      obtain ⟨c₃, hP₃, hv₃⟩ := ipa_extractV (foldGens g u₃) (foldGens b u₃) _ _ t₃ ha₃
      obtain ⟨l₁, l₂, l₃, hl0, hl1, hl2⟩ := vandermonde3 u₁ u₂ u₃ h12 h13 h23
      refine ⟨append (l₁ • (u₁ • c₁) + l₂ • (u₂ • c₂) + l₃ • (u₃ • c₃)) (l₁ • c₁ + l₂ • c₂ + l₃ • c₃),
        ?_, ?_⟩
      · rw [commitGen_append]
        exact ipa_round_commit_with_coeffs (loHalf g) (hiHalf g) P L R c₁ c₂ c₃ u₁ u₂ u₃ l₁ l₂ l₃
          hl0 hl1 hl2 hu₁ hu₂ hu₃ hP₁ hP₂ hP₃
      · rw [commitGen_append]
        exact ipa_round_commit_with_coeffs (loHalf b) (hiHalf b) v Lv Rv c₁ c₂ c₃ u₁ u₂ u₃ l₁ l₂ l₃
          hl0 hl1 hl2 hu₁ hu₂ hu₃ hv₁ hv₂ hv₃

/-- Existential projection of `ipa_extractV` for proof-only callers. -/
theorem ipa_soundV {d : ℕ} (g : Fin (2 ^ d) → G) (b : Fin (2 ^ d) → F) (P : G) (v : F)
    (t : IpaTreeV F G d) (h : IpaAcceptV g b P v t) :
    ∃ a : Fin (2 ^ d) → F, commitGen g a = P ∧ commitGen b a = v :=
  ⟨(ipa_extractV g b P v t h).1, (ipa_extractV g b P v t h).2⟩

/-! ## The multiopen batch decode

The verifier opens one linear combination of column commitments. Openings at enough distinct batching
challenges form a Vandermonde system that recovers each column opening.
-/

/-- Compute coefficients that recover polynomial coefficients from values at distinct points. -/
theorem vandermonde_inv {n : ℕ} (z : Fin n → F) (hz : Function.Injective z) :
    ∃ μ : Fin n → Fin n → F, ∀ (i j : Fin n), (∑ k, μ i k * z k ^ (j : ℕ)) = if i = j then 1 else 0 := by
  have hdet : (Matrix.vandermonde z).det ≠ 0 := by
    rw [Matrix.det_vandermonde, Finset.prod_ne_zero_iff]
    intro i _
    rw [Finset.prod_ne_zero_iff]
    intro j hj
    rw [Finset.mem_Ioi] at hj
    exact sub_ne_zero.mpr (fun h => absurd (hz h) (ne_of_lt hj).symm)
  refine ⟨fun i k => (Matrix.vandermonde z)⁻¹ i k, fun i j => ?_⟩
  have hmul : (Matrix.vandermonde z)⁻¹ * Matrix.vandermonde z = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet)
  have h2 := congrFun (congrFun hmul i) j
  rw [Matrix.mul_apply] at h2
  simpa only [Matrix.vandermonde_apply, Matrix.one_apply] using h2

/-- A length-`m` commitment is additive over a finite sum of witnesses. -/
theorem commitGen_sum {m : ℕ} (g : Fin m → G) {ι : Type*} (s : Finset ι) (f : ι → Fin m → F) :
    commitGen g (∑ k ∈ s, f k) = ∑ k ∈ s, commitGen g (f k) := by
  classical
  induction s using Finset.induction with
  | empty => simp [commitGen]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, commitGen_add_left, ih]

/-- Use Vandermonde coefficients to recover one individual opening from batched openings. -/
theorem batch_open_with_coeffs {m n : ℕ} (g : Fin m → G) (C : Fin n → G) (z : Fin n → F)
    (a : Fin n → (Fin m → F)) (μ : Fin n → Fin n → F)
    (hμ : ∀ (i j : Fin n), (∑ k, μ i k * z k ^ (j : ℕ)) = if i = j then 1 else 0)
    (ha : ∀ k, commitGen g (a k) = ∑ j : Fin n, z k ^ (j : ℕ) • C j) (i : Fin n) :
    commitGen g (∑ k, μ i k • a k) = C i := by
  rw [commitGen_sum]
  simp only [commitGen_smul_left, ha, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, hμ, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

/-- Recover each commitment and value opening from valid batches at distinct challenges. Reference
form: the live decode (`decodedColumnFamily_of_batch_openings`, `Soundness.Multiopen.Decode`) needs
the canonical witness and the reconstruction equations, so it builds them from the shared core
`batch_open_with_coeffs` directly; this existential states the recoverability fact it instantiates. -/
theorem batch_open_soundV {m n : ℕ} (g : Fin m → G) (b : Fin m → F) (C : Fin n → G) (e : Fin n → F)
    (z : Fin n → F) (hz : Function.Injective z) (a : Fin n → (Fin m → F))
    (haC : ∀ k, commitGen g (a k) = ∑ j : Fin n, z k ^ (j : ℕ) • C j)
    (hae : ∀ k, commitGen b (a k) = ∑ j : Fin n, z k ^ (j : ℕ) • e j) :
    ∃ col : Fin n → (Fin m → F), ∀ i, commitGen g (col i) = C i ∧ commitGen b (col i) = e i := by
  obtain ⟨μ, hμ⟩ := vandermonde_inv z hz
  exact ⟨fun i => ∑ k, μ i k • a k, fun i =>
    ⟨batch_open_with_coeffs g C z a μ hμ haC i, batch_open_with_coeffs b e z a μ hμ hae i⟩⟩

end Zcash.Snark
