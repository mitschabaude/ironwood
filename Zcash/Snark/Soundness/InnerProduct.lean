import Mathlib
import Zcash.Arithmetic

/-!
# Inner-product opening relation

This module defines the polynomial commitment and opening relation used by the IPA soundness proof.

The witness is a coefficient vector `a` with `P = ⟨a, G⟩` and `v = ⟨a, b⟩`, where
`b = (1, x, x², …)`.

* `commit` — `⟨a, G⟩ = Σᵢ aᵢ • gᵢ`, the polynomial commitment (the MSM's `g`-part).
* `evalVector` / `innerProduct` — `b = (1, x, …, x^{n−1})` and `⟨a, b⟩` (the polynomial at `x`).
* `IpaRelation` — the opening relation `⟨a, G⟩ = P ∧ ⟨a, b⟩ = v` the IPA is an argument of knowledge for.
* `innerProduct_add_left` gives the linearity used by the extractor.

Two distinct challenges recover one round's witness halves. The recursive extractor is defined in
`Soundness.IpaSoundness`. Opening non-uniqueness produces an explicit discrete-log relation; hardness
is used only at the computational boundary.
-/

namespace Zcash.Snark

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- The polynomial commitment of a coefficient vector `a` against the URS generators:
`⟨a, G⟩ = Σᵢ aᵢ • gᵢ`. This is the `g`-part of the fingerprint MSM (`Zcash.Arithmetic.Msm.eval`). -/
def commit (urs : URS G) (a : Fin (2 ^ urs.k) → F) : G :=
  ∑ i, a i • urs.g i

/-- The evaluation vector `b = (1, x, x², …, x^{2ᵏ−1})`. The inner product `⟨a, b⟩` is the polynomial
with coefficients `a` evaluated at `x`. -/
def evalVector (k : ℕ) (x : F) : Fin (2 ^ k) → F :=
  fun i => x ^ (i : ℕ)

/-- The inner product `⟨a, b⟩ = Σᵢ aᵢ bᵢ` of two coefficient vectors. -/
def innerProduct {n : ℕ} (a b : Fin n → F) : F :=
  ∑ i, a i * b i

/-- The coefficient vector `a` commits to `P` and has inner product `v` with `b`. -/
def IpaRelation (urs : URS G) (P : G) (b : Fin (2 ^ urs.k) → F) (v : F)
    (a : Fin (2 ^ urs.k) → F) : Prop :=
  commit urs a = P ∧ innerProduct a b = v

/-- `commit` is additive in the coefficient vector: `⟨a + a', G⟩ = ⟨a, G⟩ + ⟨a', G⟩`. -/
theorem commit_add (urs : URS G) (a a' : Fin (2 ^ urs.k) → F) :
    commit urs (a + a') = commit urs a + commit urs a' := by
  simp only [commit, Pi.add_apply, add_smul, Finset.sum_add_distrib]

/-- A single-index coefficient vector commits to that generator scaled: `⟨[i ↦ x], G⟩ = x • gᵢ`. -/
theorem commit_single (urs : URS G) (i : Fin (2 ^ urs.k)) (x : F) :
    commit urs (Pi.single i x) = x • urs.g i := by
  simp only [commit]
  rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_smul])
    (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same]

/-- `innerProduct` is additive in its left argument. -/
theorem innerProduct_add {n : ℕ} (a a' b : Fin n → F) :
    innerProduct (a + a') b = innerProduct a b + innerProduct a' b := by
  simp only [innerProduct, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- A single-index left argument: `⟨[i ↦ x], b⟩ = x · bᵢ`. -/
theorem innerProduct_single {n : ℕ} (i : Fin n) (x : F) (b : Fin n → F) :
    innerProduct (Pi.single i x) b = x * b i := by
  simp only [innerProduct]
  rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_mul])
    (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same]

/-- Convert an opening of `P − [v]g₀` at value zero to an opening of `P` at value `v`, using
`b 0 = 1`. -/
theorem ipaRelation_unshift (urs : URS G) (P : G) (b : Fin (2 ^ urs.k) → F) (v : F)
    (a : Fin (2 ^ urs.k) → F) (hb0 : b 0 = 1)
    (h : IpaRelation urs (P - v • urs.g 0) b 0 a) :
    IpaRelation urs P b v (a + Pi.single 0 v) := by
  obtain ⟨hc, hi⟩ := h
  refine ⟨?_, ?_⟩
  · rw [commit_add, commit_single, hc]; abel
  · rw [innerProduct_add, innerProduct_single, hi, hb0, mul_one, zero_add]

/-- Convert an opening of `P − [v]g₀` at value `w` to an opening of `P` at value `w + v`, using
`b 0 = 1`. This generalizes `ipaRelation_unshift` to nonzero starting values. -/
theorem ipaRelation_unshift_value (urs : URS G) (P : G) (b : Fin (2 ^ urs.k) → F) (v w : F)
    (a : Fin (2 ^ urs.k) → F) (hb0 : b 0 = 1)
    (h : IpaRelation urs (P - v • urs.g 0) b w a) :
    IpaRelation urs P b (w + v) (a + Pi.single 0 v) := by
  obtain ⟨hc, hi⟩ := h
  refine ⟨?_, ?_⟩
  · rw [commit_add, commit_single, hc]; abel
  · rw [innerProduct_add, innerProduct_single, hi, hb0, mul_one]

/-- `commit` is homogeneous: `⟨c • a, G⟩ = c • ⟨a, G⟩`. -/
theorem commit_smul (urs : URS G) (c : F) (a : Fin (2 ^ urs.k) → F) :
    commit urs (c • a) = c • commit urs a := by
  simp only [commit, Pi.smul_apply, smul_assoc, ← Finset.smul_sum]

/-- `innerProduct` is homogeneous in its left argument: `⟨c • s, b⟩ = c · ⟨s, b⟩`. -/
theorem innerProduct_smul {n : ℕ} (c : F) (s b : Fin n → F) :
    innerProduct (c • s) b = c * innerProduct s b := by
  simp only [innerProduct, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]

/-- Remove `[ξ]S` from the commitment and `ξ·s` from the witness.

The resulting opening value is `v − ξ·⟨s,b⟩`. -/
theorem ipaRelation_unblind_value (urs : URS G) (P : G) (b : Fin (2 ^ urs.k) → F) (v ξ : F)
    (s a : Fin (2 ^ urs.k) → F)
    (h : IpaRelation urs (P + ξ • commit urs s) b v a) :
    IpaRelation urs P b (v - ξ * innerProduct s b) (a - ξ • s) := by
  obtain ⟨hc, hi⟩ := h
  refine ⟨?_, ?_⟩
  · rw [sub_eq_add_neg, ← neg_smul, commit_add, commit_smul, hc, neg_smul]; abel
  · rw [sub_eq_add_neg, ← neg_smul, innerProduct_add, innerProduct_smul, hi]; ring

/-- If `⟨s,b⟩ = 0`, removing `[ξ]S` preserves the claimed opening value. -/
theorem ipaRelation_unblind (urs : URS G) (P : G) (b : Fin (2 ^ urs.k) → F) (v ξ : F)
    (s a : Fin (2 ^ urs.k) → F) (hs : innerProduct s b = 0)
    (h : IpaRelation urs (P + ξ • commit urs s) b v a) :
    IpaRelation urs P b v (a - ξ • s) := by
  have h' := ipaRelation_unblind_value urs P b v ξ s a h
  rwa [hs, mul_zero, sub_zero] at h'

/-! ## The IPA round fold and its 2-special-soundness extractor

One round of the inner-product argument halves the witness. The prover sends the cross-commitments
`(Lⱼ, Rⱼ)`, the verifier sends a challenge `uⱼ`, and the length-`2m` vector folds to length `m`. The
core of special soundness is that the same halves, folded at two distinct challenges, are uniquely
recoverable — so an accepting prover is committed to a fixed witness, which the extractor recovers. -/

/-- One IPA round folds a vector into its lower half plus `u` times its upper half (`compute_s`'s
`(1, uⱼ)` structure): `foldVec lo hi u = lo + u • hi`. The round commitments `(Lⱼ, Rⱼ)` pin `lo`, `hi`. -/
def foldVec {m : ℕ} (lo hi : Fin m → F) (u : F) : Fin m → F := lo + u • hi

/-- The IPA round extractor: from the folded vector at two distinct challenges, recover the halves —
`hi = (f₁ − f₂)/(u₁ − u₂)` and `lo = f₁ − u₁ • hi`. -/
def roundExtract {m : ℕ} (f₁ f₂ : Fin m → F) (u₁ u₂ : F) : (Fin m → F) × (Fin m → F) :=
  (f₁ - u₁ • ((u₁ - u₂)⁻¹ • (f₁ - f₂)), (u₁ - u₂)⁻¹ • (f₁ - f₂))

/-- Two distinct challenge folds uniquely recover the original vector halves. -/
theorem roundExtract_correct {m : ℕ} (lo hi : Fin m → F) (u₁ u₂ : F) (h : u₁ ≠ u₂) :
    roundExtract (foldVec lo hi u₁) (foldVec lo hi u₂) u₁ u₂ = (lo, hi) := by
  have hsub : u₁ - u₂ ≠ 0 := sub_ne_zero.mpr h
  have hi_eq : (u₁ - u₂)⁻¹ • (foldVec lo hi u₁ - foldVec lo hi u₂) = hi := by
    have hd : foldVec lo hi u₁ - foldVec lo hi u₂ = (u₁ - u₂) • hi := by
      simp only [foldVec, sub_smul]; abel
    rw [hd, smul_smul, inv_mul_cancel₀ hsub, one_smul]
  simp only [roundExtract, Prod.mk.injEq]
  refine ⟨?_, hi_eq⟩
  rw [hi_eq]
  simp only [foldVec]
  abel

/-! ## Inner-product left-additivity

The scalar side of the IPA. The fact needed downstream is that the inner product is additive in its left
argument (`innerProduct_add_left`) — the algebra the round extractor's witness fold rests on. -/

/-- The inner product is additive in its left argument. -/
theorem innerProduct_add_left {n : ℕ} (a a' b : Fin n → F) :
    innerProduct (a + a') b = innerProduct a b + innerProduct a' b := by
  simp only [innerProduct, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-! ## Commitment binding and knowledge soundness of the opening

The last ingredient is binding: distinct coefficient vectors have distinct commitments (the URS
generators are `F`-linearly independent). On the Vesta curve this is the discrete-log-relation
(DLR) hardness assumption — kept as an explicit hypothesis (project scope), not proved here,
mirroring how `Zcash/Security/BindingSignature/Balance.lean` records its cryptographic assumptions.

Given binding, the witness the special-soundness extractor produces (`roundExtract_correct` per
round, composed over the `k` rounds) is the unique opening, so an accepting proof demonstrates
knowledge of exactly one polynomial. The complementary constraint layer — that the opened
polynomials satisfy the circuit's identities — is the Schwartz–Zippel bound (`quotientCheck_sound`
in `Soundness/Constraints.lean`): a violated identity passes the random-point check only with
probability `≤ d/p`. -/

end Zcash.Snark
