import Mathlib
import Zcash.Snark.Soundness.IpaSoundness
import Zcash.Snark.Soundness.KnowledgeSoundness
import Zcash.Snark.Verifier.Assemble

/-!
# Binding the multiopen witness to decoded columns

The IPA extractor returns one coefficient vector for the batched multiopen commitment; the gate
check needs the individual columns. This module recovers them: openings of the same batch at enough
distinct batching challenges determine the columns, their commitments, and their claimed evaluations
(`decodedColumnFamily_of_batch_openings`; `batch_open_soundV` is the abstract statement). The
rewinds that produce those openings are discharged in `Soundness.Multiopen.Deployed`; gate-structure
faithfulness stays with the fingerprint.

## Scope of the model

The decode states a single-point flat power batch. That is not a modelling gap: the deployed
statement is proven to have exactly this shape in the `x₄` squeeze, over the grouping's own
aggregates (`deployedCommitment_x4_batch`/`multiopenValue_x4_batch`), and the `x₁` layer un-batches
the aggregates down to the member commitments.

The decoded capstones state `hquot`/`hgood` for the *canonical* decode of the supplied batch
not for every family opening the same commitments: quantified over all openings the
pair is jointly unsatisfiable — tweak one column by a kernel vector vanishing at the opened point
and at `x`. The `∀`-witness endpoints are kept only as compatibility forms.

## What is proven

* **The `x₄` level.** The un-batching over the deployed grouping, and the rewound families produced
  from accept measures (`openedX4Rewind_of_x4Prob`) — the runs
  are the sealed reprogramming events of `Forking.Rewind`/`Forking.Ordering`.
* **The `x₁` level.** Each aggregate is an `x₁`-power batch of the member commitments its set
  routes (`compressSet_fst_eval`), so the extracted witness is the two-level `x₄`-then-`x₁` power
  combination of member-column witnesses.
* **The value check.** Pinning each decoded member column to its claimed evaluation at each set
  point is the rewind-free AGM route's job; it returns explicit augmented-basis coefficients on
  disagreement. The rewind-based node-binding chain that used to sit here concluded an ∃-closed
  binding disjunct instead, which a prime-order group satisfies unconditionally, and has been
  removed.

The gate constraints are `vk` data evaluated generically (`vk.gates.map (Expr.eval …)`); nothing is
transcribed, and the one faithfulness question — does the generic assembly compute what the Rust
verifier computes over the same `vk` — is the fingerprint (`Fingerprint.Match`).

## What remains

The forking-floor accept measures (the RO-uniformity axiom, as everywhere), `hfold`/`hgood` at the
terminal, the layout identities, and the bookkeeping floors. Producing the batch and member decode
from a bare accepting run — coupling the coin measure to the multiopen budget, so that *the verifier
accepted* becomes *a witness can be extracted* — is done in `Soundness.Composition`. Do **not**
generalize the free-decode endpoint `orchard_verifier_vesta_constraint_of_forked`; it stays
compatibility-shaped.
-/

namespace Zcash.Snark

open Polynomial

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- Interpret a coefficient vector as the corresponding polynomial. -/
noncomputable def coeffsToPoly {n : ℕ} (a : Fin n → Fp) : Polynomial Fp :=
  ∑ i, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)

/-- Evaluating `coeffsToPoly` is the same linear form as committing to the powers evaluation vector. -/
theorem coeffsToPoly_eval {k : ℕ} (a : Fin (2 ^ k) → Fp) (x : Fp) :
    (coeffsToPoly a).eval x = commitGen (evalVector k x) a := by
  rw [coeffsToPoly, Polynomial.eval_finsetSum]
  simp [commitGen, evalVector, smul_eq_mul]

/-- A family of rewound batched openings for one batch of column commitments.

`batched r` is the IPA witness extracted when the batching challenge is `batchChallenge r`; `current_eq`
marks which rewound opening is the current deployed witness. The commitment and value equations are
`batch_open_soundV`'s premise shape; `decodedColumnFamily_of_batch_openings` inverts them into the
per-column decode. -/
structure BatchOpeningsForWitness (urs : URS G) (b : Fin (2 ^ urs.k) → Fp) {numColumns : ℕ}
    (columnCommitments : Fin numColumns → G) (columnEvals : Fin numColumns → Fp)
    (currentWitness : Fin (2 ^ urs.k) → Fp) where
  batchChallenge : Fin numColumns → Fp
  challengesDistinct : Function.Injective batchChallenge
  batched : Fin numColumns → (Fin (2 ^ urs.k) → Fp)
  current : Fin numColumns
  current_eq : batched current = currentWitness
  commitment :
    ∀ r, commit urs (batched r)
      = ∑ j : Fin numColumns, batchChallenge r ^ (j : ℕ) • columnCommitments j
  value :
    ∀ r, commitGen b (batched r)
      = ∑ j : Fin numColumns, batchChallenge r ^ (j : ℕ) • columnEvals j






/-- The recovered per-column polynomials and their opening facts. -/
structure DecodedColumnFamily (urs : URS G) (b : Fin (2 ^ urs.k) → Fp) {numColumns : ℕ}
    (columnCommitments : Fin numColumns → G) (columnEvals : Fin numColumns → Fp)
    (cols : Fin numColumns → Polynomial Fp) where
  coeffs : Fin numColumns → (Fin (2 ^ urs.k) → Fp)
  commitment : ∀ i, commit urs (coeffs i) = columnCommitments i
  value : ∀ i, commitGen b (coeffs i) = columnEvals i
  polynomial : ∀ i, cols i = coeffsToPoly (coeffs i)

/-- The same decoded columns, tied back to the full family of rewound batched witnesses. -/
structure DecodedColumnFamilyOfBatch {urs : URS G} {b : Fin (2 ^ urs.k) → Fp} {numColumns : ℕ}
    {columnCommitments : Fin numColumns → G} {columnEvals : Fin numColumns → Fp}
    {currentWitness : Fin (2 ^ urs.k) → Fp}
    (hbatch : BatchOpeningsForWitness urs b columnCommitments columnEvals currentWitness)
    (cols : Fin numColumns → Polynomial Fp) where
  decodedColumns : DecodedColumnFamily urs b columnCommitments columnEvals cols
  reconstruct :
    ∀ r, hbatch.batched r
      = ∑ i : Fin numColumns, hbatch.batchChallenge r ^ (i : ℕ) • decodedColumns.coeffs i

/-- The current extracted witness is the current batch-challenge combination of the decoded columns. -/
theorem DecodedColumnFamilyOfBatch.currentWitness_eq {urs : URS G} {b : Fin (2 ^ urs.k) → Fp}
    {numColumns : ℕ} {columnCommitments : Fin numColumns → G} {columnEvals : Fin numColumns → Fp}
    {currentWitness : Fin (2 ^ urs.k) → Fp}
    {hbatch : BatchOpeningsForWitness urs b columnCommitments columnEvals currentWitness}
    {cols : Fin numColumns → Polynomial Fp} (hdecoded : DecodedColumnFamilyOfBatch hbatch cols) :
    currentWitness
      = ∑ i : Fin numColumns, hbatch.batchChallenge hbatch.current ^ (i : ℕ)
          • hdecoded.decodedColumns.coeffs i := by
  calc
    currentWitness = hbatch.batched hbatch.current := hbatch.current_eq.symm
    _ = ∑ i : Fin numColumns, hbatch.batchChallenge hbatch.current ^ (i : ℕ)
          • hdecoded.decodedColumns.coeffs i := hdecoded.reconstruct hbatch.current

/-- Right inverse of the Vandermonde inverse: the row functional reconstructing a sample. -/
theorem vandermonde_inv_right {n : ℕ} (z : Fin n → Fp) (hz : Function.Injective z) :
    ∀ (i j : Fin n), (∑ k : Fin n, z i ^ (k : ℕ) * (Matrix.vandermonde z)⁻¹ k j)
      = if i = j then 1 else 0 := by
  have hdet : (Matrix.vandermonde z).det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr hz
  intro i j
  have hmul : Matrix.vandermonde z * (Matrix.vandermonde z)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet)
  have h2 := congrFun (congrFun hmul i) j
  rw [Matrix.mul_apply] at h2
  simpa only [Matrix.vandermonde_apply, Matrix.one_apply] using h2

/-- Left inverse of the Vandermonde inverse, specialized to the explicit inverse coefficients. -/
theorem vandermonde_inv_left {n : ℕ} (z : Fin n → Fp) (hz : Function.Injective z) :
    ∀ (i j : Fin n), (∑ k : Fin n, (Matrix.vandermonde z)⁻¹ i k * z k ^ (j : ℕ))
      = if i = j then 1 else 0 := by
  have hdet : (Matrix.vandermonde z).det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr hz
  intro i j
  have hmul : (Matrix.vandermonde z)⁻¹ * Matrix.vandermonde z = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet)
  have h2 := congrFun (congrFun hmul i) j
  rw [Matrix.mul_apply] at h2
  simpa only [Matrix.vandermonde_apply, Matrix.one_apply] using h2

/-- The explicit Vandermonde-decoded columns reconstruct each rewound batched witness. -/
theorem batch_open_reconstruct_with_coeffs {m n : ℕ} (z : Fin n → Fp)
    (a : Fin n → (Fin m → Fp)) (μ : Fin n → Fin n → Fp)
    (hμ : ∀ (i j : Fin n), (∑ k : Fin n, z i ^ (k : ℕ) * μ k j)
      = if i = j then 1 else 0)
    (i : Fin n) :
    (∑ j : Fin n, z i ^ (j : ℕ) • (∑ k : Fin n, μ j k • a k)) = a i := by
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, hμ, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

/-- Recover the individual column polynomials from rewound batched openings. -/
noncomputable def decodedColumnFamily_of_batch_openings {urs : URS G} {b : Fin (2 ^ urs.k) → Fp}
    {numColumns : ℕ} {columnCommitments : Fin numColumns → G}
    {columnEvals : Fin numColumns → Fp} {currentWitness : Fin (2 ^ urs.k) → Fp}
    (hbatch : BatchOpeningsForWitness urs b columnCommitments columnEvals currentWitness) :
    Σ cols : Fin numColumns → Polynomial Fp,
      DecodedColumnFamilyOfBatch hbatch cols := by
  have haC :
      ∀ r, commitGen urs.g (hbatch.batched r)
        = ∑ j : Fin numColumns, hbatch.batchChallenge r ^ (j : ℕ) • columnCommitments j := by
    intro r
    rw [← commit_eq_commitGen urs (hbatch.batched r)]
    exact hbatch.commitment r
  let μ : Matrix (Fin numColumns) (Fin numColumns) Fp :=
    (Matrix.vandermonde hbatch.batchChallenge)⁻¹
  let coeffs : Fin numColumns → (Fin (2 ^ urs.k) → Fp) :=
    fun i => ∑ r, μ i r • hbatch.batched r
  have hleft :
      ∀ (i j : Fin numColumns), (∑ k : Fin numColumns,
          μ i k * hbatch.batchChallenge k ^ (j : ℕ))
        = if i = j then 1 else 0 := by
    intro i j
    simpa [μ] using vandermonde_inv_left hbatch.batchChallenge hbatch.challengesDistinct i j
  have hright :
      ∀ (i j : Fin numColumns), (∑ k : Fin numColumns,
          hbatch.batchChallenge i ^ (k : ℕ) * μ k j)
        = if i = j then 1 else 0 := by
    intro i j
    simpa [μ] using vandermonde_inv_right hbatch.batchChallenge hbatch.challengesDistinct i j
  exact
    ⟨fun i => coeffsToPoly (coeffs i),
      { decodedColumns :=
          { coeffs := coeffs
            commitment := by
              intro i
              rw [commit_eq_commitGen]
              exact batch_open_with_coeffs urs.g columnCommitments hbatch.batchChallenge
                hbatch.batched μ hleft haC i
            value := by
              intro i
              exact batch_open_with_coeffs b columnEvals hbatch.batchChallenge hbatch.batched μ
                hleft hbatch.value i
            polynomial := by
              intro i
              rfl }
        reconstruct := by
          intro r
          exact (batch_open_reconstruct_with_coeffs hbatch.batchChallenge hbatch.batched μ hright r).symm }⟩



namespace DecodedColumnFamily

/-- A decoded column's claimed evaluation is the value of the recovered polynomial at the opened point. -/
theorem eval_eq {urs : URS G} {numColumns : ℕ} {columnCommitments : Fin numColumns → G}
    {columnEvals : Fin numColumns → Fp} {cols : Fin numColumns → Polynomial Fp}
    {x : Fp}
    (hcols : DecodedColumnFamily urs (evalVector urs.k x) columnCommitments columnEvals cols)
    (i : Fin numColumns) :
    (cols i).eval x = columnEvals i := by
  rw [hcols.polynomial i, coeffsToPoly_eval, hcols.value i]

end DecodedColumnFamily

/-- Select a finite family of recovered columns and totalize it for gate-expression evaluation. -/
noncomputable def selectedPolys {numColumns numSelected : ℕ} (cols : Fin numColumns → Polynomial Fp)
    (idx : Fin numSelected → Fin numColumns) : ℕ → Polynomial Fp :=
  finFn fun i : Fin numSelected => cols (idx i)

/-- A witness-indexed decode function that ignores the witness after the columns have been recovered. -/
noncomputable def selectedPolysDecode {k numColumns numSelected : ℕ}
    (cols : Fin numColumns → Polynomial Fp) (idx : Fin numSelected → Fin numColumns) :
    (Fin (2 ^ k) → Fp) → ℕ → Polynomial Fp :=
  fun _ => selectedPolys cols idx


end Zcash.Snark
