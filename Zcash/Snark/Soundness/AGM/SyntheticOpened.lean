import Zcash.Snark.Soundness.AGM.DeployedValueUnbatch
import Zcash.Snark.Soundness.Multiopen.Opened

/-!
# Offline compatibility with the opened-batch interface

Represented columns form power combinations at any distinct interpolation points locally, so this
file packages them as a *synthetic* `OpenedBatchOpenings` — algebraic calculations, not accepting
transcripts.  Its canonical Vandermonde decode returns the original AGM coordinates exactly, so
deterministic downstream constraints are reused without the old rewind loss.
-/

namespace Zcash.Snark

open Classical

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- Build an opened-batch compatibility object locally from a represented algebraic power batch,
with one interpolation point pinned to the actual batching challenge. -/
noncomputable def AlgebraicPowerBatch.toSyntheticOpened
    {urs : URS G} {numColumns : Nat} {columnCommitments : Fin numColumns -> G}
    {aggregate : Fin (2 ^ urs.k) -> Fp} {aggregateU aggregateW challenge : Fp}
    (batch : AlgebraicPowerBatch urs columnCommitments aggregate aggregateU aggregateW challenge)
    (b : Fin (2 ^ urs.k) -> Fp) (columnEvals : Fin numColumns -> Fp)
    (hvalues : forall i, commitGen b (batch.coeffs i) = columnEvals i)
    (points : Fin numColumns -> Fp) (hpoints : Function.Injective points)
    (current : Fin numColumns) (hcurrent : points current = challenge) :
    OpenedBatchOpenings urs b columnCommitments columnEvals aggregate aggregateU aggregateW := by
  let cols : AlgebraicColumnRepresentations urs columnCommitments :=
    { coeffs := batch.coeffs
      uComp := batch.uComp
      wComp := batch.wComp
      commitment := batch.commitment }
  refine
    { batchChallenge := points
      challengesDistinct := hpoints
      batched := fun r => ∑ i : Fin numColumns, points r ^ (i : Nat) • batch.coeffs i
      batchedU := fun r => ∑ i : Fin numColumns, points r ^ (i : Nat) * batch.uComp i
      batchedW := fun r => ∑ i : Fin numColumns, points r ^ (i : Nat) * batch.wComp i
      current := current
      current_eq := ?_
      currentU_eq := ?_
      currentW_eq := ?_
      commitment := ?_
      value := ?_ }
  · rw [hcurrent]
    exact batch.reconstruct.symm
  · rw [hcurrent]
    exact batch.reconstructU.symm
  · rw [hcurrent]
    exact batch.reconstructW.symm
  · intro r
    exact cols.power_commitment (points r)
  · intro r
    rw [commitGen_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [commitGen_smul_left, hvalues, smul_eq_mul]

/-- Canonically decoding a synthetic opened batch returns the original AGM witness coordinate. -/
theorem AlgebraicPowerBatch.openedColumnDecode_toSyntheticOpened_coeffs
    {urs : URS G} {numColumns : Nat} {columnCommitments : Fin numColumns -> G}
    {aggregate : Fin (2 ^ urs.k) -> Fp} {aggregateU aggregateW challenge : Fp}
    (batch : AlgebraicPowerBatch urs columnCommitments aggregate aggregateU aggregateW challenge)
    (b : Fin (2 ^ urs.k) -> Fp) (columnEvals : Fin numColumns -> Fp)
    (hvalues : forall i, commitGen b (batch.coeffs i) = columnEvals i)
    (points : Fin numColumns -> Fp) (hpoints : Function.Injective points)
    (current : Fin numColumns) (hcurrent : points current = challenge) (i : Fin numColumns) :
    (openedColumnDecode
      (batch.toSyntheticOpened b columnEvals hvalues points hpoints current hcurrent)).coeffs i =
        batch.coeffs i := by
  change (∑ r : Fin numColumns, (Matrix.vandermonde points)⁻¹ i r •
    (∑ j : Fin numColumns, points r ^ (j : Nat) • batch.coeffs j)) = batch.coeffs i
  exact vandermonde_decode_map
    ((Matrix.vandermonde points)⁻¹ : Matrix (Fin numColumns) (Fin numColumns) Fp)
    (fun i j => vandermonde_inv_left points hpoints i j) (fun _ => rfl) i

/-- Canonically decoding a synthetic opened batch returns the original AGM `U` coordinate. -/
theorem AlgebraicPowerBatch.openedColumnDecode_toSyntheticOpened_uComp
    {urs : URS G} {numColumns : Nat} {columnCommitments : Fin numColumns -> G}
    {aggregate : Fin (2 ^ urs.k) -> Fp} {aggregateU aggregateW challenge : Fp}
    (batch : AlgebraicPowerBatch urs columnCommitments aggregate aggregateU aggregateW challenge)
    (b : Fin (2 ^ urs.k) -> Fp) (columnEvals : Fin numColumns -> Fp)
    (hvalues : forall i, commitGen b (batch.coeffs i) = columnEvals i)
    (points : Fin numColumns -> Fp) (hpoints : Function.Injective points)
    (current : Fin numColumns) (hcurrent : points current = challenge) (i : Fin numColumns) :
    (openedColumnDecode
      (batch.toSyntheticOpened b columnEvals hvalues points hpoints current hcurrent)).uComp i =
        batch.uComp i := by
  change (∑ r : Fin numColumns, (Matrix.vandermonde points)⁻¹ i r •
    (∑ j : Fin numColumns, points r ^ (j : Nat) * batch.uComp j)) = batch.uComp i
  exact vandermonde_decode_map
    ((Matrix.vandermonde points)⁻¹ : Matrix (Fin numColumns) (Fin numColumns) Fp)
    (fun i j => vandermonde_inv_left points hpoints i j) (fun _ => rfl) i

/-- Canonically decoding a synthetic opened batch returns the original AGM `W` coordinate. -/
theorem AlgebraicPowerBatch.openedColumnDecode_toSyntheticOpened_wComp
    {urs : URS G} {numColumns : Nat} {columnCommitments : Fin numColumns -> G}
    {aggregate : Fin (2 ^ urs.k) -> Fp} {aggregateU aggregateW challenge : Fp}
    (batch : AlgebraicPowerBatch urs columnCommitments aggregate aggregateU aggregateW challenge)
    (b : Fin (2 ^ urs.k) -> Fp) (columnEvals : Fin numColumns -> Fp)
    (hvalues : forall i, commitGen b (batch.coeffs i) = columnEvals i)
    (points : Fin numColumns -> Fp) (hpoints : Function.Injective points)
    (current : Fin numColumns) (hcurrent : points current = challenge) (i : Fin numColumns) :
    (openedColumnDecode
      (batch.toSyntheticOpened b columnEvals hvalues points hpoints current hcurrent)).wComp i =
        batch.wComp i := by
  change (∑ r : Fin numColumns, (Matrix.vandermonde points)⁻¹ i r •
    (∑ j : Fin numColumns, points r ^ (j : Nat) * batch.wComp j)) = batch.wComp i
  exact vandermonde_decode_map
    ((Matrix.vandermonde points)⁻¹ : Matrix (Fin numColumns) (Fin numColumns) Fp)
    (fun i j => vandermonde_inv_left points hpoints i j) (fun _ => rfl) i

end Zcash.Snark
