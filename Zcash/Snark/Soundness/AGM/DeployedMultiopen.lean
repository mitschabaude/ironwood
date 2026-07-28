import Zcash.Snark.Soundness.AGM.AlgebraicUnbatch
import Zcash.Snark.Soundness.AGM.ShiftRecovery

/-!
# AGM unbatching for the deployed `x₄` multiopen collapse

This file connects the generic rewind-free algebraic unbatcher to the exact power batch assembled by
the deployed verifier.  It deliberately stops at the clean aggregate-value premise: deriving that
premise from the recursive IPA extractor, including the `U`-shift, is the next composition seam.
-/

namespace Zcash.Snark

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- At the deployed `x₄` collapse, online representations of the individual aggregate columns
either reconstruct the aggregate AGM coordinates immediately or expose an augmented-basis relation.
No accepting `x₄` rewinds are used. -/
def deployedX4AlgebraicBatchOrRelation [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs -> Nat -> G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (cols : AlgebraicColumnRepresentations urs
      (x4BatchCommitments urs hk vk instanceCommitment ps ch))
    (aggregate : Fin (2 ^ urs.k) → Fp) (aggregateU aggregateW : Fp)
    (haggregate : commit urs aggregate + aggregateU • urs.u + aggregateW • urs.w =
      deployedCommitment urs hk vk instanceCommitment ps ch) :
    AlgebraicPowerBatch urs (x4BatchCommitments urs hk vk instanceCommitment ps ch)
        aggregate aggregateU aggregateW ch.x4 ⊕'
      AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w := by
  apply algebraicPowerBatchOrRelation cols aggregate aggregateU aggregateW ch.x4
  have hbatch := deployedCommitment_x4_batch urs hk vk instanceCommitment ps ch ch.x4
  have heta : {ch with x4 := ch.x4} = ch := by cases ch; rfl
  rw [heta] at hbatch
  exact haggregate.trans hbatch

/-- Once the clean aggregate opens to the verifier's deployed value, a good `x₄` challenge makes
the represented aggregate columns open to all of the verifier's claimed `x₄` column values. -/
theorem deployedX4AlgebraicValues_of_good [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs -> Nat -> G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {aggregate : Fin (2 ^ urs.k) → Fp} {aggregateU aggregateW : Fp}
    (batch : AlgebraicPowerBatch urs
      (x4BatchCommitments urs hk vk instanceCommitment ps ch)
      aggregate aggregateU aggregateW ch.x4)
    (b : Fin (2 ^ urs.k) → Fp)
    (hvalue : commitGen b aggregate = multiopenValue vk instanceCommitment ps ch)
    (hgood : ch.x4 ∉ szBadSet
      (algebraicBatchErrorPolynomial b batch.coeffs
        (x4BatchEvals vk instanceCommitment ps ch))) :
    ∀ i, commitGen b (batch.coeffs i) = x4BatchEvals vk instanceCommitment ps ch i := by
  apply batch.values_of_good_challenge b (x4BatchEvals vk instanceCommitment ps ch)
  have hbatch := multiopenValue_x4_batch vk instanceCommitment ps ch ch.x4
  have heta : {ch with x4 := ch.x4} = ch := by cases ch; rfl
  rw [heta] at hbatch
  exact hvalue.trans hbatch
  exact hgood

/-- Compose the recursive IPA's shifted opening with AGM commitment unbatching.  A witness
mismatch exposes an augmented-basis relation; otherwise the two linear good-challenge conditions
recover the raw deployed value. -/
noncomputable def deployedX4AlgebraicBatchAndValueOrRelation
    [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs -> Nat -> G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (cols : AlgebraicColumnRepresentations urs
      (x4BatchCommitments urs hk vk instanceCommitment ps ch))
    (aggregate : Fin (2 ^ urs.k) → Fp) (aggregateU aggregateW : Fp)
    (haggregate : commit urs aggregate + aggregateU • urs.u + aggregateW • urs.w =
      deployedCommitment urs hk vk instanceCommitment ps ch)
    (openingWitness s : Fin (2 ^ urs.k) → Fp) (sU : Fp)
    (b : Fin (2 ^ urs.k) → Fp)
    (hopeningCommit : commit urs openingWitness = commit urs aggregate)
    (hz : ch.z ≠ 0)
    (hshifted : commitGen b openingWitness =
      multiopenValue vk instanceCommitment ps ch + ch.z⁻¹ * (aggregateU + ch.xi * sU) -
        ch.xi * commitGen b s)
    (hgoodXi : ch.xi ∉ szBadSet
      (ipaShiftXiPolynomial
        (commitGen b aggregate - multiopenValue vk instanceCommitment ps ch)
        (commitGen b s)))
    (hgoodZ : ch.z ∉ szBadSet
      (ipaShiftZPolynomial
        (commitGen b aggregate - multiopenValue vk instanceCommitment ps ch)
        aggregateU sU (commitGen b s) ch.xi)) :
    (Σ' _batch : AlgebraicPowerBatch urs
        (x4BatchCommitments urs hk vk instanceCommitment ps ch)
        aggregate aggregateU aggregateW ch.x4,
      commitGen b aggregate = multiopenValue vk instanceCommitment ps ch) ⊕'
      AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w := by
  match deployedX4AlgebraicBatchOrRelation urs hk vk instanceCommitment ps ch cols
      aggregate aggregateU aggregateW haggregate with
  | PSum.inr hrel => exact PSum.inr hrel
  | PSum.inl batch =>
      have hcollision :
          commitGen urs.g openingWitness + (0 : Fp) • urs.u + (0 : Fp) • urs.w =
            commitGen urs.g aggregate + (0 : Fp) • urs.u + (0 : Fp) • urs.w := by
        simpa [← commit_eq_commitGen] using hopeningCommit
      match separateOrRelationWitness urs.g urs.u urs.w openingWitness aggregate
          0 0 0 0 hcollision with
      | PSum.inr hrel => exact PSum.inr hrel
      | PSum.inl heq =>
          have hshifted' : commitGen b aggregate =
              multiopenValue vk instanceCommitment ps ch +
                ch.z⁻¹ * (aggregateU + ch.xi * sU) -
                ch.xi * commitGen b s := by
            rw [← heq.1]
            exact hshifted
          have hvalue := rawValue_of_shiftedValue_of_good
            (commitGen b aggregate) (multiopenValue vk instanceCommitment ps ch) aggregateU sU
            (commitGen b s) ch.xi ch.z hz hshifted' hgoodXi hgoodZ
          exact PSum.inl ⟨batch, hvalue⟩

end Zcash.Snark
