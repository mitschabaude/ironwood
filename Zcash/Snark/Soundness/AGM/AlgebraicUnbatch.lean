import Zcash.Snark.Soundness.AGM.OnlineMultiopen
import Zcash.Snark.Soundness.GoodChallenge

/-!
# Rewind-free algebraic power-batch unbatching

Online AGM coordinates already supply the individual column witnesses of a verifier power batch,
so no accepting rewinds are needed.  The only probabilistic step is value binding: a mismatch
makes the fresh challenge a root of one explicit error polynomial, priced separately.
-/

namespace Zcash.Snark

open Polynomial
open Classical

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- Augmented `(g,U,W)` representations of a family of column commitments. -/
structure AlgebraicColumnRepresentations (urs : URS G) {numColumns : Nat}
    (columnCommitments : Fin numColumns -> G) where
  coeffs : Fin numColumns -> (Fin (2 ^ urs.k) -> Fp)
  uComp : Fin numColumns -> Fp
  wComp : Fin numColumns -> Fp
  commitment : forall i,
    commit urs (coeffs i) + uComp i • urs.u + wComp i • urs.w = columnCommitments i

/-- The augmented representation of a power sum is the componentwise power sum of the column
representations. -/
theorem AlgebraicColumnRepresentations.power_commitment
    {urs : URS G} {numColumns : Nat} {columnCommitments : Fin numColumns -> G}
    (cols : AlgebraicColumnRepresentations urs columnCommitments) (x : Fp) :
    commit urs (∑ i : Fin numColumns, x ^ (i : Nat) • cols.coeffs i) +
        (∑ i : Fin numColumns, x ^ (i : Nat) * cols.uComp i) • urs.u +
        (∑ i : Fin numColumns, x ^ (i : Nat) * cols.wComp i) • urs.w =
      ∑ i : Fin numColumns, x ^ (i : Nat) • columnCommitments i := by
  have hlin :
      commit urs (∑ i : Fin numColumns, x ^ (i : Nat) • cols.coeffs i) +
          (∑ i : Fin numColumns, x ^ (i : Nat) * cols.uComp i) • urs.u +
          (∑ i : Fin numColumns, x ^ (i : Nat) * cols.wComp i) • urs.w =
        ∑ i : Fin numColumns, x ^ (i : Nat) •
          (commit urs (cols.coeffs i) + cols.uComp i • urs.u + cols.wComp i • urs.w) := by
    rw [commit_eq_commitGen, commitGen_sum, Finset.sum_smul, Finset.sum_smul,
      <- Finset.sum_add_distrib, <- Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_add, smul_add, commit_eq_commitGen, commitGen_smul_left,
      mul_smul, mul_smul]
  rw [hlin]
  exact Finset.sum_congr rfl fun i _ => congrArg _ (cols.commitment i)

/-- AGM coordinates for the columns of one power batch and their exact reconstruction at the
current challenge.  Unlike `OpenedColumnDecode`, these columns come from representations, not from
inverting a family of rewound openings. -/
structure AlgebraicPowerBatch (urs : URS G) {numColumns : Nat}
    (columnCommitments : Fin numColumns -> G)
    (aggregate : Fin (2 ^ urs.k) -> Fp) (aggregateU aggregateW challenge : Fp) where
  coeffs : Fin numColumns -> (Fin (2 ^ urs.k) -> Fp)
  uComp : Fin numColumns -> Fp
  wComp : Fin numColumns -> Fp
  commitment : forall i,
    commit urs (coeffs i) + uComp i • urs.u + wComp i • urs.w = columnCommitments i
  reconstruct : aggregate = ∑ i : Fin numColumns, challenge ^ (i : Nat) • coeffs i
  reconstructU : aggregateU = ∑ i : Fin numColumns, challenge ^ (i : Nat) * uComp i
  reconstructW : aggregateW = ∑ i : Fin numColumns, challenge ^ (i : Nat) * wComp i

/-- A successful algebraic unbatch together with the provenance fact that its columns are exactly
the online representations supplied to the unbatcher. -/
structure AlgebraicPowerBatchWithSource (urs : URS G) {numColumns : Nat}
    {columnCommitments : Fin numColumns -> G}
    (cols : AlgebraicColumnRepresentations urs columnCommitments)
    (aggregate : Fin (2 ^ urs.k) -> Fp) (aggregateU aggregateW challenge : Fp) where
  batch : AlgebraicPowerBatch urs columnCommitments aggregate aggregateU aggregateW challenge
  coeffs_eq : batch.coeffs = cols.coeffs
  uComp_eq : batch.uComp = cols.uComp
  wComp_eq : batch.wComp = cols.wComp

/-- Provenance-preserving algebraic unbatching.  Equality gives both the batch witnesses and a
proof that their columns are the supplied online coordinates; inequality gives an explicit
augmented-basis relation. -/
def algebraicPowerBatchWithSourceOrRelation {urs : URS G} {numColumns : Nat}
    {columnCommitments : Fin numColumns -> G}
    (cols : AlgebraicColumnRepresentations urs columnCommitments)
    (aggregate : Fin (2 ^ urs.k) -> Fp) (aggregateU aggregateW challenge : Fp)
    (haggregate : commit urs aggregate + aggregateU • urs.u + aggregateW • urs.w =
      ∑ i : Fin numColumns, challenge ^ (i : Nat) • columnCommitments i) :
    AlgebraicPowerBatchWithSource urs cols aggregate aggregateU aggregateW challenge ⊕'
      AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w := by
  let powerCoeffs := ∑ i : Fin numColumns, challenge ^ (i : Nat) • cols.coeffs i
  let powerU := ∑ i : Fin numColumns, challenge ^ (i : Nat) * cols.uComp i
  let powerW := ∑ i : Fin numColumns, challenge ^ (i : Nat) * cols.wComp i
  have hpower : commit urs powerCoeffs + powerU • urs.u + powerW • urs.w =
      ∑ i : Fin numColumns, challenge ^ (i : Nat) • columnCommitments i :=
    cols.power_commitment challenge
  have hcollision :
      commitGen urs.g aggregate + aggregateU • urs.u + aggregateW • urs.w =
        commitGen urs.g powerCoeffs + powerU • urs.u + powerW • urs.w := by
    rw [<- commit_eq_commitGen, <- commit_eq_commitGen, haggregate, hpower]
  match separateOrRelationWitness urs.g urs.u urs.w aggregate powerCoeffs
      aggregateU powerU aggregateW powerW hcollision with
  | PSum.inl heq =>
      exact PSum.inl
        { batch :=
            { coeffs := cols.coeffs
              uComp := cols.uComp
              wComp := cols.wComp
              commitment := cols.commitment
              reconstruct := heq.1
              reconstructU := heq.2.1
              reconstructW := heq.2.2 }
          coeffs_eq := rfl
          uComp_eq := rfl
          wComp_eq := rfl }
  | PSum.inr hrel => exact PSum.inr hrel

/-- Compatibility projection for callers that only need the reconstructed batch. -/
def algebraicPowerBatchOrRelation {urs : URS G} {numColumns : Nat}
    {columnCommitments : Fin numColumns -> G}
    (cols : AlgebraicColumnRepresentations urs columnCommitments)
    (aggregate : Fin (2 ^ urs.k) -> Fp) (aggregateU aggregateW challenge : Fp)
    (haggregate : commit urs aggregate + aggregateU • urs.u + aggregateW • urs.w =
      ∑ i : Fin numColumns, challenge ^ (i : Nat) • columnCommitments i) :
    AlgebraicPowerBatch urs columnCommitments aggregate aggregateU aggregateW challenge ⊕'
      AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w :=
  match algebraicPowerBatchWithSourceOrRelation cols aggregate aggregateU aggregateW challenge
      haggregate with
  | PSum.inl result => PSum.inl result.batch
  | PSum.inr relation => PSum.inr relation

/-- The value-error polynomial of represented columns against the verifier's claimed column
values.  Its coefficient at `i` is exactly
`<coeffs i,b> - columnEvals i`. -/
noncomputable def algebraicBatchErrorPolynomial {urs : URS G} {numColumns : Nat}
    (b : Fin (2 ^ urs.k) -> Fp)
    (cols : Fin numColumns -> (Fin (2 ^ urs.k) -> Fp))
    (columnEvals : Fin numColumns -> Fp) : Polynomial Fp :=
  ∑ i : Fin numColumns,
    Polynomial.C (commitGen b (cols i) - columnEvals i) * Polynomial.X ^ (i : Nat)

omit [AddCommGroup G] [Module Fp G] in
/-- Evaluating the error polynomial is the difference between the power-batched represented
evaluations and the power-batched claimed values. -/
theorem algebraicBatchErrorPolynomial_eval {urs : URS G} {numColumns : Nat}
    (b : Fin (2 ^ urs.k) -> Fp)
    (cols : Fin numColumns -> (Fin (2 ^ urs.k) -> Fp))
    (columnEvals : Fin numColumns -> Fp) (x : Fp) :
    (algebraicBatchErrorPolynomial b cols columnEvals).eval x =
      commitGen b (∑ i : Fin numColumns, x ^ (i : Nat) • cols i) -
        ∑ i : Fin numColumns, x ^ (i : Nat) * columnEvals i := by
  rw [algebraicBatchErrorPolynomial, Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  rw [commitGen_sum]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [commitGen_smul_left, smul_eq_mul]
  ring

omit [AddCommGroup G] [Module Fp G] in
/-- The error polynomial has degree below the number of batch columns.  The deliberately loose
`<= numColumns` form also covers the empty batch without a side condition. -/
theorem algebraicBatchErrorPolynomial_natDegree_le {urs : URS G} {numColumns : Nat}
    (b : Fin (2 ^ urs.k) -> Fp)
    (cols : Fin numColumns -> (Fin (2 ^ urs.k) -> Fp))
    (columnEvals : Fin numColumns -> Fp) :
    (algebraicBatchErrorPolynomial b cols columnEvals).natDegree <= numColumns := by
  rw [algebraicBatchErrorPolynomial, Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro m hm
  rw [Polynomial.finsetSum_coeff]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega), mul_zero]

omit [AddCommGroup G] [Module Fp G] in
/-- If the error polynomial is identically zero, every represented column opens to its claimed
value. -/
theorem algebraicBatch_values_of_errorPolynomial_eq_zero {urs : URS G} {numColumns : Nat}
    (b : Fin (2 ^ urs.k) -> Fp)
    (cols : Fin numColumns -> (Fin (2 ^ urs.k) -> Fp))
    (columnEvals : Fin numColumns -> Fp)
    (hzero : algebraicBatchErrorPolynomial b cols columnEvals = 0) :
    forall i, commitGen b (cols i) = columnEvals i := by
  intro i
  have hcoeff : (algebraicBatchErrorPolynomial b cols columnEvals).coeff (i : Nat) = 0 := by
    rw [hzero, Polynomial.coeff_zero]
  rw [algebraicBatchErrorPolynomial, Polynomial.finsetSum_coeff,
    Finset.sum_eq_single i] at hcoeff
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one] at hcoeff
    exact sub_eq_zero.mp hcoeff
  · intro j _ hji
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      if_neg (fun h => hji (Fin.ext h.symm)), mul_zero]
  · intro hni
    exact absurd (Finset.mem_univ i) hni

/-- A correct aggregate opening makes the current batching challenge a root of the error
polynomial. -/
theorem AlgebraicPowerBatch.errorPolynomial_eval_eq_zero {urs : URS G} {numColumns : Nat}
    {columnCommitments : Fin numColumns -> G}
    {aggregate : Fin (2 ^ urs.k) -> Fp} {aggregateU aggregateW challenge : Fp}
    (batch : AlgebraicPowerBatch urs columnCommitments aggregate aggregateU aggregateW challenge)
    (b : Fin (2 ^ urs.k) -> Fp) (columnEvals : Fin numColumns -> Fp)
    (haggregate : commitGen b aggregate =
      ∑ i : Fin numColumns, challenge ^ (i : Nat) * columnEvals i) :
    (algebraicBatchErrorPolynomial b batch.coeffs columnEvals).eval challenge = 0 := by
  rw [algebraicBatchErrorPolynomial_eval, <- batch.reconstruct, haggregate, sub_self]

/-- Outside the explicit root set, one correct aggregate opening yields all individual column
value equations.  This is the rewind-free replacement for Vandermonde extraction at one power
batch. -/
theorem AlgebraicPowerBatch.values_of_good_challenge {urs : URS G} {numColumns : Nat}
    {columnCommitments : Fin numColumns -> G}
    {aggregate : Fin (2 ^ urs.k) -> Fp} {aggregateU aggregateW challenge : Fp}
    (batch : AlgebraicPowerBatch urs columnCommitments aggregate aggregateU aggregateW challenge)
    (b : Fin (2 ^ urs.k) -> Fp) (columnEvals : Fin numColumns -> Fp)
    (haggregate : commitGen b aggregate =
      ∑ i : Fin numColumns, challenge ^ (i : Nat) * columnEvals i)
    (hgood : challenge ∉ szBadSet (algebraicBatchErrorPolynomial b batch.coeffs columnEvals)) :
    forall i, commitGen b (batch.coeffs i) = columnEvals i := by
  have heval := batch.errorPolynomial_eval_eq_zero b columnEvals haggregate
  have hzero : algebraicBatchErrorPolynomial b batch.coeffs columnEvals = 0 := by
    by_contra hne
    exact hgood (mem_szBadSet.mpr ⟨hne, heval⟩)
  exact algebraicBatch_values_of_errorPolynomial_eq_zero b batch.coeffs columnEvals hzero

omit [AddCommGroup G] [Module Fp G] in
/-- Uniform pricing of the rewind-free batch failure: at most one field element per polynomial
degree, hence at most `numColumns / |Fp|` using the generic degree bound above. -/
theorem algebraicBatch_badSet_measure_le {urs : URS G} {numColumns : Nat}
    (b : Fin (2 ^ urs.k) -> Fp)
    (cols : Fin numColumns -> (Fin (2 ^ urs.k) -> Fp))
    (columnEvals : Fin numColumns -> Fp) :
    uniformChallenge.toOuterMeasure
        (szBadSet (algebraicBatchErrorPolynomial b cols columnEvals)) <=
      (numColumns : ENNReal) / (Fintype.card Fp : ENNReal) := by
  exact le_trans (uniformChallenge_szBadSet _) <| ENNReal.div_le_div_right
    (by exact_mod_cast algebraicBatchErrorPolynomial_natDegree_le b cols columnEvals) _

end Zcash.Snark
