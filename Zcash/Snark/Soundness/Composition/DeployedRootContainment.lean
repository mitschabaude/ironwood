import Zcash.Snark.Soundness.AGM.DeployedPinnedRoots
import Zcash.Snark.Soundness.Composition.RootContainment

/-!
# Concrete containment for rewind-free deployed AGM decoding

This module closes the deterministic seam beneath the pinned root bound.  On a run with a
clean recursive-IPA opening, either an executable finder returns a relation, or avoiding the six
explicit root sets yields every deployed member value.  Thus failure of this concrete extraction
endpoint is contained in the root-family landing event; no accepting multiopen rewind is used.
-/

namespace Zcash.Snark

open Classical
open ComputedAlgebraicFSFamily
open ComputedDeployedRootFSFamily
open scoped ENNReal

local instance vestaInhabitedDeployedRootContainment : Inhabited VestaG := ⟨0⟩

variable {shape : Shape}

/-- The wrapped online output for one sampled basis and random-oracle table. -/
noncomputable abbrev deployedRootRunOutput (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) (coins : family.toFamily.Coins) :=
  (wrappedAdversary family.toFamily basis).run coins.1

/-- Data retained by a successful deployed root decode.  Keeping the batch witness and its
equality to the decoded batches is what lets the constraint layer reuse the exact online AGM
coordinates instead of choosing a fresh existential decode. -/
structure DeployedRootDecodeWitness (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) (coins : family.toFamily.Coins) where
  batchWitness : DeployedBatchWitness family.toFamily basis
    (deployedRootRunOutput family basis coins)
  outcome_eq : family.outcome basis coins.1 = PSum.inl batchWitness
  decoded : DeployedAlgebraicDecode (ursOfAugmentedBasis shape.k basis) rfl
    (family.vk basis) (family.instanceCommitment basis)
    (deployedRootRunOutput family basis coins).1.proof.1
    (wrappedPreIpaRecord (deployedRootRunOutput family basis coins))
    ((deployedRootRunOutput family basis coins).1.aMulti
      (wrappedPreIpaReads (deployedRootRunOutput family basis coins)))
    ((deployedRootRunOutput family basis coins).1.multiU
      (wrappedPreIpaReads (deployedRootRunOutput family basis coins)))
    ((deployedRootRunOutput family basis coins).1.multiBlind
      (wrappedPreIpaReads (deployedRootRunOutput family basis coins)))
  batches_eq : decoded.batches = batchWitness.batches

/-- Retained root-decode provenance is unique.  Its batch data is pinned by `family.outcome`; the
remaining decode fields are proofs about those same batches.  Thus the later proof-only use of
`Classical.choice` cannot choose different relation coefficients. -/
theorem DeployedRootDecodeWitness.unique
    (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) (coins : family.toFamily.Coins)
    (a b : DeployedRootDecodeWitness family basis coins) : a = b := by
  have hw : a.batchWitness = b.batchWitness := by
    exact PSum.inl.inj (a.outcome_eq.symm.trans b.outcome_eq)
  cases a with
  | mk aBatch aOutcome aDecoded aBatchesEq =>
      cases b with
      | mk bBatch bOutcome bDecoded bBatchesEq =>
          dsimp only at hw
          subst bBatch
          have hd : aDecoded = bDecoded := by
            cases aDecoded with
            | mk aBatches aX4 aMembers =>
                cases bDecoded with
                | mk bBatches bX4 bMembers =>
                    have hbatches : aBatches = bBatches :=
                      aBatchesEq.trans bBatchesEq.symm
                    cases hbatches
                    rfl
          subst bDecoded
          rfl

instance deployedRootDecodeWitnessSubsingleton
    (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) (coins : family.toFamily.Coins) :
    Subsingleton (DeployedRootDecodeWitness family basis coins) :=
  ⟨DeployedRootDecodeWitness.unique family basis coins⟩

/-- All deployed member-polynomial values decoded from the AGM coordinates at the run's own
record. -/
def deployedRootDecoded (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (coins : family.toFamily.Coins) : Prop :=
  Nonempty (DeployedRootDecodeWitness family basis coins)

/-- The concrete output delivered by the rewind-free multiopen layer: either the complete computed
relation finder returns a witness, or all deployed member-polynomial values are decoded.  This is
deliberately phrased as computed data rather than an ∃-closed relation, which a prime-order group
satisfies unconditionally. -/
def deployedRootExtracted (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (coins : family.toFamily.Coins) : Prop :=
  (family.deployedRelationFinder basis coins).isSome ∨
    deployedRootDecoded family basis coins

/-- A clean accepting run that does not deliver the concrete AGM decode must hit one of the six
explicit, squeeze-pinned root sets. -/
theorem deployedRootFailure_subset_landing
    (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) :
    {coins : family.toFamily.Coins |
        fsWinsFull (family.adversary basis)
          (fullAlgebraicAcceptDeployed basis (family.vk basis)
            (family.instanceCommitment basis))
          (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) coins.1 ∧
        family.hasCleanOpening basis coins ∧ ¬ deployedRootExtracted family basis coins} <=
      {coins : family.toFamily.Coins | (family.pinnedRoots basis).Landing coins.1} := by
  intro coins hfailure
  rcases hfailure with ⟨_hwin, hclean, hnex⟩
  let O := coins.1
  let pnu := (wrappedAdversary family.toFamily basis).run O
  cases hout : family.outcome basis O with
  | inr relation =>
      exfalso
      apply hnex
      apply Or.inl
      simp only [ComputedDeployedRootFSFamily.deployedRelationFinder]
      cases hfinder : family.toFamily.relationFinder basis coins with
      | some relation => simp
      | none => simp [O, hout]
  | inl witness =>
      by_contra hlanding
      have hgood := family.goodRoots_of_not_landing basis O witness hout hlanding
      obtain ⟨cert, hz, hvalid, houtInstance, opening, hrun⟩ :=
        cleanOpening_provenance_run family.toFamily basis coins hclean
      let nu := wrappedPreIpaReads pnu
      let ch := wrappedPreIpaRecord pnu
      by_cases hae : opening.1 = pnu.1.aMulti nu
      · have hz' : ch.z ≠ 0 := by
          simpa [pnu, nu, ch, wrappedPreIpaRecord, wrappedPreIpaReads_run,
            wrappedRecord_run, runRecord] using hz
        have hshifted : commitGen (evalVector shape.k ch.x3) (pnu.1.aMulti nu) =
            multiopenValue (family.vk basis) (family.instanceCommitment basis)
              pnu.1.proof.1 ch +
              ch.z⁻¹ * (pnu.1.multiU nu + ch.xi * pnu.1.sU) -
                ch.xi * commitGen (evalVector shape.k ch.x3) pnu.1.s := by
          rw [<- hae]
          simpa [pnu, nu, ch, wrappedPreIpaRecord, wrappedAdversary_run_fst,
            wrappedPreIpaReads_run, wrappedRecord_run, runRecord, commitGen, innerProduct] using
              opening.2.2
        have hgoodXi : ch.xi ∉ szBadSet
            (ipaShiftXiPolynomial
              (commitGen (evalVector shape.k ch.x3) (pnu.1.aMulti nu) -
                multiopenValue (family.vk basis) (family.instanceCommitment basis)
                  pnu.1.proof.1 ch)
              (commitGen (evalVector shape.k ch.x3) pnu.1.s)) := by
          simpa [deployedRootBad, hout, pnu, nu, ch, wrappedPreIpaRecord] using hgood.xi
        have hgoodZ : ch.z ∉ szBadSet
            (ipaShiftZPolynomial
              (commitGen (evalVector shape.k ch.x3) (pnu.1.aMulti nu) -
                multiopenValue (family.vk basis) (family.instanceCommitment basis)
                  pnu.1.proof.1 ch)
              (pnu.1.multiU nu) pnu.1.sU
              (commitGen (evalVector shape.k ch.x3) pnu.1.s) ch.xi) := by
          simpa [deployedRootBad, hout, pnu, nu, ch, wrappedPreIpaRecord] using hgood.z
        have hvalue : commitGen (evalVector shape.k ch.x3) (pnu.1.aMulti nu) =
            multiopenValue (family.vk basis) (family.instanceCommitment basis)
              pnu.1.proof.1 ch :=
          rawValue_of_shiftedValue_of_good _ _ _ _ _ _ _ hz' hshifted hgoodXi hgoodZ
        have hgood4 : ch.x4 ∉ deployedX4RootSet
            (ursOfAugmentedBasis shape.k basis) rfl (family.vk basis)
              (family.instanceCommitment basis) pnu.1.proof.1 ch
              witness.batches := by
          simpa [deployedRootBad, hout, pnu, nu, ch, wrappedPreIpaRecord] using hgood.x4
        have hgood3 : ch.x3 ∉ deployedX3RootSet
            (ursOfAugmentedBasis shape.k basis) rfl (family.vk basis)
              (family.instanceCommitment basis) pnu.1.proof.1 ch
              witness.batches := by
          simpa [deployedRootBad, hout, pnu, nu, ch, wrappedPreIpaRecord] using hgood.x3
        have hgood2 : ch.x2 ∉ deployedX2RootSet
            (ursOfAugmentedBasis shape.k basis) rfl (family.vk basis)
              (family.instanceCommitment basis) pnu.1.proof.1 ch
              witness.batches := by
          simpa [deployedRootBad, hout, pnu, nu, ch, wrappedPreIpaRecord] using hgood.x2
        have hgood1All : ch.x1 ∉ deployedX1AllRootSet
            (ursOfAugmentedBasis shape.k basis) rfl (family.vk basis)
              (family.instanceCommitment basis) pnu.1.proof.1 ch
              witness.batches := by
          simpa [deployedRootBad, hout, pnu, nu, ch, wrappedPreIpaRecord] using hgood.x1
        have hgood1 := not_mem_deployedX1RootSet_of_not_mem_all
          (ursOfAugmentedBasis shape.k basis) rfl (family.vk basis)
            (family.instanceCommitment basis) pnu.1.proof.1 ch
            witness.batches hgood1All
        let decoded := deployedAlgebraicDecode_of_good_roots
          (ursOfAugmentedBasis shape.k basis) rfl (family.vk basis)
            (family.instanceCommitment basis) pnu.1.proof.1 ch
          witness.batches hvalue hgood4 hgood3 hgood2 hgood1
        exfalso
        apply hnex
        apply Or.inr
        refine ⟨{
          batchWitness := witness
          outcome_eq := by simpa [O] using hout
          decoded := decoded
          batches_eq := rfl }⟩
      · exfalso
        apply hnex
        apply Or.inl
        simp only [ComputedDeployedRootFSFamily.deployedRelationFinder]
        have hbase : (family.toFamily.relationFinder basis coins).isSome := by
          have hae' : opening.1 ≠
              (deployedAlgebraicInstanceOfCert (runProof family.toFamily basis coins.1)
                (runReads family.toFamily basis coins.1) cert hz hvalid).aMulti := by
            simpa [pnu, nu, deployedAlgebraicInstanceOfCert, wrappedAdversary_run_fst,
              wrappedPreIpaReads_run, runProof, runReads] using hae
          simp only [ComputedAlgebraicFSFamily.relationFinder, houtInstance,
            DeployedAlgebraicForkingInstance.runRelation,
            DeployedAlgebraicForkingInstance.relationOfRun, hrun, dif_neg hae',
            Option.isSome_some]
        cases hfinder : family.toFamily.relationFinder basis coins with
        | none => exact absurd hfinder (Option.ne_none_iff_isSome.mpr hbase)
        | some relation => simp

/-- The recursive extractor's non-relation failures, indexed by the sampled augmented basis. -/
def deployedNonRelationFailureEvent (family : ComputedDeployedRootFSFamily shape) :
    Set ((AugmentedIndex (2 ^ shape.k) -> VestaG) × family.toFamily.Coins) :=
  {q | q.2 ∈ family.toFamily.snarkNonRelationFailure q.1}

/-- Deployed acceptance without a decoded AGM opening has exactly three causes: recursive
extraction failure, an explicitly returned relation, or a clean run that lands in a pinned root
set.  In particular, no bare existential relation proposition appears in this containment. -/
theorem deployedDecodeFailure_subset_union
    (family : ComputedDeployedRootFSFamily shape) :
    snarkExtractionFailureEventDeployed family.toFamily (deployedRootDecoded family) <=
      deployedNonRelationFailureEvent family ∪
        (family.deployedRelationEvent ∪
          cleanButNotExtractedDeployed family.toFamily (deployedRootExtracted family)) := by
  rintro ⟨basis, coins⟩ ⟨haccept, hnotDecoded⟩
  by_cases hrelation : (family.deployedRelationFinder basis coins).isSome
  · exact Or.inr (Or.inl hrelation)
  by_cases hclean : family.toFamily.hasCleanOpening basis coins
  · exact Or.inr (Or.inr ⟨haccept, hclean, fun hextracted => by
      rcases hextracted with hfound | hdecoded
      · exact hrelation hfound
      · exact hnotDecoded hdecoded⟩)
  have hplain : fsWinsFull (family.adversary basis)
      (fullAlgebraicAccept basis (family.vk basis) (family.instanceCommitment basis))
      (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) coins.1 := by
    exact fullAlgebraicAccept_of_deployed basis (family.vk basis)
      (family.instanceCommitment basis) ((family.adversary basis).run coins.1) _ _ haccept
  by_cases hz : coins.1 (algebraicFullPrefixesPre family.init
      ((family.adversary basis).run coins.1) 10) = 0
  · apply Or.inl
    change coins ∈ family.toFamily.snarkNonRelationFailure basis
    exact Or.inr ⟨hplain, hz⟩
  by_cases hsome : (family.toFamily.instanceAttempt basis coins).output.isSome
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hsome
    cases hrun : x.run with
    | inl opening => exact absurd ⟨x, hx, opening, hrun⟩ hclean
    | inr relation =>
        exfalso
        apply hrelation
        simp only [ComputedDeployedRootFSFamily.deployedRelationFinder,
          ComputedAlgebraicFSFamily.relationFinder, hx,
          DeployedAlgebraicForkingInstance.runRelation,
          DeployedAlgebraicForkingInstance.relationOfRun, hrun, Option.isSome_some]
  · apply Or.inl
    change coins ∈ family.toFamily.snarkNonRelationFailure basis
    apply Or.inl
    refine ⟨?_, hsome⟩
    unfold fsWinsFull at hplain ⊢
    exact ⟨hplain, hz⟩

/-- The recursive, non-relation part of the failure probability is uniform for every sampled
generator-oracle basis. -/
theorem deployedNonRelationFailure_prob_le_of_generatorRO
    {T' : Type*} [DecidableEq T']
    (query : AugmentedIndex (2 ^ shape.k) -> T')
    (family : ComputedDeployedRootFSFamily shape) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          deployedNonRelationFailureEvent family)
      <= (family.Q + shape.k) * (3 / Fintype.card Fp) +
        (family.Q + 1 : Nat) * (1 / Fintype.card Fp) := by
  change (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure
      {p | p.2 ∈ family.toFamily.snarkNonRelationFailure
        (orchardGeneratorROBasis query p.1)}
    <= (family.Q + shape.k) * (3 / Fintype.card Fp) +
      (family.Q + 1 : Nat) * (1 / Fintype.card Fp)
  refine independentProductPMF_fiber_bound (orchardGeneratorROSetup query)
    (PMF.uniformOfFintype family.toFamily.Coins)
    (fun setup => family.toFamily.snarkNonRelationFailure
      (orchardGeneratorROBasis query setup)) ?_
  intro setup
  exact family.toFamily.snarkNonRelationFailure_measure_le
    (orchardGeneratorROBasis query setup)

/-- The DLOG-based deployed capstone for the concrete rewind-free decode endpoint.

All explicit relations returned by either the recursive extractor or algebraic multiopen
unbatching are charged to the same single-instance textbook-DLOG assumption, whose reduction
loses only an additive `1/|Fp|`. -/
theorem snarkExtractionDeployed_prob_le_via_deployed_roots
    {T' : Type*} [DecidableEq T']
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ shape.k) -> T') (hquery : Function.Injective query)
    (family : ComputedDeployedRootFSFamily shape) {bound : ENNReal}
    (hDL : TextbookDLWithCoinsAdvantageLE B family.deployedRelationFinder bound) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          snarkExtractionFailureEventDeployed family.toFamily
            (deployedRootDecoded family))
      <= ((family.Q + shape.k) * (3 / Fintype.card Fp) +
          (family.Q + 1 : Nat) * (1 / Fintype.card Fp) +
          (bound + 1 / Fintype.card Fp))
        + (family.Q + (11 + shape.k) + 1 : Nat) * algebraicRootBudget shape shape.k := by
  let setup := orchardGeneratorROSetup query
  let coinPMF := PMF.uniformOfFintype family.toFamily.Coins
  let basisOf := orchardGeneratorROBasis query
  let nonRelationBound : ENNReal :=
    (family.Q + shape.k) * (3 / Fintype.card Fp) +
      (family.Q + 1 : Nat) * (1 / Fintype.card Fp)
  let relationBound : ENNReal :=
    (bound + 1 / Fintype.card Fp)
  let rootBound : ENNReal :=
    (family.Q + (11 + shape.k) + 1 : Nat) * algebraicRootBudget shape shape.k
  have hnonRelation :
      (independentProductPMF setup coinPMF).toOuterMeasure
          ((fun p => (basisOf p.1, p.2)) ⁻¹' deployedNonRelationFailureEvent family)
        <= nonRelationBound := by
    exact deployedNonRelationFailure_prob_le_of_generatorRO query family
  have hrelation :
      (independentProductPMF setup coinPMF).toOuterMeasure
          ((fun p => (basisOf p.1, p.2)) ⁻¹' family.deployedRelationEvent)
        <= relationBound := by
    exact family.deployedRelation_prob_le_of_generatorRO_textbookDL
      B hB query hquery hDL
  have hroots :
      (independentProductPMF setup coinPMF).toOuterMeasure
          ((fun p => (basisOf p.1, p.2)) ⁻¹'
            cleanButNotExtractedDeployed family.toFamily (deployedRootExtracted family))
        <= rootBound := by
    exact residual_le_via_wrapped_deployed_pinned_roots query family.toFamily
      (deployedRootExtracted family) (family.pinnedRoots)
      (family.pinnedRoots_budget_le) (deployedRootFailure_subset_landing family)
  calc
    (independentProductPMF setup coinPMF).toOuterMeasure
        ((fun p => (basisOf p.1, p.2)) ⁻¹'
          snarkExtractionFailureEventDeployed family.toFamily (deployedRootDecoded family))
      <= (independentProductPMF setup coinPMF).toOuterMeasure
          ((fun p => (basisOf p.1, p.2)) ⁻¹'
            (deployedNonRelationFailureEvent family ∪
              (family.deployedRelationEvent ∪
                cleanButNotExtractedDeployed family.toFamily
                  (deployedRootExtracted family)))) :=
        MeasureTheory.measure_mono
          (Set.preimage_mono (deployedDecodeFailure_subset_union family))
    _ = (independentProductPMF setup coinPMF).toOuterMeasure
          (((fun p => (basisOf p.1, p.2)) ⁻¹'
              deployedNonRelationFailureEvent family) ∪
            (((fun p => (basisOf p.1, p.2)) ⁻¹' family.deployedRelationEvent) ∪
              ((fun p => (basisOf p.1, p.2)) ⁻¹'
                cleanButNotExtractedDeployed family.toFamily
                  (deployedRootExtracted family)))) := by
        rw [Set.preimage_union, Set.preimage_union]
    _ <= (independentProductPMF setup coinPMF).toOuterMeasure
          ((fun p => (basisOf p.1, p.2)) ⁻¹' deployedNonRelationFailureEvent family) +
        (independentProductPMF setup coinPMF).toOuterMeasure
          ((((fun p => (basisOf p.1, p.2)) ⁻¹' family.deployedRelationEvent) ∪
            ((fun p => (basisOf p.1, p.2)) ⁻¹'
              cleanButNotExtractedDeployed family.toFamily
                (deployedRootExtracted family)))) :=
      MeasureTheory.measure_union_le _ _
    _ <= nonRelationBound +
        ((independentProductPMF setup coinPMF).toOuterMeasure
            ((fun p => (basisOf p.1, p.2)) ⁻¹' family.deployedRelationEvent) +
          (independentProductPMF setup coinPMF).toOuterMeasure
            ((fun p => (basisOf p.1, p.2)) ⁻¹'
              cleanButNotExtractedDeployed family.toFamily
                (deployedRootExtracted family))) :=
      add_le_add hnonRelation (MeasureTheory.measure_union_le _ _)
    _ <= nonRelationBound + (relationBound + rootBound) :=
      add_le_add le_rfl (add_le_add hrelation hroots)
    _ = ((family.Q + shape.k) * (3 / Fintype.card Fp) +
          (family.Q + 1 : Nat) * (1 / Fintype.card Fp) +
          (bound + 1 / Fintype.card Fp))
        + (family.Q + (11 + shape.k) + 1 : Nat) *
          algebraicRootBudget shape shape.k := by
      simp only [nonRelationBound, relationBound, rootBound]
      ac_rfl

end Zcash.Snark
