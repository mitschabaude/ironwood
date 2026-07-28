import Zcash.Snark.Soundness.Composition.DeployedRuntime
import Zcash.Snark.Soundness.Forking.PinnedRoots

/-!
# Deployed capstone through pinned root events

This module replaces the four-level joint-event coupling with a finite union of explicit bad-root
events.  Each event is fixed before its own squeeze and carries its direct root-set budget, so the
multiopen residual is linear in the sum of those budgets and has no fourth root.
-/

namespace Zcash.Snark

open scoped ENNReal
open Classical
open ComputedAlgebraicFSFamily

variable {shape : Shape}

/-- The deployed residual through a concrete family of pinned root events. -/
theorem residual_le_via_wrapped_deployed_pinned_roots
    {T' : Type*} [DecidableEq T']
    (query : AugmentedIndex (2 ^ shape.k) -> T')
    (family : ComputedAlgebraicFSFamily shape)
    (extracted : (AugmentedIndex (2 ^ shape.k) -> VestaG) -> family.Coins -> Prop)
    {n : Nat}
    (roots : forall basis, PinnedRootFamily (wrappedAdversary family basis) n)
    {s : ENNReal}
    (hbudget : forall basis,
      (∑ i : Fin n, ((roots basis).event i).budget) <= s)
    (hcont : forall basis, {coins : family.Coins |
        fsWinsFull (family.adversary basis)
          (fullAlgebraicAcceptDeployed basis (family.vk basis)
            (family.instanceCommitment basis))
          (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) coins.1 /\
        family.hasCleanOpening basis coins /\ ¬ extracted basis coins} <=
      {coins : family.Coins | (roots basis).Landing coins.1}) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          cleanButNotExtractedDeployed family extracted)
      <= (family.Q + (11 + shape.k) + 1 : Nat) * s := by
  have hset : (fun p : (↥(Set.range query) -> VestaG) × family.Coins =>
        (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
        cleanButNotExtractedDeployed family extracted
      = {x : (↥(Set.range query) -> VestaG) × family.Coins | x.2 ∈
          (fun setup => {coins : family.Coins |
            fsWinsFull (family.adversary (orchardGeneratorROBasis query setup))
              (fullAlgebraicAcceptDeployed (orchardGeneratorROBasis query setup)
                (family.vk (orchardGeneratorROBasis query setup))
                (family.instanceCommitment (orchardGeneratorROBasis query setup)))
              (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init)
              coins.1 /\
            family.hasCleanOpening (orchardGeneratorROBasis query setup) coins /\
            ¬ extracted (orchardGeneratorROBasis query setup) coins}) x.1} := by
    ext p
    simp only [Set.mem_preimage, cleanButNotExtractedDeployed, Set.mem_setOf_eq]
  rw [hset]
  refine independentProductPMF_fiber_bound (orchardGeneratorROSetup query)
    (PMF.uniformOfFintype family.Coins)
    (fun setup => {coins : family.Coins |
      fsWinsFull (family.adversary (orchardGeneratorROBasis query setup))
        (fullAlgebraicAcceptDeployed (orchardGeneratorROBasis query setup)
          (family.vk (orchardGeneratorROBasis query setup))
          (family.instanceCommitment (orchardGeneratorROBasis query setup)))
        (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) coins.1 /\
      family.hasCleanOpening (orchardGeneratorROBasis query setup) coins /\
      ¬ extracted (orchardGeneratorROBasis query setup) coins}) ?_
  intro setup
  let basis := orchardGeneratorROBasis query setup
  refine le_trans (MeasureTheory.measure_mono (hcont basis)) ?_
  refine uniformOfFintype_prod_fiber_bound
    (fun _ : RecursiveForkTape Fp shape.k =>
      {O | (roots basis).Landing O})
    (fun _ => ?_)
  refine le_trans ((roots basis).landing_measure_le
    (queryBound_wrappedAdversary family basis)) ?_
  exact mul_le_mul_right (hbudget basis) _

/-- The DLOG-based deployed extraction bound with an additive pinned-root multiopen term. -/
theorem snarkExtractionDeployed_prob_le_via_wrapped_pinned_roots
    {T' : Type*} [DecidableEq T']
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ shape.k) -> T') (hquery : Function.Injective query)
    (family : ComputedAlgebraicFSFamily shape) {bound : ENNReal}
    (hDL : TextbookDLWithCoinsAdvantageLE B family.snarkRelationFinder bound)
    (extracted : (AugmentedIndex (2 ^ shape.k) -> VestaG) -> family.Coins -> Prop)
    {n : Nat}
    (roots : forall basis, PinnedRootFamily (wrappedAdversary family basis) n)
    {s : ENNReal}
    (hbudget : forall basis,
      (∑ i : Fin n, ((roots basis).event i).budget) <= s)
    (hcont : forall basis, {coins : family.Coins |
        fsWinsFull (family.adversary basis)
          (fullAlgebraicAcceptDeployed basis (family.vk basis)
            (family.instanceCommitment basis))
          (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) coins.1 /\
        family.hasCleanOpening basis coins /\ ¬ extracted basis coins} <=
      {coins : family.Coins | (roots basis).Landing coins.1}) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          snarkExtractionFailureEventDeployed family extracted)
      <= ((family.Q + shape.k) * (3 / Fintype.card Fp) +
          (family.Q + 1 : Nat) * (1 / Fintype.card Fp) +
          (bound + 1 / Fintype.card Fp))
        + (family.Q + (11 + shape.k) + 1 : Nat) * s := by
  refine le_trans (le_of_eq (congrArg
    (fun S => (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.Coins)).toOuterMeasure S)
    (congrArg _ rfl))) ?_
  refine le_trans ((independentProductPMF (orchardGeneratorROSetup query)
    (PMF.uniformOfFintype family.Coins)).toOuterMeasure.mono
      (Set.preimage_mono (snarkExtractionFailureEventDeployed_subset_union family
        extracted))) ?_
  refine le_trans (le_of_eq (congrArg
    (fun S => (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.Coins)).toOuterMeasure S) Set.preimage_union)) ?_
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  exact add_le_add
    (snarkFailure_prob_le_of_generatorRO_textbookDL B hB query hquery family hDL)
    (residual_le_via_wrapped_deployed_pinned_roots query family extracted roots
      hbudget hcont)

end Zcash.Snark
