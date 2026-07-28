import Zcash.Snark.Fixtures.MultiAction.StaticChecks
import Zcash.Snark.Fixtures.MultiAction.Schedule
import Zcash.Snark.Soundness.AGM.DirectConstraintFamily

/-!
# The deployed compressed-identity extraction bound at the captured key

`snarkConstraintsDeployed_prob_le_of_root_schedule` bounds extraction failure for the verifier's
compressed constraint identity by five additive terms. This module instantiates it at the captured
Post-NU6.3 key: the static checks and degree caps come from the verifying key (`StaticChecks`,
`Schedule`), so the bad-`x` term is the concrete `(Q + 1) · 20470 / |𝔽|` and the multiopen term is
the shape's own root budget. No continuation threshold and no fourth root.

Named inputs: single-instance DLOG for the combined finder (`hDL`), and the two staged pre-squeeze
traces exact pinning is derived from. The captured premise pins scalar metadata, layouts, and
expressions only — verifier commitments are AGM points carrying representations over each sampled
basis, so literal point equality is deliberately not required.
-/

namespace Zcash.Snark.Fixture2

open Zcash.Snark
open scoped ENNReal

/-- **The deployed compressed-identity extraction bound at the captured key.** The rewind-free
capstone with the captured key's static checks and degree caps discharged: extraction failure for
that identity is at most the challenge-pricing terms, the tight DLOG term, the additive root budget,
and the concrete `(Q + 1) · 20470 / |𝔽|` bad-`x` term. Row-level semantics require the four
additional budgets of `snarkConstraintsSemanticDeployed_prob_le_of_root_schedule`. -/
theorem orchard_deployed_knowledge_error_captured
    {T' : Type*} [DecidableEq T'] (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ shape.k) → T') (hquery : Function.Injective query)
    (family : ComputedDeployedConstraintFSFamily shape)
    (hvk : ∀ basis, CapturedVerifierKeyProfile (family.vk basis))
    {dlogBound : ENNReal}
    (hDL : TextbookDLWithCoinsAdvantageLE B
      (deployedConstraintRelationFinder family.toRootFamily
        (deployedConstraintQuotientFinder family.toRootFamily)) dlogBound) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.toRootFamily.toFamily.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          snarkExtractionFailureEventDeployed family.toRootFamily.toFamily
            (deployedConstraintDecodedOfRoot family.toRootFamily
              (deployedConstraintStaticChecks_of_captured family.toRootFamily hvk)))
      ≤ ((family.Q + shape.k) * (3 / Fintype.card Fp) +
          (family.Q + 1 : ℕ) * (1 / Fintype.card Fp) +
          (dlogBound + 1 / Fintype.card Fp))
        + (family.Q + (11 + shape.k) + 1 : ℕ) * algebraicRootBudget shape shape.k
        + (family.Q + 1 : ℕ) * ((20470 : ℕ) / (Fintype.card Fp : ℝ≥0∞)) :=
  snarkConstraintsDeployed_prob_le_of_root_schedule B hB query hquery family.toRootFamily
    (deployedConstraintStaticChecks_of_captured family.toRootFamily hvk)
    (deployedConstraintXSqueezeSchedule_captured family hvk) hDL

/-- **The captured compressed-identity bound on the interpolation-free route.** The same capstone,
with the deployed constraint family built by `ofCovered`: its outcome is decoded from online
coverage, so the statement rests on no field-capacity premise and no offline interpolation — only
single-instance DLOG for the combined finder and the two staged chronology traces. -/
theorem orchard_deployed_knowledge_error_captured_direct
    {T' : Type*} [DecidableEq T'] (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ shape.k) → T') (hquery : Function.Injective query)
    (online : ComputedOnlineMemberFSFamily shape)
    (rootTrace : DeployedRootOnlineTrace online.toFamily
      (deployedRootOutcomeOfCovered online))
    (xTrace : DeployedConstraintXOnlineTrace
      (ComputedDeployedRootFSFamily.ofCovered online rootTrace))
    (hvk : ∀ basis, CapturedVerifierKeyProfile
      ((ComputedDeployedConstraintFSFamily.ofCovered online rootTrace xTrace).vk basis))
    {dlogBound : ENNReal}
    (hDL : TextbookDLWithCoinsAdvantageLE B
      (deployedConstraintRelationFinder
        (ComputedDeployedConstraintFSFamily.ofCovered online rootTrace xTrace).toRootFamily
        (deployedConstraintQuotientFinder
          (ComputedDeployedConstraintFSFamily.ofCovered online rootTrace xTrace).toRootFamily))
      dlogBound) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (ComputedDeployedConstraintFSFamily.ofCovered online rootTrace xTrace).toFamily.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          snarkExtractionFailureEventDeployed
            (ComputedDeployedConstraintFSFamily.ofCovered online rootTrace xTrace).toFamily
            (deployedConstraintDecodedOfRoot _
              (deployedConstraintStaticChecks_of_captured _ hvk)))
      ≤ (((ComputedDeployedConstraintFSFamily.ofCovered online rootTrace xTrace).Q + shape.k) *
            (3 / Fintype.card Fp) +
          ((ComputedDeployedConstraintFSFamily.ofCovered online rootTrace xTrace).Q + 1 : ℕ) *
            (1 / Fintype.card Fp) +
          (dlogBound + 1 / Fintype.card Fp))
        + ((ComputedDeployedConstraintFSFamily.ofCovered online rootTrace xTrace).Q +
            (11 + shape.k) + 1 : ℕ) *
            algebraicRootBudget shape shape.k
        + ((ComputedDeployedConstraintFSFamily.ofCovered online rootTrace xTrace).Q + 1 : ℕ) *
            ((20470 : ℕ) / (Fintype.card Fp : ℝ≥0∞)) :=
  orchard_deployed_knowledge_error_captured B hB query hquery
    (ComputedDeployedConstraintFSFamily.ofCovered online rootTrace xTrace) hvk hDL

end Zcash.Snark.Fixture2
