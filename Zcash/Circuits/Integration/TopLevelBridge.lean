import Zcash.Circuits.Integration.TopLevelLookups
import Zcash.Common.RelationWitness
import Zcash.Circuits.Integration.TopLevelCircuit

/-!
# Circuit-derived full bridge assembly

This module is the generic join between the circuit-derived gate and lookup
adapters and Ironwood's `FullCircuitBridge`. It keeps the verifier and soundness
layers in their native polynomial language: Clean-specific reconstruction is
finished here before the resulting bridge is handed to the semantic endpoint.
-/

namespace Zcash.Snark

open Halo2 Polynomial

set_option maxHeartbeats 20000

namespace FullCircuitBridge

variable
    {G : Type} [AddCommGroup G] [Inhabited G]
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    {top : TopLevelCircuit Fp Config PublicInput}
    {pp : Keygen.ProofParams} {urs : URS G}
    {cell : Type} [DecidableEq cell] [Fintype cell]
    {Bad : Type}

/--
Assemble the complete operation bridge from the canonical circuit-derived
constraint model.

Gate and lookup witnesses are derived here from `TopLevelCircuit`; callers supply
only the representation boundaries that genuinely come from other streams:

* packed selector activation and exact lookup-selector values from fixed keygen
  rows;
* the complete fixed/table family from those same rows;
* copy replay from keygen's cell permutation;
* one bundle-wide record of lookup challenge exclusions.
-/
noncomputable def ofTopLevelCanonical
    (gateCoherence : TopLevelGateCoherence top pp urs)
    (ch : Challenges (pp.mergeDerived top).k Fp)
    (poly : CommitmentId → Polynomial Fp)
    (proofIndex : Fin (pp.mergeDerived top).numProofs)
    (hblinding :
      (top.toVerifierKey pp urs).blindingFactors <
        (top.toVerifierKey pp urs).n)
    (satisfaction :
      ConstraintSatisfaction
        (canonicalConstraintModelOfPermutationResolver
          (top.toVerifierKey pp urs) ch poly hblinding)
        (top.toVerifierKey pp urs).n)
    (hrows : Function.Injective
      fun row : Fin (top.toVerifierKey pp urs).n =>
        (top.toVerifierKey pp urs).omega ^ (row : ℕ))
    (hroot :
      (top.toVerifierKey pp urs).omega ^
        (top.toVerifierKey pp urs).n = 1)
    (selectorActivations :
      SelectorActivationsRealized top.selectorMap
        top.selectorActivations
        (resolverEnvironment
          (top.toVerifierKey pp urs) poly proofIndex
          (top.usableRowsAt top.domainExponent)))
    (fixed :
      CircuitConstraintFamily.constraints .fixed top.placement
        (resolverEnvironment
          (top.toVerifierKey pp urs) poly proofIndex
          (top.usableRowsAt top.domainExponent))
        (top.operations) 0)
    (copies :
      CopyReplayWitness top.placement
        (resolverEnvironment
          (top.toVerifierKey pp urs) poly proofIndex
          (top.usableRowsAt top.domainExponent))
        (top.operations) cell Bad)
    (lookupConditions :
      TopLevelLookupCoherence.TopLevelLookupWitnessConditions
        top pp urs ch poly proofIndex) :
    FullCircuitBridge top.placement
      (resolverEnvironment
        (top.toVerifierKey pp urs) poly proofIndex
        (top.usableRowsAt top.domainExponent))
      (top.operations) 0 cell Bad := by
  let lookupCoherence : TopLevelLookupCoherence top :=
    TopLevelLookupCoherence.ofTopLevel
  refine
    { gates := ?_
      fixed := fixed
      copies := copies
      theta := ch.theta
      lookups := ?_ }
  · apply gateCoherence.canonicalConstraints ch poly hblinding proofIndex
      satisfaction
    · intro row
      rw [← pow_mul, Nat.mul_comm, pow_mul, hroot, one_pow]
    · exact selectorActivations
  · exact lookupCoherence.deployedWitnesses gateCoherence ch poly proofIndex
      hblinding satisfaction hrows hroot lookupConditions

/--
Lift per-proof full bridges to a bundle of circuit-owned statements while
preserving one shared exceptional event.

This is the generic finite-family join used by the Action adapter: the proof does
not inspect the circuit statement and does not introduce an `hencodes` predicate.
-/
def bundleTopLevelSoundness_or_bad
    (top : TopLevelCircuit Fp Config PublicInput)
    {numProofs : ℕ}
    (assignment : Fin numProofs → ProofAssignment Fp)
    (bridge : ∀ proofIndex,
      FullCircuitBridge
        top.placement
        (top.environment (assignment proofIndex))
        top.operations 0 cell Bad) :
    (∀ proofIndex,
      top.Statement
        (top.extractPublicInput (top.environment (assignment proofIndex)))) ⊕' Bad :=
  finForallOrRelationWitness fun proofIndex =>
    FullCircuitBridge.topLevelSoundness_or_bad
      top (assignment proofIndex) (bridge proofIndex)

end FullCircuitBridge

end Zcash.Snark
