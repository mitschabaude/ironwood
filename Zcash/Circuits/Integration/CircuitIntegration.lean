import Zcash.Circuits.Integration.OperationCopies
import Zcash.Common.RelationWitness
import Zcash.Circuits.Integration.OperationLookups
import Zcash.Circuits.Integration.OperationGates
import Zcash.Circuits.Integration.OperationFixed

/-!
# Reassembling full circuit satisfaction

The copy and lookup adapters deliberately expose small representation-boundary records.  This file
joins them to the gate and fixed/table families and returns the exact
`FullCircuitSatisfaction`/`Halo2.Constraints` endpoint.
-/

namespace Zcash.Snark

open Halo2

set_option maxHeartbeats 20000

/-- Representation data connecting the extracted Clean copies to the finite cell permutation
replayed by key generation. -/
structure CopyReplayWitness
    (place : RegionIndex → ℕ) (env : Environment Fp)
    (ops : Operations Fp) (cell : Type) [DecidableEq cell] [Fintype cell]
    (Bad : Type) where
  encode : CopyEndpoint Fp → cell
  value : cell → Fp
  read : ∀ copy ∈ operationDeclaredCopies ops,
    copy.1.eval place env = value (encode copy.1) ∧
      copy.2.eval place env = value (encode copy.2)
  cycle : ∀ {left right : cell},
    (replayKeygenPermutation
      (encodeDeclaredCopies encode (operationDeclaredCopies ops))).SameCycle left right →
      value left = value right ⊕' Bad

/-- A structured replay witness supplies the complete copy family. -/
def CopyReplayWitness.constraints_or_bad
    {place : RegionIndex → ℕ} {env : Environment Fp}
    {ops : Operations Fp} {i : RegionIndex}
    {cell : Type} [DecidableEq cell] [Fintype cell] {Bad : Type}
    (witness : CopyReplayWitness place env ops cell Bad) :
    CircuitConstraintFamily.constraints .copy place env ops i ⊕' Bad :=
  copy_constraints_or_bad_of_replay
    place env ops i witness.encode witness.value witness.read Bad witness.cycle

/-- All generic data needed to turn the separated SNARK semantic endpoints into the authoritative
Clean circuit-satisfaction predicate.  Action-specific work is confined to constructing this
record: gate/fixed coherence, endpoint encoding, and one deployed witness per enabled lookup. -/
structure FullCircuitBridge
    (place : RegionIndex → ℕ) (env : Environment Fp)
    (ops : Operations Fp) (i : RegionIndex)
    (cell : Type) [DecidableEq cell] [Fintype cell]
    (Bad : Type) where
  gates : CircuitConstraintFamily.constraints .gate place env ops i
  fixed : CircuitConstraintFamily.constraints .fixed place env ops i
  copies : CopyReplayWitness place env ops cell Bad
  theta : Fp
  lookups : ∀ lookup ∈ operationEnabledLookups ops i,
    EnabledLookup.DeployedWitness place env theta lookup

/-- Construct the full bridge directly from the deployed gate split and the three
operation-family representation witnesses. -/
def FullCircuitBridge.ofPolynomialWitnesses
    {np n : ℕ} (model : ConstraintPolyModel np) (proofIndex : Fin np)
    (omega : Fp) (place : RegionIndex → ℕ) (env : Environment Fp)
    (ops : Operations Fp) (i : RegionIndex)
    (satisfaction : ConstraintSatisfaction model n)
    (domain : ∀ row : ℕ, (omega ^ row) ^ n = 1)
    {cell : Type} [DecidableEq cell] [Fintype cell]
    {Bad : Type}
    (copies : CopyReplayWitness place env ops cell Bad)
    (theta : Fp)
    (gates : ∀ enabled ∈ operationEnabledGates ops i,
      ∀ constraint ∈ enabled.gate.constraints,
        EnabledGate.PolynomialWitness
          model proofIndex omega place env enabled constraint)
    (lookups : ∀ lookup ∈ operationEnabledLookups ops i,
      EnabledLookup.DeployedWitness place env theta lookup)
    (fixed : ∀ requirement ∈ operationFixedRequirements ops i,
      requirement.Satisfied place env) :
    FullCircuitBridge place env ops i cell Bad where
  gates := gate_constraints_of_polynomial_witnesses
    model proofIndex omega place env ops i satisfaction domain gates
  fixed := fixed_constraints_of_requirements place env ops i fixed
  copies := copies
  theta := theta
  lookups := lookups

/-- Reassemble the four semantic families, preserving the copy bridge's shared exceptional event. -/
def FullCircuitBridge.satisfaction_or_bad
    {place : RegionIndex → ℕ} {env : Environment Fp}
    {ops : Operations Fp} {i : RegionIndex}
    {cell : Type} [DecidableEq cell] [Fintype cell]
    {Bad : Type}
    (bridge : FullCircuitBridge place env ops i cell Bad) :
    FullCircuitSatisfaction place env ops i ⊕' Bad :=
  FullCircuitSatisfaction.of_components_or_bad bridge.gates
    bridge.copies.constraints_or_bad
    (PSum.inl (lookup_constraints_of_deployed_witnesses
      place env ops i bridge.theta bridge.lookups))
    bridge.fixed

/-- The same bridge stated at Clean's single ground-truth predicate. -/
def FullCircuitBridge.constraints_or_bad
    {place : RegionIndex → ℕ} {env : Environment Fp}
    {ops : Operations Fp} {i : RegionIndex}
    {cell : Type} [DecidableEq cell] [Fintype cell]
    {Bad : Type}
    (bridge : FullCircuitBridge place env ops i cell Bad) :
    Halo2.Constraints place env ops i ⊕' Bad :=
  bindOrRelationWitness bridge.satisfaction_or_bad FullCircuitSatisfaction.constraints

end Zcash.Snark
