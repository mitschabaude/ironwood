import Clean.Halo2.TopLevel
import Zcash.Circuits.Integration.CircuitIntegration
import Zcash.Common.RelationWitness

/-!
# Generic SNARK-to-top-level-circuit endpoint

`FullCircuitBridge` reconstructs Clean's authoritative operation constraints from the
separated gate, copy, lookup, and fixed arguments.  A fitting `TopLevelCircuit`
closes its own environment contract.  This module composes those two generic
boundaries; no Action-specific circuit, placement, or statement appears here.
-/

namespace Zcash.Snark

open Halo2

set_option maxHeartbeats 20000

namespace FullCircuitSatisfaction

variable
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]

/-- Exact full operation satisfaction implies the circuit-owned semantic statement. -/
theorem topLevelSoundness
    (top : TopLevelCircuit Fp Config PublicInput)
    (assignment : ProofAssignment Fp)
    (hsatisfied :
      FullCircuitSatisfaction top.placement
        (top.environment assignment) top.operations 0) :
    top.Statement (top.extractPublicInput (top.environment assignment)) := by
  apply top.statement_soundness assignment
  exact FullCircuitSatisfaction.constraints hsatisfied

end FullCircuitSatisfaction

namespace FullCircuitBridge

variable
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    {cell : Type} [DecidableEq cell] [Fintype cell]
    {Bad : Type}

/--
The generic semantic last mile: reconstructed full constraints imply the top-level
circuit's own statement, preserving the bridge's shared exceptional event.
-/
def topLevelSoundness_or_bad
    (top : TopLevelCircuit Fp Config PublicInput)
    (assignment : ProofAssignment Fp)
    (bridge : FullCircuitBridge top.placement (top.environment assignment)
      top.operations 0 cell Bad) :
    top.Statement (top.extractPublicInput (top.environment assignment)) ⊕' Bad :=
  bindOrRelationWitness bridge.satisfaction_or_bad
    fun hsatisfied => hsatisfied.topLevelSoundness top assignment

end FullCircuitBridge

/-!
`TopLevelBridgeWitness` hides the exact environment and operation stream at the
dependent-type boundary. Their equalities to the circuit-derived values are
retained as properties, so downstream soundness composition never needs to
unfold circuit synthesis.
-/
variable
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]

structure TopLevelBridgeWitness
    (top : TopLevelCircuit Fp Config PublicInput)
    (assignment : ProofAssignment Fp)
    (cell : Type) [DecidableEq cell] [Fintype cell]
    (Bad : Type) where
  environment : Environment Fp
  operations : Operations Fp
  environment_eq : environment = top.environment assignment
  operations_eq : top.operations = operations
  bridge : FullCircuitBridge top.placement environment
    operations 0 cell Bad

namespace TopLevelBridgeWitness

variable
    {cell : Type} [DecidableEq cell] [Fintype cell]
    {Bad : Type}

def statement_or_bad
    {top : TopLevelCircuit Fp Config PublicInput}
    {assignment : ProofAssignment Fp}
    (witness : TopLevelBridgeWitness top assignment cell Bad) :
    top.Statement (top.extractPublicInput (top.environment assignment)) ⊕' Bad :=
  bindOrRelationWitness witness.bridge.satisfaction_or_bad fun hsatisfied =>
    FullCircuitSatisfaction.topLevelSoundness top assignment
      (by
        rw [witness.operations_eq]
        exact witness.environment_eq ▸ hsatisfied)

end TopLevelBridgeWitness

end Zcash.Snark
