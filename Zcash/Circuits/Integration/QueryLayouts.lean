import Zcash.Snark.Keygen.Pipeline
import Zcash.Circuits.Integration.ResolverQueryEnvironment

/-!
# Circuit-owned query-layout coverage

Configure-time query registration is append-only. This module transports a
registered fixed or instance query through synthesis closure and selector projection
into the circuit-derived verifying key.
-/

namespace Zcash.Snark

open Halo2

set_option maxHeartbeats 20000

namespace QueryLayouts

variable
    {G : Type} [AddCommGroup G] [Inhabited G]
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]

/-- A query present in the synthesis-closed top-level constraint system remains in
its derived verifying key's instance-query layout. -/
theorem instanceQueryLayout_of_constraintSystem
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : Keygen.ProofParams) (urs : URS G)
    (column : Column .instance) (rotation : Rotation)
    (hquery :
      (column, rotation) ∈
        top.constraintSystem.instanceQueries) :
    (column.index, rotation) ∈
      (top.toVerifierKey pp urs).instanceQueryLayout := by
  change
    (column.index, rotation) ∈
      (PinnedConstraintSystem.derive
        top.constraintSystem top.selectorMap).instanceQueryLayout
  exact
    PinnedConstraintSystem.mem_instanceQueryLayout_derive_of_mem
      top.constraintSystem top.selectorMap column rotation hquery

end QueryLayouts

end Zcash.Snark
