import Zcash.Circuits.Action.SelectorCoherence
import Zcash.Circuits.Action.TopLevel
import Zcash.Circuits.Integration.ActionPermutationDomainCompute
import Zcash.Circuits.Integration.TopLevelGates

/-!
# Closed computations for Action gate coherence

This small module isolates the native computation certificates needed to lift the
Action configure proofs to the synthesis-closed top-level constraint system.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (scalarFieldOrder)

open Halo2 Keygen
open Zcash.Circuits
open Zcash.Circuits.Action (actionCircuit)

namespace ActionGateCoherence

/--
Closing the Action configure result under its own synthesis does not add gates or
change the selector allocation bound.
-/
theorem gateData_eq :
    actionCircuit.constraintSystem.gates =
        (Action.Circuit.configure Specs.Sinsemilla.orchardGenerators {}).2.gates ∧
      actionCircuit.constraintSystem.numSelectors =
        (Action.Circuit.configure
          Specs.Sinsemilla.orchardGenerators {}).2.numSelectors := by
  native_decide

/-- The derived Action constraint-system degree is below the Pasta field order. -/
theorem selectorDegree :
    csDegree actionCircuit.constraintSystem < scalarFieldOrder := by
  native_decide

/-- The circuit-derived Action domain exponent is within Pasta's supported range. -/
theorem domainExponent_lt :
    actionCircuit.domainExponent < 33 := by
  native_decide

assert_no_sorry gateData_eq
assert_no_sorry selectorDegree
assert_no_sorry domainExponent_lt

end ActionGateCoherence

end Zcash.Snark
