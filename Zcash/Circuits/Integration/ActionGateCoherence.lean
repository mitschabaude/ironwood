import Zcash.Circuits.Integration.ActionGateCoherenceCompute

/-!
# Action top-level gate coherence

This module packages the circuit-owned configure certificates and the small derived
layout computations into the generic static gate-coherence boundary.
-/

namespace Zcash.Circuits

open Halo2

namespace ActionGateCoherence

/-- The exact deployed configure program, named before it is made opaque. -/
def configureProgramSource : Configure Fp Action.Circuit.Config :=
  Action.Circuit.configure Specs.Sinsemilla.orchardGenerators

/-- An opaque handle carrying both the program and its source identification. -/
opaque configureHandle :
    {program : Configure Fp Action.Circuit.Config //
      program = configureProgramSource} :=
  ⟨configureProgramSource, rfl⟩

/--
The sealed program projection. Its state-monad body cannot be normalized unless the
source-identification theorem is used explicitly.
-/
def configureProgram : Configure Fp Action.Circuit.Config :=
  configureHandle.1

theorem configureProgram_eq :
    configureProgram = configureProgramSource :=
  configureHandle.2

theorem configureProgram_preservesGateSelectorsAllocated :
    Configure.PreservesGateSelectorsAllocated configureProgram := by
  rw [configureProgram_eq]
  simpa only [configureProgramSource] using
    (Action.Circuit.configure_preservesGateSelectorsAllocated
      Specs.Sinsemilla.orchardGenerators)

theorem configureProgram_gateSelectorsAllocated :
    (configureProgram {}).2.GateSelectorsAllocated :=
  Configure.PreservesGateSelectorsAllocated.fromEmpty
    configureProgram_preservesGateSelectorsAllocated

end ActionGateCoherence

end Zcash.Circuits

namespace Zcash.Snark

open Halo2 Keygen
open Halo2
open Zcash.Circuits.Action (actionCircuit)

namespace ActionGateCoherence

set_option maxRecDepth 100000

private theorem gateSelectorsAllocated_of_data_eq
    {F : Type} {source target : ConstraintSystem F}
    (hgates : source.gates = target.gates)
    (hselectors : source.numSelectors = target.numSelectors)
    (h : target.GateSelectorsAllocated) :
    source.GateSelectorsAllocated := by
  unfold ConstraintSystem.GateSelectorsAllocated at h ⊢
  rwa [hgates, hselectors]

private theorem gateSelectorsAllocated :
    actionCircuit.constraintSystem.GateSelectorsAllocated :=
  gateSelectorsAllocated_of_data_eq
    (gateData_eq.1.trans (congrArg
      (fun program => (program {}).2.gates)
      Circuits.ActionGateCoherence.configureProgram_eq.symm))
    (gateData_eq.2.trans (congrArg
      (fun program => (program {}).2.numSelectors)
      Circuits.ActionGateCoherence.configureProgram_eq.symm))
    Circuits.ActionGateCoherence.configureProgram_gateSelectorsAllocated

private theorem adviceQueryCount
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G) :
    (actionCircuit.toVerifierKey pp urs).adviceQueryLayout.length =
      (pp.mergeDerived actionCircuit).numAdviceQueries :=
  actionCircuit.toVerifierKey_adviceQueryCount pp urs

private theorem fixedQueryCount
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G) :
    (actionCircuit.toVerifierKey pp urs).fixedQueryLayout.length =
      (pp.mergeDerived actionCircuit).numFixedQueries :=
  actionCircuit.toVerifierKey_fixedQueryCount pp urs

private theorem instanceQueryCount
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G) :
    (actionCircuit.toVerifierKey pp urs).instanceQueryLayout.length =
      (pp.mergeDerived actionCircuit).numInstanceQueries :=
  actionCircuit.toVerifierKey_instanceQueryCount pp urs

/--
The deployed Orchard Action circuit satisfies the complete static gate boundary
against its own derived verifying key.
-/
theorem topLevelGateCoherence
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G) :
    TopLevelGateCoherence actionCircuit pp urs where
  gateSelectorsAllocated := gateSelectorsAllocated
  adviceQueryCount := adviceQueryCount pp urs
  fixedQueryCount := fixedQueryCount pp urs
  instanceQueryCount := instanceQueryCount pp urs
  domainExponent_lt := domainExponent_lt
  selectorDegree := selectorDegree

assert_no_sorry topLevelGateCoherence

end ActionGateCoherence

end Zcash.Snark
