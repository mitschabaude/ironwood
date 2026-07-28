import Zcash.Circuits.Integration.TopLevelBridge
import Zcash.Common.RelationWitness
import Zcash.Circuits.Integration.TopLevelAssignment

/-!
# Top-level circuit correctness interface

This module packages the named Clean/Ironwood representation boundaries consumed
by the generic soundness terminal.  It deliberately contains no final circuit
statement and no opaque encoding implication.
-/

namespace Zcash.Snark

open Halo2 Polynomial

/--
The statement owned by a top-level circuit, simultaneously for every polynomial
assignment decoded from one accepted proof bundle.
-/
def TopLevelBundleStatement
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : Keygen.ProofParams)
    (poly : CommitmentId → Polynomial Fp) : Prop :=
  ∀ proofIndex : Fin (pp.mergeDerived top).numProofs,
    let environment := ({
        polynomial := poly
      } : TopLevelAssignment top
            (pp.mergeDerived top).numProofs proofIndex).environment
    top.Statement (top.extractPublicInput environment)

namespace TopLevelBundleStatement

/--
Present the circuit-owned bundle statement at externally supplied public inputs once
the canonical polynomial assignments are known to encode them through the circuit's
declared instance-cell layout.
-/
theorem of_publicInputEncoding
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : Keygen.ProofParams)
    (poly : CommitmentId → Polynomial Fp)
    (inputs : Fin (pp.mergeDerived top).numProofs → PublicInput Fp)
    (hencoding : ∀ proofIndex,
      let assignment : TopLevelAssignment top
          (pp.mergeDerived top).numProofs proofIndex :=
        { polynomial := poly }
      assignment.PublicInputEncoding (inputs proofIndex))
    (htop : TopLevelBundleStatement top pp poly) :
    ∀ proofIndex, top.Statement (inputs proofIndex) := by
  intro proofIndex
  let assignment : TopLevelAssignment top
      (pp.mergeDerived top).numProofs proofIndex :=
    { polynomial := poly }
  have hstatement := htop proofIndex
  change top.Statement
    (top.extractPublicInput assignment.environment) at hstatement
  rw [assignment.extractPublicInput_eq
    (inputs proofIndex) (hencoding proofIndex)] at hstatement
  exact hstatement

end TopLevelBundleStatement

abbrev TopLevelFixedEncoding
    {G : Type} [AddCommGroup G] [Inhabited G]
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : Keygen.ProofParams) (urs : URS G)
    (poly : CommitmentId → Polynomial Fp)
    (proofIndex : Fin (pp.mergeDerived top).numProofs) : Prop :=
  let assignment :
      TopLevelAssignment top (pp.mergeDerived top).numProofs proofIndex :=
    { polynomial := poly }
  assignment.FixedColumnEncoding pp urs

abbrev TopLevelFixed
    {G : Type} [AddCommGroup G] [Inhabited G]
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : Keygen.ProofParams) (urs : URS G)
    (poly : CommitmentId → Polynomial Fp)
    (proofIndex : Fin (pp.mergeDerived top).numProofs) : Prop :=
  (SelectorActivationsRealized
      top.selectorMap top.selectorActivations
      (resolverEnvironment
        (top.toVerifierKey pp urs) poly proofIndex
        (top.usableRowsAt top.domainExponent))
    ∧ CircuitConstraintFamily.constraints .fixed top.placement
      (resolverEnvironment
        (top.toVerifierKey pp urs) poly proofIndex
        (top.usableRowsAt top.domainExponent))
      top.operations 0)

abbrev TopLevelCopies
    {G : Type} [AddCommGroup G] [Inhabited G]
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : Keygen.ProofParams) (urs : URS G)
    (poly : CommitmentId → Polynomial Fp)
    (cell : Type) [DecidableEq cell] [Fintype cell]
    (Bad : Type)
    (proofIndex : Fin (pp.mergeDerived top).numProofs) : Type :=
  CopyReplayWitness top.placement
    (resolverEnvironment
      (top.toVerifierKey pp urs) poly proofIndex
      (top.usableRowsAt top.domainExponent))
    top.operations cell Bad

abbrev TopLevelLookups
    {G : Type} [AddCommGroup G] [Inhabited G]
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : Keygen.ProofParams) (urs : URS G)
    (ch : Challenges (pp.mergeDerived top).k Fp)
    (poly : CommitmentId → Polynomial Fp)
    (proofIndex : Fin (pp.mergeDerived top).numProofs) : Prop :=
  TopLevelLookupCoherence.TopLevelLookupWitnessConditions
    top pp urs ch poly proofIndex

namespace TopLevelAssignment

/--
Package one successful set of component witnesses behind abstract environment
and operation values, retaining only their equalities to the circuit-derived
values.
-/
noncomputable def bridgeWitness_of_components
    {G : Type} [AddCommGroup G] [Inhabited G]
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    {top : TopLevelCircuit Fp Config PublicInput}
    {pp : Keygen.ProofParams} {urs : URS G}
    {ch : Challenges (pp.mergeDerived top).k Fp}
    {poly : CommitmentId → Polynomial Fp}
    {cell : Type} [DecidableEq cell] [Fintype cell]
    {Bad : Type}
    (proofIndex : Fin (pp.mergeDerived top).numProofs)
    (hblinding :
      (top.toVerifierKey pp urs).blindingFactors <
        (top.toVerifierKey pp urs).n)
    (satisfaction :
      ConstraintSatisfaction
        (canonicalConstraintModelOfPermutationResolver
          (top.toVerifierKey pp urs) ch poly hblinding)
        (top.toVerifierKey pp urs).n)
    (gates : TopLevelGateCoherence top pp urs)
    (fixedEncoding :
      let assignment :
          TopLevelAssignment top
            (pp.mergeDerived top).numProofs proofIndex :=
        { polynomial := poly }
      assignment.FixedColumnEncoding pp urs)
    (selectorActivations :
      SelectorActivationsRealized
        top.selectorMap top.selectorActivations
        (resolverEnvironment
          (top.toVerifierKey pp urs) poly proofIndex
          (top.usableRowsAt top.domainExponent)))
    (fixed :
      CircuitConstraintFamily.constraints .fixed top.placement
        (resolverEnvironment
          (top.toVerifierKey pp urs) poly proofIndex
          (top.usableRowsAt top.domainExponent))
        top.operations 0)
    (copies :
      CopyReplayWitness top.placement
        (resolverEnvironment
          (top.toVerifierKey pp urs) poly proofIndex
          (top.usableRowsAt top.domainExponent))
        top.operations cell Bad)
    (lookups :
      TopLevelLookupCoherence.TopLevelLookupWitnessConditions
        top pp urs ch poly proofIndex) :
    TopLevelBridgeWitness top
      (({ polynomial := poly } :
        TopLevelAssignment top
          (pp.mergeDerived top).numProofs proofIndex).proofAssignment)
      cell Bad := by
  let assignment :
      TopLevelAssignment top (pp.mergeDerived top).numProofs proofIndex :=
    { polynomial := poly }
  change TopLevelBridgeWitness top assignment.proofAssignment cell Bad
  have hrows :=
    TopLevelAssignment.domainRowsInjective
      (top := top) gates.domainExponent_lt
  have hroot :=
    TopLevelAssignment.domainRoot
      (top := top) gates.domainExponent_lt
  have hrowsVk :
      Function.Injective
        (fun row : Fin (top.toVerifierKey pp urs).n =>
          (top.toVerifierKey pp urs).omega ^ (row : ℕ)) := by
    simpa only [top.toVerifierKey_n, top.toVerifierKey_omega] using hrows
  have hrootVk :
      (top.toVerifierKey pp urs).omega ^
        (top.toVerifierKey pp urs).n = 1 := by
    simpa only [top.toVerifierKey_n, top.toVerifierKey_omega] using hroot
  let bridge :=
    FullCircuitBridge.ofTopLevelCanonical
      (top := top) (pp := pp) (urs := urs)
      (cell := cell) (Bad := Bad)
      gates ch poly proofIndex hblinding satisfaction
      hrowsVk hrootVk selectorActivations fixed copies lookups
  clear_value bridge
  generalize henvironmentValue :
    resolverEnvironment
      (top.toVerifierKey pp urs) poly proofIndex
      (top.usableRowsAt top.domainExponent) = environment at bridge
  generalize hoperations : top.operations = operations at bridge
  have henvironment :=
    assignment.resolverEnvironment_eq_environment
      pp urs fixedEncoding
  have henvironment' :
      resolverEnvironment
          (top.toVerifierKey pp urs) poly proofIndex
          (top.usableRowsAt top.domainExponent) =
        top.environment assignment.proofAssignment :=
    henvironment
  refine
    { environment := environment
      operations := operations
      environment_eq := ?_
      operations_eq := ?_
      bridge := ?_ }
  · exact henvironmentValue.symm.trans henvironment'
  · exact hoperations
  · exact bridge

end TopLevelAssignment

def TopLevelFixedEncodingOutcome
    {G : Type} [AddCommGroup G] [Inhabited G]
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : Keygen.ProofParams) (urs : URS G)
    (poly : CommitmentId → Polynomial Fp)
    (Bad : Type)
    (proofIndex : Fin (pp.mergeDerived top).numProofs) : Type :=
  TopLevelFixedEncoding top pp urs poly proofIndex ⊕' Bad

def TopLevelFixedOutcome
    {G : Type} [AddCommGroup G] [Inhabited G]
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : Keygen.ProofParams) (urs : URS G)
    (poly : CommitmentId → Polynomial Fp)
    (Bad : Type)
    (proofIndex : Fin (pp.mergeDerived top).numProofs) : Type :=
  TopLevelFixed top pp urs poly proofIndex ⊕' Bad

def TopLevelCopiesOutcome
    {G : Type} [AddCommGroup G] [Inhabited G]
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : Keygen.ProofParams) (urs : URS G)
    (poly : CommitmentId → Polynomial Fp)
    (cell : Type) [DecidableEq cell] [Fintype cell]
    (Bad : Type)
    (proofIndex : Fin (pp.mergeDerived top).numProofs) : Type :=
  TopLevelCopies top pp urs poly cell Bad proofIndex ⊕' Bad

def TopLevelLookupsOutcome
    {G : Type} [AddCommGroup G] [Inhabited G]
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : Keygen.ProofParams) (urs : URS G)
    (ch : Challenges (pp.mergeDerived top).k Fp)
    (poly : CommitmentId → Polynomial Fp)
    (Bad : Type)
    (proofIndex : Fin (pp.mergeDerived top).numProofs) : Type :=
  TopLevelLookups top pp urs ch poly proofIndex ⊕' Bad

structure TopLevelCorrectnessData
    (Gates : Prop)
    (FixedEncoding Fixed Copies Lookups : Type) : Type where
  gates : Gates
  fixedEncoding : FixedEncoding
  fixed : Fixed
  copies : Copies
  lookups : Lookups

/--
The representation-boundary data needed to interpret one canonical polynomial
assignment as an execution of a top-level circuit.

Each field names one of the four Clean constraint families.  The shared `Bad`
alternative is retained componentwise so that commitment-binding failures can be
joined without turning this record into an opaque statement-level hypothesis, and
is carried as data: a field that cannot be discharged returns the break rather
than asserting one exists.

The copy field previously squashed its witness under `Nonempty`.  With `Bad` a
type the witness is already data, so it is carried directly and the terminal no
longer has to recover it by choice.
-/
def TopLevelCircuitCorrectness
    {G : Type} [AddCommGroup G] [Inhabited G]
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : Keygen.ProofParams) (urs : URS G)
    (ch : Challenges (pp.mergeDerived top).k Fp)
    (poly : CommitmentId → Polynomial Fp)
    (cell : Type) [DecidableEq cell] [Fintype cell]
    (Bad : Type) : Type :=
  TopLevelCorrectnessData
    (TopLevelGateCoherence top pp urs)
    (∀ proofIndex,
      TopLevelFixedEncodingOutcome top pp urs poly Bad proofIndex)
    (∀ proofIndex,
      TopLevelFixedOutcome top pp urs poly Bad proofIndex)
    (∀ proofIndex,
      TopLevelCopiesOutcome top pp urs poly cell Bad proofIndex)
    (∀ proofIndex,
      TopLevelLookupsOutcome top pp urs ch poly Bad proofIndex)

end Zcash.Snark
