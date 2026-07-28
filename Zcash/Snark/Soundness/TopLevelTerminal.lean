import Zcash.Circuits.Integration.TopLevelCorrectness
import Zcash.Common.RelationWitness
import Zcash.Circuits.Integration.TopLevelAssignment
import Zcash.Snark.Soundness.Multiopen.CanonicalRelation

/-!
# Generic top-level circuit soundness terminal

This module is the core soundness endpoint for a Clean `TopLevelCircuit`.  It
turns satisfaction of the verifier-native canonical constraint model into the
circuit's own statement for every proof in the bundle.

The Clean/Ironwood representation work remains exposed as named component
conditions.  In particular, `TopLevelCircuitCorrectness` does not contain the
desired statement or an opaque encoding implication.
-/

namespace Zcash.Snark

open Halo2 Polynomial

universe u v w

def TopLevelTerminalOutcome
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : Keygen.ProofParams)
    (poly : CommitmentId → Polynomial Fp)
    (Bad : Type) : Type :=
  TopLevelBundleStatement top pp poly ⊕' Bad

private def bindOutcome {A : Sort u} {B : Sort v} {R : Sort w}
    (outcome : A ⊕' R) (next : A → B ⊕' R) : B ⊕' R :=
  match outcome with
  | .inl value => next value
  | .inr bad => .inr bad

noncomputable def topLevelBundleStatement_or_bad_of_components
    {G : Type} [AddCommGroup G] [Inhabited G]
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    {top : TopLevelCircuit Fp Config PublicInput}
    {pp : Keygen.ProofParams} {urs : URS G}
    {ch : Challenges (pp.mergeDerived top).k Fp}
    {poly : CommitmentId → Polynomial Fp}
    {cell : Type} [DecidableEq cell] [Fintype cell]
    {Bad : Type}
    (hblinding :
      (top.toVerifierKey pp urs).blindingFactors <
        (top.toVerifierKey pp urs).n)
    (satisfaction :
      ConstraintSatisfaction
        (canonicalConstraintModelOfPermutationResolver
          (top.toVerifierKey pp urs) ch poly hblinding)
        (top.toVerifierKey pp urs).n)
    (gates : TopLevelGateCoherence top pp urs)
    (fixedEncoding : ∀ proofIndex,
      TopLevelFixedEncoding top pp urs poly proofIndex)
    (fixed : ∀ proofIndex,
      TopLevelFixed top pp urs poly proofIndex)
    (copies : ∀ proofIndex,
      TopLevelCopies top pp urs poly cell Bad proofIndex)
    (lookups : ∀ proofIndex,
      TopLevelLookups top pp urs ch poly proofIndex) :
    TopLevelTerminalOutcome top pp poly Bad := by
  exact
    finForallOrRelationWitness
      (A := fun proofIndex =>
        let assignment :
            TopLevelAssignment top
              (pp.mergeDerived top).numProofs proofIndex :=
          { polynomial := poly }
        top.Statement
          (top.extractPublicInput
            (top.environment assignment.proofAssignment)))
      fun proofIndex =>
        (TopLevelAssignment.bridgeWitness_of_components
            proofIndex hblinding satisfaction gates
            (fixedEncoding proofIndex)
            (fixed proofIndex).1 (fixed proofIndex).2
            (copies proofIndex) (lookups proofIndex)).statement_or_bad

/--
Canonical constraint satisfaction plus the component-level circuit correctness
package implies the circuit-owned statement for every proof, preserving the one
shared exceptional event.
-/
noncomputable def topLevelBundleStatement_or_bad_of_constraintSatisfaction
    {G : Type} [AddCommGroup G] [Inhabited G]
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    {top : TopLevelCircuit Fp Config PublicInput}
    {pp : Keygen.ProofParams} {urs : URS G}
    {ch : Challenges (pp.mergeDerived top).k Fp}
    {poly : CommitmentId → Polynomial Fp}
    {cell : Type} [DecidableEq cell] [Fintype cell]
    {Bad : Type}
    (hblinding :
      (top.toVerifierKey pp urs).blindingFactors <
        (top.toVerifierKey pp urs).n)
    (satisfaction :
      ConstraintSatisfaction
        (canonicalConstraintModelOfPermutationResolver
          (top.toVerifierKey pp urs) ch poly hblinding)
        (top.toVerifierKey pp urs).n)
    (correctness :
      TopLevelCircuitCorrectness top pp urs ch poly cell Bad) :
    TopLevelTerminalOutcome top pp poly Bad := by
  classical
  let fixedEncodingOutcome :=
    finForallOrRelationWitness
      (A := fun proofIndex =>
        TopLevelFixedEncoding top pp urs poly proofIndex)
      correctness.fixedEncoding
  let fixedOutcome :=
    finForallOrRelationWitness
      (A := fun proofIndex =>
        TopLevelFixed top pp urs poly proofIndex)
      correctness.fixed
  let copiesOutcome :=
    finForallOrRelationWitness
      (A := fun proofIndex =>
        TopLevelCopies top pp urs poly cell Bad proofIndex)
      correctness.copies
  let lookupsOutcome :=
    finForallOrRelationWitness
      (A := fun proofIndex =>
        TopLevelLookups top pp urs ch poly proofIndex)
      correctness.lookups
  exact bindOutcome fixedEncodingOutcome fun hfixedEncoding =>
    bindOutcome fixedOutcome fun hfixed =>
      bindOutcome copiesOutcome fun hcopies =>
        bindOutcome lookupsOutcome fun hlookups =>
          topLevelBundleStatement_or_bad_of_components
            hblinding satisfaction correctness.gates
            hfixedEncoding hfixed hcopies hlookups

assert_no_sorry topLevelBundleStatement_or_bad_of_constraintSatisfaction

end Zcash.Snark
