import Zcash.Snark.Keygen.Pipeline
import Zcash.Arithmetic.Domain
import Zcash.Circuits.Integration.ResolverGates
import Zcash.Circuits.Integration.ResolverQueryEnvironment
import Zcash.Circuits.Integration.SelectorCoherence
import Zcash.Snark.Soundness.Canonical.ConstraintModel

/-!
# Generic top-level gate bridge

This module packages the static facts needed to use a closed formal circuit's own
derived verifying key. The package is circuit-independent and cannot be paired with
an arbitrary key: every verifier-side object below uses
`TopLevelCircuit.toVerifierKey`.

Given that static package and realization of the circuit-derived packed selector
rows by the decoded fixed polynomials, every enabled circuit gate receives the
polynomial witness consumed by the generic constraint-satisfaction split.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (omegaOf scalarFieldOrder)

open Halo2 Polynomial Keygen

set_option maxHeartbeats 20000

/--
Static coherence for a top-level circuit's own derived verifying key.

No placement, operation stream, selector map, or pinned constraint system is supplied
by the caller: all four are derived from `top`, and the key is fixed to
`top.toVerifierKey pp urs`. Gate/lookup registration coherence is absent because the
circuit-derived constraint system closes the raw configure result under synthesis by
construction.
-/
structure TopLevelGateCoherence
    {G : Type} [AddCommGroup G] [Inhabited G]
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS G) : Prop where
  gateSelectorsAllocated :
    top.constraintSystem.GateSelectorsAllocated
  adviceQueryCount :
    (top.toVerifierKey pp urs).adviceQueryLayout.length =
      (pp.mergeDerived top).numAdviceQueries
  fixedQueryCount :
    (top.toVerifierKey pp urs).fixedQueryLayout.length =
      (pp.mergeDerived top).numFixedQueries
  instanceQueryCount :
    (top.toVerifierKey pp urs).instanceQueryLayout.length =
      (pp.mergeDerived top).numInstanceQueries
  domainExponent_lt : top.domainExponent < 33
  selectorDegree :
    csDegree top.constraintSystem < scalarFieldOrder

namespace TopLevelGateCoherence

variable
    {G : Type} [AddCommGroup G] [Inhabited G]
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    {top : TopLevelCircuit Fp Config PublicInput}
    {pp : ProofParams} {urs : URS G}

/--
The final pinned query state interprets the resolver feeds, and restricts to the
intermediate gate-erasure state because lookup erasure only appends query entries.
-/
theorem resolverInterpretsGates
    (coherence : TopLevelGateCoherence top pp urs)
    (poly : CommitmentId → Polynomial Fp)
    (proofIndex : Fin (pp.mergeDerived top).numProofs)
    (usableRows row : ℕ) :
    Interprets
      (eraseGates
        ((flatGates top.constraintSystem).map
          (substSelectorMap top.selectorMap.lookup))
        (queryWalkInit top.selectorMap
          top.constraintSystem)).2
      (fun query =>
        (fixedQueryFeedOfResolver
          (top.toVerifierKey pp urs) poly query).eval
          ((top.toVerifierKey pp urs).omega ^ row))
      (fun query =>
        (adviceQueryFeedOfResolver
          (top.toVerifierKey pp urs) poly proofIndex query).eval
          ((top.toVerifierKey pp urs).omega ^ row))
      (fun query =>
        (instanceQueryFeedOfResolver
          (top.toVerifierKey pp urs) poly proofIndex query).eval
          ((top.toVerifierKey pp urs).omega ^ row))
      (Query.eval
        (resolverEnvironment
          (top.toVerifierKey pp urs) poly proofIndex usableRows)
        (fun _ => 0) row) := by
  have homega : (top.toVerifierKey pp urs).omega ≠ 0 := by
    change Zcash.Arithmetic.omegaOf top.domainExponent ≠ 0
    have hk : top.domainExponent ≤ 32 :=
      Nat.le_of_lt_succ (by simpa using coherence.domainExponent_lt)
    exact
      (Zcash.Arithmetic.omegaOf_isPrimitiveRoot
        top.domainExponent hk).isUnit (by positivity) |>.ne_zero
  have hfinal := resolverQueryFeeds_interpret
    (top.toVerifierKey pp urs) poly proofIndex usableRows
    (fun _ => 0) row
    homega
    (pinnedQueryState
      (PinnedConstraintSystem.derive
        top.constraintSystem top.selectorMap))
    (by rfl)
    (by rfl)
    (by rfl)
    coherence.adviceQueryCount
    coherence.fixedQueryCount
    coherence.instanceQueryCount
  apply hfinal.mono
  exact
    PinnedConstraintSystem.derive_queryState_extends_gates
      top.constraintSystem top.selectorMap

/--
Every enabled constraint in the top-level operation stream has the corresponding
resolver gate polynomial witness.
-/
noncomputable def polynomialWitness
    (coherence : TopLevelGateCoherence top pp urs)
    (ch : Challenges (pp.mergeDerived top).k Fp)
    (poly : CommitmentId → Polynomial Fp)
    (sets : Fin (pp.mergeDerived top).numProofs →
      List (PermSetEval (Polynomial Fp)))
    (chunks : Fin (pp.mergeDerived top).numProofs →
      List (PermSetEval (Polynomial Fp) ×
        List (Polynomial Fp × Polynomial Fp)))
    (l0 lLast lBlind : Polynomial Fp)
    (proofIndex : Fin (pp.mergeDerived top).numProofs)
    (usableRows : ℕ)
    (hfixed : SelectorActivationsRealized top.selectorMap
      top.selectorActivations
      (resolverEnvironment
        (top.toVerifierKey pp urs) poly proofIndex usableRows))
    (enabled : EnabledGate Fp)
    (henabled :
      enabled ∈ operationEnabledGates (top.operations) 0)
    (constraint : Constraint Fp)
    (hconstraint : constraint ∈ enabled.gate.constraints) :
    EnabledGate.PolynomialWitness
      (constraintModelOfResolver
        (top.toVerifierKey pp urs) ch poly sets chunks
        l0 lLast lBlind)
      proofIndex (top.toVerifierKey pp urs).omega top.placement
      (resolverEnvironment
        (top.toVerifierKey pp urs) poly proofIndex usableRows)
      enabled constraint := by
  have hgate : enabled.gate ∈ top.constraintSystem.gates :=
    OperationsKeygenCoherent.gate
      top.keygenCoherent henabled
  have hselector :
      enabled.gate.selector.index <
        top.constraintSystem.numSelectors :=
    coherence.gateSelectorsAllocated.gate hgate
  have hlookupSome :
      (top.selectorMap.lookup
        enabled.gate.selector.index).isSome = true := by
    simpa [TopLevelCircuit.selectorMap] using
      deriveSelCompressMap_lookup_isSome_of_lt
        top.constraintSystem
        (2 ^ top.domainExponent)
        top.selectorActivations hselector
  have hlookupPresent :
      (top.selectorMap.lookup
        enabled.gate.selector.index).isSome := by
    simpa using hlookupSome
  let compressed :=
    Classical.choose
      (Option.isSome_iff_exists.mp hlookupPresent)
  have hcompressed :
      top.selectorMap.lookup enabled.gate.selector.index =
        some compressed :=
    Classical.choose_spec
      (Option.isSome_iff_exists.mp hlookupPresent)
  have hroots :
      SelectorRootsWellFormed top.selectorMap := by
    change SelectorRootsWellFormed
      (deriveSelCompressMap top.constraintSystem
        (2 ^ top.domainExponent) top.selectorActivations)
    exact selectorRootsWellFormed_deriveSelCompressMap
        top.constraintSystem
        (2 ^ top.domainExponent)
        top.selectorActivations coherence.selectorDegree
  have hcoverage :
      ∀ expression ∈ flatGates top.constraintSystem,
        expression.selectorsCovered
          (fun selector =>
            (top.selectorMap.lookup selector).isSome) = true := by
    simpa [TopLevelCircuit.selectorMap] using
      gateSelectorsCovered_deriveSelCompressMap
        top.constraintSystem
        (2 ^ top.domainExponent)
        top.selectorActivations
        coherence.gateSelectorsAllocated
  have hgates :
      (top.toVerifierKey pp urs).gates =
        (PinnedConstraintSystem.derive
          top.constraintSystem top.selectorMap).gates.map
            RichExpression.toExpr := by
    rfl
  have hinterpret := coherence.resolverInterpretsGates
    poly proofIndex usableRows
    (top.placement enabled.region + enabled.row)
  have hscale :
      (selReplacement compressed).eval
        (Query.eval
          (resolverEnvironment
            (top.toVerifierKey pp urs) poly proofIndex usableRows)
          (fun _ => 0)
          (top.placement enabled.region + enabled.row)) ≠ 0 := by
    apply selectorScale_ne_zero_of_enabledGate
      top.selectorMap top.regionStarts (top.operations) 0
      (resolverEnvironment
        (top.toVerifierKey pp urs) poly proofIndex usableRows)
      (fun _ => 0) hroots
    · exact hfixed
    · exact henabled
    · exact hcompressed
  exact enabledGatePolynomialWitnessOfResolver
    (top.toVerifierKey pp urs)
    top.constraintSystem top.selectorMap ch poly sets chunks
    l0 lLast lBlind proofIndex top.placement usableRows
    enabled constraint hgate hconstraint
    hgates hcoverage
    compressed hcompressed hinterpret hscale

/--
Deployed gate divisibility therefore supplies the complete gate component of the
top-level circuit's Clean constraints.
-/
theorem constraints
    (coherence : TopLevelGateCoherence top pp urs)
    (ch : Challenges (pp.mergeDerived top).k Fp)
    (poly : CommitmentId → Polynomial Fp)
    (sets : Fin (pp.mergeDerived top).numProofs →
      List (PermSetEval (Polynomial Fp)))
    (chunks : Fin (pp.mergeDerived top).numProofs →
      List (PermSetEval (Polynomial Fp) ×
        List (Polynomial Fp × Polynomial Fp)))
    (l0 lLast lBlind : Polynomial Fp)
    (proofIndex : Fin (pp.mergeDerived top).numProofs)
    (usableRows n : ℕ)
    (satisfaction :
      ConstraintSatisfaction
        (constraintModelOfResolver
          (top.toVerifierKey pp urs) ch poly sets chunks
          l0 lLast lBlind) n)
    (domain : ∀ row : ℕ,
      ((top.toVerifierKey pp urs).omega ^ row) ^ n = 1)
    (hfixed : SelectorActivationsRealized top.selectorMap
      top.selectorActivations
      (resolverEnvironment
        (top.toVerifierKey pp urs) poly proofIndex usableRows)) :
    CircuitConstraintFamily.constraints .gate top.placement
      (resolverEnvironment
        (top.toVerifierKey pp urs) poly proofIndex usableRows)
      (top.operations) 0 := by
  apply gate_constraints_of_polynomial_witnesses
    (constraintModelOfResolver
      (top.toVerifierKey pp urs) ch poly sets chunks
      l0 lLast lBlind)
    proofIndex (top.toVerifierKey pp urs).omega top.placement
    (resolverEnvironment
      (top.toVerifierKey pp urs) poly proofIndex usableRows)
    (top.operations) 0 satisfaction domain
  intro enabled henabled constraint hconstraint
  exact coherence.polynomialWitness
    ch poly sets chunks l0 lLast lBlind proofIndex usableRows
    hfixed enabled henabled constraint hconstraint

/--
Specialize the top-level gate bridge to the canonical resolver model.

This removes the last opportunity for a gate caller to supply unrelated permutation
families or Lagrange-selector polynomials: they are the ones derived from the same
resolver and circuit-owned verification key.
-/
theorem canonicalConstraints
    (coherence : TopLevelGateCoherence top pp urs)
    (ch : Challenges (pp.mergeDerived top).k Fp)
    (poly : CommitmentId → Polynomial Fp)
    (hblinding :
      (top.toVerifierKey pp urs).blindingFactors <
        (top.toVerifierKey pp urs).n)
    (proofIndex : Fin (pp.mergeDerived top).numProofs)
    (satisfaction :
      ConstraintSatisfaction
        (canonicalConstraintModelOfPermutationResolver
          (top.toVerifierKey pp urs) ch poly hblinding)
        (top.toVerifierKey pp urs).n)
    (domain : ∀ row : ℕ,
      ((top.toVerifierKey pp urs).omega ^ row) ^
        (top.toVerifierKey pp urs).n = 1)
    (hfixed : SelectorActivationsRealized top.selectorMap
      top.selectorActivations
      (resolverEnvironment
        (top.toVerifierKey pp urs) poly proofIndex
        (top.usableRowsAt top.domainExponent))) :
    CircuitConstraintFamily.constraints .gate top.placement
      (resolverEnvironment
        (top.toVerifierKey pp urs) poly proofIndex
        (top.usableRowsAt top.domainExponent))
      (top.operations) 0 := by
  let selectors :=
    canonicalLagrangePolynomials
      (top.toVerifierKey pp urs).omega hblinding
  apply coherence.constraints ch poly
    (permutationSetsOfResolver
      (top.toVerifierKey pp urs) poly)
    (permutationChunksOfResolver
      (top.toVerifierKey pp urs) poly)
    selectors.1 selectors.2.1 selectors.2.2 proofIndex
    (top.usableRowsAt top.domainExponent)
    (top.toVerifierKey pp urs).n
  · simpa [canonicalConstraintModelOfPermutationResolver,
      constraintModelOfPermutationResolver, selectors] using satisfaction
  · exact domain
  · exact hfixed

end TopLevelGateCoherence

end Zcash.Snark
