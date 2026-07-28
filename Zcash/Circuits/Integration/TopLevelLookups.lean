import Zcash.Circuits.Integration.LookupProjection
import Zcash.Snark.Soundness.Canonical.ConstraintModel
import Zcash.Snark.Soundness.ChallengePricing
import Zcash.Circuits.Integration.TopLevelGates

/-!
# Resolver-backed lookup witnesses for top-level circuits

`LookupProjection` proves the compiler walk correct at a selected configured
lookup. This module selects that lookup from an enabled top-level operation and
connects its projected expressions to the resolver polynomials used by the
deployed lookup argument.

The remaining selector premise is stated explicitly. Lookup tuple semantics need
exact selector values, whereas the gate bridge only needs a nonzero selector
scale. The fixed-column compiler will discharge this premise from its complete
packed-selector rows.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (omegaOf)

open Halo2 Polynomial Keygen

set_option maxHeartbeats 20000

variable
    {G : Type} [AddCommGroup G] [Inhabited G]
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    {top : TopLevelCircuit Fp Config PublicInput}
    {pp : ProofParams} {urs : URS G}

/-- A synthesis-enabled lookup routed to its configured lookup index. -/
structure EnabledLookup.TopLevelRoute
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (lookup : EnabledLookup Fp) where
  index : Fin (pp.mergeDerived top).numLookups
  argument :
    top.constraintSystem.lookups[index.val] = lookup.argument

/--
Configure/synthesis closure selects a configured lookup index for every enabled
lookup operation.
-/
noncomputable def EnabledLookup.topLevelRoute
    (lookup : EnabledLookup Fp)
    (henabled :
      lookup ∈ operationEnabledLookups (top.operations) 0) :
    lookup.TopLevelRoute top pp := by
  have hargument :
      lookup.argument ∈ top.constraintSystem.lookups :=
    OperationsKeygenCoherent.lookup top.keygenCoherent henabled
  let index :=
    Classical.choose (List.mem_iff_getElem.mp hargument)
  let hindexAndGet :=
    Classical.choose_spec (List.mem_iff_getElem.mp hargument)
  let hindex := Classical.choose hindexAndGet
  have hget :
      top.constraintSystem.lookups[index] =
        lookup.argument :=
    Classical.choose_spec hindexAndGet
  refine
    { index := ⟨index, ?_⟩
      argument := hget }
  simpa [ProofParams.mergeDerived] using hindex

/--
Every extracted lookup activation lies inside the top-level circuit's keygen row
footprint.
-/
theorem EnabledLookup.activationRow_lt_usedRows
    (lookup : EnabledLookup Fp)
    (henabled :
      lookup ∈ operationEnabledLookups (top.operations) 0) :
    top.placement lookup.region + lookup.row < top.usedRows := by
  obtain ⟨body, hregion, hoperation⟩ :=
    (mem_operationEnabledLookups_iff lookup (top.operations) 0).mp henabled
  exact
    (absoluteRow_lt_usedRows_of_enableLookup_mem
      (top.operations) lookup.region body hregion
      lookup.argument lookup.enabled lookup.row hoperation).trans_le
      top.operations_usedRows_le_usedRows

/--
A fitting circuit-derived domain places every lookup activation in the usable-row
prefix.
-/
theorem EnabledLookup.activationRow_lt_usableRows
    (lookup : EnabledLookup Fp)
    (henabled :
      lookup ∈ operationEnabledLookups (top.operations) 0) :
    top.placement lookup.region + lookup.row <
      top.usableRowsAt top.domainExponent :=
  (lookup.activationRow_lt_usedRows henabled).trans_le
    top.usedRows_le_usableRowsAt_domainExponent

/--
Static lookup facts at the circuit-derived projection boundary.

Input coverage says selector compression eliminates every selector leaf. Table
expressions are selector-free because Halo 2 constructs them from lookup-table
columns. Arity is inherited from the list-of-pairs lookup constructor.
-/
structure TopLevelLookupCoherence
    (top : TopLevelCircuit Fp Config PublicInput) : Prop where
  inputsCovered : ∀ argument ∈ top.constraintSystem.lookups,
    ∀ expression ∈ argument.inputs,
      expression.selectorsCovered
        (fun selector =>
          (top.selectorMap.lookup selector).isSome) = true
  tablesFree : ∀ argument ∈ top.constraintSystem.lookups,
    argument.tables.Forall Expression.SelectorFree
  arity : ∀ argument ∈ top.constraintSystem.lookups,
    argument.inputs.length = argument.tables.length

namespace TopLevelLookupCoherence

/--
Every top-level circuit supplies the static lookup boundary by construction.

`FormalCircuit.toConstraintSystem` closes selector allocation over every synthesis
lookup input. `LookupArgument` itself carries selector-freedom of its table tuple and
equality of the input/table arities. The generic selector compiler then turns the
syntactic input bound into coverage by the circuit-derived compression map.
-/
theorem ofTopLevel :
    TopLevelLookupCoherence top := by
  have inputAllocated :
      ∀ argument ∈ top.constraintSystem.lookups,
        ∀ expression ∈ argument.inputs,
          expression.selectorBound ≤
            top.constraintSystem.numSelectors := by
    exact top.lookupInputsAllocated
  refine
    { inputsCovered := ?_
      tablesFree := ?_
      arity := ?_ }
  · intro argument hargument expression hexpression
    have sourceCoverage :=
      expression.selectorsCovered_lt_of_selectorBound_le
        top.constraintSystem.numSelectors
        (inputAllocated argument hargument expression hexpression)
    apply Expression.selectorsCovered_mono
      (fun selector =>
        decide (selector <
          top.constraintSystem.numSelectors))
    · intro selector hselector
      exact deriveSelCompressMap_lookup_isSome_of_lt
        top.constraintSystem
        (2 ^ top.domainExponent)
        top.selectorActivations
        (of_decide_eq_true hselector)
    · exact sourceCoverage
  · intro argument hargument
    exact List.forall_iff_forall_mem.mpr
      (fun table htable => argument.tablesFree table htable)
  · intro argument hargument
    exact argument.arity

end TopLevelLookupCoherence

/--
The exact selector-substitution facts needed by one enabled lookup.

This is stronger than gate activation realization: every source expression must
evaluate with the packed-selector substitution exactly as it does with the
operation's zero/one selector valuation. Tables usually discharge the second
field structurally because Halo 2 tables are selector-free.
-/
structure EnabledLookup.SelectorProjection
    (top : TopLevelCircuit Fp Config PublicInput)
    (environment : Environment Fp) (lookup : EnabledLookup Fp) : Prop where
  input :
    lookup.argument.inputs.map
        (Expression.eval
          (substValuation top.selectorMap.lookup
            (Query.eval environment (fun _ => 0)
              (top.placement lookup.region + lookup.row)))) =
      lookup.inputValues top.placement environment
  table : ∀ row < environment.usableRows,
    lookup.argument.tables.map
        (Expression.eval
          (substValuation top.selectorMap.lookup
            (Query.eval environment (fun _ => 0) row))) =
      lookup.tableValues environment row

/--
Selector-free expressions cannot distinguish selector substitution from an
arbitrary selector valuation. Fixed, advice, and instance queries retain the
same environment and row on both sides.
-/
theorem Expression.eval_substValuation_eq_queryEval_of_selectorFree
    (map : SelCompressMap) (environment : Environment Fp)
    (selectors : ℕ → Fp) (row : ℕ)
    (expression : Expression Fp Query)
    (hfree : expression.SelectorFree) :
    expression.eval
        (substValuation map.lookup
          (Query.eval environment (fun _ => 0) row)) =
      expression.eval (Query.eval environment selectors row) := by
  induction expression with
  | var query =>
      cases query with
      | selector selector =>
          simp [Expression.SelectorFree] at hfree
      | fixed column rotation =>
          rfl
      | advice column rotation =>
          rfl
      | «instance» column rotation =>
          rfl
  | const value =>
      rfl
  | add left right ihLeft ihRight =>
      simp only [Expression.SelectorFree] at hfree
      simp only [Expression.eval, ihLeft hfree.1, ihRight hfree.2]
  | mul left right ihLeft ihRight =>
      simp only [Expression.SelectorFree] at hfree
      simp only [Expression.eval, ihLeft hfree.1, ihRight hfree.2]

/--
At one enabled lookup's input row, selector substitution agrees with the
operation's zero/one selector valuation on every input expression.

This deliberately does not require the two valuations to agree on unrelated
selectors. A gate selector can legitimately be active on the same absolute row
without occurring in this lookup's inputs.
-/
def EnabledLookup.InputSelectorValuesRealized
    (top : TopLevelCircuit Fp Config PublicInput)
    (environment : Environment Fp) (lookup : EnabledLookup Fp) : Prop :=
  ∀ expression ∈ lookup.argument.inputs,
    expression.eval
        (substValuation top.selectorMap.lookup
          (Query.eval environment (fun _ => 0)
            (top.placement lookup.region + lookup.row))) =
      expression.eval
        (Query.eval environment lookup.selectorValue
          (top.placement lookup.region + lookup.row))

namespace EnabledLookup.SelectorProjection

/--
Exact selector values at the activation row, together with selector-free table
expressions, supply the full lookup selector-projection boundary.
-/
theorem ofInputSelectorValues
    (environment : Environment Fp)
    (lookup : EnabledLookup Fp)
    (realized :
      lookup.InputSelectorValuesRealized top environment)
    (tablesFree :
      lookup.argument.tables.Forall Expression.SelectorFree) :
    lookup.SelectorProjection top environment := by
  constructor
  · unfold EnabledLookup.inputValues
    apply List.map_congr_left
    intro expression hexpression
    exact realized expression hexpression
  · intro row hrow
    unfold EnabledLookup.tableValues
    apply List.map_congr_left
    intro expression hexpression
    exact
      Expression.eval_substValuation_eq_queryEval_of_selectorFree
        top.selectorMap environment lookup.selectorValue row expression
        (List.forall_iff_forall_mem.mp tablesFree expression hexpression)

end EnabledLookup.SelectorProjection

namespace TopLevelGateCoherence

/-- The resolver feeds interpret the complete circuit-derived pinned query state. -/
theorem resolverInterpretsPinned
    (coherence : TopLevelGateCoherence top pp urs)
    (poly : CommitmentId → Polynomial Fp)
    (proofIndex : Fin (pp.mergeDerived top).numProofs)
    (usableRows row : ℕ) :
    Interprets
      (pinnedQueryState
        (PinnedConstraintSystem.derive
          top.constraintSystem top.selectorMap))
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
      Nat.le_of_lt_succ (by
        simpa using coherence.domainExponent_lt)
    exact
      (Zcash.Arithmetic.omegaOf_isPrimitiveRoot
        top.domainExponent hk).isUnit (by positivity) |>.ne_zero
  exact resolverQueryFeeds_interpret
    (top.toVerifierKey pp urs) poly proofIndex usableRows
    (fun _ => 0) row homega
    (pinnedQueryState
      (PinnedConstraintSystem.derive
        top.constraintSystem top.selectorMap))
    (by rfl) (by rfl) (by rfl)
    coherence.adviceQueryCount
    coherence.fixedQueryCount
    coherence.instanceQueryCount

end TopLevelGateCoherence

@[simp] theorem toVerifierKey_lookupInputExprs
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS G)
    (lookup : Fin (pp.mergeDerived top).numLookups) :
    (top.toVerifierKey pp urs).lookupInputExprs lookup =
      ((PinnedConstraintSystem.derive
          top.constraintSystem top.selectorMap).lookupInputExprs.getD
        lookup.val []).map RichExpression.toExpr := by
  rfl

@[simp] theorem toVerifierKey_lookupTableExprs
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS G)
    (lookup : Fin (pp.mergeDerived top).numLookups) :
    (top.toVerifierKey pp urs).lookupTableExprs lookup =
      ((PinnedConstraintSystem.derive
          top.constraintSystem top.selectorMap).lookupTableExprs.getD
        lookup.val []).map RichExpression.toExpr := by
  rfl

@[simp] theorem toVerifierKey_n
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS G) :
    (top.toVerifierKey pp urs).n =
      2 ^ top.domainExponent := by
  rfl

@[simp] theorem toVerifierKey_blindingFactors
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS G) :
    (top.toVerifierKey pp urs).blindingFactors =
      top.blindingFactors := by
  rfl

/-- Mapping a projected lookup tuple into `Expr` does not change its evaluations. -/
theorem map_eval_toExpr
    (fixed advice instanceFeed : ℕ → Fp)
    (expressions : List (RichExpression Fp)) :
    (expressions.map RichExpression.toExpr).map
        (Expr.eval fixed advice instanceFeed) =
      expressions.map
        (RichExpression.eval fixed advice instanceFeed) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro expression _
  exact RichExpression.eval_toExpr
    fixed advice instanceFeed expression

namespace TopLevelLookupCoherence

/-- Selector-free lookup tables are covered by every compression map. -/
theorem tablesCovered
    (coherence : TopLevelLookupCoherence top)
    (argument : LookupArgument Fp)
    (hargument : argument ∈ top.constraintSystem.lookups)
    (expression : Expression Fp Query)
    (hexpression : expression ∈ argument.tables) :
    expression.selectorsCovered
      (fun selector =>
        (top.selectorMap.lookup selector).isSome) = true :=
  Expression.selectorsCovered_of_selectorFree
    (fun selector =>
      (top.selectorMap.lookup selector).isSome)
    expression
    (List.forall_iff_forall_mem.mp
      (coherence.tablesFree argument hargument)
      expression hexpression)

/--
The circuit-derived verifying key's selected lookup tuples evaluate like the
enabled Clean lookup's concrete input and table tuples.
-/
theorem projectedValues
    (coherence : TopLevelLookupCoherence top)
    (gateCoherence : TopLevelGateCoherence top pp urs)
    (poly : CommitmentId → Polynomial Fp)
    (proofIndex : Fin (pp.mergeDerived top).numProofs)
    (lookup : EnabledLookup Fp)
    (henabled :
      lookup ∈ operationEnabledLookups (top.operations) 0)
    (selectors :
      lookup.SelectorProjection top
        (resolverEnvironment
          (top.toVerifierKey pp urs) poly proofIndex
          (top.usableRowsAt top.domainExponent))) :
    let route := lookup.topLevelRoute
      (top := top) (pp := pp) henabled
    let environment :=
      resolverEnvironment
        (top.toVerifierKey pp urs) poly proofIndex
        (top.usableRowsAt top.domainExponent)
    (((top.toVerifierKey pp urs).lookupInputExprs route.index).map
        (Expr.eval
          (fun query =>
            (fixedQueryFeedOfResolver
              (top.toVerifierKey pp urs) poly query).eval
              ((top.toVerifierKey pp urs).omega ^
                (top.placement lookup.region + lookup.row)))
          (fun query =>
            (adviceQueryFeedOfResolver
              (top.toVerifierKey pp urs) poly proofIndex query).eval
              ((top.toVerifierKey pp urs).omega ^
                (top.placement lookup.region + lookup.row)))
          (fun query =>
            (instanceQueryFeedOfResolver
              (top.toVerifierKey pp urs) poly proofIndex query).eval
              ((top.toVerifierKey pp urs).omega ^
                (top.placement lookup.region + lookup.row)))) =
      lookup.inputValues top.placement environment) ∧
    (∀ row < environment.usableRows,
      ((top.toVerifierKey pp urs).lookupTableExprs route.index).map
          (Expr.eval
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
                ((top.toVerifierKey pp urs).omega ^ row))) =
        lookup.tableValues environment row) := by
  dsimp only
  let route :=
    lookup.topLevelRoute (top := top) (pp := pp) henabled
  have hrouteMem :
      top.constraintSystem.lookups[route.index.val] ∈
        top.constraintSystem.lookups :=
    List.getElem_mem ..
  have hinputCoverage :=
    coherence.inputsCovered
      top.constraintSystem.lookups[route.index.val]
      hrouteMem
  have htableCoverage :=
    coherence.tablesCovered
      top.constraintSystem.lookups[route.index.val]
      hrouteMem
  have projectAt (row : ℕ) :=
    PinnedConstraintSystem.derive_lookup_eval
      top.constraintSystem top.selectorMap
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
          (top.toVerifierKey pp urs) poly proofIndex
          (top.usableRowsAt top.domainExponent))
        (fun _ => 0) row)
      route.index.val route.index.isLt
      hinputCoverage htableCoverage
      (gateCoherence.resolverInterpretsPinned
        poly proofIndex
        (top.usableRowsAt top.domainExponent) row)
  have inputProjected :=
    (projectAt
      (top.placement lookup.region + lookup.row)).1
  have tableProjected (row : ℕ) :=
    (projectAt row).2
  have hargument := route.argument
  have inputProjected' :=
    inputProjected.trans
      (congrArg
        (fun argument : LookupArgument Fp =>
          argument.inputs.map
            (Expression.eval
              (substValuation top.selectorMap.lookup
                (Query.eval
                  (resolverEnvironment
                    (top.toVerifierKey pp urs) poly proofIndex
                    (top.usableRowsAt top.domainExponent))
                  (fun _ => 0)
                  (top.placement lookup.region + lookup.row)))))
        hargument)
  constructor
  · rw [← selectors.input]
    rw [toVerifierKey_lookupInputExprs, map_eval_toExpr]
    simpa only [route, Nat.cast_add] using
      inputProjected'
  · intro row hrow
    have tableProjectedRow :=
      (tableProjected row).trans
        (congrArg
          (fun argument : LookupArgument Fp =>
            argument.tables.map
              (Expression.eval
                (substValuation top.selectorMap.lookup
                  (Query.eval
                    (resolverEnvironment
                      (top.toVerifierKey pp urs) poly proofIndex
                      (top.usableRowsAt top.domainExponent))
                    (fun _ => 0) row))))
          hargument)
    rw [← selectors.table row hrow]
    rw [toVerifierKey_lookupTableExprs, map_eval_toExpr]
    simpa only [route] using tableProjectedRow

/--
The resolver's compressed input and table polynomials evaluate to the concrete
Clean tuples compressed with the transcript challenge.
-/
theorem projectedPolynomialValues
    (coherence : TopLevelLookupCoherence top)
    (gateCoherence : TopLevelGateCoherence top pp urs)
    (ch : Challenges (pp.mergeDerived top).k Fp)
    (poly : CommitmentId → Polynomial Fp)
    (proofIndex : Fin (pp.mergeDerived top).numProofs)
    (lookup : EnabledLookup Fp)
    (henabled :
      lookup ∈ operationEnabledLookups (top.operations) 0)
    (selectors :
      lookup.SelectorProjection top
        (resolverEnvironment
          (top.toVerifierKey pp urs) poly proofIndex
          (top.usableRowsAt top.domainExponent))) :
    let route := lookup.topLevelRoute
      (top := top) (pp := pp) henabled
    let environment :=
      resolverEnvironment
        (top.toVerifierKey pp urs) poly proofIndex
        (top.usableRowsAt top.domainExponent)
    (lookupInputPolyOfResolver
        (top.toVerifierKey pp urs) ch poly proofIndex route.index).eval
        ((top.toVerifierKey pp urs).omega ^
          (top.placement lookup.region + lookup.row)) =
      compressValues ch.theta
        (lookup.inputValues top.placement environment) ∧
    (∀ row < environment.usableRows,
      (lookupTablePolyOfResolver
          (top.toVerifierKey pp urs) ch poly proofIndex route.index).eval
          ((top.toVerifierKey pp urs).omega ^ row) =
        compressValues ch.theta
          (lookup.tableValues environment row)) := by
  dsimp only
  let route :=
    lookup.topLevelRoute (top := top) (pp := pp) henabled
  have projected :=
    coherence.projectedValues gateCoherence poly proofIndex
      lookup henabled selectors
  constructor
  · rw [lookupInputPolyOfResolver,
      compress_eval_eq_foldPoly,
      eval_foldPoly_eq_compressValues]
    change compressValues ch.theta
        (((top.toVerifierKey pp urs).lookupInputExprs
          route.index).map _) =
      compressValues ch.theta
        (lookup.inputValues top.placement
          (resolverEnvironment
            (top.toVerifierKey pp urs) poly proofIndex
            (top.usableRowsAt top.domainExponent)))
    exact congrArg (compressValues ch.theta) projected.1
  · intro row hrow
    rw [lookupTablePolyOfResolver,
      compress_eval_eq_foldPoly,
      eval_foldPoly_eq_compressValues]
    change compressValues ch.theta
        (((top.toVerifierKey pp urs).lookupTableExprs
          route.index).map _) =
      compressValues ch.theta
        (lookup.tableValues
          (resolverEnvironment
            (top.toVerifierKey pp urs) poly proofIndex
            (top.usableRowsAt top.domainExponent)) row)
    exact congrArg (compressValues ch.theta)
      (projected.2 row hrow)

/--
Full constraint satisfaction constructs the deployed lookup witness once the
static projection, exact selector values, row fit, and explicitly priced
challenge exclusions are supplied.
-/
noncomputable def deployedWitness
    (coherence : TopLevelLookupCoherence top)
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
          (top.toVerifierKey pp urs) ch poly
          hblinding)
        (top.toVerifierKey pp urs).n)
    (hrows : Function.Injective
      fun row : Fin (top.toVerifierKey pp urs).n =>
        (top.toVerifierKey pp urs).omega ^ (row : ℕ))
    (hroot :
      (top.toVerifierKey pp urs).omega ^
        (top.toVerifierKey pp urs).n = 1)
    (lookup : EnabledLookup Fp)
    (henabled :
      lookup ∈ operationEnabledLookups (top.operations) 0)
    (selectors :
      lookup.SelectorProjection top
        (resolverEnvironment
          (top.toVerifierKey pp urs) poly proofIndex
          (top.usableRowsAt top.domainExponent)))
    (activationRow :
      top.placement lookup.region + lookup.row <
        top.usableRowsAt top.domainExponent)
    (resolverGood :
      let route := lookup.topLevelRoute
        (top := top) (pp := pp) henabled
      ResolverLookupGoodChallenges
        (top.toVerifierKey pp urs) ch poly proofIndex route.index
        ((top.toVerifierKey pp urs).n -
          (top.toVerifierKey pp urs).blindingFactors - 2))
    (thetaGood :
      ch.theta ∉ lookup.thetaBadSet top.placement
        (resolverEnvironment
          (top.toVerifierKey pp urs) poly proofIndex
          (top.usableRowsAt top.domainExponent))) :
    lookup.DeployedWitness top.placement
      (resolverEnvironment
        (top.toVerifierKey pp urs) poly proofIndex
        (top.usableRowsAt top.domainExponent))
      ch.theta := by
  let vk := top.toVerifierKey pp urs
  let environment :=
    resolverEnvironment vk poly proofIndex
      (top.usableRowsAt top.domainExponent)
  let route :=
    lookup.topLevelRoute (top := top) (pp := pp) henabled
  let u := vk.n - vk.blindingFactors - 2
  have husable :
      vk.blindingFactors + 1 < vk.n := by
    have hpositive :
        0 < top.usableRowsAt top.domainExponent :=
      (Nat.zero_le
        (top.placement lookup.region + lookup.row)).trans_lt
        activationRow
    change top.blindingFactors + 1 < 2 ^ top.domainExponent
    unfold TopLevelCircuit.usableRowsAt at hpositive
    omega
  have husableRows : environment.usableRows = u + 1 := by
    change 2 ^ top.domainExponent -
        top.blindingFactors - 1 =
      vk.n - vk.blindingFactors - 2 + 1
    have hvkn : vk.n = 2 ^ top.domainExponent := by
      simp only [vk, toVerifierKey_n]
    have hvkBlinding :
        vk.blindingFactors = top.blindingFactors := by
      simp only [vk, toVerifierKey_blindingFactors]
    rw [hvkn, hvkBlinding]
    omega
  have projected :=
    coherence.projectedPolynomialValues gateCoherence ch poly
      proofIndex lookup henabled selectors
  have harity' :
      lookup.argument.inputs.length =
        lookup.argument.tables.length :=
    coherence.arity lookup.argument
      (OperationsKeygenCoherent.lookup top.keygenCoherent henabled)
  have tupleLength : ∀ row < environment.usableRows,
      (lookup.inputValues top.placement environment).length =
        (lookup.tableValues environment row).length := by
    intro row _
    unfold EnabledLookup.inputValues EnabledLookup.tableValues
    simpa only [List.length_map] using harity'
  let selectorPolynomials :=
    canonicalLagrangePolynomials vk.omega
      (by simpa only [vk] using hblinding)
  have domain :
      ResolverLookupDomain vk selectorPolynomials.1
        selectorPolynomials.2.1 selectorPolynomials.2.2
        vk.n u := by
    simpa [vk, u, selectorPolynomials,
      canonicalConstraintModelOfPermutationResolver,
      constraintModelOfPermutationResolver,
      constraintModelOfResolver] using
      (ResolverLookupDomain.ofCanonicalConstraintModel
        vk ch poly husable hrows hroot)
  have satisfaction' :
      ConstraintSatisfaction
        (constraintModelOfResolver vk ch poly
          (permutationSetsOfResolver vk poly)
          (permutationChunksOfResolver vk poly)
          selectorPolynomials.1
          selectorPolynomials.2.1
          selectorPolynomials.2.2) vk.n := by
    simpa [vk, selectorPolynomials,
      canonicalConstraintModelOfPermutationResolver,
      constraintModelOfPermutationResolver] using
      satisfaction
  have scalarSubset :
      ∀ row : Fin (u + 1), ∃ tableRow : Fin (u + 1),
        lookupColumnRows vk.omega
            (lookupInputPolyOfResolver
              vk ch poly proofIndex route.index)
            (u + 1) row =
          lookupColumnRows vk.omega
            (lookupTablePolyOfResolver
              vk ch poly proofIndex route.index)
            (u + 1) tableRow := by
    exact satisfaction'.resolverLookupSubset
      vk ch poly
      (permutationSetsOfResolver vk poly)
      (permutationChunksOfResolver vk poly)
      selectorPolynomials.1 selectorPolynomials.2.1
      selectorPolynomials.2.2 proofIndex route.index
      domain resolverGood
  exact
    { omega := vk.omega
      input :=
        lookupInputPolyOfResolver vk ch poly
          proofIndex route.index
      table :=
        lookupTablePolyOfResolver vk ch poly
          proofIndex route.index
      u := u
      usableRows := husableRows
      activationRow := by
        rw [← husableRows]
        exact activationRow
      inputEval := projected.1.symm
      tableEval := fun row hrow =>
        (projected.2 row hrow).symm
      tupleLength := tupleLength
      scalarSubset := scalarSubset
      thetaGood := thetaGood }

/--
The proof-dependent conditions shared by the deployed witnesses for every lookup
activation in one proof. Static configured-lookup coverage, arity, and activation-row
fit are derived from the top-level circuit; this record contains only selector- and
challenge-dependent facts.
-/
structure TopLevelLookupWitnessConditions
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS G)
    (ch : Challenges (pp.mergeDerived top).k Fp)
    (poly : CommitmentId → Polynomial Fp)
    (proofIndex : Fin (pp.mergeDerived top).numProofs) : Prop where
  inputSelectorValues : ∀ lookup
      (_henabled :
        lookup ∈ operationEnabledLookups (top.operations) 0),
    lookup.InputSelectorValuesRealized top
      (resolverEnvironment
        (top.toVerifierKey pp urs) poly proofIndex
        (top.usableRowsAt top.domainExponent))
  resolverGood : ∀ lookup
      (henabled :
        lookup ∈ operationEnabledLookups (top.operations) 0),
    ResolverLookupGoodChallenges
      (top.toVerifierKey pp urs) ch poly proofIndex
      (lookup.topLevelRoute
        (top := top) (pp := pp) henabled).index
      ((top.toVerifierKey pp urs).n -
        (top.toVerifierKey pp urs).blindingFactors - 2)
  thetaGood : ∀ lookup
      (_henabled :
        lookup ∈ operationEnabledLookups (top.operations) 0),
    ch.theta ∉ lookup.thetaBadSet top.placement
      (resolverEnvironment
        (top.toVerifierKey pp urs) poly proofIndex
        (top.usableRowsAt top.domainExponent))

/--
Index every lookup activation in every proof of a top-level bundle. The activation
list is shared by all proofs, while the resolver environment is proof-indexed.
-/
abbrev TopLevelLookupActivationIndex
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) :=
  Fin (pp.mergeDerived top).numProofs ×
    Fin (operationEnabledLookups (top.operations) 0).length

/--
The exact bundle-wide `θ` collision surface for a top-level circuit. A single
transcript challenge is shared by every proof and every enabled lookup activation,
so the event must be unioned across both indices.
-/
noncomputable def allTopLevelLookupThetaBadSet
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → Polynomial Fp) : Finset Fp :=
  enabledLookupThetaBadSetFamily
    (ι := TopLevelLookupActivationIndex top pp)
    (fun _ => top.placement)
    (fun index =>
      resolverEnvironment
        (top.toVerifierKey pp urs) poly index.1
        (top.usableRowsAt top.domainExponent))
    (fun index =>
      (operationEnabledLookups (top.operations) 0).get index.2)

/-- The row-by-arity root budget for the top-level bundle's `θ` surface. -/
noncomputable def topLevelLookupThetaBudget
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → Polynomial Fp) : ℕ :=
  ∑ index : TopLevelLookupActivationIndex top pp,
    (resolverEnvironment
      (top.toVerifierKey pp urs) poly index.1
      (top.usableRowsAt top.domainExponent)).usableRows *
    (EnabledLookup.inputValues
      top.placement
      (resolverEnvironment
        (top.toVerifierKey pp urs) poly index.1
        (top.usableRowsAt top.domainExponent))
      ((operationEnabledLookups
        (top.operations) 0).get index.2)).length

/--
The bundle-wide top-level `θ` surface has exactly the generic
`usableRows × tupleArity` union-bound budget, summed over every proof and
activation.
-/
theorem uniformChallenge_allTopLevelLookupThetaBadSet
    (coherence : TopLevelLookupCoherence top)
    (poly : CommitmentId → Polynomial Fp) :
    uniformChallenge.toOuterMeasure
        (allTopLevelLookupThetaBadSet top pp urs poly)
      ≤ (topLevelLookupThetaBudget top pp urs poly : ENNReal) /
        (Fintype.card Fp : ENNReal) := by
  unfold allTopLevelLookupThetaBadSet topLevelLookupThetaBudget
  apply uniformChallenge_enabledLookupThetaBadSetFamily
  intro index row _hrow
  let lookup :=
    (operationEnabledLookups (top.operations) 0).get index.2
  have henabled :
      lookup ∈ operationEnabledLookups (top.operations) 0 :=
    List.get_mem ..
  have hargument :
      lookup.argument ∈ top.constraintSystem.lookups :=
    OperationsKeygenCoherent.lookup top.keygenCoherent henabled
  have harity := coherence.arity lookup.argument hargument
  unfold EnabledLookup.inputValues EnabledLookup.tableValues
  simpa only [List.length_map] using harity

/--
The three lookup challenge exclusions at their natural bundle-wide granularity.
These are transcript/probability-layer facts, independent of fixed-column selector
realization.
-/
structure TopLevelLookupChallengeExclusions
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS G)
    (ch : Challenges (pp.mergeDerived top).k Fp)
    (poly : CommitmentId → Polynomial Fp) : Prop where
  gamma :
    ch.gamma ∉ allResolverLookupGammaBadSet
      (top.toVerifierKey pp urs) ch poly
      ((top.toVerifierKey pp urs).n -
        (top.toVerifierKey pp urs).blindingFactors - 2)
  beta :
    ch.beta ∉ allResolverLookupBetaBadSet
      (top.toVerifierKey pp urs) ch poly
      ((top.toVerifierKey pp urs).n -
        (top.toVerifierKey pp urs).blindingFactors - 2)
  theta :
    ch.theta ∉ allTopLevelLookupThetaBadSet top pp urs poly

/--
Bundle-wide challenge exclusions and exact selector realization construct the
per-proof conditions consumed by the deployed lookup witnesses.
-/
noncomputable def TopLevelLookupWitnessConditions.ofChallengeExclusions
    (ch : Challenges (pp.mergeDerived top).k Fp)
    (poly : CommitmentId → Polynomial Fp)
    (proofIndex : Fin (pp.mergeDerived top).numProofs)
    (inputSelectorValues : ∀ lookup
      (_henabled :
        lookup ∈ operationEnabledLookups (top.operations) 0),
      lookup.InputSelectorValuesRealized top
        (resolverEnvironment
          (top.toVerifierKey pp urs) poly proofIndex
          (top.usableRowsAt top.domainExponent)))
    (exclusions :
      TopLevelLookupChallengeExclusions top pp urs ch poly) :
    TopLevelLookupWitnessConditions top pp urs ch poly proofIndex := by
  refine
    { inputSelectorValues := inputSelectorValues
      resolverGood := ?_
      thetaGood := ?_ }
  · intro lookup henabled
    exact resolverLookupGoodChallenges_of_not_mem
      (top.toVerifierKey pp urs) ch poly
      ((top.toVerifierKey pp urs).n -
        (top.toVerifierKey pp urs).blindingFactors - 2)
      exclusions.gamma exclusions.beta proofIndex
      (lookup.topLevelRoute
        (top := top) (pp := pp) henabled).index
  · intro lookup henabled
    obtain ⟨index, hindex, hlookup⟩ :=
      List.mem_iff_getElem.mp henabled
    have hfamily :=
      (not_mem_enabledLookupThetaBadSetFamily_iff
        (ι := TopLevelLookupActivationIndex top pp)
        (fun _ => top.placement)
        (fun index =>
          resolverEnvironment
            (top.toVerifierKey pp urs) poly index.1
            (top.usableRowsAt top.domainExponent))
        (fun index =>
          (operationEnabledLookups (top.operations) 0).get index.2)
        ch.theta).mp exclusions.theta
        (proofIndex, ⟨index, hindex⟩)
    simpa [allTopLevelLookupThetaBadSet, hlookup] using hfamily

/-- Construct the complete deployed-witness family for one top-level proof. -/
noncomputable def deployedWitnesses
    (coherence : TopLevelLookupCoherence top)
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
    (conditions :
      TopLevelLookupWitnessConditions top pp urs ch poly proofIndex) :
    ∀ lookup ∈ operationEnabledLookups (top.operations) 0,
      lookup.DeployedWitness top.placement
        (resolverEnvironment
          (top.toVerifierKey pp urs) poly proofIndex
          (top.usableRowsAt top.domainExponent))
        ch.theta := by
  intro lookup henabled
  let environment :=
    resolverEnvironment
      (top.toVerifierKey pp urs) poly proofIndex
      (top.usableRowsAt top.domainExponent)
  have hargument :
      lookup.argument ∈ top.constraintSystem.lookups :=
    OperationsKeygenCoherent.lookup top.keygenCoherent henabled
  have selectorProjection :
      lookup.SelectorProjection top environment :=
    EnabledLookup.SelectorProjection.ofInputSelectorValues
      environment lookup
      (conditions.inputSelectorValues lookup henabled)
      (coherence.tablesFree lookup.argument hargument)
  exact coherence.deployedWitness gateCoherence ch poly proofIndex
    hblinding satisfaction hrows hroot lookup henabled
    selectorProjection
    (lookup.activationRow_lt_usableRows henabled)
    (conditions.resolverGood lookup henabled)
    (conditions.thetaGood lookup henabled)

/-- The deployed family discharges Clean's complete lookup constraint family. -/
theorem constraints
    (coherence : TopLevelLookupCoherence top)
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
    (conditions :
      TopLevelLookupWitnessConditions top pp urs ch poly proofIndex) :
    CircuitConstraintFamily.constraints .lookup top.placement
      (resolverEnvironment
        (top.toVerifierKey pp urs) poly proofIndex
        (top.usableRowsAt top.domainExponent))
      (top.operations) 0 := by
  apply lookup_constraints_of_deployed_witnesses
  exact coherence.deployedWitnesses gateCoherence ch poly proofIndex
    hblinding satisfaction hrows hroot conditions

end TopLevelLookupCoherence

end Zcash.Snark
