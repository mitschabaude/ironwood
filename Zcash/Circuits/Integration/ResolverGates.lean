import Zcash.Snark.Keygen.Pipeline
import Clean.Halo2.Keygen.GateProjection
import Zcash.Circuits.Integration.OperationGates
import Zcash.Circuits.Integration.ResolverQueryEnvironment
import Zcash.Circuits.Integration.TopLevelCoherence

/-!
# Resolver-backed gate witnesses

This module connects one configured-and-enabled Clean gate constraint to the
corresponding polynomial in the deployed resolver model.  It is generic in the
formal circuit's constraint system, selector-compression map, verifying key, and
polynomial resolver.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (scalarFieldOrder)

open Halo2 Polynomial

set_option maxHeartbeats 20000

/-- Every selector-compression entry uses a valid, scalar-field-distinct root. -/
def SelectorRootsWellFormed (map : SelCompressMap) : Prop :=
  ∀ {selector : ℕ} {compressed : SelCompress},
    map.lookup selector = some compressed →
      1 ≤ compressed.assignedRoot ∧
      compressed.assignedRoot ≤ compressed.combinationLen ∧
      compressed.combinationLen < scalarFieldOrder

/--
The packed fixed columns realize the compression map on every selector activation
derived from synthesis and placement.
-/
def SelectorActivationsRealized
    (map : SelCompressMap) (activationRows : List (ℕ × ℕ))
    (environment : Environment Fp) : Prop :=
  ∀ {selector row : ℕ} {compressed : SelCompress},
    (selector, row) ∈ activationRows →
    map.lookup selector = some compressed →
      environment.fixed ⟨compressed.packedCol⟩ row =
        (compressed.assignedRoot : Fp)

/--
The selector-compression replacement is nonzero when its packed fixed cell holds
its assigned root.  The only field-specific premise is that the combination length
is below the scalar-field modulus, making its small natural roots injective in `Fp`.
-/
theorem selectorScale_ne_zero_of_root
    (compressed : SelCompress) (valuation : Query → Fp)
    (hvalue : valuation (.fixed ⟨compressed.packedCol⟩ 0) =
      (compressed.assignedRoot : Fp))
    (hpositive : 1 ≤ compressed.assignedRoot)
    (hrootBound :
      compressed.assignedRoot ≤ compressed.combinationLen)
    (hlengthBound :
      compressed.combinationLen < scalarFieldOrder) :
    (selReplacement compressed).eval valuation ≠ 0 := by
  apply selReplacement_eval_of_root compressed valuation
    hvalue hpositive hrootBound
  intro left right hleft hright heq
  have hleftOrder : left < scalarFieldOrder := by
    omega
  have hrightOrder : right < scalarFieldOrder := by
    omega
  have hvals := congrArg
    (ZMod.val (n := scalarFieldOrder)) heq
  simpa [ZMod.val_cast_of_lt hleftOrder,
    ZMod.val_cast_of_lt hrightOrder] using hvals

/-- Environment spelling of `selectorScale_ne_zero_of_root`. -/
theorem selectorScale_ne_zero_of_environment
    (compressed : SelCompress) (environment : Environment Fp)
    (selectors : ℕ → Fp) (row : ℕ)
    (hvalue : environment.fixed ⟨compressed.packedCol⟩ row =
      (compressed.assignedRoot : Fp))
    (hpositive : 1 ≤ compressed.assignedRoot)
    (hrootBound :
      compressed.assignedRoot ≤ compressed.combinationLen)
    (hlengthBound :
      compressed.combinationLen < scalarFieldOrder) :
    (selReplacement compressed).eval
      (Query.eval environment selectors row) ≠ 0 := by
  apply selectorScale_ne_zero_of_root compressed
    (Query.eval environment selectors row)
    _ hpositive hrootBound hlengthBound
  simpa [Query.eval] using hvalue

/--
Circuit-derived activation placement and packed fixed data make the selector scale
nonzero at every extracted enabled gate.
-/
theorem selectorScale_ne_zero_of_enabledGate
    (map : SelCompressMap) (starts : List ℕ)
    (operations : Operations Fp) (i : RegionIndex)
    (environment : Environment Fp) (selectors : ℕ → Fp)
    (hroots : SelectorRootsWellFormed map)
    (hfixed : SelectorActivationsRealized map
      (activations starts (indexedRegions operations i).1) environment)
    {enabled : EnabledGate Fp}
    (henabled : enabled ∈ operationEnabledGates operations i)
    {compressed : SelCompress}
    (hcompressed :
      map.lookup enabled.gate.selector.index = some compressed) :
    (selReplacement compressed).eval
      (Query.eval environment selectors
        (starts.getD enabled.region 0 + enabled.row)) ≠ 0 := by
  have hactivation :=
    mem_activations_of_mem_operationEnabledGate starts henabled
  have hvalue := hfixed hactivation hcompressed
  obtain ⟨hpositive, hrootBound, hlengthBound⟩ :=
    hroots hcompressed
  exact selectorScale_ne_zero_of_environment
    compressed environment selectors
    (starts.getD enabled.region 0 + enabled.row)
    hvalue hpositive hrootBound hlengthBound

/-- The polynomial obtained by evaluating one VK gate over the rotated resolver feeds. -/
noncomputable def resolverGatePolynomial
    {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G)
    (poly : CommitmentId → Polynomial Fp)
    (proofIndex : Fin shape.numProofs)
    (gateIndex : Fin vk.gates.length) : Polynomial Fp :=
  (vk.gates[gateIndex].map C).eval
    (fixedQueryFeedOfResolver vk poly)
    (adviceQueryFeedOfResolver vk poly proofIndex)
    (instanceQueryFeedOfResolver vk poly proofIndex)

/-- Polynomial evaluation commutes with lifting a verifier expression by `C`. -/
private theorem eval_map_C
    (fixed advice instanceFeed : ℕ → Polynomial Fp)
    (expression : Expr Fp) (x : Fp) :
    ((expression.map C).eval fixed advice instanceFeed).eval x =
      expression.eval
        (fun query => (fixed query).eval x)
        (fun query => (advice query).eval x)
        (fun query => (instanceFeed query).eval x) := by
  induction expression <;> simp_all [Expr.map, Expr.eval]

/-- Evaluating a lifted resolver gate is evaluation of the VK expression's feeds. -/
theorem resolverGatePolynomial_eval
    {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G)
    (poly : CommitmentId → Polynomial Fp)
    (proofIndex : Fin shape.numProofs)
    (gateIndex : Fin vk.gates.length) (x : Fp) :
    (resolverGatePolynomial vk poly proofIndex gateIndex).eval x =
      vk.gates[gateIndex].eval
        (fun query =>
          (fixedQueryFeedOfResolver vk poly query).eval x)
        (fun query =>
          (adviceQueryFeedOfResolver vk poly proofIndex query).eval x)
        (fun query =>
          (instanceQueryFeedOfResolver vk poly proofIndex query).eval x) := by
  exact eval_map_C
    (fixedQueryFeedOfResolver vk poly)
    (adviceQueryFeedOfResolver vk poly proofIndex)
    (instanceQueryFeedOfResolver vk poly proofIndex)
    vk.gates[gateIndex] x

/-- The selected lifted VK gate occurs in the resolver model's gate family. -/
theorem resolverGatePolynomial_mem
    {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G)
    (ch : Challenges shape.k Fp)
    (poly : CommitmentId → Polynomial Fp)
    (sets : Fin shape.numProofs → List (PermSetEval (Polynomial Fp)))
    (chunks : Fin shape.numProofs →
      List (PermSetEval (Polynomial Fp) ×
        List (Polynomial Fp × Polynomial Fp)))
    (l0 lLast lBlind : Polynomial Fp)
    (proofIndex : Fin shape.numProofs)
    (gateIndex : Fin vk.gates.length) :
    resolverGatePolynomial vk poly proofIndex gateIndex ∈
      (constraintModelOfResolver vk ch poly sets chunks
        l0 lLast lBlind).gateConstraints proofIndex := by
  rw [List.mem_iff_getElem]
  refine ⟨gateIndex, ?_, ?_⟩
  · simp [ConstraintPolyModel.gateConstraints,
      constraintModelOfResolver]
  · simp [ConstraintPolyModel.gateConstraints,
      constraintModelOfResolver, resolverGatePolynomial]

/--
One enabled Clean constraint produces its resolver-model polynomial witness.

The premises are exactly the static representation boundary:

* the VK gate list is the pinned derivation of `cs`;
* selector compression covers every configured gate;
* the rotated feeds interpret the derivation's query walk at this row;
* the packed selector's root-finding value is nonzero at the activation.

No circuit, placement algorithm, or concrete verification key is selected here.
-/
noncomputable def enabledGatePolynomialWitnessOfResolver
    {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G)
    (cs : ConstraintSystem Fp) (map : SelCompressMap)
    (ch : Challenges shape.k Fp)
    (poly : CommitmentId → Polynomial Fp)
    (sets : Fin shape.numProofs → List (PermSetEval (Polynomial Fp)))
    (chunks : Fin shape.numProofs →
      List (PermSetEval (Polynomial Fp) ×
        List (Polynomial Fp × Polynomial Fp)))
    (l0 lLast lBlind : Polynomial Fp)
    (proofIndex : Fin shape.numProofs)
    (place : RegionIndex → ℕ) (usableRows : ℕ)
    (enabled : EnabledGate Fp) (constraint : Constraint Fp)
    (hgate : enabled.gate ∈ cs.gates)
    (hconstraint : constraint ∈ enabled.gate.constraints)
    (hgates : vk.gates =
      (PinnedConstraintSystem.derive cs map).gates.map
        RichExpression.toExpr)
    (hcoverage : ∀ expression ∈ flatGates cs,
      expression.selectorsCovered
        (fun index => (map.lookup index).isSome) = true)
    (compressed : SelCompress)
    (hcompressed :
      map.lookup enabled.gate.selector.index = some compressed)
    (hinterpret : Interprets
      (eraseGates
        ((flatGates cs).map (substSelectorMap map.lookup))
        (queryWalkInit map cs)).2
      (fun query =>
        (fixedQueryFeedOfResolver vk poly query).eval
          (vk.omega ^ (place enabled.region + enabled.row)))
      (fun query =>
        (adviceQueryFeedOfResolver vk poly proofIndex query).eval
          (vk.omega ^ (place enabled.region + enabled.row)))
      (fun query =>
        (instanceQueryFeedOfResolver vk poly proofIndex query).eval
          (vk.omega ^ (place enabled.region + enabled.row)))
      (Query.eval
        (resolverEnvironment vk poly proofIndex usableRows)
        (fun _ => 0)
        (place enabled.region + enabled.row)))
    (hscale :
      (selReplacement compressed).eval
        (Query.eval
          (resolverEnvironment vk poly proofIndex usableRows)
          (fun _ => 0)
          (place enabled.region + enabled.row)) ≠ 0) :
    EnabledGate.PolynomialWitness
      (constraintModelOfResolver vk ch poly sets chunks
        l0 lLast lBlind)
      proofIndex vk.omega place
      (resolverEnvironment vk poly proofIndex usableRows)
      enabled constraint := by
  have hflat : constraint.poly ∈ flatGates cs := by
    rw [flatGates, List.mem_flatMap]
    exact ⟨enabled.gate, hgate,
      List.mem_map.mpr ⟨constraint, hconstraint, rfl⟩⟩
  let hindex := List.mem_iff_getElem.mp hflat
  let gateIndex := Classical.choose hindex
  let hindexData := Classical.choose_spec hindex
  let hgateIndex := Classical.choose hindexData
  have hsource := Classical.choose_spec hindexData
  have hgateLength :
      vk.gates.length = (flatGates cs).length := by
    have hlength := congrArg List.length hgates
    rw [List.length_map,
      PinnedConstraintSystem.derive_gates_length] at hlength
    exact hlength
  have hgateIndexVk : gateIndex < vk.gates.length := by
    omega
  let index : Fin vk.gates.length := ⟨gateIndex, hgateIndexVk⟩
  let witnessPolynomial :=
    resolverGatePolynomial vk poly proofIndex index
  let valuation :=
    Query.eval
      (resolverEnvironment vk poly proofIndex usableRows)
      (fun _ => 0)
      (place enabled.region + enabled.row)
  refine
    { polynomial := witnessPolynomial
      member := ?_
      zero_imp := ?_ }
  · exact resolverGatePolynomial_mem vk ch poly sets chunks
      l0 lLast lBlind proofIndex index
  · intro hzero
    rw [show witnessPolynomial =
      resolverGatePolynomial vk poly proofIndex index from rfl]
      at hzero
    rw [resolverGatePolynomial_eval] at hzero
    have hderived := vk.gates_eval_of_gates_eq
      cs map hgates
      (fun query =>
        (fixedQueryFeedOfResolver vk poly query).eval
          (vk.omega ^ (place enabled.region + enabled.row)))
      (fun query =>
        (adviceQueryFeedOfResolver vk poly proofIndex query).eval
          (vk.omega ^ (place enabled.region + enabled.row)))
      (fun query =>
        (instanceQueryFeedOfResolver vk poly proofIndex query).eval
          (vk.omega ^ (place enabled.region + enabled.row)))
      valuation hcoverage hinterpret
      gateIndex hgateIndexVk hgateIndex
    rw [hsource] at hderived
    apply Expression.eval_substSelectorMap_zero_imp_queryEval_zero
      map.lookup valuation
      (resolverEnvironment vk poly proofIndex usableRows)
      constraint.poly enabled.gate.selector compressed
      (place enabled.region + enabled.row)
      (enabled.gate.wellFormed constraint hconstraint)
      hcompressed hscale
      (by intros; rfl)
      (by intros; rfl)
      (by intros; rfl)
    rw [substSelectorMap_eval]
    exact hderived.symm.trans hzero

end Zcash.Snark
