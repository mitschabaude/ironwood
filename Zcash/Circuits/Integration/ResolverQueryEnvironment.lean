import Clean.Halo2.Keygen.Semantics
import Zcash.Snark.Soundness.Canonical.LookupInstantiation
import Zcash.Snark.Soundness.Canonical.PermutationInstantiation
import Zcash.Circuits.Integration.PolynomialEnvironment

/-!
# Resolver query feeds and Clean environments

Verifier expressions index query-layout entries.  Clean expressions name the same
queries as `(column, rotation)` pairs.  This module proves that the resolver-backed
rotated polynomial feeds and the canonical row environment interpret those two
representations identically on every evaluation-domain row.
-/

namespace Zcash.Snark

open Halo2 Polynomial

set_option maxHeartbeats 20000

/-- Decode a verifier permutation query reference back to the concrete Clean
column selected by its query-layout entry. -/
def permutationColumnAddress
    {shape : Shape} {F G : Type*}
    (vk : VerifyingKey shape F G) : ColumnRef → AnyColumn
  | .advice query =>
      ⟨.advice, (vk.adviceQueryLayout.getD query (0, 0)).1⟩
  | .fixed query =>
      ⟨.fixed, (vk.fixedQueryLayout.getD query (0, 0)).1⟩
  | .instance query =>
      ⟨.instance, (vk.instanceQueryLayout.getD query (0, 0)).1⟩

/--
The value polynomial selected by a coherent permutation query reference reads
the same natural-numbered row as its decoded Clean column.
-/
theorem permutationColumnPolynomial_eval_environment
    {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G)
    (poly : CommitmentId → Polynomial Fp)
    (proofIndex : Fin shape.numProofs)
    (usableRows row : ℕ) (reference : ColumnRef)
    (hcoherent : PermutationColumnRef.Coherent vk reference) :
    (permutationColumnPolynomialOfResolver
        vk poly proofIndex reference).eval (vk.omega ^ row) =
      (resolverEnvironment vk poly proofIndex usableRows).get
        (permutationColumnAddress vk reference) (row : ℤ) := by
  cases reference with
  | advice query =>
      rcases hcoherent with ⟨hcount, -, -⟩
      simp [permutationColumnPolynomialOfResolver, ColumnRef.resolve, finFn,
        permutationColumnCommitmentId, permutationColumnAddress,
        resolverEnvironment, polynomialEnvironment, hcount]
  | fixed query =>
      rcases hcoherent with ⟨hcount, -, -⟩
      simp [permutationColumnPolynomialOfResolver, ColumnRef.resolve, finFn,
        permutationColumnCommitmentId, permutationColumnAddress,
        resolverEnvironment, polynomialEnvironment, hcount]
  | «instance» query =>
      rcases hcoherent with ⟨hcount, -, -⟩
      simp [permutationColumnPolynomialOfResolver, ColumnRef.resolve, finFn,
        permutationColumnCommitmentId, permutationColumnAddress,
        resolverEnvironment, polynomialEnvironment, hcount]

/--
One resolver permutation chunk value is the canonical environment read at the
concrete column decoded from that chunk's query reference.
-/
theorem chunkRowValue_eq_resolverEnvironment
    {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G)
    (poly : CommitmentId → Polynomial Fp)
    (proofIndex : Fin shape.numProofs)
    (usableRows chunk row column : ℕ)
    (hcolumn :
      column < (vk.permutationChunks.getD chunk []).length)
    (hcoherent :
      PermutationColumnRef.Coherent vk
        ((vk.permutationChunks.getD chunk [])[column]).1) :
    chunkRowValue vk.omega
        (permutationChunkPairsOfResolver vk poly proofIndex)
        chunk row column =
      (resolverEnvironment vk poly proofIndex usableRows).get
        (permutationColumnAddress vk
          ((vk.permutationChunks.getD chunk [])[column]).1)
        (row : ℤ) := by
  rw [chunkRowValue, rowValue]
  have hpairs :
      column <
        (permutationChunkPairsOfResolver
          vk poly proofIndex chunk).length := by
    simpa [permutationChunkPairsOfResolver] using hcolumn
  rw [List.getD_eq_getElem _ _ hpairs]
  simp only [permutationChunkPairsOfResolver, List.getElem_map]
  exact permutationColumnPolynomial_eval_environment
    vk poly proofIndex usableRows row
      ((vk.permutationChunks.getD chunk [])[column]).1 hcoherent

/-- Erasing one lookup only extends the incoming query state. -/
theorem eraseLookup_extends
    {F : Type} [Field F] [DecidableEq F]
    (argument : LookupArgument F) (state : QueryState) :
    (eraseLookup argument state).2.Extends state := by
  unfold eraseLookup
  generalize hinputs :
    eraseGates argument.inputs state = inputResult
  rcases inputResult with ⟨inputs, inputState⟩
  generalize htables :
    eraseGates argument.tables inputState = tableResult
  rcases tableResult with ⟨tables, tableState⟩
  have hinputExtends := eraseGates_extends argument.inputs state
  rw [hinputs] at hinputExtends
  have htableExtends :=
    eraseGates_extends argument.tables inputState
  rw [htables] at htableExtends
  simpa only [htables] using
    QueryState.Extends.trans hinputExtends htableExtends

/-- Erasing the complete lookup list only extends its incoming query state. -/
theorem eraseLookups_extends
    {F : Type} [Field F] [DecidableEq F]
    (arguments : List (LookupArgument F)) (state : QueryState) :
    (eraseLookups arguments state).2.Extends state := by
  induction arguments generalizing state with
  | nil =>
      exact QueryState.Extends.refl state
  | cons argument rest ih =>
      generalize hlookup :
        eraseLookup argument state = lookupResult
      rcases lookupResult with ⟨lookup, lookupState⟩
      rw [eraseLookups, hlookup]
      exact QueryState.Extends.trans
        (by
          have h := eraseLookup_extends argument state
          rw [hlookup] at h
          exact h)
        (ih lookupState)

/-- Repackage a pinned constraint system's three query layouts as a query state. -/
def pinnedQueryState
    {F : Type} (pinned : PinnedConstraintSystem F) : QueryState where
  advice := pinned.adviceQueryLayout.toArray
  fixed := pinned.fixedQueryLayout.toArray
  inst := pinned.instanceQueryLayout.toArray

/--
The final pinned query layouts extend the intermediate state after gate erasure.
Lookup projection may append queries, but cannot change any gate query index.
-/
theorem PinnedConstraintSystem.derive_queryState_extends_gates
    {F : Type} [Field F] [DecidableEq F]
    (cs : ConstraintSystem F) (map : SelCompressMap) :
    (pinnedQueryState
      (PinnedConstraintSystem.derive cs map)).Extends
      (eraseGates
        ((flatGates cs).map (substSelectorMap map.lookup))
        (queryWalkInit map cs)).2 := by
  unfold pinnedQueryState
  simp only [PinnedConstraintSystem.derive, projectCS]
  exact eraseLookups_extends
    (cs.lookups.map fun argument =>
      { inputs :=
          argument.inputs.map (substSelectorMap map.lookup)
        tables :=
          argument.tables.map (substSelectorMap map.lookup)
        tablesFree := by
          intro table htable
          rw [List.mem_map] at htable
          obtain ⟨source, hsource, rfl⟩ := htable
          rw [substSelectorMap_eq_of_selectorFree map.lookup source
            (argument.tablesFree source hsource)]
          exact argument.tablesFree source hsource
        arity := by simp [argument.arity] })
    (eraseGates
      ((flatGates cs).map (substSelectorMap map.lookup))
      (queryWalkInit map cs)).2

/-- Prepending packed fixed-selector queries leaves every configure-recorded query
at the same index. -/
theorem queryWalkInit_extends_recorded
    {F : Type} [Field F] [DecidableEq F]
    (map : SelCompressMap) (cs : ConstraintSystem F) :
    (queryWalkInit map cs).Extends (recordedQueries cs) := by
  have fixIdxExtends (state : QueryState) (column : ℕ) :
      ((state.fixIdx column 0).2).Extends state := by
    unfold QueryState.fixIdx
    cases findQuery state.fixed column 0 with
    | some index =>
        exact QueryState.Extends.refl state
    | none =>
        exact
          ⟨List.prefix_refl _,
            by
              simp only [Array.toList_push]
              exact List.prefix_append _ _,
            List.prefix_refl _⟩
  have foldExtends (columns : List ℕ) (state : QueryState) :
      (columns.foldl
        (fun current column =>
          (current.fixIdx (cs.numFixedColumns + column) 0).2)
        state).Extends state := by
    induction columns generalizing state with
    | nil =>
        exact QueryState.Extends.refl state
    | cons column columns ih =>
        rw [List.foldl_cons]
        exact QueryState.Extends.trans
          (fixIdxExtends state (cs.numFixedColumns + column))
          (ih _)
  unfold queryWalkInit
  exact foldExtends (List.range map.newFixedCols) (recordedQueries cs)

/-- The complete pinned query walk preserves the configure-recorded layouts as
prefixes. -/
theorem PinnedConstraintSystem.derive_queryState_extends_recorded
    {F : Type} [Field F] [DecidableEq F]
    (cs : ConstraintSystem F) (map : SelCompressMap) :
    (pinnedQueryState
      (PinnedConstraintSystem.derive cs map)).Extends
      (recordedQueries cs) := by
  have hinit := queryWalkInit_extends_recorded map cs
  have hgates :=
    eraseGates_extends
      ((flatGates cs).map (substSelectorMap map.lookup))
      (queryWalkInit map cs)
  have hfinal :=
    PinnedConstraintSystem.derive_queryState_extends_gates cs map
  exact QueryState.Extends.trans
    (QueryState.Extends.trans hinit hgates) hfinal

/-- Every configure-registered fixed query remains present in the final pinned
fixed-query layout. -/
theorem PinnedConstraintSystem.mem_fixedQueryLayout_derive_of_mem
    {F : Type} [Field F] [DecidableEq F]
    (cs : ConstraintSystem F) (map : SelCompressMap)
    (column : Column .fixed) (rotation : Rotation)
    (hquery : (column, rotation) ∈ cs.fixedQueries) :
    (column.index, rotation) ∈
      (PinnedConstraintSystem.derive cs map).fixedQueryLayout := by
  have hrecorded :
      (column.index, rotation) ∈
        (recordedQueries cs).fixed.toList := by
    exact List.mem_map.mpr ⟨(column, rotation), hquery, rfl⟩
  have hext :=
    PinnedConstraintSystem.derive_queryState_extends_recorded cs map
  have hfinal := hext.2.1.subset hrecorded
  simpa [pinnedQueryState] using hfinal

/-- Every configure-registered instance query remains present in the final pinned
instance-query layout. -/
theorem PinnedConstraintSystem.mem_instanceQueryLayout_derive_of_mem
    {F : Type} [Field F] [DecidableEq F]
    (cs : ConstraintSystem F) (map : SelCompressMap)
    (column : Column .instance) (rotation : Rotation)
    (hquery : (column, rotation) ∈ cs.instanceQueries) :
    (column.index, rotation) ∈
      (PinnedConstraintSystem.derive cs map).instanceQueryLayout := by
  have hrecorded :
      (column.index, rotation) ∈
        (recordedQueries cs).inst.toList := by
    exact List.mem_map.mpr ⟨(column, rotation), hquery, rfl⟩
  have hext :=
    PinnedConstraintSystem.derive_queryState_extends_recorded cs map
  have hfinal := hext.2.2.subset hrecorded
  simpa [pinnedQueryState] using hfinal

/-- Rotating a domain point is addition of its row and query rotation. -/
theorem rotateOmega_domainPoint
    (omega : Fp) (homega : omega ≠ 0) (row : ℕ) (rotation : ℤ) :
    rotateOmega omega (omega ^ row) rotation =
      omega ^ ((row : ℤ) + rotation) := by
  rw [zpow_add₀ homega]
  simp [rotateOmega, mul_comm]

/-- A fixed query feed reads the same row as the canonical resolver environment. -/
theorem fixedQueryFeedOfResolver_eval_environment
    {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G)
    (poly : CommitmentId → Polynomial Fp)
    (p : Fin shape.numProofs) (usableRows : ℕ)
    (selectors : ℕ → Fp)
    {query column : ℕ} {rotation : ℤ}
    (hquery : query < shape.numFixedQueries)
    (hentry : vk.fixedQueryLayout[query]? = some (column, rotation))
    (homega : vk.omega ≠ 0) (row : ℕ) :
    (fixedQueryFeedOfResolver vk poly query).eval (vk.omega ^ row) =
      Query.eval (resolverEnvironment vk poly p usableRows)
        selectors row (.fixed ⟨column⟩ rotation) := by
  rw [fixedQueryFeedOfResolver,
    resolverQueryFeed_eval vk.omega vk.fixedQueryLayout
      (fun column => poly (.fixedCol column)) hquery]
  have hget :
      vk.fixedQueryLayout.getD query (0, 0) = (column, rotation) := by
    simp [List.getD_eq_getElem?_getD, hentry]
  rw [hget]
  simp only [Query.eval, resolverEnvironment, polynomialEnvironment_fixed]
  rw [rotateOmega_domainPoint vk.omega homega row rotation]

/-- An advice query feed reads the same row as the canonical resolver environment. -/
theorem adviceQueryFeedOfResolver_eval_environment
    {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G)
    (poly : CommitmentId → Polynomial Fp)
    (p : Fin shape.numProofs) (usableRows : ℕ)
    (selectors : ℕ → Fp)
    {query column : ℕ} {rotation : ℤ}
    (hquery : query < shape.numAdviceQueries)
    (hentry : vk.adviceQueryLayout[query]? = some (column, rotation))
    (homega : vk.omega ≠ 0) (row : ℕ) :
    (adviceQueryFeedOfResolver vk poly p query).eval (vk.omega ^ row) =
      Query.eval (resolverEnvironment vk poly p usableRows)
        selectors row (.advice ⟨column⟩ rotation) := by
  rw [adviceQueryFeedOfResolver,
    resolverQueryFeed_eval vk.omega vk.adviceQueryLayout
      (fun column => poly (.adviceCol p column)) hquery]
  have hget :
      vk.adviceQueryLayout.getD query (0, 0) = (column, rotation) := by
    simp [List.getD_eq_getElem?_getD, hentry]
  rw [hget]
  simp only [Query.eval, resolverEnvironment, polynomialEnvironment_advice]
  rw [rotateOmega_domainPoint vk.omega homega row rotation]

/-- An instance query feed reads the same row as the canonical resolver environment. -/
theorem instanceQueryFeedOfResolver_eval_environment
    {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G)
    (poly : CommitmentId → Polynomial Fp)
    (p : Fin shape.numProofs) (usableRows : ℕ)
    (selectors : ℕ → Fp)
    {query column : ℕ} {rotation : ℤ}
    (hquery : query < shape.numInstanceQueries)
    (hentry : vk.instanceQueryLayout[query]? = some (column, rotation))
    (homega : vk.omega ≠ 0) (row : ℕ) :
    (instanceQueryFeedOfResolver vk poly p query).eval (vk.omega ^ row) =
      Query.eval (resolverEnvironment vk poly p usableRows)
        selectors row (.instance ⟨column⟩ rotation) := by
  rw [instanceQueryFeedOfResolver,
    resolverQueryFeed_eval vk.omega vk.instanceQueryLayout
      (fun column => poly (.instanceCol p column)) hquery]
  have hget :
      vk.instanceQueryLayout.getD query (0, 0) = (column, rotation) := by
    simp [List.getD_eq_getElem?_getD, hentry]
  rw [hget]
  simp only [Query.eval, resolverEnvironment, polynomialEnvironment_instance]
  rw [rotateOmega_domainPoint vk.omega homega row rotation]

/--
The three resolver query feeds interpret an arbitrary keygen query state whenever
the state layouts are the VK layouts and the shape counts those layouts exactly.
-/
theorem resolverQueryFeeds_interpret
    {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G)
    (poly : CommitmentId → Polynomial Fp)
    (p : Fin shape.numProofs) (usableRows : ℕ)
    (selectors : ℕ → Fp) (row : ℕ)
    (homega : vk.omega ≠ 0)
    (state : QueryState)
    (hadviceLayout :
      state.advice.toList = vk.adviceQueryLayout)
    (hfixedLayout :
      state.fixed.toList = vk.fixedQueryLayout)
    (hinstanceLayout :
      state.inst.toList = vk.instanceQueryLayout)
    (hadviceCount :
      vk.adviceQueryLayout.length = shape.numAdviceQueries)
    (hfixedCount :
      vk.fixedQueryLayout.length = shape.numFixedQueries)
    (hinstanceCount :
      vk.instanceQueryLayout.length = shape.numInstanceQueries) :
    Interprets state
      (fun query =>
        (fixedQueryFeedOfResolver vk poly query).eval (vk.omega ^ row))
      (fun query =>
        (adviceQueryFeedOfResolver vk poly p query).eval (vk.omega ^ row))
      (fun query =>
        (instanceQueryFeedOfResolver vk poly p query).eval (vk.omega ^ row))
      (Query.eval (resolverEnvironment vk poly p usableRows)
        selectors row) where
  advice query column rotation hentry := by
    have hentryList :
        state.advice.toList[query]? = some (column, rotation) := by
      simpa only [Array.getElem?_toList] using hentry
    rw [hadviceLayout] at hentryList
    have hqueryLayout :=
      (List.getElem?_eq_some_iff.mp hentryList).1
    apply adviceQueryFeedOfResolver_eval_environment
      vk poly p usableRows selectors
    · omega
    · exact hentryList
    · exact homega
  fixed query column rotation hentry := by
    have hentryList :
        state.fixed.toList[query]? = some (column, rotation) := by
      simpa only [Array.getElem?_toList] using hentry
    rw [hfixedLayout] at hentryList
    have hqueryLayout :=
      (List.getElem?_eq_some_iff.mp hentryList).1
    apply fixedQueryFeedOfResolver_eval_environment
      vk poly p usableRows selectors
    · omega
    · exact hentryList
    · exact homega
  inst query column rotation hentry := by
    have hentryList :
        state.inst.toList[query]? = some (column, rotation) := by
      simpa only [Array.getElem?_toList] using hentry
    rw [hinstanceLayout] at hentryList
    have hqueryLayout :=
      (List.getElem?_eq_some_iff.mp hentryList).1
    apply instanceQueryFeedOfResolver_eval_environment
      vk poly p usableRows selectors
    · omega
    · exact hentryList
    · exact homega

end Zcash.Snark
