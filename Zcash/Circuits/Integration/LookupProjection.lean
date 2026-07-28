import Zcash.Snark.Keygen.Pipeline
import Zcash.Circuits.Integration.OperationLookups
import Zcash.Circuits.Integration.ResolverQueryEnvironment

/-!
# Lookup projection across the Clean boundary

Key generation substitutes the circuit's virtual selectors, then erases each
configured `LookupArgument` into the verifier's query-index expression language.
This module proves the semantic part of that translation for one selected lookup.

The result deliberately stops at the selector-substitution valuation.  A lookup
activation needs the stronger row fact that its complex selectors have their exact
zero/one values; unlike a custom gate, an arbitrary nonzero selector scale is not
enough for tuple membership.
-/

namespace Zcash.Snark

open Halo2

set_option maxHeartbeats 20000

/-- Substitute the selector-compression map through one lookup while retaining the
lawfulness facts carried by `LookupArgument`. -/
private abbrev substitutedLookup
    {F : Type} [Field F] [DecidableEq F]
    (map : SelCompressMap) (argument : LookupArgument F) :
    LookupArgument F where
  inputs := argument.inputs.map (substSelectorMap map.lookup)
  tables := argument.tables.map (substSelectorMap map.lookup)
  tablesFree := by
    intro table htable
    rw [List.mem_map] at htable
    obtain ⟨source, hsource, rfl⟩ := htable
    rw [substSelectorMap_eq_of_selectorFree map.lookup source
      (argument.tablesFree source hsource)]
    exact argument.tablesFree source hsource
  arity := by simp [argument.arity]

/-- The lookup walk emits one fixture per source argument. -/
theorem eraseLookups_length
    {F : Type} [Field F] [DecidableEq F]
    (arguments : List (LookupArgument F)) (state : QueryState) :
    (eraseLookups arguments state).1.length = arguments.length := by
  induction arguments generalizing state with
  | nil => rfl
  | cons argument rest ih =>
      simp only [eraseLookups, List.length_cons]
      exact congrArg Nat.succ (ih (eraseLookup argument state).2)

/--
Selecting one result of the threaded lookup-erasure walk exposes the source
argument, the state at which it was erased, and the fact that the complete walk's
final state extends that local result.
-/
theorem eraseLookups_getElem
    {F : Type} [Field F] [DecidableEq F]
    (arguments : List (LookupArgument F)) (state : QueryState)
    (lookupIndex : ℕ) (hlookup : lookupIndex < arguments.length) :
    ∃ localState,
      (eraseLookups arguments state).1[lookupIndex]'(by
        rw [eraseLookups_length]
        exact hlookup) =
        (eraseLookup arguments[lookupIndex] localState).1 ∧
      (eraseLookups arguments state).2.Extends
        (eraseLookup arguments[lookupIndex] localState).2 := by
  induction arguments generalizing state lookupIndex with
  | nil =>
      exact absurd hlookup (Nat.not_lt_zero lookupIndex)
  | cons argument rest ih =>
      cases lookupIndex with
      | zero =>
          refine ⟨state, rfl, ?_⟩
          exact eraseLookups_extends rest (eraseLookup argument state).2
      | succ lookupIndex =>
          have hrest : lookupIndex < rest.length := by
            simpa using hlookup
          obtain ⟨localState, hfixture, hextends⟩ :=
            ih (eraseLookup argument state).2 lookupIndex hrest
          exact ⟨localState, hfixture, hextends⟩

/-- Evaluation of every projected input expression agrees with its source input. -/
theorem eraseLookup_inputs_eval
    {F : Type} [Field F] [DecidableEq F]
    (argument : LookupArgument F) (state finalState : QueryState)
    (fixed advice instanceFeed : ℕ → F) (valuation : Query → F)
    (hfree : ∀ expression ∈ argument.inputs, expression.SelectorFree)
    (hextends :
      finalState.Extends (eraseLookup argument state).2)
    (hinterprets :
      Interprets finalState fixed advice instanceFeed valuation) :
    (eraseLookup argument state).1.inputs.map
        (RichExpression.eval fixed advice instanceFeed) =
      argument.inputs.map (Expression.eval valuation) := by
  unfold eraseLookup at hextends ⊢
  generalize hinputs :
    eraseGates argument.inputs state = inputResult
  rcases inputResult with ⟨inputs, inputState⟩
  generalize htables :
    eraseGates argument.tables inputState = tableResult
  rcases tableResult with ⟨tables, tableState⟩
  simp only
  have hextends' : finalState.Extends tableState := by
    have hinputState :
        (eraseGates argument.inputs state).2 = inputState :=
      congrArg Prod.snd hinputs
    have htableState :
        (eraseGates argument.tables inputState).2 = tableState :=
      congrArg Prod.snd htables
    simpa only [hinputState, htableState] using hextends
  apply List.ext_getElem
  · simp only [List.length_map]
    have hlength := eraseGates_length argument.inputs state
    rw [hinputs] at hlength
    exact hlength
  · intro index hleft hright
    simp only [List.getElem_map]
    have hinputExtends :
        finalState.Extends inputState := by
      have htableExtends :=
        eraseGates_extends argument.tables inputState
      rw [htables] at htableExtends
      apply QueryState.Extends.trans
        htableExtends
      exact hextends'
    have heval := eraseGates_eval fixed advice instanceFeed valuation
      argument.inputs state finalState hfree
      (by simpa [hinputs] using hinputExtends) hinterprets
      index
      (by simpa [hinputs] using hleft)
      (by simpa using hright)
    simpa [hinputs] using heval

/-- Evaluation of every projected table expression agrees with its source table. -/
theorem eraseLookup_tables_eval
    {F : Type} [Field F] [DecidableEq F]
    (argument : LookupArgument F) (state finalState : QueryState)
    (fixed advice instanceFeed : ℕ → F) (valuation : Query → F)
    (hfree : ∀ expression ∈ argument.tables, expression.SelectorFree)
    (hextends :
      finalState.Extends (eraseLookup argument state).2)
    (hinterprets :
      Interprets finalState fixed advice instanceFeed valuation) :
    (eraseLookup argument state).1.tables.map
        (RichExpression.eval fixed advice instanceFeed) =
      argument.tables.map (Expression.eval valuation) := by
  unfold eraseLookup at hextends ⊢
  generalize hinputs :
    eraseGates argument.inputs state = inputResult
  rcases inputResult with ⟨inputs, inputState⟩
  generalize htables :
    eraseGates argument.tables inputState = tableResult
  rcases tableResult with ⟨tables, tableState⟩
  simp only
  have hextends' : finalState.Extends tableState := by
    have hinputState :
        (eraseGates argument.inputs state).2 = inputState :=
      congrArg Prod.snd hinputs
    have htableState :
        (eraseGates argument.tables inputState).2 = tableState :=
      congrArg Prod.snd htables
    simpa only [hinputState, htableState] using hextends
  apply List.ext_getElem
  · simp only [List.length_map]
    exact eraseGates_length argument.tables inputState
  · intro index hleft hright
    simp only [List.getElem_map]
    have heval := eraseGates_eval fixed advice instanceFeed valuation
      argument.tables inputState finalState hfree
      (by simpa [htables] using hextends') hinterprets
      index
      (by simpa [htables] using hleft)
      (by simpa using hright)
    simpa [htables] using heval

/--
The selected projected lookup evaluates like the corresponding selector-substituted
configured argument under any interpretation of the final query layouts.
-/
theorem PinnedConstraintSystem.derive_lookup_eval
    {F : Type} [Field F] [DecidableEq F]
    (cs : ConstraintSystem F) (map : SelCompressMap)
    (fixed advice instanceFeed : ℕ → F) (valuation : Query → F)
    (lookupIndex : ℕ) (hlookup : lookupIndex < cs.lookups.length)
    (hinputCoverage : ∀ expression ∈ cs.lookups[lookupIndex].inputs,
      expression.selectorsCovered
        (fun selector => (map.lookup selector).isSome) = true)
    (htableCoverage : ∀ expression ∈ cs.lookups[lookupIndex].tables,
      expression.selectorsCovered
        (fun selector => (map.lookup selector).isSome) = true)
    (hinterprets :
      Interprets
        (pinnedQueryState
          (PinnedConstraintSystem.derive cs map))
        fixed advice instanceFeed valuation) :
    let pinned := PinnedConstraintSystem.derive cs map
    let argument := cs.lookups[lookupIndex]
    ((pinned.lookupInputExprs.getD lookupIndex []).map
        (RichExpression.eval fixed advice instanceFeed) =
      argument.inputs.map
        (Expression.eval (substValuation map.lookup valuation))) ∧
    ((pinned.lookupTableExprs.getD lookupIndex []).map
        (RichExpression.eval fixed advice instanceFeed) =
      argument.tables.map
        (Expression.eval (substValuation map.lookup valuation))) := by
  let arguments : List (LookupArgument F) :=
    cs.lookups.map (substitutedLookup map)
  let gateState :=
    (eraseGates
      ((flatGates cs).map (substSelectorMap map.lookup))
      (queryWalkInit map cs)).2
  have hargumentsLength :
      arguments.length = cs.lookups.length := by
    simp [arguments]
  have hlookup' : lookupIndex < arguments.length := by
    simpa [hargumentsLength] using hlookup
  obtain ⟨localState, hselected, hselectedExtends⟩ :=
    eraseLookups_getElem arguments gateState lookupIndex hlookup'
  have hfinal :
      pinnedQueryState (PinnedConstraintSystem.derive cs map) =
        (eraseLookups arguments gateState).2 := by
    simp [pinnedQueryState, PinnedConstraintSystem.derive,
      projectCS, arguments, gateState]
  have hfixture :
      ((PinnedConstraintSystem.derive cs map).lookupInputExprs.getD
          lookupIndex [],
        (PinnedConstraintSystem.derive cs map).lookupTableExprs.getD
          lookupIndex []) =
      ((eraseLookup arguments[lookupIndex] localState).1.inputs,
        (eraseLookup arguments[lookupIndex] localState).1.tables) := by
    have hfixtureIndex :
        (eraseLookups arguments gateState).1[lookupIndex]'(by
          rw [eraseLookups_length]
          exact hlookup') =
          (eraseLookup arguments[lookupIndex] localState).1 :=
      hselected
    have hpinnedInputs :
        (PinnedConstraintSystem.derive cs map).lookupInputExprs =
          (eraseLookups arguments gateState).1.map (·.inputs) := by
      simp [PinnedConstraintSystem.derive, projectCS, arguments, gateState]
    have hpinnedTables :
        (PinnedConstraintSystem.derive cs map).lookupTableExprs =
          (eraseLookups arguments gateState).1.map (·.tables) := by
      simp [PinnedConstraintSystem.derive, projectCS, arguments, gateState]
    have hemitted :
        lookupIndex <
          (eraseLookups arguments gateState).1.length := by
      rw [eraseLookups_length]
      exact hlookup'
    have hemittedInputs :
        lookupIndex <
          ((eraseLookups arguments gateState).1.map
            (·.inputs)).length := by
      simpa using hemitted
    have hemittedTables :
        lookupIndex <
          ((eraseLookups arguments gateState).1.map
            (·.tables)).length := by
      simpa using hemitted
    apply Prod.ext
    · rw [hpinnedInputs,
        List.getD_eq_getElem _ _ hemittedInputs,
        List.getElem_map, hfixtureIndex]
    · rw [hpinnedTables,
        List.getD_eq_getElem _ _ hemittedTables,
        List.getElem_map, hfixtureIndex]
  have hargument :
      arguments[lookupIndex] =
        substitutedLookup map cs.lookups[lookupIndex] := by
    simp [arguments]
  have hinputFree :
      ∀ expression ∈ arguments[lookupIndex].inputs,
        expression.SelectorFree := by
    intro expression hexpression
    rw [hargument] at hexpression
    simp only at hexpression
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hexpression
    exact (substSelectorMap_selectorFree _ source).2
      (hinputCoverage source hsource)
  have htableFree :
      ∀ expression ∈ arguments[lookupIndex].tables,
        expression.SelectorFree := by
    intro expression hexpression
    rw [hargument] at hexpression
    simp only at hexpression
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hexpression
    exact (substSelectorMap_selectorFree _ source).2
      (htableCoverage source hsource)
  have hextends :
      (pinnedQueryState
        (PinnedConstraintSystem.derive cs map)).Extends
          (eraseLookup arguments[lookupIndex] localState).2 := by
    rw [hfinal]
    exact hselectedExtends
  have hinputs := eraseLookup_inputs_eval
    arguments[lookupIndex] localState
    (pinnedQueryState (PinnedConstraintSystem.derive cs map))
    fixed advice instanceFeed valuation hinputFree hextends hinterprets
  have htables := eraseLookup_tables_eval
    arguments[lookupIndex] localState
    (pinnedQueryState (PinnedConstraintSystem.derive cs map))
    fixed advice instanceFeed valuation htableFree hextends hinterprets
  rw [hargument] at hinputs htables
  simp only [substitutedLookup, List.map_map] at hinputs htables
  have hinputMap :
      cs.lookups[lookupIndex].inputs.map
          (Expression.eval valuation ∘
            substSelectorMap map.lookup) =
        cs.lookups[lookupIndex].inputs.map
          (Expression.eval
            (substValuation map.lookup valuation)) := by
    apply List.map_congr_left
    intro expression _
    exact substSelectorMap_eval map.lookup valuation expression
  have htableMap :
      cs.lookups[lookupIndex].tables.map
          (Expression.eval valuation ∘
            substSelectorMap map.lookup) =
        cs.lookups[lookupIndex].tables.map
          (Expression.eval
            (substValuation map.lookup valuation)) := by
    apply List.map_congr_left
    intro expression _
    exact substSelectorMap_eval map.lookup valuation expression
  rw [hinputMap] at hinputs
  rw [htableMap] at htables
  have hfixtureInputs := congrArg Prod.fst hfixture
  have hfixtureTables := congrArg Prod.snd hfixture
  have hfixtureInputs' :
      (PinnedConstraintSystem.derive cs map).lookupInputExprs.getD
          lookupIndex [] =
        (eraseLookup
          (substitutedLookup map cs.lookups[lookupIndex])
          localState).1.inputs := by
    simpa only [hargument] using hfixtureInputs
  have hfixtureTables' :
      (PinnedConstraintSystem.derive cs map).lookupTableExprs.getD
          lookupIndex [] =
        (eraseLookup
          (substitutedLookup map cs.lookups[lookupIndex])
          localState).1.tables := by
    simpa only [hargument] using hfixtureTables
  dsimp only
  rw [hfixtureInputs', hfixtureTables']
  exact And.intro hinputs htables

end Zcash.Snark
