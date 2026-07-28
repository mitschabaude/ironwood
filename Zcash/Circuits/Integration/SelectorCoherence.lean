import Zcash.Circuits.Integration.ResolverGates
import Clean.Halo2.Keygen.Layout
import Std.Data.HashSet.Lemmas

/-!
# Selector compiler coherence

Structural facts about Clean's `compress_selectors` port.  These proofs are
circuit-independent: they reason about the greedy packing algorithm rather than a
captured Action selector map.
-/

namespace Halo2

open Zcash.Arithmetic (scalarFieldOrder)

set_option maxHeartbeats 20000

/--
A gate's distinguished selector and every selector atom occurring in its constraints
name allocated selector indices.

The second clause is deliberately syntactic.  Semantic gate well-formedness cannot
imply it: foreign selector atoms may cancel algebraically while still violating the
keygen representation invariant.
-/
def Gate.SelectorsAllocated
    {F : Type} (gate : Gate F) (numSelectors : ℕ) : Prop :=
  gate.selector.index < numSelectors ∧
    gate.constraints.Forall fun constraint =>
      constraint.poly.selectorsCovered
        (fun selector => decide (selector < numSelectors)) = true

/--
A gate constraint mentions no selector other than the gate's distinguished selector.
This is the local certificate used by the standard allocate-selector/create-gate
configure pattern.
-/
def Gate.SelectorsOwned
    {F : Type} (gate : Gate F) : Prop :=
  gate.constraints.Forall fun constraint =>
    constraint.poly.selectorsCovered
      (fun selector =>
        decide (selector = gate.selector.index)) = true

/-- Every configured gate uses only allocated selector indices. -/
def ConstraintSystem.GateSelectorsAllocated
    {F : Type} (cs : ConstraintSystem F) : Prop :=
  cs.gates.Forall fun gate => gate.SelectorsAllocated cs.numSelectors

namespace ConstraintSystem.GateSelectorsAllocated

/-- The distinguished selector of a configured gate is allocated. -/
theorem gate
    {F : Type} {cs : ConstraintSystem F}
    (hallocated : cs.GateSelectorsAllocated)
    {gate : Gate F} (hgate : gate ∈ cs.gates) :
    gate.selector.index < cs.numSelectors :=
  (List.forall_iff_forall_mem.mp hallocated gate hgate).1

/-- Every selector atom of a configured constraint is allocated. -/
theorem constraint
    {F : Type} {cs : ConstraintSystem F}
    (hallocated : cs.GateSelectorsAllocated)
    {gate : Gate F} (hgate : gate ∈ cs.gates)
    {constraint : Constraint F}
    (hconstraint : constraint ∈ gate.constraints) :
    constraint.poly.selectorsCovered
      (fun selector => decide (selector < cs.numSelectors)) = true := by
  have hgateAllocated :=
    List.forall_iff_forall_mem.mp hallocated gate hgate
  exact List.forall_iff_forall_mem.mp hgateAllocated.2
    constraint hconstraint

end ConstraintSystem.GateSelectorsAllocated

/--
Selector coverage is monotone in its domain predicate.
-/
theorem Expression.selectorsCovered_mono
    {F : Type} (source target : ℕ → Bool)
    (hdom : ∀ selector, source selector = true →
      target selector = true)
    (expression : Expression F Query)
    (hcovered : expression.selectorsCovered source = true) :
    expression.selectorsCovered target = true := by
  induction expression with
  | var query =>
      cases query with
      | selector selector =>
          exact hdom selector.index hcovered
      | fixed column rotation =>
          rfl
      | advice column rotation =>
          rfl
      | «instance» column rotation =>
          rfl
  | const value =>
      rfl
  | add left right ihLeft ihRight =>
      simp only [Expression.selectorsCovered,
        Bool.and_eq_true] at hcovered ⊢
      exact ⟨ihLeft hcovered.1, ihRight hcovered.2⟩
  | mul left right ihLeft ihRight =>
      simp only [Expression.selectorsCovered,
        Bool.and_eq_true] at hcovered ⊢
      exact ⟨ihLeft hcovered.1, ihRight hcovered.2⟩

/-- A selector-free expression is covered by every selector domain. -/
theorem Expression.selectorsCovered_of_selectorFree
    {F : Type} (domain : ℕ → Bool)
    (expression : Expression F Query)
    (hfree : expression.SelectorFree) :
    expression.selectorsCovered domain = true := by
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
      simp only [Expression.SelectorFree,
        Expression.selectorsCovered, Bool.and_eq_true] at hfree ⊢
      exact ⟨ihLeft hfree.1, ihRight hfree.2⟩
  | mul left right ihLeft ihRight =>
      simp only [Expression.SelectorFree,
        Expression.selectorsCovered, Bool.and_eq_true] at hfree ⊢
      exact ⟨ihLeft hfree.1, ihRight hfree.2⟩

/-- The standard `Gate.withSelector` shape mentions no foreign selectors. -/
@[circuit_norm]
theorem Gate.selectorsOwned_of_withSelector
    {F : Type} [Field F]
    (name : String) (selector : Selector)
    (queriedCells : List (Expression F Query))
    (constraints : List (String × Expression F Query))
    (hfree : constraints.Forall fun constraint =>
      constraint.2.SelectorFree) :
    (Gate.withSelector name selector queriedCells constraints
      (List.forall_iff_forall_mem.mp hfree)).SelectorsOwned := by
  rw [Gate.SelectorsOwned, List.forall_iff_forall_mem]
  intro constraint hconstraint
  change constraint ∈ constraints.map _ at hconstraint
  obtain ⟨source, hsource, rfl⟩ :=
    List.mem_map.mp hconstraint
  simp only [Gate.withSelector, querySelector,
    Expression.selectorsCovered, decide_true, Bool.true_and]
  exact Expression.selectorsCovered_of_selectorFree
    (fun index => decide (index = selector.index))
    source.2
    (List.forall_iff_forall_mem.mp hfree source hsource)

namespace Gate.SelectorsAllocated

/-- Increasing the selector allocation bound preserves gate validity. -/
theorem mono
    {F : Type} {gate : Gate F} {source target : ℕ}
    (hgate : gate.SelectorsAllocated source)
    (hbound : source ≤ target) :
    gate.SelectorsAllocated target := by
  constructor
  · exact hgate.1.trans_le hbound
  · rw [List.forall_iff_forall_mem]
    intro constraint hconstraint
    apply Expression.selectorsCovered_mono
      (fun selector => decide (selector < source))
    · intro selector hselector
      exact decide_eq_true
        (lt_of_lt_of_le
          (of_decide_eq_true hselector) hbound)
    · exact List.forall_iff_forall_mem.mp hgate.2
        constraint hconstraint

/--
A gate whose constraints mention only its own selector is allocated whenever that
distinguished selector is below the allocation bound.
-/
theorem of_owned
    {F : Type} {gate : Gate F} {numSelectors : ℕ}
    (howned : gate.SelectorsOwned)
    (hselector : gate.selector.index < numSelectors) :
    gate.SelectorsAllocated numSelectors := by
  constructor
  · exact hselector
  · rw [List.forall_iff_forall_mem]
    intro constraint hconstraint
    apply Expression.selectorsCovered_mono
      (fun selector =>
        decide (selector = gate.selector.index))
    · intro selector heq
      exact decide_eq_true
        (by
          rw [of_decide_eq_true heq]
          exact hselector)
    · exact List.forall_iff_forall_mem.mp howned
        constraint hconstraint

end Gate.SelectorsAllocated

namespace ConstraintSystem.GateSelectorsAllocated

/-- Increasing the allocation bound preserves every existing gate. -/
theorem mono
    {F : Type} {gates : List (Gate F)} {source target : ℕ}
    (hallocated :
      gates.Forall fun gate => gate.SelectorsAllocated source)
    (hbound : source ≤ target) :
    gates.Forall fun gate => gate.SelectorsAllocated target := by
  rw [List.forall_iff_forall_mem] at hallocated ⊢
  intro gate hgate
  exact (hallocated gate hgate).mono hbound

end ConstraintSystem.GateSelectorsAllocated

namespace ConfigureDelta

@[simp] theorem gates_append
    {F : Type} (left right : ConfigureDelta F) :
    (left.append right).gates = left.gates ++ right.gates :=
  rfl

@[simp] theorem queriedCell_gates
    {F : Type} (owner : String) (expression : Expression F Query) :
    (queriedCell owner expression).gates = [] := by
  cases expression with
  | var query =>
      cases query <;> rfl
  | const value =>
      rfl
  | add left right =>
      rfl
  | mul left right =>
      rfl

@[simp] theorem queriedCells_gates
    {F : Type} (owner : String)
    (expressions : List (Expression F Query)) :
    (queriedCells owner expressions).gates = [] := by
  unfold queriedCells
  have aux (initial : ConfigureDelta F)
      (cells : List (Expression F Query)) :
      (cells.foldl
        (fun delta cell => delta.append (queriedCell owner cell))
        initial).gates = initial.gates := by
    induction cells generalizing initial with
    | nil =>
        rfl
    | cons cell cells ih =>
        rw [List.foldl_cons, ih, gates_append,
          queriedCell_gates, List.append_nil]
  exact aux {} expressions

end ConfigureDelta

namespace Configure

@[simp] theorem counts_numSelectors
    {F : Type} (cs : ConstraintSystem F) :
    (ConfigureCounts.ofConstraintSystem cs).numSelectors =
      cs.numSelectors :=
  rfl

@[simp] theorem run_output
    {F α : Type} (program : Configure F α)
    (cs : ConstraintSystem F) :
    (program cs).1 =
      program.output (ConfigureCounts.ofConstraintSystem cs) :=
  rfl

@[simp] theorem run_gates
    {F α : Type} (program : Configure F α)
    (cs : ConstraintSystem F) :
    (program cs).2.gates =
      cs.gates ++
        (program.delta
          (ConfigureCounts.ofConstraintSystem cs)).gates :=
  rfl

@[simp] theorem run_numSelectors
    {F α : Type} (program : Configure F α)
    (cs : ConstraintSystem F) :
    (program cs).2.numSelectors =
      (program.finalCounts
        (ConfigureCounts.ofConstraintSystem cs)).numSelectors :=
  rfl

@[simp] theorem counts_run
    {F α : Type} (program : Configure F α)
    (cs : ConstraintSystem F) :
    ConfigureCounts.ofConstraintSystem (program cs).2 =
      program.finalCounts (ConfigureCounts.ofConstraintSystem cs) :=
  rfl

@[simp] theorem delta_lookup_gates
    {F : Type} (queriedCells : List (Expression F Query))
    (tableMap : List (Expression F Query × TableColumn))
    (counts : ConfigureCounts) :
    (delta (Halo2.lookup queriedCells tableMap) counts).gates = [] := by
  simp only [delta, Halo2.lookup, ConfigureDelta.gates_append,
    ConfigureDelta.queriedCells_gates, List.nil_append]
  have aux (initial : ConfigureDelta F) (tables : List TableColumn) :
      (tables.foldl
        (fun delta table =>
          delta.append { fixedQueries := [(table.inner, 0)] })
        initial).gates = initial.gates := by
    induction tables generalizing initial with
    | nil =>
        rfl
    | cons table tables ih =>
        rw [List.foldl_cons, ih, ConfigureDelta.gates_append,
          List.append_nil]
  simp [aux]

@[simp] theorem delta_createGate_gates
    {F : Type} (gate : Gate F) (counts : ConfigureCounts) :
    (delta (Halo2.createGate gate) counts).gates = [gate] := by
  simp [delta, Halo2.createGate]

@[simp] theorem delta_pure_gates
    {F α : Type} (value : α) (counts : ConfigureCounts) :
    (delta (pure value : Configure F α) counts).gates = [] :=
  rfl

@[simp] theorem delta_adviceColumn_gates
    {F : Type} (counts : ConfigureCounts) :
    (delta (Halo2.adviceColumn : Configure F (Column .advice))
      counts).gates = [] :=
  rfl

@[simp] theorem delta_fixedColumn_gates
    {F : Type} (counts : ConfigureCounts) :
    (delta (Halo2.fixedColumn : Configure F (Column .fixed))
      counts).gates = [] :=
  rfl

@[simp] theorem delta_instanceColumn_gates
    {F : Type} (counts : ConfigureCounts) :
    (delta (Halo2.instanceColumn : Configure F (Column .instance))
      counts).gates = [] :=
  rfl

@[simp] theorem delta_selector_gates
    {F : Type} (counts : ConfigureCounts) :
    (delta (Halo2.selector : Configure F Selector) counts).gates = [] :=
  rfl

@[simp] theorem delta_complexSelector_gates
    {F : Type} (counts : ConfigureCounts) :
    (delta (Halo2.complexSelector : Configure F Selector) counts).gates = [] :=
  rfl

@[simp] theorem delta_enableEquality_gates
    {F : Type} (column : AnyColumn) (counts : ConfigureCounts) :
    (delta (Halo2.enableEquality (F := F) column) counts).gates = [] := by
  cases column with
  | mk kind index =>
      cases kind <;> rfl

@[simp] theorem delta_enableConstant_gates
    {F : Type} (column : Column .fixed) (counts : ConfigureCounts) :
    (delta (Halo2.enableConstant (F := F) column) counts).gates = [] :=
  rfl

@[simp] theorem run_bind_gates
    {F α β : Type} (program : Configure F α)
    (next : α → Configure F β) (cs : ConstraintSystem F) :
    ((program >>= next) cs).2.gates =
      ((next (program cs).1) (program cs).2).2.gates := by
  simp only [run_gates, delta_bind, ConfigureDelta.gates_append,
    run_output, counts_run]
  simp [List.append_assoc]

@[simp] theorem run_bind_numSelectors
    {F α β : Type} (program : Configure F α)
    (next : α → Configure F β) (cs : ConstraintSystem F) :
    ((program >>= next) cs).2.numSelectors =
      ((next (program cs).1) (program cs).2).2.numSelectors := by
  simp

end Configure

namespace ConstraintSystem

/-- Lookup registration does not change the configured gate list. -/
@[simp]
theorem lookup_gates
    {F : Type} (queriedCells : List (Expression F Query))
    (tableMap : List (Expression F Query × TableColumn))
    (cs : ConstraintSystem F) :
    ((Halo2.lookup queriedCells tableMap) cs).2.gates =
      cs.gates := by
  simp

/-- Lookup registration does not change the selector allocation count. -/
@[simp]
theorem lookup_numSelectors
    {F : Type} (queriedCells : List (Expression F Query))
    (tableMap : List (Expression F Query × TableColumn))
    (cs : ConstraintSystem F) :
    ((Halo2.lookup queriedCells tableMap) cs).2.numSelectors =
      cs.numSelectors := by
  simp

end ConstraintSystem

/-- The empty configure state has no invalid selector references. -/
@[circuit_norm]
theorem ConstraintSystem.gateSelectorsAllocated_empty
    {F : Type} :
    ({} : ConstraintSystem F).GateSelectorsAllocated := by
  simp [ConstraintSystem.GateSelectorsAllocated]

/--
Appending one gate preserves selector allocation exactly when the prior gates and
the new gate are allocated at the current selector count.
-/
@[circuit_norm]
theorem ConstraintSystem.gateSelectorsAllocated_createGate
    {F : Type} (cs : ConstraintSystem F) (gate : Gate F) :
    ((createGate gate cs).2).GateSelectorsAllocated ↔
      cs.GateSelectorsAllocated ∧
        gate.SelectorsAllocated cs.numSelectors := by
  unfold ConstraintSystem.GateSelectorsAllocated
  simp only [Configure.run_gates, Configure.delta_createGate_gates,
    Configure.run_numSelectors, Configure.finalCounts_createGate,
    Configure.counts_numSelectors, List.forall_append,
    List.forall_cons]
  simp

@[simp]
theorem ConstraintSystem.createGate_numSelectors
    {F : Type} (cs : ConstraintSystem F) (gate : Gate F) :
    (createGate gate cs).2.numSelectors = cs.numSelectors := by
  simp

namespace Configure

/--
A configure program preserves the invariant that every registered gate refers only
to allocated selectors.
-/
structure PreservesGateSelectorsAllocated
    {F α : Type} (program : Configure F α) : Prop where
  run : ∀ cs, cs.GateSelectorsAllocated →
    (program cs).2.GateSelectorsAllocated

namespace PreservesGateSelectorsAllocated

variable {F α β : Type}

@[simp] theorem gateSelectorsAllocated_run_pure
    (value : α) (cs : ConstraintSystem F) :
    ((pure value : Configure F α) cs).2.GateSelectorsAllocated ↔
      cs.GateSelectorsAllocated := by
  unfold ConstraintSystem.GateSelectorsAllocated
  simp

@[simp] theorem gateSelectorsAllocated_run_bind
    (program : Configure F α) (next : α → Configure F β)
    (cs : ConstraintSystem F) :
    ((program >>= next) cs).2.GateSelectorsAllocated ↔
      ((next (program cs).1) (program cs).2).2.GateSelectorsAllocated := by
  unfold ConstraintSystem.GateSelectorsAllocated
  simp only [Configure.run_bind_gates,
    Configure.run_bind_numSelectors]

/--
Any configure action that changes neither the gate list nor selector count preserves
selector allocation.
-/
theorem of_gates_numSelectors
    (program : Configure F α)
    (hgates : ∀ cs, (program cs).2.gates = cs.gates)
    (hselectors : ∀ cs,
      (program cs).2.numSelectors = cs.numSelectors) :
    PreservesGateSelectorsAllocated program := by
  constructor
  intro cs hcs
  unfold ConstraintSystem.GateSelectorsAllocated at hcs ⊢
  rw [hgates, hselectors]
  exact hcs

@[circuit_norm]
theorem pure (value : α) :
    PreservesGateSelectorsAllocated
      (pure value : Configure F α) := by
  apply of_gates_numSelectors <;> simp

@[circuit_norm]
theorem bind
    {program : Configure F α} {next : α → Configure F β}
    (hprogram : PreservesGateSelectorsAllocated program)
    (hnext : ∀ value,
      PreservesGateSelectorsAllocated (next value)) :
    PreservesGateSelectorsAllocated (program >>= next) := by
  constructor
  intro cs hcs
  have hresult :=
    (hnext (program cs).1).run (program cs).2
      (hprogram.run cs hcs)
  unfold ConstraintSystem.GateSelectorsAllocated at hresult ⊢
  simpa only [Configure.run_bind_gates,
    Configure.run_bind_numSelectors] using hresult

@[circuit_norm]
theorem map
    (function : α → β) {program : Configure F α}
    (hprogram : PreservesGateSelectorsAllocated program) :
    PreservesGateSelectorsAllocated (function <$> program) := by
  exact bind hprogram fun _ => pure _

@[circuit_norm]
theorem adviceColumn :
    PreservesGateSelectorsAllocated
      (Halo2.adviceColumn : Configure F (Column .advice)) := by
  apply of_gates_numSelectors <;> simp

@[circuit_norm]
theorem fixedColumn :
    PreservesGateSelectorsAllocated
      (Halo2.fixedColumn : Configure F (Column .fixed)) := by
  apply of_gates_numSelectors <;> simp

@[circuit_norm]
theorem instanceColumn :
    PreservesGateSelectorsAllocated
      (Halo2.instanceColumn : Configure F (Column .instance)) := by
  apply of_gates_numSelectors <;> simp

@[circuit_norm]
theorem selector :
    PreservesGateSelectorsAllocated
      (Halo2.selector : Configure F Selector) := by
  constructor
  intro cs hcs
  unfold ConstraintSystem.GateSelectorsAllocated
  simp only [Configure.run_gates, Configure.delta_selector_gates,
    List.append_nil, Configure.run_numSelectors,
    Configure.finalCounts_selector, Configure.counts_numSelectors]
  exact ConstraintSystem.GateSelectorsAllocated.mono
    hcs (Nat.le_succ cs.numSelectors)

@[circuit_norm]
theorem complexSelector :
    PreservesGateSelectorsAllocated
      (Halo2.complexSelector : Configure F Selector) := by
  constructor
  intro cs hcs
  unfold ConstraintSystem.GateSelectorsAllocated
  simp only [Configure.run_gates, Configure.delta_complexSelector_gates,
    List.append_nil, Configure.run_numSelectors,
    Configure.finalCounts_complexSelector, Configure.counts_numSelectors]
  exact ConstraintSystem.GateSelectorsAllocated.mono
    hcs (Nat.le_succ cs.numSelectors)

@[circuit_norm]
theorem enableEquality (column : AnyColumn) :
    PreservesGateSelectorsAllocated
      (Halo2.enableEquality (F := F) column) := by
  apply of_gates_numSelectors
  · intro cs; simp
  · intro cs; simp

@[circuit_norm]
theorem enableConstant (column : Column .fixed) :
    PreservesGateSelectorsAllocated
      (Halo2.enableConstant (F := F) column) := by
  apply of_gates_numSelectors
  · intro cs; simp
  · intro cs; simp

@[circuit_norm]
theorem lookupTableColumn :
    PreservesGateSelectorsAllocated
      (Halo2.lookupTableColumn : Configure F TableColumn) :=
  bind fixedColumn fun _ => pure _

@[circuit_norm]
theorem lookup
    (queriedCells : List (Expression F Query))
    (tableMap : List (Expression F Query × TableColumn)) :
    PreservesGateSelectorsAllocated
      (Halo2.lookup queriedCells tableMap) := by
  apply of_gates_numSelectors
  · exact ConstraintSystem.lookup_gates
      queriedCells tableMap
  · exact ConstraintSystem.lookup_numSelectors
      queriedCells tableMap

/--
The standard leaf configure pattern allocates a selector and immediately creates a
gate whose constraints mention only that selector.
-/
@[circuit_norm]
theorem selectorCreateGate
    (gate : Selector → Gate F) (result : Selector → α)
    (hselector : ∀ selector,
      (gate selector).selector.index = selector.index)
    (howned : ∀ selector, (gate selector).SelectorsOwned) :
    PreservesGateSelectorsAllocated (do
      let selector ← Halo2.selector
      Halo2.createGate (gate selector)
      return result selector) := by
  constructor
  intro cs hcs
  simp only [gateSelectorsAllocated_run_bind,
    gateSelectorsAllocated_run_pure]
  let selector := (Halo2.selector (F := F) cs).1
  let allocated := (Halo2.selector (F := F) cs).2
  change
    ConstraintSystem.GateSelectorsAllocated
      ((Halo2.createGate
      (gate selector) allocated).2)
  rw [ConstraintSystem.gateSelectorsAllocated_createGate]
  constructor
  · exact
      PreservesGateSelectorsAllocated.selector.run cs hcs
  · apply Gate.SelectorsAllocated.of_owned
      (howned selector)
    rw [hselector]
    simp [selector, allocated]

/--
Continuation form of `selectorCreateGate`.  Keeping the continuation inside this
rule preserves the fresh-selector relation without forcing elaboration through a
large reassociated state-monad term.
-/
@[circuit_norm]
theorem selectorCreateGateThen
    (gate : Selector → Gate F)
    {next : Selector → Configure F α}
    (hselector : ∀ selector,
      (gate selector).selector.index = selector.index)
    (howned : ∀ selector, (gate selector).SelectorsOwned)
    (hnext : ∀ selector,
      PreservesGateSelectorsAllocated (next selector)) :
    PreservesGateSelectorsAllocated (do
      let selector ← Halo2.selector
      Halo2.createGate (gate selector)
      next selector) := by
  constructor
  intro cs hcs
  simp only [gateSelectorsAllocated_run_bind]
  let selector := (Halo2.selector (F := F) cs).1
  let allocated := (Halo2.selector (F := F) cs).2
  let afterGate :=
    (Halo2.createGate (gate selector) allocated).2
  apply (hnext selector).run afterGate
  change ConstraintSystem.GateSelectorsAllocated
    ((Halo2.createGate (gate selector) allocated).2)
  rw [ConstraintSystem.gateSelectorsAllocated_createGate]
  constructor
  · exact
      PreservesGateSelectorsAllocated.selector.run cs hcs
  · apply Gate.SelectorsAllocated.of_owned
      (howned selector)
    rw [hselector]
    simp [selector, allocated]

/-- Complex-selector counterpart of `selectorCreateGate`. -/
@[circuit_norm]
theorem complexSelectorCreateGate
    (gate : Selector → Gate F) (result : Selector → α)
    (hselector : ∀ selector,
      (gate selector).selector.index = selector.index)
    (howned : ∀ selector, (gate selector).SelectorsOwned) :
    PreservesGateSelectorsAllocated (do
      let selector ← Halo2.complexSelector
      Halo2.createGate (gate selector)
      return result selector) := by
  constructor
  intro cs hcs
  simp only [gateSelectorsAllocated_run_bind,
    gateSelectorsAllocated_run_pure]
  let selector := (Halo2.complexSelector (F := F) cs).1
  let allocated := (Halo2.complexSelector (F := F) cs).2
  change
    ConstraintSystem.GateSelectorsAllocated
      ((Halo2.createGate
      (gate selector) allocated).2)
  rw [ConstraintSystem.gateSelectorsAllocated_createGate]
  constructor
  · exact
      PreservesGateSelectorsAllocated.complexSelector.run cs hcs
  · apply Gate.SelectorsAllocated.of_owned
      (howned selector)
    rw [hselector]
    simp [selector, allocated]

/--
Allocate two simple selectors and create one owned gate for each.  This retains the
selector-index facts across the second allocation without exposing a giant completed
configure state.
-/
@[circuit_norm]
theorem twoSelectorsTwoGates
    (firstGate secondGate : Selector → Selector → Gate F)
    (result : Selector → Selector → α)
    (hfirstSelector : ∀ first second,
      (firstGate first second).selector.index = first.index)
    (hsecondSelector : ∀ first second,
      (secondGate first second).selector.index = second.index)
    (hfirstOwned : ∀ first second,
      (firstGate first second).SelectorsOwned)
    (hsecondOwned : ∀ first second,
      (secondGate first second).SelectorsOwned) :
    PreservesGateSelectorsAllocated (do
      let first ← Halo2.selector
      let second ← Halo2.selector
      Halo2.createGate (firstGate first second)
      Halo2.createGate (secondGate first second)
      return result first second) := by
  constructor
  intro cs hcs
  simp only [gateSelectorsAllocated_run_bind,
    gateSelectorsAllocated_run_pure]
  let first := (Halo2.selector (F := F) cs).1
  let afterFirst := (Halo2.selector (F := F) cs).2
  let second := (Halo2.selector (F := F) afterFirst).1
  let allocated := (Halo2.selector (F := F) afterFirst).2
  change
    ConstraintSystem.GateSelectorsAllocated
      ((Halo2.createGate (secondGate first second)
      (Halo2.createGate
        (firstGate first second) allocated).2).2)
  rw [ConstraintSystem.gateSelectorsAllocated_createGate]
  constructor
  · rw [ConstraintSystem.gateSelectorsAllocated_createGate]
    constructor
    · exact PreservesGateSelectorsAllocated.selector.run afterFirst
        (PreservesGateSelectorsAllocated.selector.run cs hcs)
    · apply Gate.SelectorsAllocated.of_owned
        (hfirstOwned first second)
      rw [hfirstSelector]
      simp [first, allocated, afterFirst]
  · apply Gate.SelectorsAllocated.of_owned
      (hsecondOwned first second)
    rw [hsecondSelector]
    simp [second, allocated, afterFirst]

/-- Three-selector/three-gate counterpart of `twoSelectorsTwoGates`. -/
@[circuit_norm]
theorem threeSelectorsThreeGates
    (firstGate secondGate thirdGate :
      Selector → Selector → Selector → Gate F)
    (result : Selector → Selector → Selector → α)
    (hfirstSelector : ∀ first second third,
      (firstGate first second third).selector.index =
        first.index)
    (hsecondSelector : ∀ first second third,
      (secondGate first second third).selector.index =
        second.index)
    (hthirdSelector : ∀ first second third,
      (thirdGate first second third).selector.index =
        third.index)
    (hfirstOwned : ∀ first second third,
      (firstGate first second third).SelectorsOwned)
    (hsecondOwned : ∀ first second third,
      (secondGate first second third).SelectorsOwned)
    (hthirdOwned : ∀ first second third,
      (thirdGate first second third).SelectorsOwned) :
    PreservesGateSelectorsAllocated (do
      let first ← Halo2.selector
      let second ← Halo2.selector
      let third ← Halo2.selector
      Halo2.createGate (firstGate first second third)
      Halo2.createGate (secondGate first second third)
      Halo2.createGate (thirdGate first second third)
      return result first second third) := by
  constructor
  intro cs hcs
  simp only [gateSelectorsAllocated_run_bind,
    gateSelectorsAllocated_run_pure]
  let first := (Halo2.selector (F := F) cs).1
  let afterFirst := (Halo2.selector (F := F) cs).2
  let second := (Halo2.selector (F := F) afterFirst).1
  let afterSecond := (Halo2.selector (F := F) afterFirst).2
  let third := (Halo2.selector (F := F) afterSecond).1
  let allocated := (Halo2.selector (F := F) afterSecond).2
  change
    ConstraintSystem.GateSelectorsAllocated
      ((Halo2.createGate (thirdGate first second third)
      (Halo2.createGate (secondGate first second third)
        (Halo2.createGate
          (firstGate first second third) allocated).2).2).2)
  rw [ConstraintSystem.gateSelectorsAllocated_createGate]
  constructor
  · rw [ConstraintSystem.gateSelectorsAllocated_createGate]
    constructor
    · rw [ConstraintSystem.gateSelectorsAllocated_createGate]
      constructor
      · exact PreservesGateSelectorsAllocated.selector.run afterSecond
          (PreservesGateSelectorsAllocated.selector.run afterFirst
            (PreservesGateSelectorsAllocated.selector.run cs hcs))
      · apply Gate.SelectorsAllocated.of_owned
          (hfirstOwned first second third)
        rw [hfirstSelector]
        simp [first, allocated, afterSecond, afterFirst]
        omega
    · apply Gate.SelectorsAllocated.of_owned
        (hsecondOwned first second third)
      rw [hsecondSelector]
      simp [second, allocated, afterSecond, afterFirst]
  · apply Gate.SelectorsAllocated.of_owned
      (hthirdOwned first second third)
    rw [hthirdSelector]
    simp [third, allocated, afterSecond, afterFirst]

/--
The common lookup-chip pattern: two complex selectors and one simple selector,
followed by lookup registration and one gate owned by the simple selector.
-/
@[circuit_norm]
theorem complexComplexSimpleLookupGate
    (gate : Selector → Selector → Selector → Gate F)
    (result : Selector → Selector → Selector → α)
    (queriedCells :
      Selector → Selector → Selector →
        List (Expression F Query))
    (tableMap :
      Selector → Selector → Selector →
        List (Expression F Query × TableColumn))
    (hselector : ∀ first second third,
      (gate first second third).selector.index = third.index)
    (howned : ∀ first second third,
      (gate first second third).SelectorsOwned) :
    PreservesGateSelectorsAllocated (do
      let first ← Halo2.complexSelector
      let second ← Halo2.complexSelector
      let third ← Halo2.selector
      Halo2.lookup (queriedCells first second third)
        (tableMap first second third)
      Halo2.createGate (gate first second third)
      return result first second third) := by
  constructor
  intro cs hcs
  simp only [gateSelectorsAllocated_run_bind,
    gateSelectorsAllocated_run_pure]
  let first := (Halo2.complexSelector (F := F) cs).1
  let afterFirst := (Halo2.complexSelector (F := F) cs).2
  let second := (Halo2.complexSelector (F := F) afterFirst).1
  let afterSecond := (Halo2.complexSelector (F := F) afterFirst).2
  let third := (Halo2.selector (F := F) afterSecond).1
  let allocated := (Halo2.selector (F := F) afterSecond).2
  let afterLookup :=
    (Halo2.lookup (queriedCells first second third)
      (tableMap first second third) allocated).2
  change ConstraintSystem.GateSelectorsAllocated
    ((Halo2.createGate
      (gate first second third) afterLookup).2)
  rw [ConstraintSystem.gateSelectorsAllocated_createGate]
  constructor
  · exact
      (lookup (queriedCells first second third)
        (tableMap first second third)).run allocated
        (PreservesGateSelectorsAllocated.selector.run afterSecond
          (PreservesGateSelectorsAllocated.complexSelector.run afterFirst
            (PreservesGateSelectorsAllocated.complexSelector.run cs hcs)))
  · apply Gate.SelectorsAllocated.of_owned
      (howned first second third)
    rw [hselector]
    have hcount :=
      ConstraintSystem.lookup_numSelectors
        (queriedCells first second third)
        (tableMap first second third) allocated
    change third.index < afterLookup.numSelectors
    rw [hcount]
    simp [third, allocated, afterSecond, afterFirst]

/--
The Sinsemilla-style registration pattern: allocate a complex selector, a fixed
column, and a simple selector, register a lookup, then register one owned gate for
each selector.
-/
@[circuit_norm]
theorem complexFixedSimpleLookupTwoGates
    (firstGate secondGate :
      Selector → Column .fixed → Selector → Gate F)
    (result : Selector → Column .fixed → Selector → α)
    (queriedCells :
      Selector → Column .fixed → Selector →
        List (Expression F Query))
    (tableMap :
      Selector → Column .fixed → Selector →
        List (Expression F Query × TableColumn))
    (hfirstSelector : ∀ complex fixed simple,
      (firstGate complex fixed simple).selector.index =
        simple.index)
    (hsecondSelector : ∀ complex fixed simple,
      (secondGate complex fixed simple).selector.index =
        complex.index)
    (hfirstOwned : ∀ complex fixed simple,
      (firstGate complex fixed simple).SelectorsOwned)
    (hsecondOwned : ∀ complex fixed simple,
      (secondGate complex fixed simple).SelectorsOwned) :
    PreservesGateSelectorsAllocated (do
      let complex ← Halo2.complexSelector
      let fixed ← Halo2.fixedColumn
      let simple ← Halo2.selector
      Halo2.lookup (queriedCells complex fixed simple)
        (tableMap complex fixed simple)
      Halo2.createGate (firstGate complex fixed simple)
      Halo2.createGate (secondGate complex fixed simple)
      return result complex fixed simple) := by
  constructor
  intro cs hcs
  simp only [gateSelectorsAllocated_run_bind,
    gateSelectorsAllocated_run_pure]
  let complex := (Halo2.complexSelector (F := F) cs).1
  let afterComplex := (Halo2.complexSelector (F := F) cs).2
  let fixed := (Halo2.fixedColumn (F := F) afterComplex).1
  let afterFixed := (Halo2.fixedColumn (F := F) afterComplex).2
  let simple := (Halo2.selector (F := F) afterFixed).1
  let allocated := (Halo2.selector (F := F) afterFixed).2
  let afterLookup :=
    (Halo2.lookup (queriedCells complex fixed simple)
      (tableMap complex fixed simple) allocated).2
  change ConstraintSystem.GateSelectorsAllocated
    ((Halo2.createGate
      (secondGate complex fixed simple)
      (Halo2.createGate
        (firstGate complex fixed simple) afterLookup).2).2)
  rw [ConstraintSystem.gateSelectorsAllocated_createGate]
  constructor
  · rw [ConstraintSystem.gateSelectorsAllocated_createGate]
    constructor
    · exact
        (lookup (queriedCells complex fixed simple)
          (tableMap complex fixed simple)).run allocated
          (PreservesGateSelectorsAllocated.selector.run afterFixed
            (PreservesGateSelectorsAllocated.fixedColumn.run afterComplex
              (PreservesGateSelectorsAllocated.complexSelector.run cs hcs)))
    · apply Gate.SelectorsAllocated.of_owned
        (hfirstOwned complex fixed simple)
      rw [hfirstSelector]
      have hcount :=
        ConstraintSystem.lookup_numSelectors
          (queriedCells complex fixed simple)
          (tableMap complex fixed simple) allocated
      change simple.index < afterLookup.numSelectors
      rw [hcount]
      simp [simple, allocated, afterFixed, afterComplex]
  · apply Gate.SelectorsAllocated.of_owned
      (hsecondOwned complex fixed simple)
    rw [hsecondSelector]
    rw [ConstraintSystem.createGate_numSelectors]
    have hcount :=
      ConstraintSystem.lookup_numSelectors
        (queriedCells complex fixed simple)
        (tableMap complex fixed simple) allocated
    rw [hcount]
    simp [complex, allocated, afterFixed, afterComplex]

/--
Carry a freshly allocated simple selector through a count-preserving subprogram and
use it in one later owned gate.

This is the relational rule for child configure functions that intentionally accept
a selector allocated by their parent. Such a child cannot truthfully preserve
allocation from every arbitrary starting state; `hprogram` receives the exact
fresh-index fact instead.
-/
@[circuit_norm]
theorem selectorProgramGate
    (program : Selector → Configure F β)
    (gate : Selector → β → Gate F)
    (result : Selector → β → α)
    (hprogram : ∀ selector cs,
      cs.GateSelectorsAllocated →
      selector.index < cs.numSelectors →
      ((program selector) cs).2.GateSelectorsAllocated)
    (hprogramCount : ∀ selector cs,
      ((program selector) cs).2.numSelectors =
        cs.numSelectors)
    (hselector : ∀ selector cs,
      (gate selector
        ((program selector) cs).1).selector.index =
          selector.index)
    (howned : ∀ selector cs,
      (gate selector
        ((program selector) cs).1).SelectorsOwned) :
    PreservesGateSelectorsAllocated (do
      let selector ← Halo2.selector
      let value ← program selector
      Halo2.createGate (gate selector value)
      return result selector value) := by
  constructor
  intro cs hcs
  simp only [gateSelectorsAllocated_run_bind,
    gateSelectorsAllocated_run_pure]
  let selector := (Halo2.selector (F := F) cs).1
  let allocated := (Halo2.selector (F := F) cs).2
  let value := ((program selector) allocated).1
  let afterProgram := ((program selector) allocated).2
  change ConstraintSystem.GateSelectorsAllocated
    ((Halo2.createGate
      (gate selector value) afterProgram).2)
  rw [ConstraintSystem.gateSelectorsAllocated_createGate]
  constructor
  · apply hprogram selector allocated
    · exact PreservesGateSelectorsAllocated.selector.run cs hcs
    · simp [selector, allocated]
  · apply Gate.SelectorsAllocated.of_owned
      (howned selector allocated)
    rw [hselector selector allocated]
    rw [hprogramCount selector allocated]
    simp [selector, allocated]

/-- Run a preserving configure program from the empty Halo 2 builder state. -/
theorem fromEmpty
    {program : Configure F α}
    (hprogram : PreservesGateSelectorsAllocated program) :
    (program {}).2.GateSelectorsAllocated :=
  hprogram.run {} ConstraintSystem.gateSelectorsAllocated_empty

end PreservesGateSelectorsAllocated

end Configure

/--
The inner greedy scan only transfers selector descriptions between the chosen
combination and the remainder.
-/
theorem extendCombination_length_conservation
    (maxDegree d : ℕ) (comb selectors : List SelectorDescription) :
    let result := extendCombination maxDegree d comb selectors
    result.1.length + result.2.length =
      comb.length + selectors.length := by
  induction selectors generalizing d comb with
  | nil =>
      simp [extendCombination]
  | cons selector rest ih =>
      simp only [extendCombination]
      split
      · simp
      · split
        · generalize hresult :
            extendCombination maxDegree d comb rest = result
          rcases result with ⟨chosen, remaining⟩
          have hlength := ih d comb
          rw [hresult] at hlength
          simp only [List.length_cons] at hlength ⊢
          omega
        · let nextDegree :=
            max d (selector.maxDegree - 1)
          split
          · generalize hresult :
              extendCombination maxDegree d comb rest = result
            rcases result with ⟨chosen, remaining⟩
            have hlength := ih d comb
            rw [hresult] at hlength
            simp only [List.length_cons] at hlength ⊢
            omega
          · have hlength :=
              ih nextDegree (comb ++ [selector])
            simpa [nextDegree, Nat.add_assoc, Nat.add_left_comm,
              Nat.add_comm] using hlength

/--
The inner greedy scan partitions the initial combination and candidate list:
it neither drops nor invents selector descriptions.
-/
theorem mem_extendCombination_iff
    (maxDegree d : ℕ) (comb selectors : List SelectorDescription)
    (description : SelectorDescription) :
    description ∈ (extendCombination maxDegree d comb selectors).1 ∨
        description ∈ (extendCombination maxDegree d comb selectors).2 ↔
      description ∈ comb ∨ description ∈ selectors := by
  induction selectors generalizing d comb with
  | nil =>
      simp [extendCombination]
  | cons selector rest ih =>
      simp only [extendCombination]
      split
      · simp [or_assoc, or_comm]
      · split
        · generalize hresult :
            extendCombination maxDegree d comb rest = result
          rcases result with ⟨chosen, remaining⟩
          have hpartition := ih d comb
          rw [hresult] at hpartition
          simp only [List.mem_cons] at *
          change
            (description ∈ chosen ∨ description = selector ∨
              description ∈ remaining) ↔
            (description ∈ comb ∨ description = selector ∨
              description ∈ rest)
          constructor
          · intro h
            rcases h with hchosen | rfl | hremaining
            · rcases hpartition.mp (Or.inl hchosen) with
                hcomb | hrest
              · exact Or.inl hcomb
              · exact Or.inr (Or.inr hrest)
            · exact Or.inr (Or.inl rfl)
            · rcases hpartition.mp (Or.inr hremaining) with
                hcomb | hrest
              · exact Or.inl hcomb
              · exact Or.inr (Or.inr hrest)
          · intro h
            rcases h with hcomb | rfl | hrest
            · rcases hpartition.mpr (Or.inl hcomb) with
                hchosen | hremaining
              · exact Or.inl hchosen
              · exact Or.inr (Or.inr hremaining)
            · exact Or.inr (Or.inl rfl)
            · rcases hpartition.mpr (Or.inr hrest) with
                hchosen | hremaining
              · exact Or.inl hchosen
              · exact Or.inr (Or.inr hremaining)
        · let nextDegree :=
            max d (selector.maxDegree - 1)
          split
          · generalize hresult :
              extendCombination maxDegree d comb rest = result
            rcases result with ⟨chosen, remaining⟩
            have hpartition := ih d comb
            rw [hresult] at hpartition
            simp only [List.mem_cons] at *
            change
              (description ∈ chosen ∨ description = selector ∨
                description ∈ remaining) ↔
              (description ∈ comb ∨ description = selector ∨
                description ∈ rest)
            constructor
            · intro h
              rcases h with hchosen | rfl | hremaining
              · rcases hpartition.mp (Or.inl hchosen) with
                  hcomb | hrest
                · exact Or.inl hcomb
                · exact Or.inr (Or.inr hrest)
              · exact Or.inr (Or.inl rfl)
              · rcases hpartition.mp (Or.inr hremaining) with
                  hcomb | hrest
                · exact Or.inl hcomb
                · exact Or.inr (Or.inr hrest)
            · intro h
              rcases h with hcomb | rfl | hrest
              · rcases hpartition.mpr (Or.inl hcomb) with
                  hchosen | hremaining
                · exact Or.inl hchosen
                · exact Or.inr (Or.inr hremaining)
              · exact Or.inr (Or.inl rfl)
              · rcases hpartition.mpr (Or.inr hrest) with
                  hchosen | hremaining
                · exact Or.inl hchosen
                · exact Or.inr (Or.inr hremaining)
          · generalize hresult :
              extendCombination maxDegree nextDegree
                (comb ++ [selector]) rest = result
            rcases result with ⟨chosen, remaining⟩
            have hpartition :=
              ih nextDegree (comb ++ [selector])
            rw [hresult] at hpartition
            simp only [List.mem_cons] at *
            change
              (description ∈ chosen ∨ description ∈ remaining) ↔
              (description ∈ comb ∨ description = selector ∨
                description ∈ rest)
            simpa only [List.mem_append, List.mem_singleton,
              or_assoc] using hpartition

/-- The inner scan's remaining candidates are no longer than its input candidates. -/
theorem extendCombination_remaining_length_le
    (maxDegree d : ℕ) (comb selectors : List SelectorDescription) :
    (extendCombination maxDegree d comb selectors).2.length ≤
      selectors.length := by
  induction selectors generalizing d comb with
  | nil =>
      simp [extendCombination]
  | cons selector rest ih =>
      simp only [extendCombination]
      split
      · simp
      · split
        · generalize hresult :
            extendCombination maxDegree d comb rest = result
          rcases result with ⟨chosen, remaining⟩
          have hlength := ih d comb
          rw [hresult] at hlength
          change remaining.length ≤ rest.length at hlength
          simpa only [List.length_cons] using
            Nat.succ_le_succ hlength
        · let nextDegree :=
            max d (selector.maxDegree - 1)
          split
          · generalize hresult :
              extendCombination maxDegree d comb rest = result
            rcases result with ⟨chosen, remaining⟩
            have hlength := ih d comb
            rw [hresult] at hlength
            change remaining.length ≤ rest.length at hlength
            simpa only [List.length_cons] using
              Nat.succ_le_succ hlength
          · exact (ih nextDegree (comb ++ [selector])).trans
              (Nat.le_succ _)

/-- Every list member occurs in the list paired with its zero-based index. -/
private theorem exists_mem_zipIdx_of_mem
    {α : Type} {item : α} {items : List α}
    (hitem : item ∈ items) :
    ∃ index, (item, index) ∈ items.zipIdx := by
  obtain ⟨index, hindex, hget⟩ :=
    List.mem_iff_getElem.mp hitem
  refine ⟨index, ?_⟩
  rw [List.mk_mem_zipIdx_iff_getElem?,
    List.getElem?_eq_some_iff]
  exact ⟨hindex, hget⟩

/--
With enough outer-loop fuel, every candidate occurs in one returned selector
combination.
-/
theorem exists_mem_buildCombinations
    (maxDegree fuel : ℕ) (selectors : List SelectorDescription)
    (hfuel : selectors.length ≤ fuel)
    {description : SelectorDescription}
    (hdescription : description ∈ selectors) :
    ∃ combination ∈ buildCombinations maxDegree fuel selectors,
      description ∈ combination := by
  induction fuel generalizing selectors with
  | zero =>
      have : selectors = [] := List.eq_nil_of_length_eq_zero (by omega)
      simp [this] at hdescription
  | succ fuel ih =>
      cases selectors with
      | nil =>
          simp at hdescription
      | cons selector rest =>
          simp only [buildCombinations]
          generalize hresult :
              extendCombination maxDegree
                (selector.maxDegree - 1) [selector] rest =
                result
          rcases result with ⟨chosen, remaining⟩
          have hsource :
              description ∈ [selector] ∨ description ∈ rest := by
            simpa only [List.mem_cons, List.mem_singleton,
              List.not_mem_nil, or_false] using hdescription
          have hpartition :=
            (mem_extendCombination_iff maxDegree
              (selector.maxDegree - 1) [selector] rest
              description).mpr hsource
          rw [hresult] at hpartition
          rcases hpartition with hchosen | hremaining
          · exact ⟨chosen, List.mem_cons_self, hchosen⟩
          · have hremainingLength :=
              extendCombination_remaining_length_le maxDegree
                (selector.maxDegree - 1) [selector] rest
            rw [hresult] at hremainingLength
            change remaining.length ≤ rest.length at hremainingLength
            have hremainingFuel : remaining.length ≤ fuel := by
              simp only [List.length_cons] at hfuel
              omega
            obtain ⟨combination, hcombination, hmember⟩ :=
              ih remaining hremainingFuel hremaining
            exact ⟨combination,
              List.mem_cons_of_mem chosen hcombination, hmember⟩

/--
The greedy extension never exceeds the degree budget when its initial combination
already fits.  Candidate degrees need no separate bound: the algorithm checks the
updated degree and length before every insertion.
-/
theorem extendCombination_length_le
    (maxDegree d : ℕ) (comb selectors : List SelectorDescription)
    (hcomb : comb.length ≤ maxDegree) :
    (extendCombination maxDegree d comb selectors).1.length ≤
      maxDegree := by
  induction selectors generalizing d comb with
  | nil =>
      simpa [extendCombination] using hcomb
  | cons selector rest ih =>
      simp only [extendCombination]
      split
      · exact hcomb
      · split
        · exact ih d comb hcomb
        · let nextDegree :=
            max d (selector.maxDegree - 1)
          split
          · exact ih d comb hcomb
          · apply ih nextDegree (comb ++ [selector])
            simp only [List.length_append, List.length_singleton]
            omega

/-- Every combination returned by the outer packing loop fits in its input list. -/
theorem length_le_of_mem_buildCombinations
    (maxDegree fuel : ℕ) (selectors combination :
      List SelectorDescription)
    (hcombination :
      combination ∈ buildCombinations maxDegree fuel selectors) :
    combination.length ≤ selectors.length := by
  induction fuel generalizing selectors with
  | zero =>
      simp [buildCombinations] at hcombination
  | succ fuel ih =>
      cases selectors with
      | nil =>
          simp [buildCombinations] at hcombination
      | cons selector rest =>
          simp only [buildCombinations] at hcombination
          generalize hresult :
              extendCombination maxDegree
                (selector.maxDegree - 1) [selector] rest =
                result at hcombination
          rcases result with ⟨chosen, remaining⟩
          simp only [List.mem_cons] at hcombination
          have hlength :=
            extendCombination_length_conservation maxDegree
              (selector.maxDegree - 1) [selector] rest
          rw [hresult] at hlength
          simp only [List.length_cons, List.length_nil,
            Nat.zero_add] at hlength
          rcases hcombination with rfl | hcombination
          · simp only [List.length_cons]
            omega
          · have hrecursive :=
              ih remaining hcombination
            simp only [List.length_cons]
            omega

/--
Every combination returned by the outer packing loop fits in the selector
compression degree budget.
-/
theorem length_le_maxDegree_of_mem_buildCombinations
    (maxDegree fuel : ℕ) (selectors combination :
      List SelectorDescription)
    (hpositive : 1 ≤ maxDegree)
    (hcombination :
      combination ∈ buildCombinations maxDegree fuel selectors) :
    combination.length ≤ maxDegree := by
  induction fuel generalizing selectors with
  | zero =>
      simp [buildCombinations] at hcombination
  | succ fuel ih =>
      cases selectors with
      | nil =>
          simp [buildCombinations] at hcombination
      | cons selector rest =>
          simp only [buildCombinations] at hcombination
          generalize hresult :
              extendCombination maxDegree
                (selector.maxDegree - 1) [selector] rest =
                result at hcombination
          rcases result with ⟨chosen, remaining⟩
          simp only [List.mem_cons] at hcombination
          rcases hcombination with rfl | hcombination
          · have hchosen :=
              extendCombination_length_le maxDegree
                (selector.maxDegree - 1) [selector] rest
                (by simpa using hpositive)
            simpa [hresult] using hchosen
          · exact ih remaining hcombination

/--
Every `process` entry receives a positive root within its combination, and the
combination cannot be larger than the input selector list.
-/
theorem process_entry_root_bounds
    (selectors : List SelectorDescription) (maxDegree : ℕ)
    (entry : ℕ × SelCompress)
    (hentry : entry ∈ (process selectors maxDegree).entries) :
    1 ≤ entry.2.assignedRoot ∧
      entry.2.assignedRoot ≤ entry.2.combinationLen ∧
      entry.2.combinationLen ≤ selectors.length := by
  let degreeZero := selectors.filter (·.maxDegree = 0)
  let remaining := selectors.filter (·.maxDegree ≠ 0)
  let combinations :=
    buildCombinations maxDegree remaining.length remaining
  change entry ∈
    (degreeZero.zipIdx.map fun (description, column) =>
      (description.selector, SelCompress.mk column 1 1)) ++
    (combinations.zipIdx.flatMap fun (combination, column) =>
      combination.zipIdx.map fun (description, position) =>
        (description.selector,
          SelCompress.mk (degreeZero.length + column)
            combination.length (position + 1))) at hentry
  rw [List.mem_append] at hentry
  rcases hentry with hdegreeZero | hcombination
  · obtain ⟨indexed, hindexed, rfl⟩ :=
      List.mem_map.mp hdegreeZero
    have hdescription : indexed.1 ∈ selectors := by
      have hfiltered :=
        List.fst_mem_of_mem_zipIdx hindexed
      exact (List.mem_filter.mp hfiltered).1
    have hselectorsPositive : 1 ≤ selectors.length := by
      have := List.length_pos_of_mem hdescription
      omega
    simpa using hselectorsPositive
  · rw [List.mem_flatMap] at hcombination
    obtain ⟨indexedCombination, hindexedCombination,
      hcombinationEntry⟩ := hcombination
    rcases indexedCombination with ⟨combination, column⟩
    obtain ⟨indexedDescription, hindexedDescription, rfl⟩ :=
      List.mem_map.mp hcombinationEntry
    rcases indexedDescription with ⟨description, position⟩
    have hposition :
        position < combination.length := by
      simpa using
        List.snd_lt_of_mem_zipIdx hindexedDescription
    have hcombinationMem :
        combination ∈ combinations :=
      List.fst_mem_of_mem_zipIdx hindexedCombination
    have hcombinationLength :
        combination.length ≤ remaining.length :=
      length_le_of_mem_buildCombinations maxDegree remaining.length
        remaining combination hcombinationMem
    have hremainingLength :
        remaining.length ≤ selectors.length := by
      exact List.length_filter_le _ _
    change 1 ≤ position + 1 ∧
      position + 1 ≤ combination.length ∧
      combination.length ≤ selectors.length
    refine ⟨by omega, by omega, ?_⟩
    exact hcombinationLength.trans hremainingLength

/--
Every `process` entry's assigned root is bounded by the compression degree,
independently of how many selectors the circuit declares.
-/
theorem process_entry_root_degree_bounds
    (selectors : List SelectorDescription) (maxDegree : ℕ)
    (hpositive : 1 ≤ maxDegree)
    (entry : ℕ × SelCompress)
    (hentry : entry ∈ (process selectors maxDegree).entries) :
    1 ≤ entry.2.assignedRoot ∧
      entry.2.assignedRoot ≤ entry.2.combinationLen ∧
      entry.2.combinationLen ≤ maxDegree := by
  let degreeZero := selectors.filter (·.maxDegree = 0)
  let remaining := selectors.filter (·.maxDegree ≠ 0)
  let combinations :=
    buildCombinations maxDegree remaining.length remaining
  change entry ∈
    (degreeZero.zipIdx.map fun (description, column) =>
      (description.selector, SelCompress.mk column 1 1)) ++
    (combinations.zipIdx.flatMap fun (combination, column) =>
      combination.zipIdx.map fun (description, position) =>
        (description.selector,
          SelCompress.mk (degreeZero.length + column)
            combination.length (position + 1))) at hentry
  rw [List.mem_append] at hentry
  rcases hentry with hdegreeZero | hcombination
  · obtain ⟨indexed, _hindexed, rfl⟩ :=
      List.mem_map.mp hdegreeZero
    simpa using hpositive
  · rw [List.mem_flatMap] at hcombination
    obtain ⟨indexedCombination, hindexedCombination,
      hcombinationEntry⟩ := hcombination
    rcases indexedCombination with ⟨combination, column⟩
    obtain ⟨indexedDescription, hindexedDescription, rfl⟩ :=
      List.mem_map.mp hcombinationEntry
    rcases indexedDescription with ⟨description, position⟩
    have hposition :
        position < combination.length := by
      simpa using
        List.snd_lt_of_mem_zipIdx hindexedDescription
    have hcombinationMem :
        combination ∈ combinations :=
      List.fst_mem_of_mem_zipIdx hindexedCombination
    have hcombinationLength :
        combination.length ≤ maxDegree :=
      length_le_maxDegree_of_mem_buildCombinations
        maxDegree remaining.length remaining combination
        hpositive hcombinationMem
    change 1 ≤ position + 1 ∧
      position + 1 ≤ combination.length ∧
      combination.length ≤ maxDegree
    exact ⟨by omega, by omega, hcombinationLength⟩

/-- Every input selector description receives an entry in the packed map. -/
theorem exists_mem_process_entries
    (selectors : List SelectorDescription) (maxDegree : ℕ)
    {description : SelectorDescription}
    (hdescription : description ∈ selectors) :
    ∃ compressed,
      (description.selector, compressed) ∈
        (process selectors maxDegree).entries := by
  let degreeZero := selectors.filter (·.maxDegree = 0)
  let remaining := selectors.filter (·.maxDegree ≠ 0)
  let combinations :=
    buildCombinations maxDegree remaining.length remaining
  change ∃ compressed,
    (description.selector, compressed) ∈
      (degreeZero.zipIdx.map fun (source, column) =>
        (source.selector, SelCompress.mk column 1 1)) ++
      (combinations.zipIdx.flatMap fun (combination, column) =>
        combination.zipIdx.map fun (source, position) =>
          (source.selector,
            SelCompress.mk (degreeZero.length + column)
              combination.length (position + 1)))
  by_cases hdegree : description.maxDegree = 0
  · have hdegreeZero : description ∈ degreeZero :=
      List.mem_filter.mpr ⟨hdescription, by simp [hdegree]⟩
    obtain ⟨column, hzip⟩ :=
      exists_mem_zipIdx_of_mem hdegreeZero
    refine ⟨SelCompress.mk column 1 1, ?_⟩
    apply List.mem_append_left
    exact List.mem_map.mpr
      ⟨(description, column), hzip, rfl⟩
  · have hremaining : description ∈ remaining :=
      List.mem_filter.mpr ⟨hdescription, by simp [hdegree]⟩
    obtain ⟨combination, hcombination, hmember⟩ :=
      exists_mem_buildCombinations maxDegree remaining.length
        remaining (Nat.le_refl _) hremaining
    obtain ⟨column, hcombinationZip⟩ :=
      exists_mem_zipIdx_of_mem hcombination
    obtain ⟨position, hdescriptionZip⟩ :=
      exists_mem_zipIdx_of_mem hmember
    refine
      ⟨SelCompress.mk (degreeZero.length + column)
        combination.length (position + 1), ?_⟩
    apply List.mem_append_right
    rw [List.mem_flatMap]
    exact ⟨(combination, column), hcombinationZip,
      List.mem_map.mpr
        ⟨(description, position), hdescriptionZip, rfl⟩⟩

/-- An association-list entry makes the corresponding map lookup present. -/
theorem SelCompressMap.lookup_isSome_of_mem
    (map : SelCompressMap) {selector : ℕ} {compressed : SelCompress}
    (hentry : (selector, compressed) ∈ map.entries) :
    (map.lookup selector).isSome = true := by
  have hfind :
      (map.entries.find? (fun entry => entry.1 = selector)).isSome := by
    rw [List.find?_isSome]
    exact ⟨(selector, compressed), hentry, by simp⟩
  obtain ⟨entry, hentryEq⟩ :=
    Option.isSome_iff_exists.mp hfind
  simp [SelCompressMap.lookup, hentryEq]

/-- `process` covers every input selector key. -/
theorem process_lookup_isSome_of_mem
    (selectors : List SelectorDescription) (maxDegree : ℕ)
    {description : SelectorDescription}
    (hdescription : description ∈ selectors) :
    ((process selectors maxDegree).lookup
      description.selector).isSome = true := by
  obtain ⟨compressed, hentry⟩ :=
    exists_mem_process_entries selectors maxDegree hdescription
  exact SelCompressMap.lookup_isSome_of_mem
    (process selectors maxDegree) hentry

/--
A degree-zero selector is looked up with the dedicated degree-zero packing datum.
No uniqueness hypothesis on selector indices is needed: all degree-zero entries form
the prefix of `process.entries`, and every datum in that prefix has length/root `1`.
-/
theorem process_lookup_degreeZero_of_mem
    (selectors : List SelectorDescription) (maxDegree : ℕ)
    {description : SelectorDescription}
    (hdescription : description ∈ selectors)
    (hdegree : description.maxDegree = 0) :
    ∃ compressed,
      (process selectors maxDegree).lookup description.selector =
        some compressed ∧
      compressed.combinationLen = 1 ∧
      compressed.assignedRoot = 1 := by
  let degreeZero := selectors.filter (·.maxDegree = 0)
  let remaining := selectors.filter (·.maxDegree ≠ 0)
  let degreeZeroEntries :=
    degreeZero.zipIdx.map fun (source, column) =>
      (source.selector, SelCompress.mk column 1 1)
  let combinations :=
    buildCombinations maxDegree remaining.length remaining
  let combinationEntries :=
    combinations.zipIdx.flatMap fun (combination, column) =>
      combination.zipIdx.map fun (source, position) =>
        (source.selector,
          SelCompress.mk (degreeZero.length + column)
            combination.length (position + 1))
  have hdegreeZero : description ∈ degreeZero :=
    List.mem_filter.mpr ⟨hdescription, by simp [hdegree]⟩
  obtain ⟨column, hzip⟩ :=
    exists_mem_zipIdx_of_mem hdegreeZero
  have hentry :
      (description.selector, SelCompress.mk column 1 1) ∈
        degreeZeroEntries := by
    exact List.mem_map.mpr
      ⟨(description, column), hzip, rfl⟩
  have hfindSome :
      (degreeZeroEntries.find?
        (fun entry => entry.1 = description.selector)).isSome = true := by
    rw [List.find?_isSome]
    exact ⟨(description.selector, SelCompress.mk column 1 1),
      hentry, by simp⟩
  obtain ⟨entry, hfind⟩ :=
    Option.isSome_iff_exists.mp hfindSome
  have hentryMem : entry ∈ degreeZeroEntries :=
    List.mem_of_find?_eq_some hfind
  obtain ⟨indexed, hindexed, hentryEq⟩ :=
    List.mem_map.mp hentryMem
  rcases indexed with ⟨source, sourceColumn⟩
  subst entry
  let compressed := SelCompress.mk sourceColumn 1 1
  refine ⟨compressed, ?_, rfl, rfl⟩
  change
    Option.map Prod.snd
      (List.find? (fun entry => entry.1 = description.selector)
        (degreeZeroEntries ++ combinationEntries)) =
      some compressed
  rw [List.find?_append, hfind, Option.some_or]
  rfl

/-- A successful association-list lookup originates in the map's entries. -/
theorem SelCompressMap.exists_mem_entries_of_lookup
    (map : SelCompressMap) {selector : ℕ} {compressed : SelCompress}
    (hlookup : map.lookup selector = some compressed) :
    ∃ entry ∈ map.entries, entry.2 = compressed := by
  simp only [SelCompressMap.lookup, Option.map_eq_some_iff] at hlookup
  obtain ⟨entry, hfind, hcompressed⟩ := hlookup
  exact ⟨entry, List.mem_of_find?_eq_some hfind, hcompressed⟩

/-- Mapping a fixed-column offset over every entry preserves successful lookup. -/
private theorem SelCompressMap.lookup_mapPackedOffset
    (map : SelCompressMap) (offset selector : ℕ)
    {source : SelCompress}
    (hlookup : map.lookup selector = some source) :
    ({ newFixedCols := map.newFixedCols
       entries := map.entries.map fun (key, compressed) =>
         (key, { compressed with
           packedCol := compressed.packedCol + offset }) } :
        SelCompressMap).lookup selector =
      some { source with
        packedCol := source.packedCol + offset } := by
  rcases map with ⟨newFixedCols, entries⟩
  simp only [SelCompressMap.lookup] at hlookup ⊢
  induction entries with
  | nil =>
      simp at hlookup
  | cons entry rest ih =>
      rcases entry with ⟨key, compressed⟩
      simp only [List.map_cons, List.find?_cons] at hlookup ⊢
      by_cases heq : key = selector
      · simp only [heq, decide_true] at hlookup ⊢
        simp only [Option.map_some] at hlookup ⊢
        have hsource : compressed = source :=
          Option.some.inj hlookup
        subst compressed
        rfl
      · simp only [heq, decide_false] at hlookup ⊢
        exact ih hlookup

/--
The circuit-derived compression map covers every allocated selector index.
Selector packing changes columns and roots, but never drops a configured selector.
-/
theorem deriveSelCompressMap_lookup_isSome_of_lt
    {F : Type} (cs : ConstraintSystem F) (n : ℕ)
    (activations : List (ℕ × ℕ)) {selector : ℕ}
    (hselector : selector < cs.numSelectors) :
    ((deriveSelCompressMap cs n activations).lookup selector).isSome =
      true := by
  let table := activationTable n cs.numSelectors activations
  let degrees := selectorMaxDegrees cs
  let descriptions :=
    (List.range cs.numSelectors).map fun index =>
      SelectorDescription.mk index table[index]! degrees[index]!
  let packing := process descriptions (csDegree cs)
  let description :=
    SelectorDescription.mk selector
      table[selector]! degrees[selector]!
  have hdescription : description ∈ descriptions := by
    apply List.mem_map.mpr
    exact ⟨selector, List.mem_range.mpr hselector, rfl⟩
  obtain ⟨source, hsource⟩ :=
    exists_mem_process_entries descriptions (csDegree cs)
      hdescription
  let compressed : SelCompress :=
    { source with
      packedCol := source.packedCol + cs.numFixedColumns }
  apply SelCompressMap.lookup_isSome_of_mem
  change (selector, compressed) ∈
    packing.entries.map (fun (sourceSelector, sourceCompressed) =>
      (sourceSelector,
        { sourceCompressed with
          packedCol :=
            sourceCompressed.packedCol + cs.numFixedColumns }))
  exact List.mem_map.mpr
    ⟨(selector, source), hsource, rfl⟩

/--
A selector with no gate degree is packed alone by the circuit-derived map. Its
column is in the newly appended fixed-column suffix.
-/
theorem deriveSelCompressMap_lookup_degreeZero_of_lt
    {F : Type} (cs : ConstraintSystem F) (n : ℕ)
    (activations : List (ℕ × ℕ)) {selector : ℕ}
    (hselector : selector < cs.numSelectors)
    (hdegree : (selectorMaxDegrees cs)[selector]! = 0) :
    ∃ compressed,
      (deriveSelCompressMap cs n activations).lookup selector =
        some compressed ∧
      compressed.combinationLen = 1 ∧
      compressed.assignedRoot = 1 ∧
      cs.numFixedColumns ≤ compressed.packedCol := by
  let table := activationTable n cs.numSelectors activations
  let degrees := selectorMaxDegrees cs
  let descriptions :=
    (List.range cs.numSelectors).map fun index =>
      SelectorDescription.mk index table[index]! degrees[index]!
  let packing := process descriptions (csDegree cs)
  let description :=
    SelectorDescription.mk selector table[selector]! degrees[selector]!
  have hdescription : description ∈ descriptions := by
    apply List.mem_map.mpr
    exact ⟨selector, List.mem_range.mpr hselector, rfl⟩
  have hdescriptionDegree : description.maxDegree = 0 :=
    hdegree
  obtain ⟨source, hsource, hlength, hroot⟩ :=
    process_lookup_degreeZero_of_mem descriptions (csDegree cs)
      hdescription hdescriptionDegree
  let compressed : SelCompress :=
    { source with
      packedCol := source.packedCol + cs.numFixedColumns }
  refine ⟨compressed, ?_, hlength, hroot, by
    simp only [compressed]
    omega⟩
  have hsource' : packing.lookup selector = some source := by
    simpa only [packing, descriptions, description, degrees, table] using
      hsource
  change
    ({ newFixedCols := packing.newFixedCols
       entries := packing.entries.map fun (key, source) =>
         (key, { source with
           packedCol := source.packedCol + cs.numFixedColumns }) } :
      SelCompressMap).lookup selector = some compressed
  exact SelCompressMap.lookup_mapPackedOffset
    packing cs.numFixedColumns selector hsource'

/--
The circuit-derived compression map covers every selector atom of every configured
gate once the configure phase certifies that those atoms name allocated selectors.
-/
theorem gateSelectorsCovered_deriveSelCompressMap
    {F : Type} (cs : ConstraintSystem F) (n : ℕ)
    (activations : List (ℕ × ℕ))
    (hallocated : cs.GateSelectorsAllocated) :
    ∀ expression ∈ flatGates cs,
      expression.selectorsCovered
        (fun selector =>
          ((deriveSelCompressMap cs n activations).lookup selector).isSome) =
        true := by
  intro expression hexpression
  rw [flatGates, List.mem_flatMap] at hexpression
  obtain ⟨gate, hgate, hexpression⟩ := hexpression
  obtain ⟨constraint, hconstraint, hexpression⟩ :=
    List.mem_map.mp hexpression
  subst expression
  apply Expression.selectorsCovered_mono
    (fun selector => decide (selector < cs.numSelectors))
  · intro selector hselector
    exact deriveSelCompressMap_lookup_isSome_of_lt
      cs n activations (of_decide_eq_true hselector)
  · exact hallocated.constraint hgate hconstraint

end Halo2

namespace Halo2.Layout

set_option maxHeartbeats 20000

/--
Folding `HashSet.insert` over a list retains every element of both the initial
set and the input list.
-/
private theorem mem_foldl_insert_iff
    (item : ℕ × ℕ) (items : List (ℕ × ℕ))
    (initial : Std.HashSet (ℕ × ℕ)) :
    item ∈ items.foldl (fun set next => set.insert next) initial ↔
      item ∈ initial ∨ item ∈ items := by
  induction items generalizing initial with
  | nil =>
      simp
  | cons head tail ih =>
      rw [List.foldl_cons, ih]
      simp only [Std.HashSet.mem_insert, beq_iff_eq, List.mem_cons]
      aesop

/--
Every activated selector with a compression-map entry is emitted by the generic
layout compiler as the corresponding packed fixed assignment.
-/
theorem mem_selectorFixed_of_activation
    (map : SelCompressMap) (activationRows : List (ℕ × ℕ))
    {selector row : ℕ} {compressed : SelCompress}
    (hactivation : (selector, row) ∈ activationRows)
    (hlookup : map.lookup selector = some compressed) :
    (compressed.packedCol, row, compressed.assignedRoot) ∈
      selectorFixed map activationRows := by
  simp only [SelCompressMap.lookup, Option.map_eq_some_iff] at hlookup
  obtain ⟨entry, hfind, hcompressed⟩ := hlookup
  unfold selectorFixed
  rw [List.mem_filterMap]
  refine ⟨(selector, row), ?_, ?_⟩
  · rw [Std.HashSet.mem_toList, mem_foldl_insert_iff]
    exact Or.inr hactivation
  · simp only [hfind, Option.map_some]
    rw [← hcompressed]

/--
Conversely, every packed fixed assignment emitted by `selectorFixed` retains the
row of some source activation.  Selector deduplication may forget multiplicity and
order, but it cannot invent rows.
-/
theorem exists_activation_of_mem_selectorFixed
    (map : SelCompressMap) (activationRows : List (ℕ × ℕ))
    {column row value : ℕ}
    (hentry :
      (column, row, value) ∈ selectorFixed map activationRows) :
    ∃ selector, (selector, row) ∈ activationRows := by
  unfold selectorFixed at hentry
  rw [List.mem_filterMap] at hentry
  obtain ⟨⟨selector, sourceRow⟩, huniq, hmapped⟩ := hentry
  rw [Std.HashSet.mem_toList, mem_foldl_insert_iff] at huniq
  rcases huniq with hfalse | hactivation
  · simp at hfalse
  · simp only [Option.map_eq_some_iff] at hmapped
    obtain ⟨entry, _hfind, hresult⟩ := hmapped
    simp only [Prod.mk.injEq] at hresult
    exact ⟨selector, by simpa [hresult.2.1] using hactivation⟩

end Halo2.Layout

namespace Zcash.Snark

open Zcash.Arithmetic (scalarFieldOrder)
open Halo2
open Halo2.Layout

set_option maxHeartbeats 20000

/--
The selector packer assigns valid roots whenever its compression degree fits below
the scalar-field characteristic.
-/
theorem selectorRootsWellFormed_process
    (selectors : List SelectorDescription) (maxDegree : ℕ)
    (hpositive : 1 ≤ maxDegree)
    (hdegree : maxDegree < scalarFieldOrder) :
    SelectorRootsWellFormed (process selectors maxDegree) := by
  intro selector compressed hlookup
  obtain ⟨entry, hentry, hcompressed⟩ :=
    SelCompressMap.exists_mem_entries_of_lookup
      (process selectors maxDegree) hlookup
  have hbounds :=
    process_entry_root_degree_bounds selectors maxDegree
      hpositive entry hentry
  rw [← hcompressed]
  exact ⟨hbounds.1, hbounds.2.1,
    hbounds.2.2.trans_lt hdegree⟩

/--
The circuit-derived selector map has valid roots under the minimal generic size
condition: the constraint-system degree is below the scalar-field order.
-/
theorem selectorRootsWellFormed_deriveSelCompressMap
    {F : Type} (cs : ConstraintSystem F) (n : ℕ)
    (activations : List (ℕ × ℕ))
    (hdegree : csDegree cs < scalarFieldOrder) :
    SelectorRootsWellFormed
      (deriveSelCompressMap cs n activations) := by
  let table := activationTable n cs.numSelectors activations
  let degrees := selectorMaxDegrees cs
  let descriptions :=
    (List.range cs.numSelectors).map fun index =>
      SelectorDescription.mk index table[index]! degrees[index]!
  let packing := process descriptions (csDegree cs)
  intro selector compressed hlookup
  obtain ⟨entry, hentry, hcompressed⟩ :=
    SelCompressMap.exists_mem_entries_of_lookup
      (deriveSelCompressMap cs n activations) hlookup
  change entry ∈ packing.entries.map (fun (sourceSelector, source) =>
    (sourceSelector,
      { source with
        packedCol := source.packedCol + cs.numFixedColumns })) at hentry
  obtain ⟨⟨sourceSelector, source⟩, hsource, rfl⟩ :=
    List.mem_map.mp hentry
  have hbounds :=
    process_entry_root_degree_bounds descriptions (csDegree cs)
      (by
        unfold csDegree
        exact le_trans (by omega) (Nat.le_max_left _ _))
      (sourceSelector, source) hsource
  rw [← hcompressed]
  exact ⟨hbounds.1, hbounds.2.1,
    hbounds.2.2.trans_lt hdegree⟩

/--
It is enough to realize the fixed assignments emitted by `selectorFixed` in
order to realize every selector activation expected by the gate resolver.
-/
theorem selectorActivationsRealized_of_selectorFixed
    (map : SelCompressMap) (activationRows : List (ℕ × ℕ))
    (environment : Environment Fp)
    (hfixed :
      ∀ {column row value : ℕ},
        (column, row, value) ∈ selectorFixed map activationRows →
          environment.fixed ⟨column⟩ row = (value : Fp)) :
    SelectorActivationsRealized map activationRows environment := by
  intro selector row compressed hactivation hlookup
  exact hfixed
    (mem_selectorFixed_of_activation map activationRows
      hactivation hlookup)

/--
Dense fixed-column rows compiled into their canonical interpolation polynomials
realize selector activations whenever the sparse selector assignments occur at
in-domain rows with the expected dense values.

This is the polynomial boundary expected from key generation: the selector compiler
does not need to know how commitments or a concrete verifying key are assembled.
-/
theorem selectorActivationsRealized_of_fixedRowPolynomials
    {n : ℕ} (omega : Fp)
    (fixedRows : ℕ → List Fp)
    (adviceCols instanceCols : ℕ → Polynomial Fp)
    (usableRows : ℕ)
    (map : SelCompressMap) (activationRows : List (ℕ × ℕ))
    (hrows :
      Function.Injective fun row : Fin n => omega ^ (row : ℕ))
    (hroots : SelectorRootsWellFormed map)
    (hlength : ∀ column, (fixedRows column).length = n)
    (hfixed :
      ∀ {column row value : ℕ},
        (column, row, value) ∈ selectorFixed map activationRows →
          (fixedRows column).getD row 0 = (value : Fp)) :
    SelectorActivationsRealized map activationRows
      (polynomialEnvironment omega usableRows
        (fun column =>
          rowPolynomial omega
            (zeroPaddedRows (n := n) (fixedRows column)))
        adviceCols instanceCols) := by
  intro selector row compressed hactivation hlookup
  have hentry :=
    mem_selectorFixed_of_activation map activationRows
      hactivation hlookup
  have hvalue := hfixed hentry
  obtain ⟨hpositive, hrootBound, hcombinationBound⟩ :=
    hroots hlookup
  have hrootLt :
      compressed.assignedRoot < scalarFieldOrder :=
    hrootBound.trans_lt hcombinationBound
  have hrootNe :
      (compressed.assignedRoot : Fp) ≠ 0 := by
    intro hzero
    have hval := congrArg ZMod.val hzero
    have : compressed.assignedRoot = 0 := by
      simpa [ZMod.val_cast_of_lt hrootLt] using hval
    omega
  have hrow : row < n := by
    by_contra hout
    have hge : (fixedRows compressed.packedCol).length ≤ row := by
      rw [hlength]
      omega
    have hzero :
        (fixedRows compressed.packedCol).getD row 0 = 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]
      rfl
    rw [hzero] at hvalue
    exact hrootNe hvalue.symm
  rw [polynomialEnvironment_fixed_nat,
    rowPolynomial_eval hrows ⟨row, hrow⟩]
  exact hvalue

end Zcash.Snark
