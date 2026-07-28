import Clean.Halo2.TopLevel
import Clean.Halo2.Keygen.FloorPlanner
import Zcash.Circuits.Integration.OperationGates
import Zcash.Circuits.Integration.OperationLookups

/-!
# Top-level configure/synthesis coherence

`FormalCircuit` deliberately keeps configuration and synthesis independent. A
deployed top-level circuit therefore certifies once that every gate and lookup
activation emitted by synthesis was registered by configuration.

This module proves that the compact operation-level certificate supplies exactly
the membership facts needed by the generic gate and lookup bridges. No circuit,
placement, or verifying key is selected here.
-/

namespace Zcash.Snark

open Halo2

set_option maxHeartbeats 20000

namespace OperationsKeygenCoherent

/-- A coherent region registers every extracted enabled gate. -/
theorem region_gate
    {F : Type} {cs : ConstraintSystem F}
    {self : RegionIndex} {body : RegionOperations F}
    (hcoherent :
      body.Forall (RegionOperation.KeygenCoherent cs))
    {enabled : EnabledGate F}
    (henabled : enabled ∈ regionEnabledGates self body) :
    enabled.gate ∈ cs.gates := by
  induction body with
  | nil => simp [regionEnabledGates] at henabled
  | cons operation rest ih =>
      rw [List.forall_cons] at hcoherent
      cases operation with
      | enableGate gate row =>
          simp only [RegionOperation.KeygenCoherent] at hcoherent
          simp only [regionEnabledGates, List.mem_cons] at henabled
          rcases henabled with rfl | henabled
          · exact hcoherent.1
          · exact ih hcoherent.2 henabled
      | assignAdvice column row witness =>
          exact ih hcoherent.2 henabled
      | assignFixed column row value =>
          exact ih hcoherent.2 henabled
      | enableLookup argument selectors row =>
          exact ih hcoherent.2 henabled
      | constrainEqual left right =>
          exact ih hcoherent.2 henabled
      | constrainConstant cell value =>
          exact ih hcoherent.2 henabled
      | constrainInstance cell column row =>
          exact ih hcoherent.2 henabled

/-- A coherent operation stream registers every extracted enabled gate. -/
theorem gate
    {F : Type} {cs : ConstraintSystem F}
    {operations : Operations F} {i : RegionIndex}
    (hcoherent : OperationsKeygenCoherent cs operations)
    {enabled : EnabledGate F}
    (henabled : enabled ∈ operationEnabledGates operations i) :
    enabled.gate ∈ cs.gates := by
  induction operations generalizing i with
  | nil => simp [operationEnabledGates] at henabled
  | cons operation rest ih =>
      rw [OperationsKeygenCoherent, List.forall_cons] at hcoherent
      rcases hcoherent with ⟨hoperation, hrest⟩
      cases operation with
      | region name body =>
          simp only [Operation.KeygenCoherent] at hoperation
          simp only [operationEnabledGates, List.mem_append] at henabled
          rcases henabled with henabled | henabled
          · exact region_gate hoperation henabled
          · exact ih hrest henabled
      | constrainInstance cell column row =>
          exact ih hrest henabled
      | loadTable table values =>
          exact ih hrest henabled

/-- A coherent region registers every extracted enabled lookup. -/
theorem region_lookup
    {F : Type} {cs : ConstraintSystem F}
    {self : RegionIndex} {body : RegionOperations F}
    (hcoherent :
      body.Forall (RegionOperation.KeygenCoherent cs))
    {enabled : EnabledLookup F}
    (henabled : enabled ∈ regionEnabledLookups self body) :
    enabled.argument ∈ cs.lookups := by
  induction body with
  | nil => simp [regionEnabledLookups] at henabled
  | cons operation rest ih =>
      rw [List.forall_cons] at hcoherent
      cases operation with
      | enableLookup argument selectors row =>
          simp only [RegionOperation.KeygenCoherent] at hcoherent
          simp only [regionEnabledLookups, List.mem_cons] at henabled
          rcases henabled with rfl | henabled
          · exact hcoherent.1
          · exact ih hcoherent.2 henabled
      | assignAdvice column row witness =>
          exact ih hcoherent.2 henabled
      | assignFixed column row value =>
          exact ih hcoherent.2 henabled
      | enableGate gate row =>
          exact ih hcoherent.2 henabled
      | constrainEqual left right =>
          exact ih hcoherent.2 henabled
      | constrainConstant cell value =>
          exact ih hcoherent.2 henabled
      | constrainInstance cell column row =>
          exact ih hcoherent.2 henabled

/-- A coherent operation stream registers every extracted enabled lookup. -/
theorem lookup
    {F : Type} {cs : ConstraintSystem F}
    {operations : Operations F} {i : RegionIndex}
    (hcoherent : OperationsKeygenCoherent cs operations)
    {enabled : EnabledLookup F}
    (henabled : enabled ∈ operationEnabledLookups operations i) :
    enabled.argument ∈ cs.lookups := by
  induction operations generalizing i with
  | nil => simp [operationEnabledLookups] at henabled
  | cons operation rest ih =>
      rw [OperationsKeygenCoherent, List.forall_cons] at hcoherent
      rcases hcoherent with ⟨hoperation, hrest⟩
      cases operation with
      | region name body =>
          simp only [Operation.KeygenCoherent] at hoperation
          simp only [operationEnabledLookups, List.mem_append] at henabled
          rcases henabled with henabled | henabled
          · exact region_lookup hoperation henabled
          · exact ih hrest henabled
      | constrainInstance cell column row =>
          exact ih hrest henabled
      | loadTable table values =>
          exact ih hrest henabled

end OperationsKeygenCoherent

/-- A region gate activation occurs in the keygen selector-activation table. -/
theorem mem_regionActivations_of_mem_enabledGate
    {F : Type} (starts : List ℕ)
    {self : RegionIndex} {body : RegionOperations F}
    {enabled : EnabledGate F}
    (henabled : enabled ∈ regionEnabledGates self body) :
    (enabled.gate.selector.index,
      starts.getD enabled.region 0 + enabled.row) ∈
      activations starts [(self, body)] := by
  simp only [activations, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]
  induction body with
  | nil =>
      simp [regionEnabledGates] at henabled
  | cons operation rest ih =>
      cases operation with
      | enableGate gate row =>
          simp only [regionEnabledGates, List.mem_cons] at henabled
          rcases henabled with rfl | henabled
          · simp
          · exact List.mem_append_right _ (ih henabled)
      | assignAdvice column row witness =>
          simpa only [List.flatMap_cons, List.nil_append] using ih henabled
      | assignFixed column row value =>
          simpa only [List.flatMap_cons, List.nil_append] using ih henabled
      | enableLookup argument selectors row =>
          exact List.mem_append_right _ (ih henabled)
      | constrainEqual left right =>
          simpa only [List.flatMap_cons, List.nil_append] using ih henabled
      | constrainConstant cell value =>
          simpa only [List.flatMap_cons, List.nil_append] using ih henabled
      | constrainInstance cell column row =>
          simpa only [List.flatMap_cons, List.nil_append] using ih henabled

/--
Every extracted enabled gate occurs in the selector activations derived from the
same operation stream and V1 placement inputs.
-/
theorem mem_activations_of_mem_operationEnabledGate
    {F : Type} (starts : List ℕ)
    {operations : Operations F} {i : RegionIndex}
    {enabled : EnabledGate F}
    (henabled : enabled ∈ operationEnabledGates operations i) :
    (enabled.gate.selector.index,
      starts.getD enabled.region 0 + enabled.row) ∈
      activations starts (indexedRegions operations i).1 := by
  induction operations generalizing i with
  | nil =>
      simp [operationEnabledGates] at henabled
  | cons operation rest ih =>
      cases operation with
      | region name body =>
          simp only [operationEnabledGates, List.mem_append] at henabled
          rcases henabled with henabled | henabled
          · have hregion :=
              mem_regionActivations_of_mem_enabledGate starts henabled
            have hregion' :
                (enabled.gate.selector.index,
                  starts.getD enabled.region 0 + enabled.row) ∈
                  body.flatMap fun operation =>
                    match operation with
                    | .enableGate gate row =>
                        [(gate.selector.index, starts.getD i 0 + row)]
                    | .enableLookup _ selectors row =>
                        selectors.map fun selector =>
                          (selector.index, starts.getD i 0 + row)
                    | _ => [] := by
              simpa only [activations, List.flatMap_cons,
                List.flatMap_nil, List.append_nil] using hregion
            exact List.mem_append_left _ hregion'
          · have hrest := ih (i := i + 1) henabled
            exact List.mem_append_right _ hrest
      | constrainInstance cell column row =>
          exact ih (i := i) henabled
      | loadTable table values =>
          exact ih (i := i) henabled

end Zcash.Snark
