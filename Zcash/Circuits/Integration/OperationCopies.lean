import Zcash.Circuits.Integration.CircuitSatisfaction
import Zcash.Common.RelationWitness
import Zcash.Snark.Soundness.Canonical.PermutationSemantics

/-!
# Declared operation copies and permutation-cycle satisfaction

This is the operation-trace side of the copy bridge.  It extracts the three copy forms carried by
Clean operations—cell equality, instance equality, and constant equality—into one endpoint type,
and proves that satisfying the extracted list is exactly the `copy` field of
`FullCircuitSatisfaction`.

The final theorem is independent of a concrete layout.  A caller supplies an encoding of semantic
endpoints into the finite keygen cell type.  If endpoint reads agree with encoded cell values and
the permutation argument enforces equality on replayed cycles, every declared copy holds (or the
single explicit bad event survives).
-/

namespace Zcash.Snark

open Halo2

/-- A semantic endpoint of a Clean copy operation.  Constants are represented by their value here;
the floor planner's allocated constants-column cell belongs to the later concrete encoding. -/
inductive CopyEndpoint (F : Type) where
  | cell : Cell → CopyEndpoint F
  | instance : Column .instance → ℕ → CopyEndpoint F
  | constant : F → CopyEndpoint F
deriving Repr

namespace CopyEndpoint

variable {F : Type} [FiniteField F]

/-- Read an endpoint in Clean's placed environment. -/
def eval (place : RegionIndex → ℕ) (env : Environment F) : CopyEndpoint F → F
  | .cell c => c.eval place env
  | .instance col row => env.get col (row : ℤ)
  | .constant value => value

end CopyEndpoint

/-- A declared semantic equality. -/
abbrev DeclaredCopy (F : Type) := CopyEndpoint F × CopyEndpoint F

namespace DeclaredCopy

variable {F : Type} [FiniteField F]

/-- The equality denoted by one declared copy. -/
def Satisfied (place : RegionIndex → ℕ) (env : Environment F)
    (copy : DeclaredCopy F) : Prop :=
  copy.1.eval place env = copy.2.eval place env

end DeclaredCopy

/-- The copy, if any, declared by one region operation. -/
def regionOperationDeclaredCopy? {F : Type} : RegionOperation F → Option (DeclaredCopy F)
  | .constrainEqual left right => some (.cell left, .cell right)
  | .constrainConstant cell value => some (.cell cell, .constant value)
  | .constrainInstance cell col row => some (.cell cell, .instance col row)
  | _ => none

/-- Declared copies in one region, in operation order. -/
def regionDeclaredCopies {F : Type} :
    RegionOperations F → List (DeclaredCopy F)
  | [] => []
  | op :: rest =>
      match regionOperationDeclaredCopy? op with
      | some copy => copy :: regionDeclaredCopies rest
      | none => regionDeclaredCopies rest

/-- Declared copies in a complete layouter stream.  Region-local copies retain the `Cell` region
indices they were synthesized with; layouter-level instance copies are inserted in stream order. -/
def operationDeclaredCopies {F : Type} : Operations F → List (DeclaredCopy F)
  | [] => []
  | .region _ body :: rest => regionDeclaredCopies body ++ operationDeclaredCopies rest
  | .constrainInstance cell col row :: rest =>
      (.cell cell, .instance col row) :: operationDeclaredCopies rest
  | .loadTable _ _ :: rest => operationDeclaredCopies rest

namespace CircuitConstraintFamily

variable {F : Type} [FiniteField F]

/-- The copy-family projection of a region is exactly satisfaction of its extracted copies. -/
theorem region_copy_constraints_iff
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : Environment F)
    (ops : RegionOperations F) :
    regionConstraints .copy place self env ops ↔
      (regionDeclaredCopies ops).Forall (DeclaredCopy.Satisfied place env) := by
  induction ops with
  | nil => simp [regionConstraints, regionDeclaredCopies]
  | cons op rest ih =>
      cases op <;>
        simp_all [regionConstraints, regionConstraint, RegionOperation.Constraints,
          regionDeclaredCopies, regionOperationDeclaredCopy?,
          DeclaredCopy.Satisfied, CopyEndpoint.eval]

/-- The complete copy-family projection is exactly satisfaction of the copies extracted from the
whole operation stream. -/
theorem copy_constraints_iff_declaredCopies
    (place : RegionIndex → ℕ) (env : Environment F)
    (ops : Operations F) (i : RegionIndex) :
    constraints .copy place env ops i ↔
      (operationDeclaredCopies ops).Forall (DeclaredCopy.Satisfied place env) := by
  induction ops generalizing i with
  | nil => simp [constraints, operationDeclaredCopies]
  | cons op rest ih =>
      cases op with
      | region name body =>
          rw [constraints, ih, region_copy_constraints_iff]
          simp [operationDeclaredCopies, List.forall_append]
      | constrainInstance cell col row =>
          rw [constraints, ih]
          simp [operationDeclaredCopies, DeclaredCopy.Satisfied, CopyEndpoint.eval]
      | loadTable table values =>
          rw [constraints, ih]
          simp [operationDeclaredCopies]

end CircuitConstraintFamily

/-- Encode a semantic copy list into the finite cell type on which keygen replays its permutation. -/
def encodeDeclaredCopies
    {F cell : Type} (encode : CopyEndpoint F → cell)
    (copies : List (DeclaredCopy F)) : List (cell × cell) :=
  copies.map fun copy => (encode copy.1, encode copy.2)

/-- **Generic copy bridge.** Equality on every replayed permutation cycle implies satisfaction of
every declared Clean copy.  The caller's `Bad` is shared across all copies, so the result exposes one
global exceptional branch rather than one branch per operation.

The concrete layout layer only needs to provide `encode` and `hread`; constant endpoints may be
encoded by the floor planner's allocated constants-column cells there. `hread` is required
only at the DECLARED endpoints — an unconditional read fact is uninstantiable for any
finite cell type, since a constant endpoint evaluates to an arbitrary field element.

`hcycle` reports its exceptional branch as data, so this bridge cannot decide that branch once
for all copies; it walks `copies` and returns the first break `hcycle` computes
(`listForallOrRelationWitness`). -/
def declaredCopies_satisfied_or_bad_of_replay
    {F cell : Type} [FiniteField F] [DecidableEq cell] [Fintype cell]
    (place : RegionIndex → ℕ) (env : Environment F)
    (copies : List (DeclaredCopy F))
    (encode : CopyEndpoint F → cell) (value : cell → F)
    (hread : ∀ copy ∈ copies,
      copy.1.eval place env = value (encode copy.1) ∧
        copy.2.eval place env = value (encode copy.2))
    (Bad : Type)
    (hcycle : ∀ {left right : cell},
      (replayKeygenPermutation (encodeDeclaredCopies encode copies)).SameCycle left right →
        value left = value right ⊕' Bad) :
    copies.Forall (DeclaredCopy.Satisfied place env) ⊕' Bad :=
  bindOrRelationWitness
    (listForallOrRelationWitness copies fun copy hcopy => by
      have hencoded :
          (encode copy.1, encode copy.2) ∈ encodeDeclaredCopies encode copies := by
        exact List.mem_map.mpr ⟨copy, hcopy, rfl⟩
      have hlinked :=
        replayKeygenPermutation_pair_linked
          (encodeDeclaredCopies encode copies) hencoded
      rcases hcycle hlinked with heq | hbad
      · refine PSum.inl ?_
        obtain ⟨h1, h2⟩ := hread copy hcopy
        simpa [DeclaredCopy.Satisfied, h1, h2] using heq
      · exact PSum.inr hbad)
    List.forall_iff_forall_mem.mpr

/-- The generic replay bridge, phrased directly as the `copies` field of full circuit
satisfaction. -/
def copy_constraints_or_bad_of_replay
    {F cell : Type} [FiniteField F] [DecidableEq cell] [Fintype cell]
    (place : RegionIndex → ℕ) (env : Environment F)
    (ops : Operations F) (i : RegionIndex)
    (encode : CopyEndpoint F → cell) (value : cell → F)
    (hread : ∀ copy ∈ operationDeclaredCopies ops,
      copy.1.eval place env = value (encode copy.1) ∧
        copy.2.eval place env = value (encode copy.2))
    (Bad : Type)
    (hcycle : ∀ {left right : cell},
      (replayKeygenPermutation
        (encodeDeclaredCopies encode (operationDeclaredCopies ops))).SameCycle left right →
        value left = value right ⊕' Bad) :
    CircuitConstraintFamily.constraints .copy place env ops i ⊕' Bad :=
  bindOrRelationWitness
    (declaredCopies_satisfied_or_bad_of_replay
      place env (operationDeclaredCopies ops) encode value hread Bad hcycle)
    (CircuitConstraintFamily.copy_constraints_iff_declaredCopies place env ops i).mpr

end Zcash.Snark
