import Zcash.Arithmetic.Domain
import Clean.Halo2.TopLevel
import Zcash.Circuits.Integration.PolynomialEnvironment
import Zcash.Snark.Keygen.Pipeline

/-!
# Generic assignments for closed top-level circuits

A decoded verifier witness supplies commitment-ID-indexed advice and instance
polynomials. A `TopLevelCircuit` supplies the operation stream, V1 placement, fixed
rows, blinding rows, and table-fit proof. This module joins those two
circuit-independent views without accepting an arbitrary verifying key.

The domain exponent comes from the top-level circuit's own keygen inputs. One
top-level circuit is reused for every proof in a bundle, and indexing the assignment
by its member prevents a bundle construction from silently selecting a different
member's columns. A decoded constructor connects this shell to the verifier-side
resolver using the key derived from the formal circuit; no accepted key is a free
input to this type.
-/

namespace Zcash.Snark

open Halo2 Polynomial

set_option maxHeartbeats 20000

/--
The polynomial assignment for one member of a bundle of the same top-level circuit.

The circuit is an index, not a stored choice. In particular there is no
caller-supplied domain exponent or `VerifyingKey`: decoded constructors use the key
derived from `top.formalCircuit`.
-/
structure TopLevelAssignment
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (numProofs : ℕ) (proofIndex : Fin numProofs) where
  polynomial : CommitmentId → Polynomial Fp

namespace TopLevelAssignment

/--
One assignment for every proof in a bundle.

The dependent member index ensures that the assignment at `proofIndex` resolves
exactly that member's advice and instance columns.
-/
abbrev Bundle
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (numProofs : ℕ) :=
  (proofIndex : Fin numProofs) →
    TopLevelAssignment top numProofs proofIndex

variable
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    {top : TopLevelCircuit Fp Config PublicInput}
    {numProofs : ℕ} {proofIndex : Fin numProofs}

/-- The circuit-derived domain generator has exact order `2^k`. -/
theorem domainRoot
    (hbound : top.domainExponent < 33) :
    Zcash.Arithmetic.omegaOf top.domainExponent ^
      (2 ^ top.domainExponent) = 1 := by
  simpa using Zcash.Arithmetic.omegaOf_domain
    top.domainExponent 1 (by omega)

/-- Circuit-derived domain row names are injective. -/
theorem domainRowsInjective
    (hbound : top.domainExponent < 33) :
    Function.Injective fun row : Fin (2 ^ top.domainExponent) =>
      Zcash.Arithmetic.omegaOf top.domainExponent ^ (row : ℕ) :=
  Zcash.Arithmetic.omegaOf_powers_injective
    top.domainExponent (by omega)

/-- The circuit-derived domain size is nonzero in the verifier scalar field. -/
theorem domainSizeCastNeZero
    (hbound : top.domainExponent < 33) :
    (((2 ^ top.domainExponent : ℕ) : Fp)) ≠ 0 :=
  Zcash.Arithmetic.domainSize_cast_ne_zero
    top.domainExponent (by omega)

/-- A fitting top-level circuit has fewer blinding rows than domain rows. -/
theorem blindingFactors_lt_domainSize
    : top.blindingFactors < 2 ^ top.domainExponent := by
  have h := top.blindingFactors_add_three_le_domainSize
  omega

/--
The compiler-derived domain has room beyond the blinding rows and final unusable row.
-/
theorem blindingFactors_succ_lt_domainSize
    : top.blindingFactors + 1 < 2 ^ top.domainExponent := by
  have h := top.blindingFactors_add_three_le_domainSize
  omega

/--
The Clean proof-varying assignment decoded from this bundle member.

Fixed columns are intentionally absent: `TopLevelCircuit.environment` compiles them
from `top.fixedRows`.
-/
def proofAssignment
    (assignment : TopLevelAssignment top numProofs proofIndex) :
    ProofAssignment Fp :=
  resolverAssignment
    (Zcash.Arithmetic.omegaOf top.domainExponent)
    assignment.polynomial proofIndex

/-- The circuit-owned semantic environment for this bundle member. -/
def environment
    (assignment : TopLevelAssignment top numProofs proofIndex) : Environment Fp :=
  top.environment assignment.proofAssignment

/--
The verifier-decoded fixed polynomials encode the fixed rows compiled by the
top-level circuit.

Unlike advice and instance columns, fixed columns are not part of
`ProofAssignment`: this is the representation boundary that identifies their
verifier-side polynomial values with the circuit-owned keygen data.
-/
def FixedColumnEncoding
    {G : Type} [AddCommGroup G] [Inhabited G]
    (assignment : TopLevelAssignment top numProofs proofIndex)
    (pp : Keygen.ProofParams) (urs : URS G) : Prop :=
  ∀ column row,
    (assignment.polynomial (.fixedCol column.index)).eval
        ((top.toVerifierKey pp urs).omega ^ row) =
      top.fixedValue column row

/--
Fixed-column encoding makes the verifier resolver environment exactly the
circuit-owned environment built from the corresponding proof assignment.
-/
theorem resolverEnvironment_eq_environment
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : Keygen.ProofParams) (urs : URS G)
    {proofIndex : Fin (pp.mergeDerived top).numProofs}
    (assignment :
      TopLevelAssignment top (pp.mergeDerived top).numProofs proofIndex)
    (hfixed : assignment.FixedColumnEncoding pp urs) :
    resolverEnvironment
        (top.toVerifierKey pp urs) assignment.polynomial proofIndex
        (top.usableRowsAt top.domainExponent) =
      assignment.environment := by
  apply congrArg₂ Environment.mk
  · funext column row
    cases column.kind with
    | advice => rfl
    | fixed =>
        exact hfixed ⟨column.index⟩ row
    | «instance» => rfl
  · rfl

@[simp] theorem environment_usableRows
    (assignment : TopLevelAssignment top numProofs proofIndex) :
    assignment.environment.usableRows =
      top.usableRowsAt top.domainExponent :=
  rfl

@[simp] theorem environment_fixed
    (assignment : TopLevelAssignment top numProofs proofIndex)
    (column : Column .fixed) (row : ℤ) :
    assignment.environment.fixed column row =
      top.fixedValue column row :=
  by exact top.environment_fixed assignment.proofAssignment column row

@[simp] theorem environment_advice
    (assignment : TopLevelAssignment top numProofs proofIndex)
    (column : Column .advice) (row : ℤ) :
    assignment.environment.advice column row =
      (assignment.polynomial
        (.adviceCol proofIndex column.index)).eval
          (Zcash.Arithmetic.omegaOf top.domainExponent ^ row) :=
  rfl

@[simp] theorem environment_instance
    (assignment : TopLevelAssignment top numProofs proofIndex)
    (column : Column .instance) (row : ℤ) :
    assignment.environment.inst column row =
      (assignment.polynomial
        (.instanceCol proofIndex column.index)).eval
          (Zcash.Arithmetic.omegaOf top.domainExponent ^ row) :=
  rfl

/--
The assignment's instance reads agree with the public-input elements at every cell
declared by the top-level circuit.
-/
def PublicInputEncoding
    (assignment : TopLevelAssignment top numProofs proofIndex)
    (input : PublicInput Fp) : Prop :=
  ∀ index,
    assignment.environment.inst
        (top.publicInputLayout.cells index).1
        (top.publicInputLayout.cells index).2 =
      (toElements input)[index]

/-- A public-input encoding determines the value extracted through the circuit's
declared instance-cell layout. -/
theorem extractPublicInput_eq
    (assignment : TopLevelAssignment top numProofs proofIndex)
    (input : PublicInput Fp)
    (hencoding : assignment.PublicInputEncoding input) :
    top.extractPublicInput assignment.environment = input := by
  unfold TopLevelCircuit.extractPublicInput
  apply top.publicInputLayout.extract_eq
  exact hencoding

/--
Derive the public-input encoding from canonical row polynomials, for an arbitrary
multi-column public-input layout.

`rows column` is the verifier serialization of that instance column. Only columns
actually named by the layout need a polynomial identity.
-/
theorem publicInputEncoding_of_rowPolynomials
    (assignment : TopLevelAssignment top numProofs proofIndex)
    (input : PublicInput Fp)
    (rows : ℕ → List Fp)
    (hpoly : ∀ index,
      assignment.polynomial
          (.instanceCol proofIndex
            (top.publicInputLayout.cells index).1.index) =
        instanceRowPolynomial (2 ^ top.domainExponent)
          (Zcash.Arithmetic.omegaOf top.domainExponent)
          (rows (top.publicInputLayout.cells index).1.index))
    (hencoded : ∀ index,
      (rows (top.publicInputLayout.cells index).1.index).getD
          (top.publicInputLayout.cells index).2 0 =
        (toElements input)[index])
    (hinjective : Function.Injective
      fun row : Fin (2 ^ top.domainExponent) =>
        Zcash.Arithmetic.omegaOf top.domainExponent ^ (row : ℕ)) :
    assignment.PublicInputEncoding input := by
  intro index
  let cell := top.publicInputLayout.cells index
  let domainRow : Fin (2 ^ top.domainExponent) :=
    ⟨cell.2, by
      have hrow :=
        top.publicInputLayout_cells_snd_lt_usableRowsAt_domainExponent index
      have hrow' :
          cell.2 <
            2 ^ top.domainExponent - top.blindingFactors - 1 := by
        simpa only [cell] using hrow
      have hfit := top.blindingFactors_add_three_le_domainSize
      omega⟩
  rw [environment_instance, hpoly index]
  have hrow := instanceRowPolynomial_eval
    (values := rows cell.1.index) hinjective domainRow
  rw [show
    (instanceRowPolynomial (2 ^ top.domainExponent)
      (Zcash.Arithmetic.omegaOf top.domainExponent)
      (rows cell.1.index)).eval
        (Zcash.Arithmetic.omegaOf top.domainExponent ^ (cell.2 : ℤ)) =
      (rows cell.1.index).getD cell.2 0 by
    simpa only [cell, domainRow] using hrow]
  exact hencoded index

/--
Derive public-input encoding directly from the row polynomials serialized by the
top-level circuit's own public-input layout.
-/
theorem publicInputEncoding_of_publicInputRowPolynomials
    (assignment : TopLevelAssignment top numProofs proofIndex)
    (input : PublicInput Fp)
    (hpoly : ∀ index,
      assignment.polynomial
          (.instanceCol proofIndex
            (top.publicInputLayout.cells index).1.index) =
        instanceRowPolynomial (2 ^ top.domainExponent)
          (Zcash.Arithmetic.omegaOf top.domainExponent)
          (top.publicInputRows input
            (top.publicInputLayout.cells index).1))
    (hinjective : Function.Injective
      fun row : Fin (2 ^ top.domainExponent) =>
        Zcash.Arithmetic.omegaOf top.domainExponent ^ (row : ℕ)) :
    assignment.PublicInputEncoding input := by
  apply assignment.publicInputEncoding_of_rowPolynomials input
    (fun column => top.publicInputRows input ⟨column⟩)
  · intro index
    exact hpoly index
  · intro index
    exact top.publicInputRows_getD_cell input index
  · exact hinjective

end TopLevelAssignment

end Zcash.Snark
