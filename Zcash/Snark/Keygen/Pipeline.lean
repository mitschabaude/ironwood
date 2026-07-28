import CompElliptic.Curves.Pasta
import Zcash.Common.ParMap
import Zcash.Arithmetic.Domain
import Zcash.Arithmetic.Fft
import CompElliptic.Curves.Pasta.Fast.Msm
import Zcash.Circuits.Integration.ExprRich
import Clean.Halo2.Keygen.Layout
import Clean.Halo2.Keygen
import Clean.Halo2.TopLevel
import Zcash.Arithmetic
import Zcash.Snark.Verifier.Assemble

/-!
# `TopLevelCircuit.toVerifierKey` — the circuit-side half of halo2 `keygen_vk`, generic

The single generic pipeline from a closed circuit (+ a monomial URS) to the full
`VerifyingKey`: Clean's `Halo2.Keygen` supplies the pinned constraint system, domain
exponent and selector map; this module adds the group side — the Lagrange-basis URS by
inverse FFT, the dense fixed columns from the derived layout, the keygen permutation
polynomials, `commit_lagrange` for both commitment families — and assembles the record.

`ProofParams` carries the only two `Shape` counts that are proof-shape rather than
circuit data (batch size, multiopen point sets); `ProofParams.mergeDerived` computes the
rest from the circuit, so `TopLevelCircuit.toVerifierKey` carries its derived `Shape` in
the return type with no lawfulness side condition. The Action instantiation and its
capture certification live in `Derivation.lean` / `Certificate.lean`.

## Rust reference

* Lagrange URS: `poly/commitment.rs:75-88` (`Params::new`'s `g_lagrange`),
  `arithmetic.rs:192` (`best_fft` — bit-reversal + iterative Cooley–Tukey butterflies).
* `commit_lagrange` blind: `poly/commitment.rs:212-216` (`Blind::default() = Blind(F::ONE)`).
* Fixed commitments: `plonk/keygen.rs:230-240` (`keygen_vk`'s `fixed_commitments`).
* Permutation commitments: `plonk/permutation/keygen.rs:102-152` (`Assembly::build_vk`).
-/

namespace Zcash.Snark.Keygen

open Zcash.Snark
open Zcash.Arithmetic (deltaFp omegaOf)
open Halo2
-- The concrete fast MSM lives in the CompElliptic pin; opening `Curves.Pasta` is what makes its
-- `Fast.Msm.*` spellings resolve here.
open CompElliptic.Curves.Pasta

variable {G : Type} [AddCommGroup G] [Inhabited G]

/-! ## Generalized Lagrange commitment (`poly/commitment.rs:212-216`) -/

/-- Commit to a zero-padded Lagrange-coefficient column against an arbitrary basis with
`Blind::default () = Blind(F::ONE)` (`poly/commitment.rs:212-216`):
`(∑ᵢ coeffsᵢ • basisᵢ) + w` — the same `+ w` blind convention the existing
`commitLagrange` uses, generalized to an arbitrary basis and coefficient list (the
instance-commitment path through `commitLagrange` is deliberately left untouched). -/
def commitLagrangeWith (blind : G) (basis : List G) (coeffs : List Fp) : G :=
  ((List.range coeffs.length).map
    (fun i => (coeffs.getD i 0).val • basis.getD i 0)).sum + blind

/-! ## Commitment helpers over Clean-compiled fixed rows -/

/-- V1 constant allocations in the legacy copy-list tuple order. Values remain
field-valued in Clean; only this permutation-copy adapter reads their canonical `Fp.val`. -/
def constantCopyEntries (cs : ConstraintSystem Fp) (ops : Operations Fp) :
    List (ℕ × ℕ × ℕ) :=
  (FloorPlanner.V1.constantAssignments ops (cs.constants.map (·.index))).map
    fun (value, column, row) => (value.val, column, row)

/-- Commit Clean-compiled fixed rows with one task per column. -/
def fixedCommitmentsWith (commit : List Fp → G)
    (rows : List (List Fp)) : List G :=
  rows.parMap commit

/-- Sequential fixed-row commitment variant used by the concrete certificate. -/
def fixedCommitmentsSeqWith (commit : List Fp → G)
    (rows : List (List Fp)) : List G :=
  rows.map commit

omit [AddCommGroup G] [Inhabited G] in
theorem fixedCommitmentsSeqWith_eq (commit : List Fp → G)
    (rows : List (List Fp)) :
    fixedCommitmentsSeqWith commit rows = fixedCommitmentsWith commit rows := by
  simp only [fixedCommitmentsSeqWith, fixedCommitmentsWith, List.parMap_eq_map]

omit [AddCommGroup G] [Inhabited G] in
theorem fixedCommitmentsSeqWith_congr {f g : List Fp → G}
    (rows : List (List Fp))
    (h : ∀ row ∈ rows, f row = g row) :
    fixedCommitmentsSeqWith f rows = fixedCommitmentsSeqWith g rows := by
  simp only [fixedCommitmentsSeqWith]
  exact List.map_congr_left h

/-- Commit Clean-compiled fixed rows against a Lagrange basis. -/
def fixedCommitmentsOf (blind : G) (lagrange : List G)
    (rows : List (List Fp)) : List G :=
  fixedCommitmentsWith
    (Fast.Msm.commitLagrangeFastWith Fast.Msm.defaultWindow blind lagrange) rows

/-! ## Derived permutation commitments (`plonk/permutation/keygen.rs:102-152`) -/

/-- The permutation columns as `ColRef`s in `enable_equality` order
(`cs.permutationColumns`) — the order the keygen `Assembly` mapping and the `δ^i` scaling
are indexed by, and the column shape `V1.copyList` resolves cells against. -/
def permColsOf (cs : ConstraintSystem Fp) : List Halo2.Layout.ColRef :=
  cs.permutationColumns.map fun c =>
    match c.kind with
    | .advice => .advice c.index
    | .fixed => .fixed c.index
    | .instance => .instance c.index

/-- `[ω^0, ω^1, …, ω^(n−1)]` (`build_vk`'s `omega_powers`, `permutation/keygen.rs:108-116`;
map form rather than iterated multiplication so entries are `getElem`-transparent for the
σ-row identification — `ZMod` powers are binary-fast, so the cost difference is noise). -/
def omegaPowersArr (omega : Fp) (n : ℕ) : Array Fp :=
  (Array.range n).map (omega ^ ·)

/-- `[δ^0, δ^1, …, δ^(m−1)]` (`build_vk`'s `cur *= DELTA`, `permutation/keygen.rs:118-133`;
map form, see `omegaPowersArr`). -/
def deltaPowersArr (delta : Fp) (m : ℕ) : Array Fp :=
  (Array.range m).map (delta ^ ·)

@[simp] theorem omegaPowersArr_getElem! (omega : Fp) {n j : ℕ} (hj : j < n) :
    (omegaPowersArr omega n)[j]! = omega ^ j := by
  simp [omegaPowersArr, hj]

@[simp] theorem deltaPowersArr_getElem! (delta : Fp) {m j : ℕ} (hj : j < m) :
    (deltaPowersArr delta m)[j]! = delta ^ j := by
  simp [deltaPowersArr, hj]

/-- The permutation columns chunked for the verifier (`permutation/verifier.rs:43-47`:
`columns.chunks(chunk_len)` with global position indices), in the `ColumnRef`
QUERY-INDEX space the verifier resolves evals with (`ColumnRef.resolve`): each column's
cur-rotation query index in the post-compression layouts. -/
def permutationChunksOf (map : Halo2.SelCompressMap) (cs : ConstraintSystem Fp) :
    List (List (Snark.ColumnRef × ℕ)) :=
  let proj := projectCS map cs
  let ref : AnyColumn → Snark.ColumnRef := fun c =>
    match c.kind with
    | .advice => .advice (proj.adviceQueryLayout.findIdx (· = (c.index, 0)))
    | .fixed => .fixed (proj.fixedQueryLayout.findIdx (· = (c.index, 0)))
    | .instance => .instance (proj.instanceQueryLayout.findIdx (· = (c.index, 0)))
  ((cs.permutationColumns.map ref).zipIdx).toChunks cs.chunkLen

/-- The per-column permutation polynomials in Lagrange form:
`p_i[j] = deltaomega[i'][j'] = δ^{i'} · ω^{j'}` where `(i', j') = mapping[i][j]`
(`build_vk`, `permutation/keygen.rs:135-146`), over the keygen `Assembly` mapping
(`Assembly::copy` replay, `Layout.runAssembly`) of the derived V1 copy list. -/
def permPolysOf (k : ℕ) (cs : ConstraintSystem Fp) (ops : Operations Fp) :
    List (List Fp) :=
  let n := 2 ^ k
  let permCols := permColsOf cs
  let copyList := Layout.V1.copyList permCols (FloorPlanner.V1.starts ops) ops
    (constantCopyEntries cs ops)
  let mapping := Layout.runAssembly n permCols.length copyList
  let omegaPows := omegaPowersArr (omegaOf k) n
  let deltaPows := deltaPowersArr deltaFp permCols.length
  (List.range permCols.length).map fun i =>
    (List.range n).map fun j =>
      let pij := (mapping[i]!)[j]!
      deltaPows[pij.1]! * omegaPows[pij.2]!

/-- The derived permutation common commitments at an explicit per-column committer
(see `fixedCommitmentsWith`). -/
def permutationCommitmentsWith (commit : List Fp → G) (k : ℕ)
    (cs : ConstraintSystem Fp) (ops : Operations Fp) : List G :=
  -- `parMap`: one task per column (`parMap_eq_map` — evaluation strategy only)
  (permPolysOf k cs ops).parMap commit

/-- Sequential variant of `permutationCommitmentsWith` (see `fixedCommitmentsSeqWith`). -/
def permutationCommitmentsSeqWith (commit : List Fp → G) (k : ℕ)
    (cs : ConstraintSystem Fp) (ops : Operations Fp) : List G :=
  (permPolysOf k cs ops).map commit

omit [AddCommGroup G] [Inhabited G] in
theorem permutationCommitmentsSeqWith_eq (commit : List Fp → G) (k : ℕ)
    (cs : ConstraintSystem Fp) (ops : Operations Fp) :
    permutationCommitmentsSeqWith commit k cs ops
      = permutationCommitmentsWith commit k cs ops := by
  simp only [permutationCommitmentsSeqWith, permutationCommitmentsWith,
    List.parMap_eq_map]

/-- Every permutation polynomial is a full-domain row vector. -/
theorem permPolysOf_mem_length (k : ℕ) (cs : ConstraintSystem Fp) (ops : Operations Fp) :
    ∀ l ∈ permPolysOf k cs ops, l.length = 2 ^ k := by
  intro l hl
  simp only [permPolysOf, List.mem_map] at hl
  obtain ⟨i, -, rfl⟩ := hl
  simp

omit [AddCommGroup G] [Inhabited G] in
/-- The permutation twin of `fixedCommitmentsSeqWith_congr`. -/
theorem permutationCommitmentsSeqWith_congr {f g : List Fp → G} (k : ℕ)
    (cs : ConstraintSystem Fp) (ops : Operations Fp)
    (h : ∀ l : List Fp, l.length = 2 ^ k → f l = g l) :
    permutationCommitmentsSeqWith f k cs ops = permutationCommitmentsSeqWith g k cs ops := by
  simp only [permutationCommitmentsSeqWith]
  exact List.map_congr_left fun c hc => h c (permPolysOf_mem_length k cs ops c hc)

/-- The derived permutation common commitments — `commit_lagrange` of each permutation
polynomial with the default blind (`build_vk`, `permutation/keygen.rs:147-151`;
Pippenger per MSM, `commitLagrangeFastWith_eq` — evaluation strategy only). -/
def permutationCommitmentsOf (blind : G) (lagrange : List G) (k : ℕ)
    (cs : ConstraintSystem Fp) (ops : Operations Fp) : List G :=
  permutationCommitmentsWith
    (Fast.Msm.commitLagrangeFastWith Fast.Msm.defaultWindow blind lagrange)
    k cs ops

/-! ## Assembly -/

end Zcash.Snark.Keygen

namespace Zcash.Snark.VerifyingKey

open Zcash.Arithmetic (deltaFp derivedUrsGLagrange omegaOf)
open Zcash.Snark.Keygen
open Halo2

variable {G : Type} [AddCommGroup G] [Inhabited G]

/-- The verifying key of a circuit given its keygen-view operation stream and a monomial
URS (which must be sized for the circuit, `urs.k = minimalK cs ops` — orchard's
`Params::new(K)`): every field derived — domain scalars from the minimal fitting
exponent, gates/query layouts/lookups from the pinned CS (carried across the
`RichExpression → Expr` boundary), and the two commitment families from the derived
layout over the URS's Lagrange basis. -/
def ofOperations (shape : Shape) (urs : URS G) (k : ℕ)
    (cs : ConstraintSystem Fp) (ops : Operations Fp)
    (fixedRows : List (List Fp)) : VerifyingKey shape Fp G :=
  let selMap := deriveSelCompressMap cs (2 ^ k)
    (activations (FloorPlanner.V1.starts ops) (indexedRegions ops 0).1)
  let pinned := PinnedConstraintSystem.derive cs selMap
  let lagrange := derivedUrsGLagrange urs
  { omega := omegaOf k
    n := 2 ^ k
    blindingFactors := cs.blindingFactors
    delta := deltaFp
    chunkLen := cs.chunkLen
    gates := pinned.gates.map RichExpression.toExpr
    instanceQueryLayout := pinned.instanceQueryLayout
    adviceQueryLayout := pinned.adviceQueryLayout
    fixedQueryLayout := pinned.fixedQueryLayout
    fixedCommitment := fun i =>
      (fixedCommitmentsOf urs.w lagrange fixedRows).getD i 0
    permutationCommonCommitment := fun i =>
      (permutationCommitmentsOf urs.w lagrange k cs ops).getD i.val 0
    permutationChunks := permutationChunksOf selMap cs
    lookupInputExprs := fun l =>
      (pinned.lookupInputExprs.getD l.val []).map RichExpression.toExpr
    lookupTableExprs := fun l =>
      (pinned.lookupTableExprs.getD l.val []).map RichExpression.toExpr }

/-- Projection API for the domain generator produced by `ofOperations`. -/
@[simp] theorem ofOperations_omega
    (shape : Shape) (urs : URS G) (k : ℕ)
    (cs : ConstraintSystem Fp) (ops : Operations Fp)
    (fixedRows : List (List Fp)) :
    (ofOperations shape urs k cs ops fixedRows).omega = omegaOf k := by
  simp [ofOperations]

/-- Projection API for the fixed commitments produced by `ofOperations`.

Downstream proofs should rewrite with this lemma instead of asking definitional
equality to unfold the complete verifying-key constructor. -/
@[simp] theorem ofOperations_fixedCommitment
    (shape : Shape) (urs : URS G) (k : ℕ)
    (cs : ConstraintSystem Fp) (ops : Operations Fp)
    (fixedRows : List (List Fp))
    (column : ℕ) :
    (ofOperations shape urs k cs ops fixedRows).fixedCommitment column =
      (fixedCommitmentsOf urs.w (derivedUrsGLagrange urs)
        fixedRows).getD column 0 := by
  simp only [ofOperations]

/-- Projection API for common permutation commitments produced by
`ofOperations`. -/
@[simp] theorem ofOperations_permutationCommonCommitment
    (shape : Shape) (urs : URS G) (k : ℕ)
    (cs : ConstraintSystem Fp) (ops : Operations Fp)
    (fixedRows : List (List Fp))
    (column : Fin shape.numPermutationColumns) :
    (ofOperations shape urs k cs ops fixedRows).permutationCommonCommitment column =
      (permutationCommitmentsOf urs.w (derivedUrsGLagrange urs)
        k cs ops).getD column.val 0 := by
  simp only [ofOperations]

/-- **A verifying key whose gate list is a derivation's evaluates like the source
circuit.** The verifier holds `Zcash.Snark.Expr` gates while the derivation produces
`Halo2.RichExpression` gates, so the hypothesis follows keygen's construction direction:
`vk.gates = (.derive cs map).gates.map RichExpression.toExpr`. Given that and selector
coverage, the `j`-th VK gate — at query families interpreting the derivation walk's
layout — evaluates to the `j`-th flattened Clean gate expression under the
selector-replacement valuation. -/
theorem gates_eval_of_gates_eq
    {shape : Shape} {G' : Type*} (vk : VerifyingKey shape Fp G')
    (cs : ConstraintSystem Fp) (map : Halo2.SelCompressMap)
    (hgates : vk.gates =
      (PinnedConstraintSystem.derive cs map).gates.map
        RichExpression.toExpr)
    (fE aE iE : ℕ → Fp) (v : Query → Fp)
    (hcov : ∀ p ∈ flatGates cs,
      p.selectorsCovered (fun i => (map.lookup i).isSome) = true)
    (hint : Interprets
      (eraseGates ((flatGates cs).map (substSelectorMap map.lookup))
        (queryWalkInit map cs)).2 fE aE iE v)
    (j : ℕ) (hg : j < vk.gates.length) (hp : j < (flatGates cs).length) :
    Expr.eval fE aE iE vk.gates[j]
      = Expression.eval (substValuation map.lookup v) (flatGates cs)[j] := by
  have hg' : j < (PinnedConstraintSystem.derive cs map).gates.length := by
    rw [hgates, List.length_map] at hg
    exact hg
  have key := PinnedConstraintSystem.derive_gates_eval cs map fE aE iE v hcov hint j hg' hp
  rw [List.getElem_of_eq hgates hg, List.getElem_map,
    RichExpression.eval_toExpr]
  exact key

end Zcash.Snark.VerifyingKey

namespace Zcash.Snark.Keygen

open Zcash.Snark
open Halo2

variable {G : Type} [AddCommGroup G] [Inhabited G]

/-- Transporting `ofOperations` along a shape equality is `ofOperations` at the other
shape — the record mentions the shape only in its `Fin`-domain types, never in a field
value. -/
theorem ofOperations_cast {s₁ s₂ : Shape} (hs : s₁ = s₂) (urs : URS G) (k : ℕ)
    (cs : ConstraintSystem Fp) (ops : Operations Fp)
    (fixedRows : List (List Fp)) :
    hs ▸ VerifyingKey.ofOperations s₁ urs k cs ops fixedRows
      = VerifyingKey.ofOperations s₂ urs k cs ops fixedRows := by
  cases hs; rfl

/-! ## The method form -/

/-- The two `Shape` counts that are genuinely proof-shape rather than circuit data: the
batch size and the multiopen point-set count. Everything else merges in derived
(`ProofParams.mergeDerived`). -/
structure ProofParams where
  numProofs : ℕ
  numPointSets : ℕ
deriving DecidableEq, Repr

/-- The `Shape` of a top-level circuit's proofs: the proof-shape counts merged with
everything the circuit derives — the domain exponent (`TopLevelCircuit.domainExponent`),
column/lookup/permutation counts from the configure-recorded constraint system, the
query counts from the derived pinned CS layouts (`TopLevelCircuit.pinnedCS`), the
verifier's permutation chunking `⌈columns / chunkLen⌉` (`permutation/verifier.rs:43-47`),
and the quotient split `cs.degree() − 1` (`vk.domain.get_quotient_poly_degree()`). -/
def ProofParams.mergeDerived (pp : ProofParams)
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput) : Shape :=
  let cs := top.constraintSystem
  let pinned :=
    PinnedConstraintSystem.derive top.constraintSystem top.selectorMap
  { k := top.domainExponent
    numProofs := pp.numProofs
    numAdviceColumns := cs.numAdviceColumns
    numLookups := cs.lookups.length
    numPermutationSets :=
      (cs.permutationColumns.length + cs.chunkLen - 1) / cs.chunkLen
    numPermutationColumns := cs.permutationColumns.length
    numQuotientPieces := csDegree cs - 1
    numInstanceQueries := pinned.instanceQueryLayout.length
    numAdviceQueries := pinned.adviceQueryLayout.length
    numFixedQueries := pinned.fixedQueryLayout.length
    numPointSets := pp.numPointSets }

end Zcash.Snark.Keygen

namespace Halo2.TopLevelCircuit

open Zcash.Snark
-- This section declares under `Halo2`, not `Zcash`, so the root re-exports of `Fp`/`URS` are not
-- on the enclosing-namespace walk and have to be opened explicitly.
open Zcash.Arithmetic (Fp URS derivedUrsGLagrange)
open Zcash.Snark.Keygen
open Halo2
open CompElliptic.Curves.Pasta

variable {G : Type} [AddCommGroup G] [Inhabited G]
variable {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]

/-- The derived fixed-column commitments of a closed circuit against a URS. -/
def fixedCommitments
    (top : TopLevelCircuit Fp Config PublicInput) (urs : URS G) : List G :=
  top.fixedRows.parMap
    (Fast.Msm.commitLagrangeFastWith Fast.Msm.defaultWindow urs.w
      (derivedUrsGLagrange urs))

/-- The named top-level fixed-row view is exactly the fixed-commitment computation
used by generic keygen. -/
@[simp] theorem fixedCommitments_eq_fixedCommitmentsOf
    (top : TopLevelCircuit Fp Config PublicInput) (urs : URS G) :
    top.fixedCommitments urs =
      fixedCommitmentsOf urs.w (derivedUrsGLagrange urs)
        top.fixedRows := by
  simp only [fixedCommitments, fixedCommitmentsOf, fixedCommitmentsWith]

/-- The derived permutation common commitments of a closed circuit against a URS. -/
def permutationCommitments
    (top : TopLevelCircuit Fp Config PublicInput) (urs : URS G) : List G :=
  permutationCommitmentsOf urs.w (derivedUrsGLagrange urs) top.domainExponent
    top.constraintSystem (top.operations)

/-- The verifying key of a closed circuit at an explicitly-given `Shape` (the
shape-explicit core `Certificate.lean` certifies; `toVerifierKey` below supplies the
derived shape). -/
def verifierKeyAt
    (top : TopLevelCircuit Fp Config PublicInput)
    (shape : Shape) (urs : URS G) : VerifyingKey shape Fp G :=
  .ofOperations shape urs top.domainExponent
    top.constraintSystem top.operations top.fixedRows

/-- The shape-explicit key uses the circuit's fitting-domain generator. -/
@[simp] theorem verifierKeyAt_omega
    (top : TopLevelCircuit Fp Config PublicInput)
    (shape : Shape) (urs : URS G) :
    (top.verifierKeyAt shape urs).omega =
      Zcash.Arithmetic.omegaOf top.domainExponent := by
  simp only [verifierKeyAt, VerifyingKey.ofOperations_omega]

/-- Projection API for the fixed commitments of the shape-explicit top-level key. -/
@[simp] theorem verifierKeyAt_fixedCommitment
    (top : TopLevelCircuit Fp Config PublicInput)
    (shape : Shape) (urs : URS G) (column : ℕ) :
    (top.verifierKeyAt shape urs).fixedCommitment column =
      (top.fixedCommitments urs).getD column 0 := by
  simp only [verifierKeyAt, VerifyingKey.ofOperations_fixedCommitment,
    fixedCommitments_eq_fixedCommitmentsOf]

/-- **The verifying key of a closed top-level circuit**: the `TopLevelCircuit` carries
unit configuration and synthesis inputs, so the only remaining inputs are the
proof-shape counts and the URS — `keygen_vk` at the `TopLevelCircuit` level, with the
derived `Shape` in the return type. -/
def toVerifierKey
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS G) :
    VerifyingKey (pp.mergeDerived top) Fp G :=
  top.verifierKeyAt (pp.mergeDerived top) urs

/-- The derived key uses the circuit's fitting-domain generator. -/
@[simp] theorem toVerifierKey_omega
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS G) :
    (top.toVerifierKey pp urs).omega =
      Zcash.Arithmetic.omegaOf top.domainExponent := by
  simp only [toVerifierKey, verifierKeyAt_omega]

/-- The derived key uses the circuit-owned fitting domain size. -/
@[simp]
theorem toVerifierKey_n
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS G) :
    (top.toVerifierKey pp urs).n = 2 ^ top.domainExponent := by
  simp [toVerifierKey, verifierKeyAt, VerifyingKey.ofOperations,
    TopLevelCircuit.domainExponent, TopLevelCompilation.domainExponent,
    TopLevelCircuit.constraintSystem, TopLevelCircuit.operations]

/-- The derived key preserves the closed constraint system's blinding count. -/
@[simp]
theorem toVerifierKey_blindingFactors
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS G) :
    (top.toVerifierKey pp urs).blindingFactors = top.blindingFactors := by
  simp [toVerifierKey, verifierKeyAt, VerifyingKey.ofOperations,
    TopLevelCircuit.blindingFactors]

/-- The derived key exposes the fixed commitments computed from its own dense rows. -/
theorem toVerifierKey_fixedCommitment
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS G) (column : ℕ) :
    (top.toVerifierKey pp urs).fixedCommitment column =
      (top.fixedCommitments urs).getD column 0 := by
  simp only [toVerifierKey, verifierKeyAt_fixedCommitment]

/-- The derived key exposes the common permutation commitments computed from
its own keygen permutation rows. -/
theorem toVerifierKey_permutationCommonCommitment
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS G)
    (column : Fin (pp.mergeDerived top).numPermutationColumns) :
    (top.toVerifierKey pp urs).permutationCommonCommitment column =
      (top.permutationCommitments urs).getD column.val 0 := by
  simp only [toVerifierKey, verifierKeyAt,
    VerifyingKey.ofOperations_permutationCommonCommitment,
    permutationCommitments, domainExponent,
    TopLevelCompilation.domainExponent, constraintSystem, operations]

/-- The derived key exposes exactly the advice-query layout of its selector-map
derivation. -/
theorem toVerifierKey_adviceQueryLayout_derived
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS G) :
    (top.toVerifierKey pp urs).adviceQueryLayout =
      (PinnedConstraintSystem.derive
        top.constraintSystem top.selectorMap).adviceQueryLayout := by
  rfl

/-- The derived key exposes exactly the fixed-query layout of its selector-map
derivation. -/
theorem toVerifierKey_fixedQueryLayout_derived
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS G) :
    (top.toVerifierKey pp urs).fixedQueryLayout =
      (PinnedConstraintSystem.derive
        top.constraintSystem top.selectorMap).fixedQueryLayout := by
  rfl

/-- The derived key exposes exactly the instance-query layout of its selector-map
derivation. -/
theorem toVerifierKey_instanceQueryLayout_derived
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS G) :
    (top.toVerifierKey pp urs).instanceQueryLayout =
      (PinnedConstraintSystem.derive
        top.constraintSystem top.selectorMap).instanceQueryLayout := by
  rfl

/-- The derived key's advice-query layout has the shape count computed from the same
top-level pinned constraint system. -/
theorem toVerifierKey_adviceQueryCount
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS G) :
    (top.toVerifierKey pp urs).adviceQueryLayout.length =
      (pp.mergeDerived top).numAdviceQueries := by
  change
    (PinnedConstraintSystem.derive
      top.constraintSystem top.selectorMap).adviceQueryLayout.length =
    (PinnedConstraintSystem.derive
      top.constraintSystem top.selectorMap).adviceQueryLayout.length
  rw [show top.selectorMap = top.selectorMap by rfl]

/-- The derived key's fixed-query layout has the shape count computed from the same
top-level pinned constraint system. -/
theorem toVerifierKey_fixedQueryCount
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS G) :
    (top.toVerifierKey pp urs).fixedQueryLayout.length =
      (pp.mergeDerived top).numFixedQueries := by
  change
    (PinnedConstraintSystem.derive
      top.constraintSystem top.selectorMap).fixedQueryLayout.length =
    (PinnedConstraintSystem.derive
      top.constraintSystem top.selectorMap).fixedQueryLayout.length
  rw [show top.selectorMap = top.selectorMap by rfl]

/-- The derived key's instance-query layout has the shape count computed from the same
top-level pinned constraint system. -/
theorem toVerifierKey_instanceQueryCount
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS G) :
    (top.toVerifierKey pp urs).instanceQueryLayout.length =
      (pp.mergeDerived top).numInstanceQueries := by
  change
    (PinnedConstraintSystem.derive
      top.constraintSystem top.selectorMap).instanceQueryLayout.length =
    (PinnedConstraintSystem.derive
      top.constraintSystem top.selectorMap).instanceQueryLayout.length
  rw [show top.selectorMap = top.selectorMap by rfl]

end Halo2.TopLevelCircuit
