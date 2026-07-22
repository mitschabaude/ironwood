import Mathlib
import Zcash.Snark.Soundness.Main
import Zcash.Snark.Soundness.Multiopen.Deployed
import Zcash.Snark.Soundness.Multiopen.Opened
import Zcash.Snark.Soundness.Multiopen.RPoly

/-!
# Fixture: the decoded-column hypotheses are dischargeable

Regression guard for the decoded-column capstones' hypothesis shapes: every hypothesis of the terminal
decoded lemmas is discharged *concretely* on a toy instance, so a future reshape that reintroduces an
unsatisfiable form (the ∀-families `hquot ∧ hgood` vacuity described in the scope section of
`Soundness.Multiopen.Decode`) breaks this file instead of passing silently.

The first instance is the smallest single-point, rotation-free one in the model's documented scope:
`k = 0` (one URS generator, over `G := Fp` itself, where `commit` has trivial kernel), one column, all
data zero — the zero column satisfies the one-gate circuit `advice 0` with zero quotient at the opened
point. Both terminal entry points are exercised: `decoded_constraint_of_relation_and_batch` on a bare
batch, and `decoded_constraint_of_opening_or_relation` with its `hbatch` *derived* from a family of
accepting IPA transcripts (`multiopenRewindForRelation_of_acceptedFamily`), not assumed.

The second instance (`Prod` section) is multi-column with nonzero data: three columns `2, 3, 6` at
distinct batching challenges `0, 1, 2`, a two-advice/one-instance gate `a₀·a₁ − i₀` satisfied with zero
quotient, and both terminal endpoints discharged again — so the decoded shapes are exercised beyond the
degenerate all-zero point.

The third instance (`Rot` section) exercises the deployed `x₄` power form (`Soundness.Multiopen.Deployed`)
on a minimal *rotated-query* deployed instance: one proof, one advice column queried at rotations `0`
and `1` (points `x` and `ωx`), plus the vanishing queries — two point sets, so the fingerprinted
`constructIntermediateSets` grouping is genuinely multi-set and rotated. The `x₄` pair count and the
batch column values are *computed* (`decide`), and `deployedCommitment_x4_batch` instantiates on it.

The fourth instance (`toyUrsUW` section) discharges the *opened* terminal endpoint
(`Soundness.Multiopen.Opened`) on a `k = 0` URS with nonzero `u`/`w`, so the augmented
declared-component equations carry genuine content. The fifth (`rotBind` section) discharges
`deployed_witness_member_binding`'s full hypothesis package on a rotated instance whose aggregates
equal its claimed set evaluations — the satisfiable shape at `k = 0`, where the commitment and value
functionals coincide. The sixth (`rotChB` section) discharges the pinned capstone's derived opening
(`OpenedBatchOpenings.ipaRelation_of_x4Current`) on a designated batch at the honest batching
challenge.
-/

namespace Zcash.Snark
namespace MultiopenDecodeFixture

open Polynomial

/-- Toy URS at `k = 0` over the scalar field itself: the single generator is `1`. -/
abbrev toyUrs : URS Fp := ⟨0, fun _ => 1, 0, 0⟩

/-- The toy index type is a singleton. -/
theorem toy_fin_eq_zero (j : Fin (2 ^ toyUrs.k)) : j = 0 := by
  cases j using Fin.cases with
  | zero => rfl
  | succ i => exact i.elim0

/-- At `k = 0` with generator `1`, a commitment is its single coefficient: `commit` has trivial
kernel, so the canonical decode is pinned by its spec alone. -/
theorem toy_commit_eq (a : Fin 1 → Fp) : commit toyUrs a = a 0 := by
  simp [commit, toyUrs]

/-- One column, everything zero: the batch family whose decode the fixture checks. -/
noncomputable def toyBatch :
    BatchOpeningsForWitness toyUrs (evalVector 0 0) (fun _ : Fin 1 => (0 : Fp))
      (fun _ => 0) (fun _ => 0) where
  batchChallenge := fun _ => 0
  challengesDistinct := fun r s _ => Subsingleton.elim r s
  batched := fun _ _ => 0
  current := 0
  current_eq := rfl
  commitment := fun r => by simp [commit, toyUrs]
  value := fun r => by simp [commitGen]

/-- Any zero-column batch over the toy URS decodes to the zero columns — from the decode's spec and
the trivial kernel, without unfolding the Vandermonde inverse. -/
theorem toy_decode_zero {bvec : Fin 1 → Fp} {w : Fin 1 → Fp}
    (hb : BatchOpeningsForWitness toyUrs bvec (fun _ : Fin 1 => (0 : Fp)) (fun _ => 0) w) :
    decodedCols hb = fun _ => 0 := by
  funext i
  have hfam := (decodedCols_spec hb).decodedColumns
  have hz : hfam.coeffs i = fun _ => 0 := by
    funext j
    have h0 : hfam.coeffs i 0 = 0 := by
      have hc := hfam.commitment i
      rwa [toy_commit_eq] at hc
    have hj : j = 0 := toy_fin_eq_zero j
    rw [hj]; exact h0
  rw [hfam.polynomial i, hz]
  simp [coeffsToPoly]

/-- The one-gate circuit: read advice column `0`. -/
def toyGates : Fin 1 → Expr Fp := fun _ => Expr.advice 0

/-- The zero witness opens the zero statement over the toy URS. -/
theorem toy_opens :
    IpaRelation toyUrs (0 : Fp) (evalVector 0 (0 : Fp)) (0 : Fp) (fun _ => (0 : Fp)) := by
  constructor
  · simp [commit, toyUrs]
  · simp [innerProduct]

/-- The combined gate numerator over the decoded (zero) columns is the zero polynomial. -/
theorem toy_numerator {w : Fin 1 → Fp}
    (hb : BatchOpeningsForWitness toyUrs (evalVector 0 0) (fun _ : Fin 1 => (0 : Fp))
      (fun _ => 0) w) :
    combineGates (fun _ => 0) (selectedPolys (decodedCols hb) (fun i : Fin 1 => i))
      (selectedPolys (decodedCols hb) (fun i : Fin 1 => i)) 0 toyGates = 0 := by
  rw [toy_decode_zero hb]
  simp [combineGates, gatePolys, toyGates, Expr.toPoly, selectedPolys, finFn]

/-- All hypotheses of `decoded_constraint_of_relation_and_batch` discharged concretely: the
regression guard that the decoded hypothesis shapes stay satisfiable. -/
theorem toy_relation_and_batch_discharged : True :=
  decoded_constraint_of_relation_and_batch (urs := toyUrs)
    (fun _ : Fin 1 => (0 : Fp)) (fun _ => 0) (fun i : Fin 1 => i) (fun i : Fin 1 => i)
    (fun _ => 0) 0 toyGates 0 1 0 toy_opens toyBatch
    (by rw [toy_numerator toyBatch]; simp [quotientCheck])
    (by rw [toy_numerator toyBatch]; intro h; simp at h)
    (fun _ _ _ => trivial)

/-- Accepting transcripts for every batching challenge of the zero batch: the depth-`0` leaf `0`. -/
noncomputable def toyFamily :
    AcceptedBatchFamily toyUrs 0 (evalVector 0 0) 0 (fun _ : Fin 1 => (0 : Fp))
      (fun _ => 0) where
  batchChallenge := fun _ => 0
  challengesDistinct := fun r s _ => Subsingleton.elim r s
  trees := fun _ => .leaf 0
  accepts := fun r => ⟨by simp [commitGen], by simp [commitGen]⟩
  current := 0
  current_P := by simp
  current_v := by simp

/-- The opening-or-relation terminal endpoint discharged end-to-end, with `hbatch` *derived* from
accepting transcripts (`multiopenRewindForRelation_of_acceptedFamily toyFamily`), not assumed. -/
theorem toy_terminal_discharged :
    True ∨ HasNontrivialRelation (F := Fp) toyUrs.g toyUrs.u toyUrs.w :=
  decoded_constraint_of_opening_or_relation (urs := toyUrs)
    (fun _ : Fin 1 => (0 : Fp)) (fun _ => 0) (fun i : Fin 1 => i) (fun i : Fin 1 => i)
    (fun _ => 0) 0 toyGates 0 1 0
    (Or.inl ⟨fun _ => 0, toy_opens⟩)
    (multiopenRewindForRelation_of_acceptedFamily toyFamily)
    (fun a hrel => by rw [toy_numerator]; simp [quotientCheck])
    (fun a hrel => by rw [toy_numerator]; intro h; simp at h)
    (fun _ _ _ => trivial)

/-! ## Multi-column, nonzero data

Three columns holding `2`, `3`, `6`, batched at the distinct challenges `0`, `1`, `2`; the gate
`advice 0 · advice 1 − instance 0` reads columns `0`/`1` as advice and column `2` as instance and is
satisfied (`2·3 = 6`) with zero quotient. The same two terminal endpoints are discharged, so the decoded
hypothesis shapes are exercised on genuinely nonzero, multi-column data. -/

/-- Any batch over the toy URS decodes to the constant polynomials pinned by the column commitments:
at `k = 0` the commitment has trivial kernel, so the canonical decode is determined by its spec alone —
for arbitrary targets, generalizing `toy_decode_zero`. -/
theorem toy_decode_pinned {n : ℕ} {bvec : Fin 1 → Fp} {cc ce : Fin n → Fp} {w : Fin 1 → Fp}
    (hb : BatchOpeningsForWitness toyUrs bvec cc ce w) :
    decodedCols hb = fun i => Polynomial.C (cc i) := by
  funext i
  have hfam := (decodedCols_spec hb).decodedColumns
  have hcoeff : hfam.coeffs i = fun _ => cc i := by
    funext j
    have h0 : hfam.coeffs i 0 = cc i := by
      have hc := hfam.commitment i
      rwa [toy_commit_eq] at hc
    rw [toy_fin_eq_zero j]
    exact h0
  rw [hfam.polynomial i, hcoeff]
  simp [coeffsToPoly]

/-- The two-advice/one-instance gate `advice 0 · advice 1 − instance 0`. -/
def toyGatesProd : Fin 1 → Expr Fp :=
  fun _ => .sum (.product (.advice 0) (.advice 1)) (.negated (.instance 0))

/-- The nonzero three-column batch: columns `2`, `3`, `6` at batching challenges `0`, `1`, `2`; the
current witness is the challenge-`0` batch, the column-`0` constant `2`. -/
noncomputable def toyBatchProd :
    BatchOpeningsForWitness toyUrs (evalVector 0 0) (![2, 3, 6] : Fin 3 → Fp)
      (![2, 3, 6] : Fin 3 → Fp) (fun _ => 2) where
  batchChallenge := ![0, 1, 2]
  challengesDistinct := by decide
  batched := ![fun _ => 2, fun _ => 11, fun _ => 32]
  current := 0
  current_eq := rfl
  commitment := by decide
  value := by decide

/-- The witness `2` opens the statement `(P, v) = (2, 2)` over the toy URS. -/
theorem toyProd_opens :
    IpaRelation toyUrs (2 : Fp) (evalVector 0 (0 : Fp)) (2 : Fp) (fun _ => (2 : Fp)) := by
  constructor <;> decide

/-- The combined gate numerator over the decoded nonzero columns vanishes: `2·3 − 6 = 0`. -/
theorem toyProd_numerator {w : Fin 1 → Fp}
    (hb : BatchOpeningsForWitness toyUrs (evalVector 0 0) (![2, 3, 6] : Fin 3 → Fp)
      (![2, 3, 6] : Fin 3 → Fp) w) :
    combineGates (fun _ => 0) (selectedPolys (decodedCols hb) ![0, 1])
      (selectedPolys (decodedCols hb) ![2]) 0 toyGatesProd = 0 := by
  rw [toy_decode_pinned hb]
  have h0 : selectedPolys (fun i => Polynomial.C ((![2, 3, 6] : Fin 3 → Fp) i))
      (![0, 1] : Fin 2 → Fin 3) 0 = Polynomial.C 2 := by
    simp [selectedPolys, finFn]
  have h1 : selectedPolys (fun i => Polynomial.C ((![2, 3, 6] : Fin 3 → Fp) i))
      (![0, 1] : Fin 2 → Fin 3) 1 = Polynomial.C 3 := by
    simp [selectedPolys, finFn]
  have h2 : selectedPolys (fun i => Polynomial.C ((![2, 3, 6] : Fin 3 → Fp) i))
      (![2] : Fin 1 → Fin 3) 0 = Polynomial.C 6 := by
    simp [selectedPolys, finFn]
  simp only [combineGates, gatePolys, toyGatesProd, List.ofFn_succ, List.ofFn_zero,
    List.foldl_cons, List.foldl_nil, Expr.toPoly, h0, h1, h2, zero_mul, zero_add]
  simp only [← Polynomial.C_mul, ← Polynomial.C_neg, ← Polynomial.C_add, Polynomial.C_eq_zero]
  norm_num

/-- `decoded_constraint_of_relation_and_batch` discharged concretely on the nonzero multi-column
batch. -/
theorem toyProd_relation_and_batch_discharged : True :=
  decoded_constraint_of_relation_and_batch (urs := toyUrs)
    (![2, 3, 6] : Fin 3 → Fp) (![2, 3, 6] : Fin 3 → Fp) ![0, 1] ![2]
    (fun _ => 0) 0 toyGatesProd 0 1 0 toyProd_opens toyBatchProd
    (by rw [toyProd_numerator toyBatchProd]; simp [quotientCheck])
    (by rw [toyProd_numerator toyBatchProd]; intro h; simp at h)
    (fun _ _ _ => trivial)

/-- Accepting leaf transcripts for the three batching challenges of the nonzero batch: the depth-`0`
leaves carry the batched constants `2`, `11`, `32`. -/
noncomputable def toyFamilyProd :
    AcceptedBatchFamily toyUrs 2 (evalVector 0 0) 2 (![2, 3, 6] : Fin 3 → Fp)
      (![2, 3, 6] : Fin 3 → Fp) where
  batchChallenge := ![0, 1, 2]
  challengesDistinct := by decide
  trees := ![.leaf 2, .leaf 11, .leaf 32]
  accepts := by
    intro r
    fin_cases r <;> exact ⟨by decide, by decide⟩
  current := 0
  current_P := by decide
  current_v := by decide

/-- The opening-or-relation terminal endpoint discharged end-to-end on nonzero multi-column data, with
`hbatch` *derived* from the accepting transcripts. -/
theorem toyProd_terminal_discharged :
    True ∨ HasNontrivialRelation (F := Fp) toyUrs.g toyUrs.u toyUrs.w :=
  decoded_constraint_of_opening_or_relation (urs := toyUrs)
    (![2, 3, 6] : Fin 3 → Fp) (![2, 3, 6] : Fin 3 → Fp) ![0, 1] ![2]
    (fun _ => 0) 0 toyGatesProd 0 1 0
    (Or.inl ⟨fun _ => 2, toyProd_opens⟩)
    (multiopenRewindForRelation_of_acceptedFamily toyFamilyProd)
    (fun a hrel => by rw [toyProd_numerator]; simp [quotientCheck])
    (fun a hrel => by rw [toyProd_numerator]; intro h; simp at h)
    (fun _ _ _ => trivial)

/-! ## The deployed `x₄` power form on a rotated two-set instance

A minimal deployed instance whose fingerprinted grouping is genuinely multi-set and rotated: one proof
with one advice column queried at rotations `0` and `1` (points `x = 2` and `ωx = 6`), plus the two
vanishing queries at `x`. `constructIntermediateSets` derives two point sets — `{x, ωx}` for the advice
column and `{x}` for the vanishing pair — so the `x₄` collapse has two `(qᵢ, uᵢ)` pairs and the batch
three columns: the `{x}` aggregate (`random + x₁·h`, evaluating to `7`), the `{x, ωx}` aggregate (the
advice commitment `10`), and the quotient commitment `q′ = 5` on top. The counts and values are
*computed* (`decide`), and the power-form theorem instantiates — exercising
`Soundness.Multiopen.Deployed` against a rotated deployed grouping. -/

/-- Shape of the rotated toy: `k = 0`, one proof, one advice column with two advice queries, no
lookups/permutations/quotient pieces, two point sets. -/
def rotShape : Shape :=
  { k := 0, numProofs := 1, numAdviceColumns := 1, numLookups := 0, numPermutationSets := 0,
    numPermutationColumns := 0, numQuotientPieces := 0, numInstanceQueries := 0,
    numAdviceQueries := 2, numFixedQueries := 0, numPointSets := 2 }

/-- Verifying key of the rotated toy: domain generator `ω = 3`, the advice column queried at rotations
`0` and `1`, everything else empty. -/
def rotVk : VerifyingKey rotShape Fp Fp :=
  { omega := 3, n := 1, blindingFactors := 0, delta := 1, chunkLen := 1, gates := [],
    instanceQueryLayout := [], adviceQueryLayout := [(0, 0), (0, 1)], fixedQueryLayout := [],
    fixedCommitment := fun _ => 0, instanceCommitment := fun _ _ => 0,
    permutationCommonCommitment := Fin.elim0, permutationChunks := [],
    lookupInputExprs := Fin.elim0, lookupTableExprs := Fin.elim0 }

/-- Proof string of the rotated toy: advice commitment `10` (opened at both rotations, evals `11`/`12`),
vanishing random commitment `7` (eval `13`), quotient commitment `q′ = 5`, claimed set evaluations
`u = (4, 8)`. -/
def rotPs : ProofString rotShape Fp Fp :=
  { adviceCommitments := fun _ _ => 10, lookupPermutedInput := fun _ => Fin.elim0,
    lookupPermutedTable := fun _ => Fin.elim0, permutationProduct := fun _ => Fin.elim0,
    lookupProduct := fun _ => Fin.elim0, vanishingRandom := 7, hPieces := Fin.elim0,
    instanceEvals := fun _ => Fin.elim0, adviceEvals := fun _ => ![11, 12],
    fixedEvals := Fin.elim0, vanishingRandomEval := 13, permutationCommonEvals := Fin.elim0,
    permutationSetEvals := fun _ => Fin.elim0, lookupEvals := fun _ => Fin.elim0,
    multiopenQPrime := 5, multiopenU := ![4, 8], ipaS := 0, ipaRounds := Fin.elim0,
    ipaC := 0, ipaF := 0 }

/-- Challenges of the rotated toy: gate point `x = 2` (so the rotated advice point is `ωx = 6`),
compression challenge `x₁ = 3`. -/
def rotCh : Challenges rotShape.k Fp :=
  { theta := 0, beta := 0, gamma := 0, y := 0, x := 2, x1 := 3, x2 := 0, x3 := 0, x4 := 9,
    xi := 0, z := 0, ipaRound := Fin.elim0 }

/-- The fingerprinted grouping of the rotated toy has two point sets, so the `x₄` collapse has two
`(qᵢ, uᵢ)` pairs — the count is *computed* from `constructIntermediateSets`. -/
theorem rot_pairCount : deployedX4PairCount rotVk rotPs rotCh = 2 := by decide

/-- The `x₄` batch columns of the rotated toy, computed: power `ξ⁰` carries the `{x}` point-set
aggregate (`random 7 + x₁ · h`, with `h` the empty-piece zero MSM), power `ξ¹` the rotated advice
aggregate (`10`), and the top power the quotient commitment `q′ = 5`. -/
theorem rot_x4BatchCommitments :
    x4BatchCommitments toyUrs rfl rotVk rotPs rotCh ⟨0, by decide⟩ = 7
      ∧ x4BatchCommitments toyUrs rfl rotVk rotPs rotCh ⟨1, by decide⟩ = 10
      ∧ x4BatchCommitments toyUrs rfl rotVk rotPs rotCh ⟨2, by decide⟩ = 5 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- The `x₄` batch evaluations on the `u` slots, computed: the claimed set evaluations in reverse fold
order. -/
theorem rot_x4BatchEvals :
    x4BatchEvals (G := Fp) rotVk rotPs rotCh ⟨0, by decide⟩ = 8
      ∧ x4BatchEvals (G := Fp) rotVk rotPs rotCh ⟨1, by decide⟩ = 4 := by
  refine ⟨?_, ?_⟩ <;> decide

/-- The deployed `x₄` power form instantiated on the rotated two-set instance: the pinned deployed
commitment over the rewound runs `{rotCh with x4 := ξ}` is the `ξ`-power batch of the computed
aggregates. -/
theorem rot_deployed_x4_batch (ξ : Fp) :
    deployedCommitment (G := Fp) toyUrs rfl rotVk rotPs {rotCh with x4 := ξ}
      = ∑ j : Fin (deployedX4PairCount rotVk rotPs rotCh + 1),
          ξ ^ (j : ℕ) • x4BatchCommitments toyUrs rfl rotVk rotPs rotCh j :=
  deployedCommitment_x4_batch toyUrs rfl rotVk rotPs rotCh ξ

/-! ## The opened batch on augmented data

A `k = 0` URS with *nonzero* `u`/`w` (`toyUrsUW`), so the opened batch's declared-component
equations are exercised with genuine augmented content: three columns `10, 20, 30` opened at
challenges `0, 1, 2` by witnesses `3, 23, 73` with per-run components `(1, 2)`, `(11, 2)`,
`(31, 2)`, values `3, 5, 15`, and the gate `a₀·a₁ − i₀` satisfied on the decoded columns
(`3·5 = 15`). The terminal opened endpoint is discharged concretely, guarding the opened
hypothesis shapes the same way the plain fixtures guard the decoded ones. -/

/-- Toy URS at `k = 0` with nonzero blinding and inner-product generators: `g = 1`, `w = 2`,
`u = 3`. -/
abbrev toyUrsUW : URS Fp := ⟨0, fun _ => 1, 2, 3⟩

/-- On the value side the opened decode is pinned at `k = 0`: `commitGen (fun _ => 1)` has trivial
kernel, so the canonical decode is the claimed evaluations as constants. -/
theorem toyUW_opened_decode_pinned {n : ℕ} {cc : Fin n → Fp} {ce : Fin n → Fp}
    {w : Fin (2 ^ toyUrsUW.k) → Fp} {pU pW : Fp}
    (hb : OpenedBatchOpenings toyUrsUW (fun _ => 1) cc ce w pU pW) :
    openedDecodedCols hb = fun i => Polynomial.C (ce i) := by
  funext i
  have hcoeff : (openedColumnDecode hb).coeffs i = fun _ => ce i := by
    funext j
    have h0 : (openedColumnDecode hb).coeffs i 0 = ce i := by
      have hv := (openedColumnDecode hb).value i
      simpa [commitGen] using hv
    rw [toy_fin_eq_zero j]
    exact h0
  show coeffsToPoly ((openedColumnDecode hb).coeffs i) = _
  rw [hcoeff]
  simp [coeffsToPoly]

/-- The nonzero opened batch: columns `10, 20, 30` at challenges `0, 1, 2`, witnesses with genuine
`u`/`w` components, values `3, 5, 15`. -/
noncomputable def toyOpenedBatch :
    OpenedBatchOpenings toyUrsUW (fun _ => 1) (![10, 20, 30] : Fin 3 → Fp)
      (![3, 5, 15] : Fin 3 → Fp) (fun _ => 3) 1 2 where
  batchChallenge := ![0, 1, 2]
  challengesDistinct := by decide
  batched := ![fun _ => 3, fun _ => 23, fun _ => 73]
  batchedU := ![1, 11, 31]
  batchedW := ![2, 2, 2]
  current := 0
  current_eq := rfl
  currentU_eq := rfl
  currentW_eq := rfl
  commitment := by decide
  value := by decide

/-- The witness `3` opens the statement `(P, v) = (3, 3)` over `toyUrsUW`. -/
theorem toyUW_opens :
    IpaRelation toyUrsUW (3 : Fp) (fun _ => 1) (3 : Fp) (fun _ => (3 : Fp)) := by
  constructor <;> decide

/-- The combined gate numerator over the opened decoded columns vanishes: `3·5 − 15 = 0`. -/
theorem toyUW_numerator {w : Fin (2 ^ toyUrsUW.k) → Fp} {pU pW : Fp}
    (hb : OpenedBatchOpenings toyUrsUW (fun _ => 1) (![10, 20, 30] : Fin 3 → Fp)
      (![3, 5, 15] : Fin 3 → Fp) w pU pW) :
    combineGates (fun _ => 0) (selectedPolys (openedDecodedCols hb) ![0, 1])
      (selectedPolys (openedDecodedCols hb) ![2]) 0 toyGatesProd = 0 := by
  rw [toyUW_opened_decode_pinned hb]
  have h0 : selectedPolys (fun i => Polynomial.C ((![3, 5, 15] : Fin 3 → Fp) i))
      (![0, 1] : Fin 2 → Fin 3) 0 = Polynomial.C 3 := by
    simp [selectedPolys, finFn]
  have h1 : selectedPolys (fun i => Polynomial.C ((![3, 5, 15] : Fin 3 → Fp) i))
      (![0, 1] : Fin 2 → Fin 3) 1 = Polynomial.C 5 := by
    simp [selectedPolys, finFn]
  have h2 : selectedPolys (fun i => Polynomial.C ((![3, 5, 15] : Fin 3 → Fp) i))
      (![2] : Fin 1 → Fin 3) 0 = Polynomial.C 15 := by
    simp [selectedPolys, finFn]
  simp only [combineGates, gatePolys, toyGatesProd, List.ofFn_succ, List.ofFn_zero,
    List.foldl_cons, List.foldl_nil, Expr.toPoly, h0, h1, h2, zero_mul, zero_add]
  simp only [← Polynomial.C_mul, ← Polynomial.C_neg, ← Polynomial.C_add, Polynomial.C_eq_zero]
  norm_num

/-- The terminal opened constraint endpoint discharged concretely on augmented data: the guard that
the opened hypothesis shapes stay satisfiable. -/
theorem toyUW_opened_relation_and_batch_discharged : True :=
  opened_constraint_of_relation_and_batch (urs := toyUrsUW)
    (![10, 20, 30] : Fin 3 → Fp) (![3, 5, 15] : Fin 3 → Fp) ![0, 1] ![2]
    (fun _ => 0) 0 toyGatesProd 0 1 0 toyUW_opens toyOpenedBatch
    (by rw [toyUW_numerator toyOpenedBatch]; simp [quotientCheck])
    (by rw [toyUW_numerator toyOpenedBatch]; intro h; simp at h)
    (fun _ _ _ => trivial)

/-! ## The member binding, discharged on a rotated deployed instance

`deployed_witness_member_binding`'s hypothesis package — the plain `x₄` batch, the `x₁` family
with the honest run in the current slot, and the per-run aggregate witnesses pinned to the
canonical decode — is discharged concretely, so a reshape that makes the package unsatisfiable
breaks this file. At `k = 0` the commitment and value functionals coincide, so the batch is
satisfiable only when the aggregates equal the claimed set evaluations: `rotBindPs` tweaks the
rotated instance's proof string to sit exactly there (advice commitment `4 = u₀`, vanishing
random `8 = u₁`, `q′` the recomputed base evaluation). -/

/-- The rotated instance with aggregates matching evaluations, `q′` pending. -/
def rotBindPs0 : ProofString rotShape Fp Fp :=
  { rotPs with adviceCommitments := fun _ _ => 4, vanishingRandom := 8, multiopenQPrime := 0 }

/-- The rotated instance for the member-binding guard: aggregates equal claimed set evaluations
and `q′` is the recomputed base evaluation (which reads no `q′`), so the `x₄` batch columns and
evaluations coincide. -/
def rotBindPs : ProofString rotShape Fp Fp :=
  { rotBindPs0 with multiopenQPrime := deployedBaseEval rotVk rotBindPs0 rotCh }

/-- The `x₄` batch columns and evaluations of the guard instance coincide — computed. -/
theorem rotBind_CE :
    x4BatchCommitments toyUrs rfl rotVk rotBindPs rotCh = x4BatchEvals rotVk rotBindPs rotCh := by
  decide

/-- The plain `x₄` batch of the guard instance: each rewound witness is the power combination of
the (coinciding) batch evaluations, at the batching challenges `0, 1, 2` read off the slot index. -/
noncomputable def rotBindBatch :
    BatchOpeningsForWitness toyUrs (fun _ => 1)
      (x4BatchCommitments toyUrs rfl rotVk rotBindPs rotCh) (x4BatchEvals rotVk rotBindPs rotCh)
      (fun _ => ∑ j : Fin (deployedX4PairCount rotVk rotBindPs rotCh + 1),
        (((0 : Fin (deployedX4PairCount rotVk rotBindPs rotCh + 1)) : ℕ) : Fp) ^ (j : ℕ)
          • x4BatchEvals rotVk rotBindPs rotCh j) where
  batchChallenge := fun r => ((r : ℕ) : Fp)
  challengesDistinct := by decide
  batched := fun r _ => ∑ j : Fin (deployedX4PairCount rotVk rotBindPs rotCh + 1),
    (((r : Fin (deployedX4PairCount rotVk rotBindPs rotCh + 1)) : ℕ) : Fp) ^ (j : ℕ)
      • x4BatchEvals rotVk rotBindPs rotCh j
  current := 0
  current_eq := rfl
  commitment := by decide
  value := by decide

/-- `deployed_witness_member_binding`'s hypotheses discharged concretely on the guard instance:
the advice point set (one member), the honest `x₁` run in the single slot, and the aggregate
witness pinned to the canonical decode. -/
theorem rotBind_member_binding_discharged : True := by
  have hres := deployed_witness_member_binding (shape := rotShape) toyUrs rfl rotVk rotBindPs
    rotCh (b := fun _ => 1) rotBindBatch 0 (by decide)
    (fun _ => 3) (by decide) ⟨0, by decide⟩ rfl
    (fun _ => honestX1Run rotBindPs rotCh)
    (fun _ => (decodedCols_spec rotBindBatch).decodedColumns.coeffs
      ⟨deployedX4PairCount rotVk rotBindPs rotCh - 1 - 0, by omega⟩)
    (fun _ _ => 1)
    (fun _ => commitGen (fun _ => (1 : Fp))
      ((decodedCols_spec rotBindBatch).decodedColumns.coeffs
        ⟨deployedX4PairCount rotVk rotBindPs rotCh - 1 - 0, by omega⟩))
    ?_ ?_ ?_
  · trivial
  · intro r
    show commit toyUrs ((decodedCols_spec rotBindBatch).decodedColumns.coeffs
        ⟨deployedX4PairCount rotVk rotBindPs rotCh - 1 - 0, by omega⟩)
        = ((deployedX4Qs rotVk rotBindPs rotCh).getD 0 (Msm.zero rotShape.k Fp Fp)).eval
            ⟨rotShape.k, toyUrs.g, toyUrs.w, toyUrs.u⟩
    rw [(decodedCols_spec rotBindBatch).decodedColumns.commitment
      ⟨deployedX4PairCount rotVk rotBindPs rotCh - 1 - 0, by omega⟩]
    decide
  · intro r
    rfl
  · rfl

/-! ## Member-column constraint guard — status

The load-bearing hypothesis of the member-column endpoints (`member_constraint_of_relation_and_batch`
and its `_xgood`/`_hbound` variants, `Soundness.Multiopen.Opened`) is the member *binding*
`deployed_witness_member_binding`, discharged concretely just above (`rotBind_member_binding_discharged`).
A full discharge of `member_constraint_of_relation_and_batch` additionally requires an
`OpenedMemberDecode` for *every* point set, and a genuinely multi-member set's decode is produced by
the `x₁`-family machinery (`openedMemberDecode_of_x1Prob`), not by `decide`: `OpenedMemberDecode`'s
`reconstruct` fields relate the members to the *noncomputable* Vandermonde `openedColumnDecode`, so a
concrete multi-set discharge needs the same per-run `x₁`-family fixture that feeds that producer. The
member-binding guard above is the meaningful satisfiability witness; the constraint wrapper adds only
the gate check on the decoded members, structurally the same shape guarded by
`toyUW_opened_relation_and_batch_discharged`. -/

/-! ## The pinned-capstone derivation, exercised

`rotChB` puts the honest batching challenge at `0`, so a designated batch whose current slot sits
at challenge `0` satisfies the pinned capstone's `hξcur`, and the derived opening
(`OpenedBatchOpenings.ipaRelation_of_x4Current`) is exercised concretely. -/

/-- The guard instance's challenge record with the honest batching challenge at `0`. -/
def rotChB : Challenges rotShape.k Fp := { rotCh with x4 := 0 }

/-- A designated opened batch for the guard instance at the honest batching challenge, with
component-free slots (`toyUrs` has `u = w = 0`). -/
noncomputable def rotBindOpenedBatch :
    OpenedBatchOpenings toyUrs (fun _ => 1)
      (x4BatchCommitments toyUrs rfl rotVk rotBindPs rotChB)
      (x4BatchEvals rotVk rotBindPs rotChB)
      (fun _ => ∑ j : Fin (deployedX4PairCount rotVk rotBindPs rotChB + 1),
        (((0 : Fin (deployedX4PairCount rotVk rotBindPs rotChB + 1)) : ℕ) : Fp) ^ (j : ℕ)
          • x4BatchEvals rotVk rotBindPs rotChB j) 0 0 where
  batchChallenge := fun r => ((r : ℕ) : Fp)
  challengesDistinct := by decide
  batched := fun r _ => ∑ j : Fin (deployedX4PairCount rotVk rotBindPs rotChB + 1),
    (((r : Fin (deployedX4PairCount rotVk rotBindPs rotChB + 1)) : ℕ) : Fp) ^ (j : ℕ)
      • x4BatchEvals rotVk rotBindPs rotChB j
  batchedU := fun _ => 0
  batchedW := fun _ => 0
  current := 0
  current_eq := rfl
  currentU_eq := rfl
  currentW_eq := rfl
  commitment := by decide
  value := by decide

/-- The pinned capstone's derived opening discharged concretely: the designated batch at the
honest batching challenge opens the opened statement, no opening assumed. -/
theorem rotBindB_pinned_opening_discharged : True := by
  have := rotBindOpenedBatch.ipaRelation_of_x4Current (by decide)
  trivial

/-! ## Regression guards for the halo2-faithfulness fixes (PR #30)

Concrete guards that would break if the rotation feed or the multiopen value-separation floor
regressed. -/

/-- **Rotation feed (`rotatedFeed`, P0-1).** The gate reads each column composed with its layout
rotation, so at the gate point `x` the value is the column at the rotated point `ω^rot·x`. Here the
column `X` at layout rotation `2` under `ω = 3`, evaluated at `x = 5`, is `3²·5` — *not* `5`, which
is what the pre-fix raw-column feed (rotation-0) produced. -/
theorem rotatedFeed_eval_fixture :
    ((rotatedFeed (n := 1) (3 : Fp) [(0, 2)] (fun _ => Polynomial.X)) 0).eval 5
      = (3 : Fp) ^ (2 : ℤ) * 5 := by
  simp only [rotatedFeed, finFn, dif_pos (show (0 : ℕ) < 1 by norm_num), List.getD_cons_zero,
    eval_comp_rotate, Polynomial.eval_X]

/-- **The `x₂` value-separation floor (value check).** A combined-evaluation power sum
`∑_{j<2} ξ^j·cⱼ` that vanishes at the two distinct challenges `0, 1` forces both coefficients to
zero — the per-set separation `multiopenEval_perSet_zero_of_samples` rests on, exercised concretely
through `coeffs_zero_of_power_sum_vanishes`. -/
theorem power_sum_vanishes_fixture (c : ℕ → Fp)
    (h : ∀ r : Fin 2, ∑ j ∈ Finset.range 2, (![0, 1] : Fin 2 → Fp) r ^ j * c j = 0)
    (i : Fin 2) : c i = 0 :=
  coeffs_zero_of_power_sum_vanishes c ![0, 1]
    (by intro a b hab; fin_cases a <;> fin_cases b <;> simp_all) h i

/-- **Retained `CommitmentId`s are aligned with the members (P0-2a).** Per point set, the retained
slot-identity list `deployedSetCommIds` is positionally aligned with the member list
`deployedSetQueries` — the alignment the layout selection (`adviceLayout`) and quotient binding
(`quotCommitted`) index into. The pre-fix `CommitmentRef`-only projection dropped the identities, so
this equality could not be stated. -/
theorem rot_setCommIds_aligned :
    (deployedSetCommIds rotVk rotPs rotCh 0).length = (deployedSetQueries rotVk rotPs rotCh 0).length
      ∧ (deployedSetCommIds rotVk rotPs rotCh 1).length
          = (deployedSetQueries rotVk rotPs rotCh 1).length :=
  ⟨deployedSetCommIds_length rotVk rotPs rotCh 0, deployedSetCommIds_length rotVk rotPs rotCh 1⟩

end MultiopenDecodeFixture
end Zcash.Snark
