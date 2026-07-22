import Mathlib
import Zcash.Snark.Soundness.Main
import Zcash.Snark.Soundness.Multiopen.Decode
import Zcash.Snark.Soundness.Multiopen.Deployed
import Zcash.Snark.Soundness.Multiopen.Compat
import Zcash.Snark.Soundness.GoodChallenge

/-!
# The opened `x₄` chain: batch decode through the declared `U`/`W` components

The fork bridge opens the *adjusted* commitment: a `ForkedTranscript` declares `U`/`W` components
`pU`/`pW` and its clean IPA transcript accepts `openedCommitment = deployedCommitment − pU•u − pW•w`,
not the raw `deployedCommitment` the plain batch decode (`Soundness.Multiopen.Decode`) consumes. This
module closes that gap: it re-runs the `x₄` batch decode with every witness carried in *augmented*
`(g, u, w)` representation, so the rewound forks' openings — each with its own declared components —
batch, decode, and reconstruct exactly as the plain chain does.

The route, mirroring the plain chain step for step:

1. `OpenedBatchOpenings` — the batch family: per-run witnesses with declared components, the
   commitment equations in augmented power form `commit(aᵣ) + pUᵣ•u + pWᵣ•w = Σⱼ ξᵣʲ • Cⱼ`
   (the plain `BatchOpeningsForWitness` is the `pUᵣ = pWᵣ = 0` slice).
2. `openedColumnDecode` — the canonical Vandermonde decode, run componentwise: the same inverse
   matrix decodes the witness vectors, the `U`-components, and the `W`-components
   (`vandermonde_decode_map`/`vandermonde_reconstruct_map`, the module-valued decode core).
   Each decoded column opens its aggregate in augmented form and every run's triple is
   reconstructed as its `ξᵣ`-power combination.
3. `openedX4Batch_of_witnessFamily` — the deployed instantiation: the power form of the batch
   equations is `deployedCommitment_x4_batch`/`multiopenValue_x4_batch`, so the columns are the
   deployed aggregates (`x4BatchCommitments`/`x4BatchEvals`), as in the plain chain.
4. `openedX4Rewind_of_x4Prob` — the accept-measure floor: the event `OpenedX4Accept` asks each
   rewound `x₄` run (an `X4Run`, presenting its *own* re-sent IPA opening) for a fork and a clean
   accepting transcript on its opened commitment — exactly what the adaptive feeder
   `x4_cleanTree_of_deployedAccepts_adaptive` produces (`openedX4Accept_of_deployedAccepts`) — and
   the single-squeeze counting floor (`exists_injective_accepting_of_measure`) turns the measure
   into the rewound family. Ranging over `X4Run`s (not the honest `ps`) makes the measure adaptive,
   retiring the fixed-`ps` static-dichotomy caveat.
5. `opened_constraint_of_opening_or_relation` — the terminal constraint endpoint over the decoded
   columns, mirroring `decoded_constraint_of_opening_or_relation`.

The augmented representation is not a detour: the deployed aggregates genuinely carry `u`/`w`
contributions (the fingerprint MSM has `uScalar`/`wScalar` slots), and the binding story already
lives in the augmented basis — a collision computes a `NontrivialRelation` among `(g, u, w)`. The
`hquot`/`hgood` hypotheses of the terminal endpoints keep the plain chain's canonical-decode scoping
(`Soundness.Multiopen.Decode`, the scope section).

The `x₁` layer continues the chain to the member commitments: each `x₁`-rewound run's aggregate
witness arrives in this same augmented representation, so `opened_witness_member_binding` mirrors
the plain member binding with componentwise decode, and `openedMemberDecode_of_x1Prob` produces
its inputs from the `x₁` accept measure (`OpenedX1Accept` — each run carrying its own opened `x₄`
batch, the stacked floors explicit). The per-set gluing is `deployed_witness_two_level`
(`Soundness.Multiopen.Deployed`). What remains fingerprint-delegated: the per-member claimed
evaluations at the original rotated points and the gate/`x`→`x₃` transport
(`Soundness.Multiopen.Decode`, the deployed-status section).
-/

namespace Zcash.Snark

section Opened

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-! ## The Vandermonde decode core, module-valued

The plain decode inverts the power system for witness vectors (`batch_open_with_coeffs`). The opened
decode inverts the same system three times — witness vectors, `U`-components, `W`-components — so the
core is stated once over an arbitrary `Fp`-module and instantiated per component. -/

/-- Vandermonde decode in any `Fp`-module: a family in flat power form over columns `C` is inverted
columnwise by the inverse-matrix combination. `batch_open_with_coeffs` is the `commitGen` image of
this fact. -/
theorem vandermonde_decode_map {M : Type*} [AddCommMonoid M] [Module Fp M] {n : ℕ}
    {z : Fin n → Fp} {C F : Fin n → M} (μ : Fin n → Fin n → Fp)
    (hμ : ∀ (i j : Fin n), (∑ k : Fin n, μ i k * z k ^ (j : ℕ)) = if i = j then 1 else 0)
    (hF : ∀ r, F r = ∑ j : Fin n, z r ^ (j : ℕ) • C j) (i : Fin n) :
    (∑ r : Fin n, μ i r • F r) = C i := by
  simp only [hF, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, hμ, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

/-- Vandermonde reconstruction in any `Fp`-module: the power combination of the decoded columns
returns each family member. `batch_open_reconstruct_with_coeffs` is the vector instance. -/
theorem vandermonde_reconstruct_map {M : Type*} [AddCommMonoid M] [Module Fp M] {n : ℕ}
    {z : Fin n → Fp} (F : Fin n → M) (μ : Fin n → Fin n → Fp)
    (hμ : ∀ (i j : Fin n), (∑ k : Fin n, z i ^ (k : ℕ) * μ k j) = if i = j then 1 else 0)
    (i : Fin n) :
    (∑ j : Fin n, z i ^ (j : ℕ) • (∑ k : Fin n, μ j k • F k)) = F i := by
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, hμ, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

/-! ## The opened batch family and its canonical decode -/

/-- A family of rewound batched openings carried in augmented `(g, u, w)` representation: run `r`'s
witness `batched r` opens the power batch after removing its declared components, so the commitment
equation reads `commit(batched r) + batchedU r • u + batchedW r • w = Σⱼ ξᵣʲ • Cⱼ`. The current slot
pins the designated run's triple to `(currentWitness, pU, pW)` — for the deployed instantiation, the
honest fork's extracted witness and declared components. `BatchOpeningsForWitness` is the
`batchedU = batchedW = 0` slice. -/
structure OpenedBatchOpenings (urs : URS G) (b : Fin (2 ^ urs.k) → Fp) {numColumns : ℕ}
    (columnCommitments : Fin numColumns → G) (columnEvals : Fin numColumns → Fp)
    (currentWitness : Fin (2 ^ urs.k) → Fp) (pU pW : Fp) where
  batchChallenge : Fin numColumns → Fp
  challengesDistinct : Function.Injective batchChallenge
  batched : Fin numColumns → (Fin (2 ^ urs.k) → Fp)
  batchedU : Fin numColumns → Fp
  batchedW : Fin numColumns → Fp
  current : Fin numColumns
  current_eq : batched current = currentWitness
  currentU_eq : batchedU current = pU
  currentW_eq : batchedW current = pW
  commitment :
    ∀ r, commit urs (batched r) + batchedU r • urs.u + batchedW r • urs.w
      = ∑ j : Fin numColumns, batchChallenge r ^ (j : ℕ) • columnCommitments j
  value :
    ∀ r, commitGen b (batched r)
      = ∑ j : Fin numColumns, batchChallenge r ^ (j : ℕ) • columnEvals j

/-- The decoded columns of an opened batch: per column, a witness vector plus `U`/`W` components
opening the column commitment in augmented form and the claimed evaluation, with every run's triple
reconstructed as its power combination of the decoded triples. -/
structure OpenedColumnDecode {urs : URS G} {b : Fin (2 ^ urs.k) → Fp} {numColumns : ℕ}
    {columnCommitments : Fin numColumns → G} {columnEvals : Fin numColumns → Fp}
    {currentWitness : Fin (2 ^ urs.k) → Fp} {pU pW : Fp}
    (hbatch : OpenedBatchOpenings urs b columnCommitments columnEvals currentWitness pU pW) where
  coeffs : Fin numColumns → (Fin (2 ^ urs.k) → Fp)
  uComp : Fin numColumns → Fp
  wComp : Fin numColumns → Fp
  commitment :
    ∀ i, commit urs (coeffs i) + uComp i • urs.u + wComp i • urs.w = columnCommitments i
  value : ∀ i, commitGen b (coeffs i) = columnEvals i
  reconstruct :
    ∀ r, hbatch.batched r
      = ∑ i : Fin numColumns, hbatch.batchChallenge r ^ (i : ℕ) • coeffs i
  reconstructU :
    ∀ r, hbatch.batchedU r
      = ∑ i : Fin numColumns, hbatch.batchChallenge r ^ (i : ℕ) • uComp i
  reconstructW :
    ∀ r, hbatch.batchedW r
      = ∑ i : Fin numColumns, hbatch.batchChallenge r ^ (i : ℕ) • wComp i

/-- The canonical decode of an opened batch: the Vandermonde-inverse combination, run componentwise
on the witness vectors and the two declared-component families — the same matrix inverts all three
power systems (`vandermonde_decode_map`, one instance per component). -/
noncomputable def openedColumnDecode {urs : URS G} {b : Fin (2 ^ urs.k) → Fp} {numColumns : ℕ}
    {columnCommitments : Fin numColumns → G} {columnEvals : Fin numColumns → Fp}
    {currentWitness : Fin (2 ^ urs.k) → Fp} {pU pW : Fp}
    (hbatch : OpenedBatchOpenings urs b columnCommitments columnEvals currentWitness pU pW) :
    OpenedColumnDecode hbatch := by
  classical
  set μ : Matrix (Fin numColumns) (Fin numColumns) Fp :=
    (Matrix.vandermonde hbatch.batchChallenge)⁻¹ with hμdef
  have hleft :
      ∀ (i j : Fin numColumns), (∑ k : Fin numColumns,
          μ i k * hbatch.batchChallenge k ^ (j : ℕ))
        = if i = j then 1 else 0 := fun i j => by
    simpa [hμdef] using
      vandermonde_inv_left hbatch.batchChallenge hbatch.challengesDistinct i j
  have hright :
      ∀ (i j : Fin numColumns), (∑ k : Fin numColumns,
          hbatch.batchChallenge i ^ (k : ℕ) * μ k j)
        = if i = j then 1 else 0 := fun i j => by
    simpa [hμdef] using
      vandermonde_inv_right hbatch.batchChallenge hbatch.challengesDistinct i j
  refine
    { coeffs := fun i => ∑ r, μ i r • hbatch.batched r
      uComp := fun i => ∑ r, μ i r • hbatch.batchedU r
      wComp := fun i => ∑ r, μ i r • hbatch.batchedW r
      commitment := ?_
      value := ?_
      reconstruct := fun r =>
        (vandermonde_reconstruct_map hbatch.batched μ hright r).symm
      reconstructU := fun r =>
        (vandermonde_reconstruct_map hbatch.batchedU μ hright r).symm
      reconstructW := fun r =>
        (vandermonde_reconstruct_map hbatch.batchedW μ hright r).symm }
  · -- The three linear pieces collapse to one μ-combination of the per-run augmented equations,
    -- which `vandermonde_decode_map` inverts.
    intro i
    have hlin :
        commit urs (∑ r, μ i r • hbatch.batched r)
            + (∑ r, μ i r • hbatch.batchedU r) • urs.u
            + (∑ r, μ i r • hbatch.batchedW r) • urs.w
          = ∑ r, μ i r • (commit urs (hbatch.batched r) + hbatch.batchedU r • urs.u
              + hbatch.batchedW r • urs.w) := by
      rw [commit_eq_commitGen, commitGen_sum, Finset.sum_smul, Finset.sum_smul,
        ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [commitGen_smul_left, smul_eq_mul, smul_eq_mul, mul_smul, mul_smul, smul_add, smul_add,
        commit_eq_commitGen]
    rw [hlin]
    exact vandermonde_decode_map μ hleft hbatch.commitment i
  · intro i
    have hlin : commitGen b (∑ r, μ i r • hbatch.batched r)
        = ∑ r, μ i r • commitGen b (hbatch.batched r) := by
      rw [commitGen_sum]
      exact Finset.sum_congr rfl fun r _ => commitGen_smul_left b _ _
    rw [hlin]
    exact vandermonde_decode_map μ hleft hbatch.value i

/-- The canonical decoded column polynomials of an opened batch. -/
noncomputable def openedDecodedCols {urs : URS G} {b : Fin (2 ^ urs.k) → Fp} {numColumns : ℕ}
    {columnCommitments : Fin numColumns → G} {columnEvals : Fin numColumns → Fp}
    {currentWitness : Fin (2 ^ urs.k) → Fp} {pU pW : Fp}
    (hbatch : OpenedBatchOpenings urs b columnCommitments columnEvals currentWitness pU pW) :
    Fin numColumns → Polynomial Fp :=
  fun i => coeffsToPoly ((openedColumnDecode hbatch).coeffs i)

/-- **Each decoded `x₄`-slot column opens to its claimed batch evaluation at `x₃`.** The opened
batch's base vector is `evalVector urs.k ch.x3`, so `commitGen` of a decoded column vector is that
column polynomial evaluated at `ch.x3` (`coeffsToPoly_eval`); the decode's `value` field pins it to
the slot's claimed evaluation `x4BatchEvals`. This is the `x₄`-level value binding the multiopen
value check un-batches through. -/
theorem openedDecodedCols_eval_x3 [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {a₀ : Fin (2 ^ urs.k) → Fp} {pU pW : Fp}
    (pbatch : OpenedBatchOpenings urs (evalVector urs.k ch.x3)
      (x4BatchCommitments urs hk vk ps ch) (x4BatchEvals vk ps ch) a₀ pU pW)
    (i : Fin (deployedX4PairCount vk ps ch + 1)) :
    (openedDecodedCols pbatch i).eval ch.x3 = x4BatchEvals vk ps ch i := by
  rw [openedDecodedCols, coeffsToPoly_eval]
  exact (openedColumnDecode pbatch).value i

/-- **The decoded quotient column `q′` opens to `deployedBaseEval` at `x₃`.** The top `x₄` slot's
claimed evaluation is the base evaluation `multiopenEval ch.x2 ch.x3 …` the quotient commitment is
claimed to open to (`x4BatchEvals` top branch). This is the anchor of the commitment-binding value
check: `q′` is fixed across `x₃`-rewinds (absorbed before `x₃`), so this identity, taken over enough
rewound `x₃`, forces the per-set `r`-polynomial consistency. -/
theorem openedDecodedCols_top_eval_x3 [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {a₀ : Fin (2 ^ urs.k) → Fp} {pU pW : Fp}
    (pbatch : OpenedBatchOpenings urs (evalVector urs.k ch.x3)
      (x4BatchCommitments urs hk vk ps ch) (x4BatchEvals vk ps ch) a₀ pU pW) :
    (openedDecodedCols pbatch ⟨deployedX4PairCount vk ps ch, Nat.lt_succ_self _⟩).eval ch.x3
      = deployedBaseEval vk ps ch := by
  rw [openedDecodedCols_eval_x3]
  show (if deployedX4PairCount vk ps ch < deployedX4PairCount vk ps ch then _
    else deployedBaseEval vk ps ch) = deployedBaseEval vk ps ch
  rw [if_neg (lt_irrefl _)]

/-- The current witness is the current-challenge power combination of the decoded column vectors —
the opened counterpart of `DecodedColumnFamilyOfBatch.currentWitness_eq`. -/
theorem OpenedColumnDecode.currentWitness_eq {urs : URS G} {b : Fin (2 ^ urs.k) → Fp}
    {numColumns : ℕ} {columnCommitments : Fin numColumns → G} {columnEvals : Fin numColumns → Fp}
    {currentWitness : Fin (2 ^ urs.k) → Fp} {pU pW : Fp}
    {hbatch : OpenedBatchOpenings urs b columnCommitments columnEvals currentWitness pU pW}
    (hdecoded : OpenedColumnDecode hbatch) :
    currentWitness
      = ∑ i : Fin numColumns, hbatch.batchChallenge hbatch.current ^ (i : ℕ)
          • hdecoded.coeffs i := by
  calc
    currentWitness = hbatch.batched hbatch.current := hbatch.current_eq.symm
    _ = ∑ i : Fin numColumns, hbatch.batchChallenge hbatch.current ^ (i : ℕ)
          • hdecoded.coeffs i := hdecoded.reconstruct hbatch.current

/-! ## The terminal `∀`-witness form and its transfer -/

/-- Terminal form of the opened rewinding output: a batch family for every opening of the pinned
statement `(P, b, v)`, at the fixed declared components `(pU, pW)`. As in the plain chain
(`MultiopenRewindForRelation`), the `∀`-witness shape costs nothing beyond a transcript-tied one —
the current-slot equations mention only the shared `P`, `v`, `pU`, `pW`, so any opening swaps into
the current slot (`openedRewindForRelation_of_batch`). At the deployed instantiation `P` is the
honest fork's `openedCommitment` and `(pU, pW)` its declared components. -/
abbrev OpenedRewindForRelation (urs : URS G) (P : G) (b : Fin (2 ^ urs.k) → Fp) (v : Fp)
    {numColumns : ℕ} (columnCommitments : Fin numColumns → G) (columnEvals : Fin numColumns → Fp)
    (pU pW : Fp) : Type _ :=
  ∀ a, IpaRelation urs P b v a →
    OpenedBatchOpenings urs b columnCommitments columnEvals a pU pW

/-- The `∀`-witness transfer for opened batches: a family for one witness of `(P, b, v)` yields the
terminal form, swapping any other opening into the current slot — the declared-component families are
untouched, and the current-slot equations only read the shared `P`, `v`, `pU`, `pW`. -/
noncomputable def openedRewindForRelation_of_batch {urs : URS G} {P : G}
    {b : Fin (2 ^ urs.k) → Fp} {v : Fp} {numColumns : ℕ}
    {columnCommitments : Fin numColumns → G} {columnEvals : Fin numColumns → Fp}
    {w : Fin (2 ^ urs.k) → Fp} {pU pW : Fp} (hw : IpaRelation urs P b v w)
    (hb : OpenedBatchOpenings urs b columnCommitments columnEvals w pU pW) :
    OpenedRewindForRelation urs P b v columnCommitments columnEvals pU pW := fun a hrel => by
  classical
  obtain ⟨z, hzinj, batched, bU, bW, cur, hcur, hcurU, hcurW, hcomm, hval⟩ := hb
  refine
    { batchChallenge := z
      challengesDistinct := hzinj
      batched := Function.update batched cur a
      batchedU := bU
      batchedW := bW
      current := cur
      current_eq := Function.update_self cur a batched
      currentU_eq := hcurU
      currentW_eq := hcurW
      commitment := ?_
      value := ?_ }
  · intro r
    rcases eq_or_ne r cur with hr | hr
    · rw [hr, Function.update_self, hrel.1, ← hw.1, ← hcur]
      exact hcomm cur
    · rw [Function.update_of_ne hr]
      exact hcomm r
  · intro r
    rcases eq_or_ne r cur with hr | hr
    · have hia : commitGen b a = innerProduct a b := by
        simp [innerProduct, commitGen, smul_eq_mul]
      have hiw : commitGen b w = innerProduct w b := by
        simp [innerProduct, commitGen, smul_eq_mul]
      rw [hr, Function.update_self, hia, hrel.2, ← hw.2, ← hiw, ← hcur]
      exact hval cur
    · rw [Function.update_of_ne hr]
      exact hval r

/-! ## The deployed instantiation -/

/-- Package a family of augmented openings of the rewound deployed statements as an opened batch
over the deployed aggregates: the power form of each run's equations is
`deployedCommitment_x4_batch`/`multiopenValue_x4_batch`, proven, not assumed. -/
noncomputable def openedX4Batch_of_witnessFamily [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) {b : Fin (2 ^ urs.k) → Fp}
    (ξ : Fin (deployedX4PairCount vk ps ch + 1) → Fp) (hξinj : Function.Injective ξ)
    (cur : Fin (deployedX4PairCount vk ps ch + 1))
    (aF : Fin (deployedX4PairCount vk ps ch + 1) → (Fin (2 ^ urs.k) → Fp))
    (pUF pWF : Fin (deployedX4PairCount vk ps ch + 1) → Fp)
    (hC : ∀ r, commit urs (aF r) + pUF r • urs.u + pWF r • urs.w
      = deployedCommitment urs hk vk ps {ch with x4 := ξ r})
    (hv : ∀ r, commitGen b (aF r) = multiopenValue vk ps {ch with x4 := ξ r}) :
    OpenedBatchOpenings urs b (x4BatchCommitments urs hk vk ps ch) (x4BatchEvals vk ps ch)
      (aF cur) (pUF cur) (pWF cur) where
  batchChallenge := ξ
  challengesDistinct := hξinj
  batched := aF
  batchedU := pUF
  batchedW := pWF
  current := cur
  current_eq := rfl
  currentU_eq := rfl
  currentW_eq := rfl
  commitment := fun r => by
    rw [hC r]
    exact deployedCommitment_x4_batch urs hk vk ps ch (ξ r)
  value := fun r => by
    rw [hv r]
    exact multiopenValue_x4_batch vk ps ch (ξ r)

/-- The opened `x₄` accept event at a rewound batching challenge: *some* rewound run (an `X4Run`,
carrying its own re-sent IPA opening `r.spliced ps`) has a fork with a clean accepting transcript on
its opened commitment, for the *shared* honest `multiopenValue` (`x4Run_multiopenValue`). Ranging
over `X4Run`s rather than reusing the honest `ps` is what makes the event adaptive — each `ξ`-run may
present a distinct opening — so the measure `openedX4Rewind_of_x4Prob` spends no longer inherits the
constant strategy. Fed by `openedX4Accept_of_deployedAccepts` (via
`x4_cleanTree_of_deployedAccepts_adaptive`). -/
def OpenedX4Accept [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (b : Fin (2 ^ urs.k) → Fp) (ξv : Fp) : Prop :=
  ∃ (r : X4Run shape G) (z blind : Fp)
    (fs : ForkedTranscript urs hk vk (r.spliced ps) (r.challenges ch ξv) b z blind)
    (t : IpaTreeV Fp G urs.k),
    IpaAcceptV urs.g b fs.openedCommitment (multiopenValue vk ps {ch with x4 := ξv}) t

/-- Feed the opened `x₄` accept event from deployed-accept facts for a rewound run `r`: off the
relation branch, the run's Fiat–Shamir bridge peels to a clean accepting transcript on its opened
commitment (`x4_cleanTree_of_deployedAccepts_adaptive`), for the shared honest value. -/
theorem openedX4Accept_of_deployedAccepts [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {b : Fin (2 ^ urs.k) → Fp} {z blind : Fp} (hz : z ≠ 0)
    (hnrel : ¬HasNontrivialRelation (F := Fp) urs.g urs.u urs.w)
    (r : X4Run shape G) (ξv : Fp)
    (hFS : FiatShamirTree urs hk vk (r.spliced ps) (r.challenges ch ξv) b z blind)
    (hacc : DeployedAccepts urs hk vk (r.spliced ps) (r.challenges ch ξv)) :
    OpenedX4Accept urs hk vk ps ch b ξv := by
  obtain ⟨fs, t, ht⟩ :=
    x4_cleanTree_of_deployedAccepts_adaptive urs hk vk ps ch hz hnrel r ξv hFS hacc
  exact ⟨r, z, blind, fs, t, ht⟩

/-- **The opened `x₃` accept event.** The `x₃` analogue of `OpenedX4Accept`, for the interpolation
squeeze. Unlike `x₄` (the last squeeze), an `x₃`-rewound run re-sends its post-`x₃` fields
(`multiopenU`, the IPA opening — `X3Continuation`), so its `multiopenValue` is the *run's own*, not
the honest `{ch with x3 := χ}` value; the event therefore carries `multiopenValue vk (r.spliced ps)
(r.challenges ch χ)`. The quotient commitment `q′` is absorbed before `x₃` (`X3Continuation` omits
it), so it is shared across the family — the commitment-binding lever for the value check. -/
def OpenedX3Accept [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (b : Fin (2 ^ urs.k) → Fp) (χ : Fp) : Prop :=
  ∃ (r : X3Run shape G) (z blind : Fp)
    (fs : ForkedTranscript urs hk vk (r.spliced ps) (r.challenges ch χ) b z blind)
    (t : IpaTreeV Fp G urs.k),
    IpaAcceptV urs.g b fs.openedCommitment
      (multiopenValue vk (r.spliced ps) (r.challenges ch χ)) t

/-- Feed the opened `x₃` accept event from deployed-accept facts for an `x₃`-rewound run `r`: off the
relation branch, the run's Fiat–Shamir bridge peels to a clean accepting transcript on its opened
commitment for the run's own value (`deployed_to_acceptV`), the run being a `reprogramX3` event. -/
theorem openedX3Accept_of_deployedAccepts [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {b : Fin (2 ^ urs.k) → Fp} {z blind : Fp} (hz : z ≠ 0)
    (hnrel : ¬HasNontrivialRelation (F := Fp) urs.g urs.u urs.w)
    (r : X3Run shape G) (χ : Fp)
    (hFS : FiatShamirTree urs hk vk (r.spliced ps) (r.challenges ch χ) b z blind)
    (hacc : DeployedAccepts urs hk vk (r.spliced ps) (r.challenges ch χ)) :
    OpenedX3Accept urs hk vk ps ch b χ := by
  set fs := hFS (deployedAccepts_verifierEq urs hk vk (r.spliced ps) _ hacc) with hfs
  rcases deployed_to_acceptV hz urs.g b fs.openedCommitment
      (multiopenValue vk (r.spliced ps) (r.challenges ch χ)) blind fs.tree fs.accepts with
      hclean | hrel
  · exact ⟨r, z, blind, fs, projTree fs.tree, hclean⟩
  · exact absurd hrel hnrel

/-- **The opened `x₂` accept event.** The `x₂` (set-separation) analogue; an `x₂`-rewound run re-sends
its post-`x₂` fields including `q′` (`X2Continuation` carries `multiopenQPrime`), so again the event
carries the run's own `multiopenValue`. -/
def OpenedX2Accept [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (b : Fin (2 ^ urs.k) → Fp) (χ : Fp) : Prop :=
  ∃ (r : X2Run shape G) (z blind : Fp)
    (fs : ForkedTranscript urs hk vk (r.spliced ps) (r.challenges ch χ) b z blind)
    (t : IpaTreeV Fp G urs.k),
    IpaAcceptV urs.g b fs.openedCommitment
      (multiopenValue vk (r.spliced ps) (r.challenges ch χ)) t

/-- Feed the opened `x₂` accept event from deployed-accept facts for an `x₂`-rewound run `r`. -/
theorem openedX2Accept_of_deployedAccepts [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {b : Fin (2 ^ urs.k) → Fp} {z blind : Fp} (hz : z ≠ 0)
    (hnrel : ¬HasNontrivialRelation (F := Fp) urs.g urs.u urs.w)
    (r : X2Run shape G) (χ : Fp)
    (hFS : FiatShamirTree urs hk vk (r.spliced ps) (r.challenges ch χ) b z blind)
    (hacc : DeployedAccepts urs hk vk (r.spliced ps) (r.challenges ch χ)) :
    OpenedX2Accept urs hk vk ps ch b χ := by
  set fs := hFS (deployedAccepts_verifierEq urs hk vk (r.spliced ps) _ hacc) with hfs
  rcases deployed_to_acceptV hz urs.g b fs.openedCommitment
      (multiopenValue vk (r.spliced ps) (r.challenges ch χ)) blind fs.tree fs.accepts with
      hclean | hrel
  · exact ⟨r, z, blind, fs, projTree fs.tree, hclean⟩
  · exact absurd hrel hnrel

open scoped ENNReal in
open Classical in
/-- **The `x₄` forking floor through the opened commitment.** If the honest run's opened accept
event holds and the opened accept measure of the `x₄`-rewound runs beats `pairCount / p`, the
terminal opened rewinding output exists for any statement `P` sitting at declared components
`(pU, pW)` of the deployed commitment — over the deployed aggregates. Each rewound run contributes
its own fork's augmented opening; each opening of `P` seeds the current slot itself, so differing
declared components across runs are absorbed by the augmented batch, not assumed away. The measure
hypothesis carries the same random-oracle uniformity axiom as every `hprob`
(`Soundness.Forking.Oracle`); the runs are the `reprogramX4` reprogramming events
(`Soundness.Forking.Rewind`); each run's accepting transcript is that run's own round-forking
output, and `openedX4Accept_of_deployedAccepts` feeds the event from deployed accepts. -/
noncomputable def openedX4Rewind_of_x4Prob [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) {b : Fin (2 ^ urs.k) → Fp}
    (P : G) (pU pW : Fp)
    (hP : P = deployedCommitment urs hk vk ps ch - pU • urs.u - pW • urs.w)
    (hx₀ : OpenedX4Accept urs hk vk ps ch b ch.x4)
    (hprob4 : ((deployedX4PairCount vk ps ch : ℝ≥0∞)) / Fintype.card Fp
      < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
          (OpenedX4Accept urs hk vk ps ch b))) :
    OpenedRewindForRelation urs P b (multiopenValue vk ps ch)
      (x4BatchCommitments urs hk vk ps ch) (x4BatchEvals vk ps ch) pU pW := fun a hrel => by
  -- The counting floor yields the injective rewound family with `ch.x4` in slot `0`
  -- (`{ch with x4 := ch.x4}` is `ch` by structure eta). Everything is destructured with
  -- `Classical.choose`/`ipa_extractV` — the target is data, so the bare existentials cannot be
  -- case-split. The supplied opening `a` seeds slot `0`, so no honest-run extraction is needed.
  have hex := exists_injective_accepting_of_measure
    (acc := OpenedX4Accept urs hk vk ps ch b) (x₀ := ch.x4) hx₀ hprob4
  set ξ := Classical.choose hex with hξdef
  have hspec := Classical.choose_spec hex
  have hξinj : Function.Injective ξ := hspec.1
  have hξ0 : ξ 0 = ch.x4 := hspec.2.1
  have hacc : ∀ r : Fin (deployedX4PairCount vk ps ch + 1),
      ∃ (run : X4Run shape G) (z' blind' : Fp)
        (fs : ForkedTranscript urs hk vk (run.spliced ps) (run.challenges ch (ξ r)) b z' blind')
        (t : IpaTreeV Fp G urs.k),
        IpaAcceptV urs.g b fs.openedCommitment (multiopenValue vk ps {ch with x4 := ξ r}) t :=
    hspec.2.2
  choose runF zf blindf fsf tf htf using hacc
  let extF := fun r => ipa_extractV urs.g b ((fsf r).openedCommitment)
    (multiopenValue vk ps {ch with x4 := ξ r}) (tf r) (htf r)
  have hC : ∀ r, commit urs (Fin.cases a (fun i => (extF i.succ).1) r)
      + (Fin.cases (motive := fun _ => Fp) pU (fun i => (fsf i.succ).pU) r) • urs.u
      + (Fin.cases (motive := fun _ => Fp) pW (fun i => (fsf i.succ).pW) r) • urs.w
      = deployedCommitment urs hk vk ps {ch with x4 := ξ r} := by
    intro r
    cases r using Fin.cases with
    | zero =>
        simp only [Fin.cases_zero]
        rw [hξ0, hrel.1, hP]
        show deployedCommitment urs hk vk ps ch - pU • urs.u - pW • urs.w
            + pU • urs.u + pW • urs.w = deployedCommitment urs hk vk ps ch
        abel
    | succ i =>
        simp only [Fin.cases_succ]
        rw [commit_eq_commitGen, (extF i.succ).2.1]
        show deployedCommitment urs hk vk ps {ch with x4 := ξ i.succ}
            - (fsf i.succ).pU • urs.u - (fsf i.succ).pW • urs.w
            + (fsf i.succ).pU • urs.u + (fsf i.succ).pW • urs.w
          = deployedCommitment urs hk vk ps {ch with x4 := ξ i.succ}
        abel
  have hv : ∀ r, commitGen b (Fin.cases a (fun i => (extF i.succ).1) r)
      = multiopenValue vk ps {ch with x4 := ξ r} := by
    intro r
    cases r using Fin.cases with
    | zero =>
        simp only [Fin.cases_zero]
        rw [hξ0]
        have hib : commitGen b a = innerProduct a b := by
          simp [innerProduct, commitGen, smul_eq_mul]
        rw [hib]
        exact hrel.2
    | succ i =>
        simp only [Fin.cases_succ]
        exact (extF i.succ).2.2
  have hbatch := openedX4Batch_of_witnessFamily urs hk vk ps ch ξ hξinj 0
    (Fin.cases (motive := fun _ => Fin (2 ^ urs.k) → Fp) a fun i => (extF i.succ).1)
    (Fin.cases (motive := fun _ => Fp) pU fun i => (fsf i.succ).pU)
    (Fin.cases (motive := fun _ => Fp) pW fun i => (fsf i.succ).pW) hC hv
  simp only [Fin.cases_zero] at hbatch
  exact hbatch

open scoped ENNReal in
open Classical in
/-- `openedX4Rewind_of_x4Prob` at a given honest fork: the statement is the fork's
`openedCommitment` at its declared components, and the fork's clean accepting transcript supplies
the honest-slot event. -/
noncomputable def openedX4Rewind_of_x4Prob_forked [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) {b : Fin (2 ^ urs.k) → Fp}
    {z blind : Fp} (fsCur : ForkedTranscript urs hk vk ps ch b z blind)
    (hcur : ∃ t : IpaTreeV Fp G urs.k,
      IpaAcceptV urs.g b fsCur.openedCommitment (multiopenValue vk ps ch) t)
    (hprob4 : ((deployedX4PairCount vk ps ch : ℝ≥0∞)) / Fintype.card Fp
      < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
          (OpenedX4Accept urs hk vk ps ch b))) :
    OpenedRewindForRelation urs fsCur.openedCommitment b (multiopenValue vk ps ch)
      (x4BatchCommitments urs hk vk ps ch) (x4BatchEvals vk ps ch) fsCur.pU fsCur.pW :=
  openedX4Rewind_of_x4Prob urs hk vk ps ch fsCur.openedCommitment fsCur.pU fsCur.pW rfl
    (by obtain ⟨t, ht⟩ := hcur; exact ⟨honestX4Run ps ch, z, blind, fsCur, t, ht⟩) hprob4

-- The `deployedSetQueries`-shaped index types make the power-sum defeq checks heavy under the
-- v4.30.0 toolchain; the budget below matches the other heavy proofs in this file.
set_option maxHeartbeats 1000000 in
/-- At the deployed instantiation with the honest batching challenge in the current slot, the
batch's own current-slot equations already open the fork's statement: the power sums collapse to
`deployedCommitment`/`multiopenValue` at `ch.x4`
(`deployedCommitment_x4_batch`/`multiopenValue_x4_batch`), so the current triple `(a₀, pU, pW)` is
an `IpaRelation` witness for the opened commitment. The pinned capstone derives its opening from
this rather than assuming it. -/
theorem OpenedBatchOpenings.ipaRelation_of_x4Current [DecidableEq G] [Inhabited G] {shape : Shape}
    {urs : URS G} {hk : shape.k = urs.k} {vk : VerifyingKey shape Fp G}
    {ps : ProofString shape Fp G} {ch : Challenges shape.k Fp} {b : Fin (2 ^ urs.k) → Fp}
    {a₀ : Fin (2 ^ urs.k) → Fp} {pU pW : Fp}
    (hb : OpenedBatchOpenings urs b (x4BatchCommitments urs hk vk ps ch)
      (x4BatchEvals vk ps ch) a₀ pU pW)
    (hξcur : hb.batchChallenge hb.current = ch.x4) :
    IpaRelation urs (deployedCommitment urs hk vk ps ch - pU • urs.u - pW • urs.w) b
      (multiopenValue vk ps ch) a₀ := by
  constructor
  · have hc := hb.commitment hb.current
    rw [hb.current_eq, hb.currentU_eq, hb.currentW_eq, hξcur] at hc
    have hd : (∑ j : Fin (deployedX4PairCount vk ps ch + 1),
        ch.x4 ^ (j : ℕ) • x4BatchCommitments urs hk vk ps ch j)
        = deployedCommitment urs hk vk ps ch :=
      (deployedCommitment_x4_batch urs hk vk ps ch ch.x4).symm
    rw [hd] at hc
    rw [← hc]
    abel
  · have hv := hb.value hb.current
    rw [hb.current_eq, hξcur] at hv
    have hd : (∑ j : Fin (deployedX4PairCount vk ps ch + 1),
        ch.x4 ^ (j : ℕ) • x4BatchEvals vk ps ch j) = multiopenValue vk ps ch :=
      (multiopenValue_x4_batch vk ps ch ch.x4).symm
    rw [hd] at hv
    have hib : innerProduct a₀ b = commitGen b a₀ := by
      simp [innerProduct, commitGen, smul_eq_mul]
    rw [hib]
    exact hv

/-! ## The terminal constraint endpoints -/

open Polynomial in
/-- The SNARK relation with the circuit side fed by columns decoded from the opened batch family
containing the extracted witness — the opened counterpart of `SnarkRelationWithDecodedColumns`, the
declared components carried through. -/
structure SnarkRelationWithOpenedColumns (urs : URS G) (P : G) (b : Fin (2 ^ urs.k) → Fp) (v : Fp)
    {numColumns numAdvice numInstance : ℕ}
    (columnCommitments : Fin numColumns → G) (columnEvals : Fin numColumns → Fp)
    (adviceIndex : Fin numAdvice → Fin numColumns) (instanceIndex : Fin numInstance → Fin numColumns)
    (fixedCols : ℕ → Polynomial Fp)
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ)
    (pU pW : Fp)
    (a : Fin (2 ^ urs.k) → Fp) (cols : Fin numColumns → Polynomial Fp) where
  opens : IpaRelation urs P b v a
  batchOpenings : OpenedBatchOpenings urs b columnCommitments columnEvals a pU pW
  decodedColumns : OpenedColumnDecode batchOpenings
  polynomial : ∀ i, cols i = coeffsToPoly (decodedColumns.coeffs i)
  satisfiesCircuit :
    circuitSatViaGates fixedCols (selectedPolysDecode (k := urs.k) cols adviceIndex)
      (selectedPolysDecode (k := urs.k) cols instanceIndex) y gates hpoly deg a

open Polynomial in
/-- Turn a final opened relation plus its batch family into the opened decoded-column SNARK
relation. `hquot`/`hgood` are stated for the canonical decode `openedDecodedCols hbatch` — the
family this proof constructs — with the plain chain's scoping (`Soundness.Multiopen.Decode`, the
scope section). -/
theorem opened_constraint_of_relation_and_batch {urs : URS G} {P : G}
    {b : Fin (2 ^ urs.k) → Fp} {v : Fp}
    {numColumns numAdvice numInstance : ℕ}
    (columnCommitments : Fin numColumns → G) (columnEvals : Fin numColumns → Fp)
    (adviceIndex : Fin numAdvice → Fin numColumns) (instanceIndex : Fin numInstance → Fin numColumns)
    (fixedCols : ℕ → Polynomial Fp)
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ) (x : Fp)
    {pU pW : Fp} {a : Fin (2 ^ urs.k) → Fp}
    (hrel : IpaRelation urs P b v a)
    (hbatch : OpenedBatchOpenings urs b columnCommitments columnEvals a pU pW)
    (hquot : quotientCheck
      (combineGates fixedCols (selectedPolys (openedDecodedCols hbatch) adviceIndex)
        (selectedPolys (openedDecodedCols hbatch) instanceIndex) y gates) hpoly deg x)
    (hgood : combineGates fixedCols (selectedPolys (openedDecodedCols hbatch) adviceIndex)
        (selectedPolys (openedDecodedCols hbatch) instanceIndex) y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols (selectedPolys (openedDecodedCols hbatch) adviceIndex)
        (selectedPolys (openedDecodedCols hbatch) instanceIndex) y gates
          - hpoly * (X ^ deg - 1)).eval x ≠ 0)
    {S : Prop}
    (hencodes : ∀ a cols,
      SnarkRelationWithOpenedColumns urs P b v columnCommitments columnEvals adviceIndex
        instanceIndex fixedCols y gates hpoly deg pU pW a cols → S) :
    S := by
  have hsat : circuitSatViaGates fixedCols
      (selectedPolysDecode (k := urs.k) (openedDecodedCols hbatch) adviceIndex)
      (selectedPolysDecode (k := urs.k) (openedDecodedCols hbatch) instanceIndex)
      y gates hpoly deg a :=
    circuitSatViaGates_of_check fixedCols
      (selectedPolysDecode (k := urs.k) (openedDecodedCols hbatch) adviceIndex)
      (selectedPolysDecode (k := urs.k) (openedDecodedCols hbatch) instanceIndex)
      y gates hpoly deg a x hquot hgood
  exact hencodes a (openedDecodedCols hbatch)
    { opens := hrel
      batchOpenings := hbatch
      decodedColumns := openedColumnDecode hbatch
      polynomial := fun i => rfl
      satisfiesCircuit := hsat }

open Polynomial in
/-- Lift an opening-or-relation terminal capstone to the opened decoded-column constraint endpoint,
the batch family supplied by `OpenedRewindForRelation` — the opened counterpart of
`decoded_constraint_of_opening_or_relation`, with the same conditional interface and `hquot`/`hgood`
scoping. Reduction-shaped: quantifying `hquot ∧ hgood` over every opening is jointly unsatisfiable
once the commitment kernel is nontrivial (see the scope section of `Soundness.Multiopen.Decode`);
the live capstones pin the witness instead — the fork's extraction
(`orchard_verifier_vesta_decoded_constraint_of_forked_x4`) or a designated batch with the
mismatch-to-DLR split (`orchard_verifier_vesta_forking_constraint_deployed_x4`). -/
theorem opened_constraint_of_opening_or_relation {urs : URS G} {P : G}
    {b : Fin (2 ^ urs.k) → Fp} {v : Fp}
    {numColumns numAdvice numInstance : ℕ}
    (columnCommitments : Fin numColumns → G) (columnEvals : Fin numColumns → Fp)
    (adviceIndex : Fin numAdvice → Fin numColumns) (instanceIndex : Fin numInstance → Fin numColumns)
    (fixedCols : ℕ → Polynomial Fp)
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ) (x : Fp)
    {pU pW : Fp}
    (hopening : (∃ a, IpaRelation urs P b v a) ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w)
    (hbatch : OpenedRewindForRelation urs P b v columnCommitments columnEvals pU pW)
    (hquot : ∀ a (hrel : IpaRelation urs P b v a),
      quotientCheck
        (combineGates fixedCols (selectedPolys (openedDecodedCols (hbatch a hrel)) adviceIndex)
          (selectedPolys (openedDecodedCols (hbatch a hrel)) instanceIndex) y gates) hpoly deg x)
    (hgood : ∀ a (hrel : IpaRelation urs P b v a),
      combineGates fixedCols (selectedPolys (openedDecodedCols (hbatch a hrel)) adviceIndex)
          (selectedPolys (openedDecodedCols (hbatch a hrel)) instanceIndex) y gates
        ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols (selectedPolys (openedDecodedCols (hbatch a hrel)) adviceIndex)
          (selectedPolys (openedDecodedCols (hbatch a hrel)) instanceIndex) y gates
        - hpoly * (X ^ deg - 1)).eval x ≠ 0)
    {S : Prop}
    (hencodes : ∀ a cols,
      SnarkRelationWithOpenedColumns urs P b v columnCommitments columnEvals adviceIndex
        instanceIndex fixedCols y gates hpoly deg pU pW a cols → S) :
    S ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  rcases hopening with ⟨a, hrel⟩ | hrel
  · exact Or.inl (opened_constraint_of_relation_and_batch columnCommitments columnEvals adviceIndex
      instanceIndex fixedCols y gates hpoly deg x hrel (hbatch a hrel) (hquot a hrel) (hgood a hrel)
      hencodes)
  · exact Or.inr hrel


/-! ## The opened `x₁` layer: member binding through the declared components -/

/-- The scalar-component Vandermonde decode across `x₁` rewinds — the companion of `x1DecodeCols`
for the declared `U`/`W` components. -/
noncomputable def x1DecodeComp {n : ℕ} (z : Fin n → Fp) (c : Fin n → Fp) : Fin n → Fp :=
  fun j => ∑ r, (Matrix.vandermonde z)⁻¹ j r • c r

/-- **The extracted witness bound to the member commitments, through the opened chain.** Augmented
mirror of `deployed_witness_member_binding`: each `x₁`-rewound run's aggregate witness arrives with
declared `U`/`W` components (its own opened `x₄` decode), so the member decode runs componentwise —
the same inverse matrix decodes the witness vectors and both component families. The conclusions:
each decoded member triple opens its member commitment in augmented form; the honest opened `x₄`
decode triple at set `i`'s batch position is the `ch.x1`-power combination of the decoded member
triples; and every run's value equation transports to the decoded members. Per-member claimed
evaluations at the original rotated points and the gate/`x`→`x₃` transport remain the
fingerprint-delegated half (`Soundness.Multiopen.Decode`, the deployed-status section). -/
theorem opened_witness_member_binding [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {b : Fin (2 ^ urs.k) → Fp} {a : Fin (2 ^ urs.k) → Fp} {pU pW : Fp}
    (pbatch : OpenedBatchOpenings urs b (x4BatchCommitments urs hk vk ps ch)
      (x4BatchEvals vk ps ch) a pU pW)
    (i : ℕ) (hi : i < deployedX4PairCount vk ps ch)
    (χ : Fin (deployedSetQueries vk ps ch i).length → Fp) (hχ : Function.Injective χ)
    (cur : Fin (deployedSetQueries vk ps ch i).length) (hcur : χ cur = ch.x1)
    (runs : Fin (deployedSetQueries vk ps ch i).length → X1Run shape G)
    (w : Fin (deployedSetQueries vk ps ch i).length → (Fin (2 ^ urs.k) → Fp))
    (wU wW : Fin (deployedSetQueries vk ps ch i).length → Fp)
    (bv : Fin (deployedSetQueries vk ps ch i).length → (Fin (2 ^ urs.k) → Fp))
    (uv : Fin (deployedSetQueries vk ps ch i).length → Fp)
    (hwC : ∀ r, commit urs (w r) + wU r • urs.u + wW r • urs.w
      = ((deployedX4Qs vk ((runs r).spliced ps) ((runs r).challenges ch (χ r))).getD i
            (Msm.zero shape.k Fp G)).eval ⟨shape.k, hk ▸ urs.g, urs.w, urs.u⟩)
    (hwu : ∀ r, commitGen (bv r) (w r) = uv r)
    (hwcur : w cur = (openedColumnDecode pbatch).coeffs
      ⟨deployedX4PairCount vk ps ch - 1 - i, by omega⟩)
    (hwUcur : wU cur = (openedColumnDecode pbatch).uComp
      ⟨deployedX4PairCount vk ps ch - 1 - i, by omega⟩)
    (hwWcur : wW cur = (openedColumnDecode pbatch).wComp
      ⟨deployedX4PairCount vk ps ch - 1 - i, by omega⟩) :
    (∀ m : Fin (deployedSetQueries vk ps ch i).length,
      commit urs (x1DecodeCols χ w m) + x1DecodeComp χ wU m • urs.u
          + x1DecodeComp χ wW m • urs.w
        = ((deployedSetQueries vk ps ch i).getD (m : ℕ) (.point 0, [])).1.eval
            ⟨shape.k, hk ▸ urs.g, urs.w, urs.u⟩)
    ∧ ((openedColumnDecode pbatch).coeffs ⟨deployedX4PairCount vk ps ch - 1 - i, by omega⟩
        = ∑ m : Fin (deployedSetQueries vk ps ch i).length,
            ch.x1 ^ (m : ℕ) • x1DecodeCols χ w m)
    ∧ ((openedColumnDecode pbatch).uComp ⟨deployedX4PairCount vk ps ch - 1 - i, by omega⟩
        = ∑ m : Fin (deployedSetQueries vk ps ch i).length,
            ch.x1 ^ (m : ℕ) • x1DecodeComp χ wU m)
    ∧ ((openedColumnDecode pbatch).wComp ⟨deployedX4PairCount vk ps ch - 1 - i, by omega⟩
        = ∑ m : Fin (deployedSetQueries vk ps ch i).length,
            ch.x1 ^ (m : ℕ) • x1DecodeComp χ wW m)
    ∧ (∀ r, ∑ m : Fin (deployedSetQueries vk ps ch i).length,
        χ r ^ (m : ℕ) • commitGen (bv r) (x1DecodeCols χ w m) = uv r) := by
  have hqs : i < (deployedX4Qs vk ps ch).length := by
    have hle : deployedX4PairCount vk ps ch ≤ (deployedX4Qs vk ps ch).length := by
      simp only [deployedX4PairCount, deployedX4Pairs, List.length_zip]
      exact min_le_left _ _
    omega
  have haC : ∀ r, commit urs (w r) + wU r • urs.u + wW r • urs.w
      = ∑ m : Fin (deployedSetQueries vk ps ch i).length, χ r ^ (m : ℕ)
          • ((deployedSetQueries vk ps ch i).getD (m : ℕ) (.point 0, [])).1.eval
              ⟨shape.k, hk ▸ urs.g, urs.w, urs.u⟩ := by
    intro r
    rw [hwC r,
      x1Run_x4Qs_getD_eval (hk ▸ urs.g) urs.w urs.u vk ps ch (runs r) (χ r) hqs,
      Fin.sum_univ_eq_sum_range
        (fun m => χ r ^ m • ((deployedSetQueries vk ps ch i).getD m (.point 0, [])).1.eval
          ⟨shape.k, hk ▸ urs.g, urs.w, urs.u⟩)]
  refine ⟨fun m => ?_, ?_, ?_, ?_, fun r => x1DecodeCols_value χ hχ w bv uv hwu r⟩
  · -- The three linear pieces collapse to one inverse-matrix combination of the per-run augmented
    -- equations, which the module-valued decode inverts.
    have hlin : commit urs (x1DecodeCols χ w m) + x1DecodeComp χ wU m • urs.u
        + x1DecodeComp χ wW m • urs.w
        = ∑ r, (Matrix.vandermonde χ)⁻¹ m r •
            (commit urs (w r) + wU r • urs.u + wW r • urs.w) := by
      simp only [x1DecodeCols, x1DecodeComp]
      rw [commit_eq_commitGen, commitGen_sum, Finset.sum_smul, Finset.sum_smul,
        ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [commitGen_smul_left, smul_eq_mul, smul_eq_mul, mul_smul, mul_smul, smul_add, smul_add,
        commit_eq_commitGen]
    rw [hlin]
    exact vandermonde_decode_map _ (vandermonde_inv_left χ hχ) haC m
  · rw [← hwcur, ← hcur]
    exact x1DecodeCols_reconstruct χ hχ w cur
  · rw [← hwUcur, ← hcur]
    simp only [x1DecodeComp]
    exact (vandermonde_reconstruct_map wU _ (vandermonde_inv_right χ hχ) cur).symm
  · rw [← hwWcur, ← hcur]
    simp only [x1DecodeComp]
    exact (vandermonde_reconstruct_map wW _ (vandermonde_inv_right χ hχ) cur).symm


/-- The opened `x₁` accept event at compression challenge `χv`: some `x₁`-rewound run carries a
full opened `x₄` batch over its own deployed aggregates. Each run's aggregate witnesses are that
run's own `x₄`-level decode — the stacked floors, per run, made explicit; the honest run witnesses
the event at `ch.x1` through the honest batch. -/
def OpenedX1Accept [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (χv : Fp) : Prop :=
  ∃ (run : X1Run shape G) (bR aR : Fin (2 ^ urs.k) → Fp) (pUR pWR : Fp),
    DeployedAccepts urs hk vk (run.spliced ps) (run.challenges ch χv) ∧
    Nonempty (OpenedBatchOpenings urs bR
      (x4BatchCommitments urs hk vk (run.spliced ps) (run.challenges ch χv))
      (x4BatchEvals vk (run.spliced ps) (run.challenges ch χv)) aR pUR pWR)

/-- Feed the opened `x₁` accept event from a genuine deployed accept for a rewound run — the `x₁`
analogue of `openedX4Accept_of_deployedAccepts`. The redrawn compression challenge `χv` is a
`reprogramX1` reprogramming event on the spliced string (`Soundness.Forking.Rewind`); the deployed
verifier accepting on that reprogrammed transcript is what the `x₁` forking measure counts, and its
batch opening is the extraction witness the member decode consumes. -/
theorem openedX1Accept_of_deployedAccepts [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) (run : X1Run shape G) (χv : Fp)
    {bR aR : Fin (2 ^ urs.k) → Fp} {pUR pWR : Fp}
    (hacc : DeployedAccepts urs hk vk (run.spliced ps) (run.challenges ch χv))
    (hopen : OpenedBatchOpenings urs bR
      (x4BatchCommitments urs hk vk (run.spliced ps) (run.challenges ch χv))
      (x4BatchEvals vk (run.spliced ps) (run.challenges ch χv)) aR pUR pWR) :
    OpenedX1Accept urs hk vk ps ch χv :=
  ⟨run, bR, aR, pUR, pWR, hacc, ⟨hopen⟩⟩

-- The member-index types carry `deployedSetQueries`-shaped lengths, so defeq checks are heavy;
-- the budget below covers them (as on the producer).
set_option maxHeartbeats 1000000 in
/-- The decoded member triples for point set `i`: each opens its member commitment — an actual
queried column commitment — in augmented form, and the honest opened `x₄`-decode triple at set
`i`'s batch position is the `ch.x1`-power combination of the decoded triples. Produced from the
`x₁` accept measure by `openedMemberDecode_of_x1Prob`; consumed by the member-column constraint
endpoint. -/
structure OpenedMemberDecode [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {b : Fin (2 ^ urs.k) → Fp} {a : Fin (2 ^ urs.k) → Fp} {pU pW : Fp}
    (pbatch : OpenedBatchOpenings urs b (x4BatchCommitments urs hk vk ps ch)
      (x4BatchEvals vk ps ch) a pU pW)
    (i : ℕ) (hi : i < deployedX4PairCount vk ps ch) where
  cols : Fin (deployedSetQueries vk ps ch i).length → (Fin (2 ^ urs.k) → Fp)
  uComp : Fin (deployedSetQueries vk ps ch i).length → Fp
  wComp : Fin (deployedSetQueries vk ps ch i).length → Fp
  commitment : ∀ m : Fin (deployedSetQueries vk ps ch i).length,
    commit urs (cols m) + uComp m • urs.u + wComp m • urs.w
      = ((deployedSetQueries vk ps ch i).getD (m : ℕ) (.point 0, [])).1.eval
          ⟨shape.k, hk ▸ urs.g, urs.w, urs.u⟩
  reconstruct :
    (openedColumnDecode pbatch).coeffs ⟨deployedX4PairCount vk ps ch - 1 - i, by omega⟩
      = ∑ m : Fin (deployedSetQueries vk ps ch i).length, ch.x1 ^ (m : ℕ) • cols m
  reconstructU :
    (openedColumnDecode pbatch).uComp ⟨deployedX4PairCount vk ps ch - 1 - i, by omega⟩
      = ∑ m : Fin (deployedSetQueries vk ps ch i).length, ch.x1 ^ (m : ℕ) • uComp m
  reconstructW :
    (openedColumnDecode pbatch).wComp ⟨deployedX4PairCount vk ps ch - 1 - i, by omega⟩
      = ∑ m : Fin (deployedSetQueries vk ps ch i).length, ch.x1 ^ (m : ℕ) • wComp m

open scoped ENNReal in
open Classical in
-- The member-index types carry `deployedSetQueries`-shaped lengths, so defeq checks are heavy;
-- the budget below covers them.
set_option maxHeartbeats 1000000 in
/-- **The `x₁` forking floor through the opened chain.** If the opened `x₁` accept measure beats
`(len − 1) / p` for point set `i`'s member count, the member-binding output exists — decoded member
triples opening the actual queried column commitments in augmented form, with the honest opened
`x₄`-decode triple at set `i`'s batch position reconstructed as their `ch.x1`-power combination —
produced, not assumed: each rewound run's aggregate witness is its own opened `x₄` decode, and the
honest slot is rebuilt from the honest batch. The measure hypothesis carries the same random-oracle
uniformity axiom as every `hprob` (`Soundness.Forking.Oracle`); the runs are the `reprogramX1`
reprogramming events (`Soundness.Forking.Rewind`) on the spliced strings. -/
noncomputable def openedMemberDecode_of_x1Prob [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {b : Fin (2 ^ urs.k) → Fp} {a : Fin (2 ^ urs.k) → Fp} {pU pW : Fp}
    (pbatch : OpenedBatchOpenings urs b (x4BatchCommitments urs hk vk ps ch)
      (x4BatchEvals vk ps ch) a pU pW)
    (i : ℕ) (hi : i < deployedX4PairCount vk ps ch)
    (hlen : 0 < (deployedSetQueries vk ps ch i).length)
    (hprob1 : (((deployedSetQueries vk ps ch i).length - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
      < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
          (OpenedX1Accept urs hk vk ps ch)))
    (hacc0 : DeployedAccepts urs hk vk ps ch) :
    OpenedMemberDecode urs hk vk ps ch pbatch i hi := by
  classical
  have hcast : (deployedSetQueries vk ps ch i).length - 1 + 1
      = (deployedSetQueries vk ps ch i).length := Nat.succ_pred_eq_of_pos hlen
  -- The honest slot is a genuine deployed accept at `ch.x1`: splicing the honest run is the identity
  -- (`honestX1Run_spliced`/`_challenges`, both `rfl`), so `hacc0` and `pbatch` land at it definitionally.
  have hx₁ : OpenedX1Accept urs hk vk ps ch ch.x1 :=
    ⟨honestX1Run ps ch, b, a, pU, pW, hacc0, ⟨pbatch⟩⟩
  have hex := exists_injective_accepting_of_measure
    (acc := OpenedX1Accept urs hk vk ps ch) (x₀ := ch.x1) hx₁ hprob1
  set ξ₀ := Classical.choose hex with hξ₀def
  have hspec := Classical.choose_spec hex
  have hξinj₀ : Function.Injective ξ₀ := hspec.1
  have hξzero₀ : ξ₀ 0 = ch.x1 := hspec.2.1
  have hacc₀ : ∀ r, OpenedX1Accept urs hk vk ps ch (ξ₀ r) := hspec.2.2
  -- Recast the rewound family to the member index type and pin the honest slot.
  set χ : Fin (deployedSetQueries vk ps ch i).length → Fp :=
    fun m => ξ₀ (Fin.cast hcast.symm m) with hχdef
  have hχinj : Function.Injective χ := by
    intro m m' h
    have h2 : Fin.cast hcast.symm m = Fin.cast hcast.symm m' := hξinj₀ h
    have h3 := congrArg Fin.val h2
    exact Fin.ext h3
  have hcurv : χ ⟨0, hlen⟩ = ch.x1 := by
    have hzero : Fin.cast hcast.symm
        (⟨0, hlen⟩ : Fin (deployedSetQueries vk ps ch i).length)
        = (0 : Fin ((deployedSetQueries vk ps ch i).length - 1 + 1)) := by
      apply Fin.ext
      simp
    rw [hχdef]
    show ξ₀ (Fin.cast hcast.symm ⟨0, hlen⟩) = ch.x1
    rw [hzero, hξzero₀]
  have hacc : ∀ m : Fin (deployedSetQueries vk ps ch i).length,
      OpenedX1Accept urs hk vk ps ch (χ m) := fun m => hacc₀ _
  -- Each rewound accept is a genuine deployed accept (`hdaccF`, carried — it is what the `x₁` measure
  -- counts) together with its batch opening (`hpbne`, the extraction witness the decode consumes).
  choose runsF bF aF pUF pWF hdaccF hpbne using hacc
  -- Per-run aggregate triples: each run's own opened x₄ decode, at set i's batch position.
  have hidx : ∀ m : Fin (deployedSetQueries vk ps ch i).length,
      deployedX4PairCount vk ps ch - 1 - i
        < deployedX4PairCount vk ((runsF m).spliced ps) ((runsF m).challenges ch (χ m)) + 1 := by
    intro m
    rw [x1Run_pairCount vk ps ch (runsF m) (χ m)]
    omega
  -- The x₁ family fed to the member binding: choice data off the honest slot, the honest batch at it.
  set cur : Fin (deployedSetQueries vk ps ch i).length := ⟨0, hlen⟩ with hcurdef
  set runs' : Fin (deployedSetQueries vk ps ch i).length → X1Run shape G :=
    Function.update runsF cur (honestX1Run ps ch) with hrunsdef
  set w' : Fin (deployedSetQueries vk ps ch i).length → (Fin (2 ^ urs.k) → Fp) :=
    Function.update
      (fun m => (openedColumnDecode (hpbne m).some).coeffs
        ⟨deployedX4PairCount vk ps ch - 1 - i, hidx m⟩)
      cur
      ((openedColumnDecode pbatch).coeffs
        ⟨deployedX4PairCount vk ps ch - 1 - i, by omega⟩) with hwdef
  set wU' : Fin (deployedSetQueries vk ps ch i).length → Fp :=
    Function.update
      (fun m => (openedColumnDecode (hpbne m).some).uComp
        ⟨deployedX4PairCount vk ps ch - 1 - i, hidx m⟩)
      cur
      ((openedColumnDecode pbatch).uComp
        ⟨deployedX4PairCount vk ps ch - 1 - i, by omega⟩) with hwUdef
  set wW' : Fin (deployedSetQueries vk ps ch i).length → Fp :=
    Function.update
      (fun m => (openedColumnDecode (hpbne m).some).wComp
        ⟨deployedX4PairCount vk ps ch - 1 - i, hidx m⟩)
      cur
      ((openedColumnDecode pbatch).wComp
        ⟨deployedX4PairCount vk ps ch - 1 - i, by omega⟩) with hwWdef
  have hIdxEq : deployedX4PairCount vk ps ch - 1 - (deployedX4PairCount vk ps ch - 1 - i)
      = i := by omega
  have hwC : ∀ r, commit urs (w' r) + wU' r • urs.u + wW' r • urs.w
      = ((deployedX4Qs vk ((runs' r).spliced ps) ((runs' r).challenges ch (χ r))).getD i
            (Msm.zero shape.k Fp G)).eval ⟨shape.k, hk ▸ urs.g, urs.w, urs.u⟩ := by
    intro r
    rcases eq_or_ne r cur with hr | hr
    · subst hr
      rw [hwdef, hwUdef, hwWdef, hrunsdef]
      simp only [Function.update_self]
      have hj : ((⟨deployedX4PairCount vk ps ch - 1 - i, by omega⟩ :
          Fin (deployedX4PairCount vk ps ch + 1)) : ℕ) < deployedX4PairCount vk ps ch := by
        show deployedX4PairCount vk ps ch - 1 - i < deployedX4PairCount vk ps ch
        omega
      rw [(openedColumnDecode pbatch).commitment
          ⟨deployedX4PairCount vk ps ch - 1 - i, by omega⟩,
        x4BatchCommitments_getD urs hk vk ps ch hj, hIdxEq, hcurv]
      rfl
    · rw [hwdef, hwUdef, hwWdef, hrunsdef]
      simp only [Function.update_of_ne hr]
      have hpc := x1Run_pairCount vk ps ch (runsF r) (χ r)
      have hjR : ((⟨deployedX4PairCount vk ps ch - 1 - i, hidx r⟩ :
          Fin (deployedX4PairCount vk ((runsF r).spliced ps)
            ((runsF r).challenges ch (χ r)) + 1)) : ℕ)
          < deployedX4PairCount vk ((runsF r).spliced ps) ((runsF r).challenges ch (χ r)) := by
        show deployedX4PairCount vk ps ch - 1 - i
          < deployedX4PairCount vk ((runsF r).spliced ps) ((runsF r).challenges ch (χ r))
        omega
      rw [(openedColumnDecode (hpbne r).some).commitment
          ⟨deployedX4PairCount vk ps ch - 1 - i, hidx r⟩,
        x4BatchCommitments_getD urs hk vk ((runsF r).spliced ps)
          ((runsF r).challenges ch (χ r)) hjR]
      have hIdxR : deployedX4PairCount vk ((runsF r).spliced ps) ((runsF r).challenges ch (χ r))
          - 1 - (deployedX4PairCount vk ps ch - 1 - i) = i := by
        omega
      rw [hIdxR]
  have hmb := opened_witness_member_binding urs hk vk ps ch pbatch i hi χ hχinj cur hcurv
    runs' w' wU' wW' (fun _ _ => 0) (fun r => commitGen (fun _ => (0 : Fp)) (w' r))
    hwC (fun r => rfl)
    (by rw [hwdef]; exact Function.update_self ..)
    (by rw [hwUdef]; exact Function.update_self ..)
    (by rw [hwWdef]; exact Function.update_self ..)
  exact
    { cols := x1DecodeCols χ w'
      uComp := x1DecodeComp χ wU'
      wComp := x1DecodeComp χ wW'
      commitment := hmb.1
      reconstruct := hmb.2.1
      reconstructU := hmb.2.2.1
      reconstructW := hmb.2.2.2.1 }


/-! ## The member-column constraint endpoint -/

open Polynomial in
/-- **The halo2-faithful gate feed for one column family.** halo2 evaluates a gate on the claimed
evaluation `advice_evals[query_index]` of query `j = (column, rotation)`, opened at
`rotate_omega x rot = ω^rot·x` (`plonk/verifier.rs`). Feeding the gate the decoded column composed
with its layout rotation — `col_j ∘ (ω^rot_j · X)` — makes its value at the gate point `x` equal
`col_j (ω^rot_j·x)`, which the multiopen binds to `advice_evals[query_index]`
(`Soundness.Multiopen.RPoly.col_eval_node_eq_claimed`). The rotation `rot_j` is read from the
verifying key's query layout (`(column, rotation)` list), so it is not a free choice. -/
noncomputable def rotatedFeed {n : ℕ} (omega : Fp) (layout : List (ℕ × ℤ))
    (col : Fin n → Polynomial Fp) : ℕ → Polynomial Fp :=
  finFn fun j : Fin n =>
    (col j).comp (Polynomial.C (omega ^ (layout.getD (j : ℕ) (0, 0)).2) * Polynomial.X)

open Polynomial in
set_option maxHeartbeats 1000000 in
/-- The SNARK relation with the circuit side fed by decoded *member* columns — the actual queried
column commitments' openings, selected per advice/instance index from their point sets. The witness
chain is carried in full: `a` opens the statement, the opened `x₄` batch contains it, and each
in-range batch position's decode triple is the `ch.x1`-power combination of its set's member
triples, each opening its member commitment in augmented form. The gate check runs on the member
polynomials. -/
structure SnarkRelationWithMemberColumns [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (P : G) (b : Fin (2 ^ urs.k) → Fp) (v : Fp) (p : Fin shape.numProofs)
    {numAdvice numInstance : ℕ}
    (adviceSet : Fin numAdvice → ℕ)
    (hadviceSet : ∀ j, adviceSet j < deployedX4PairCount vk ps ch)
    (adviceMem : ∀ j : Fin numAdvice, Fin (deployedSetQueries vk ps ch (adviceSet j)).length)
    (instanceSet : Fin numInstance → ℕ)
    (hinstanceSet : ∀ j, instanceSet j < deployedX4PairCount vk ps ch)
    (instanceMem : ∀ j : Fin numInstance,
      Fin (deployedSetQueries vk ps ch (instanceSet j)).length)
    (fixedCols : ℕ → Polynomial Fp) (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp)
    (hpoly : Polynomial Fp) (deg : ℕ) (pU pW : Fp)
    (a : Fin (2 ^ urs.k) → Fp) where
  opens : IpaRelation urs P b v a
  batchOpenings : OpenedBatchOpenings urs b (x4BatchCommitments urs hk vk ps ch)
    (x4BatchEvals vk ps ch) a pU pW
  /-- **Advice selection is forced by the verifying key's query layout.** The member `(adviceSet j,
  adviceMem j)` fed to advice query `j` is exactly the commitment the layout routes query `j`'s
  advice column to (identity via `deployedSetCommIds`, halo2's `CommitmentData` identity), not a
  free choice — so the gate reads the prover's actual advice column, not an arbitrary member. -/
  adviceLayout : ∀ j : Fin numAdvice,
    (deployedSetCommIds vk ps ch (adviceSet j)).getD (adviceMem j : ℕ) CommitmentId.vanishingH
      = CommitmentId.adviceCol p (vk.adviceQueryLayout.getD (j : ℕ) (0, 0)).1
  /-- Instance selection is likewise forced by the layout. -/
  instanceLayout : ∀ j : Fin numInstance,
    (deployedSetCommIds vk ps ch (instanceSet j)).getD (instanceMem j : ℕ) CommitmentId.vanishingH
      = CommitmentId.instanceCol p (vk.instanceQueryLayout.getD (j : ℕ) (0, 0)).1
  memberDecode : ∀ i (hi : i < deployedX4PairCount vk ps ch),
    OpenedMemberDecode urs hk vk ps ch batchOpenings i hi
  /-- **The quotient is the committed vanishing-`h` polynomial, not a free choice.** `hpoly` is the
  decode of the member whose retained `CommitmentId` is `vanishingH` — the `Σᵢ hᵢ·(xⁿ)ⁱ` fold the
  verifier queries and opens (halo2 `vanishing/verifier.rs`, `constructIntermediateSets` identity),
  so the gate identity `gate = hpoly·(Xⁿ−1)` is against the *committed* quotient, not an arbitrary
  polynomial the prover picks after seeing the gate. -/
  quotCommitted : ∃ (hSet : ℕ) (hhSet : hSet < deployedX4PairCount vk ps ch)
      (hMem : Fin (deployedSetQueries vk ps ch hSet).length),
    hpoly = coeffsToPoly ((memberDecode hSet hhSet).cols hMem) ∧
    (deployedSetCommIds vk ps ch hSet).getD (hMem : ℕ) CommitmentId.randomPoly = CommitmentId.vanishingH
  satisfiesCircuit :
    circuitSatViaGates fixedCols
      (fun _ => rotatedFeed vk.omega vk.adviceQueryLayout
        (fun j : Fin numAdvice =>
          coeffsToPoly ((memberDecode (adviceSet j) (hadviceSet j)).cols (adviceMem j))))
      (fun _ => rotatedFeed vk.omega vk.instanceQueryLayout
        (fun j : Fin numInstance =>
          coeffsToPoly ((memberDecode (instanceSet j) (hinstanceSet j)).cols (instanceMem j))))
      y gates hpoly deg a

open Polynomial in
set_option maxHeartbeats 1000000 in
/-- Turn a final opened relation, its batch family, and per-set member decodes into the
member-column SNARK relation: the gate check is stated once, on the member polynomials of the
supplied decodes — the satisfiable pinned shape. Its truth for the deployed verifier — the claimed
evaluations at the rotated points and the gate/`x`→`x₃` transport — is the fingerprint-delegated
half (`Soundness.Multiopen.Decode`, the deployed-status section). -/
theorem member_constraint_of_relation_and_batch [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {P : G} {b : Fin (2 ^ urs.k) → Fp} {v : Fp}
    {numAdvice numInstance : ℕ}
    (adviceSet : Fin numAdvice → ℕ)
    (hadviceSet : ∀ j, adviceSet j < deployedX4PairCount vk ps ch)
    (adviceMem : ∀ j : Fin numAdvice, Fin (deployedSetQueries vk ps ch (adviceSet j)).length)
    (instanceSet : Fin numInstance → ℕ)
    (hinstanceSet : ∀ j, instanceSet j < deployedX4PairCount vk ps ch)
    (instanceMem : ∀ j : Fin numInstance,
      Fin (deployedSetQueries vk ps ch (instanceSet j)).length)
    (fixedCols : ℕ → Polynomial Fp) (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp)
    (hpoly : Polynomial Fp) (deg : ℕ) (x : Fp)
    {pU pW : Fp} {a : Fin (2 ^ urs.k) → Fp}
    (hrel : IpaRelation urs P b v a)
    (pbatch : OpenedBatchOpenings urs b (x4BatchCommitments urs hk vk ps ch)
      (x4BatchEvals vk ps ch) a pU pW)
    (mdec : ∀ i (hi : i < deployedX4PairCount vk ps ch),
      OpenedMemberDecode urs hk vk ps ch pbatch i hi)
    (hquot : quotientCheck
      (combineGates fixedCols
        (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((mdec (adviceSet j) (hadviceSet j)).cols (adviceMem j))))
        (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((mdec (instanceSet j) (hinstanceSet j)).cols (instanceMem j))))
        y gates) hpoly deg x)
    (hgood :
      combineGates fixedCols
        (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((mdec (adviceSet j) (hadviceSet j)).cols (adviceMem j))))
        (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((mdec (instanceSet j) (hinstanceSet j)).cols (instanceMem j))))
        y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols
        (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((mdec (adviceSet j) (hadviceSet j)).cols (adviceMem j))))
        (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((mdec (instanceSet j) (hinstanceSet j)).cols (instanceMem j))))
        y gates - hpoly * (X ^ deg - 1)).eval x ≠ 0)
    (p : Fin shape.numProofs)
    (hadviceLayout : ∀ j : Fin numAdvice,
      (deployedSetCommIds vk ps ch (adviceSet j)).getD (adviceMem j : ℕ) CommitmentId.vanishingH
        = CommitmentId.adviceCol p (vk.adviceQueryLayout.getD (j : ℕ) (0, 0)).1)
    (hinstanceLayout : ∀ j : Fin numInstance,
      (deployedSetCommIds vk ps ch (instanceSet j)).getD (instanceMem j : ℕ) CommitmentId.vanishingH
        = CommitmentId.instanceCol p (vk.instanceQueryLayout.getD (j : ℕ) (0, 0)).1)
    (hquotCommitted : ∃ (hSet : ℕ) (hhSet : hSet < deployedX4PairCount vk ps ch)
        (hMem : Fin (deployedSetQueries vk ps ch hSet).length),
      hpoly = coeffsToPoly ((mdec hSet hhSet).cols hMem) ∧
      (deployedSetCommIds vk ps ch hSet).getD (hMem : ℕ) CommitmentId.randomPoly
        = CommitmentId.vanishingH)
    {S : Prop}
    (hencodes : ∀ a,
      SnarkRelationWithMemberColumns urs hk vk ps ch P b v p adviceSet hadviceSet adviceMem
        instanceSet hinstanceSet instanceMem fixedCols y gates hpoly deg pU pW a → S) :
    S := by
  have hsat := circuitSatViaGates_of_check fixedCols
    (fun _ => rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
      coeffsToPoly ((mdec (adviceSet j) (hadviceSet j)).cols (adviceMem j))))
    (fun _ => rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
      coeffsToPoly ((mdec (instanceSet j) (hinstanceSet j)).cols (instanceMem j))))
    y gates hpoly deg a x hquot hgood
  exact hencodes a
    { opens := hrel
      batchOpenings := pbatch
      memberDecode := mdec
      adviceLayout := hadviceLayout
      instanceLayout := hinstanceLayout
      quotCommitted := hquotCommitted
      satisfiesCircuit := hsat }


open Polynomial in
open scoped ENNReal in
open Classical in
set_option maxHeartbeats 1000000 in
/-- The member-column endpoint with the good challenge *derived*, not assumed: the fixed gate-check
point `x` and its `hgood` are replaced by an accept event `accX` whose uniform measure beats the
vanishing-check budget `max (deg numerator) (deg hpoly + deg) / p`; the good challenge is produced
at the pinned member decode by `exists_accepting_good_challenge_quotient`
(`Soundness.GoodChallenge`), so `hgood` is gone from this signature. The measure hypothesis carries
the random-oracle uniformity axiom (`Soundness.Forking.Oracle`). -/
theorem member_constraint_of_relation_and_batch_xgood [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {P : G} {b : Fin (2 ^ urs.k) → Fp} {v : Fp}
    {numAdvice numInstance : ℕ}
    (adviceSet : Fin numAdvice → ℕ)
    (hadviceSet : ∀ j, adviceSet j < deployedX4PairCount vk ps ch)
    (adviceMem : ∀ j : Fin numAdvice, Fin (deployedSetQueries vk ps ch (adviceSet j)).length)
    (instanceSet : Fin numInstance → ℕ)
    (hinstanceSet : ∀ j, instanceSet j < deployedX4PairCount vk ps ch)
    (instanceMem : ∀ j : Fin numInstance,
      Fin (deployedSetQueries vk ps ch (instanceSet j)).length)
    (fixedCols : ℕ → Polynomial Fp) (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp)
    (hpoly : Polynomial Fp) (deg : ℕ)
    (accX : Fp → Prop) [DecidablePred accX]
    {pU pW : Fp} {a : Fin (2 ^ urs.k) → Fp}
    (hrel : IpaRelation urs P b v a)
    (pbatch : OpenedBatchOpenings urs b (x4BatchCommitments urs hk vk ps ch)
      (x4BatchEvals vk ps ch) a pU pW)
    (mdec : ∀ i (hi : i < deployedX4PairCount vk ps ch),
      OpenedMemberDecode urs hk vk ps ch pbatch i hi)
    (hquot : ∀ xv, accX xv → quotientCheck
      (combineGates fixedCols
        (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((mdec (adviceSet j) (hadviceSet j)).cols (adviceMem j))))
        (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((mdec (instanceSet j) (hinstanceSet j)).cols (instanceMem j))))
        y gates) hpoly deg xv)
    (hprobX : ((max (combineGates fixedCols
        (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((mdec (adviceSet j) (hadviceSet j)).cols (adviceMem j))))
        (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((mdec (instanceSet j) (hinstanceSet j)).cols (instanceMem j))))
        y gates).natDegree (hpoly.natDegree + deg) : ℕ) : ℝ≥0∞)
        / (Fintype.card Fp : ℝ≥0∞)
      < uniformChallenge.toOuterMeasure (Finset.univ.filter accX))
    (p : Fin shape.numProofs)
    (hadviceLayout : ∀ j : Fin numAdvice,
      (deployedSetCommIds vk ps ch (adviceSet j)).getD (adviceMem j : ℕ) CommitmentId.vanishingH
        = CommitmentId.adviceCol p (vk.adviceQueryLayout.getD (j : ℕ) (0, 0)).1)
    (hinstanceLayout : ∀ j : Fin numInstance,
      (deployedSetCommIds vk ps ch (instanceSet j)).getD (instanceMem j : ℕ) CommitmentId.vanishingH
        = CommitmentId.instanceCol p (vk.instanceQueryLayout.getD (j : ℕ) (0, 0)).1)
    (hquotCommitted : ∃ (hSet : ℕ) (hhSet : hSet < deployedX4PairCount vk ps ch)
        (hMem : Fin (deployedSetQueries vk ps ch hSet).length),
      hpoly = coeffsToPoly ((mdec hSet hhSet).cols hMem) ∧
      (deployedSetCommIds vk ps ch hSet).getD (hMem : ℕ) CommitmentId.randomPoly
        = CommitmentId.vanishingH)
    {S : Prop}
    (hencodes : ∀ a,
      SnarkRelationWithMemberColumns urs hk vk ps ch P b v p adviceSet hadviceSet adviceMem
        instanceSet hinstanceSet instanceMem fixedCols y gates hpoly deg pU pW a → S) :
    S := by
  obtain ⟨xg, haccX, hxg⟩ := exists_accepting_good_challenge_quotient
    (combineGates fixedCols
        (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((mdec (adviceSet j) (hadviceSet j)).cols (adviceMem j))))
        (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((mdec (instanceSet j) (hinstanceSet j)).cols (instanceMem j))))
        y gates) hpoly deg hprobX
  exact member_constraint_of_relation_and_batch urs hk vk ps ch adviceSet hadviceSet adviceMem
    instanceSet hinstanceSet instanceMem fixedCols y gates hpoly deg xg hrel pbatch mdec
    (hquot xg haccX)
    (fun hne => not_mem_szBadSet.mp hxg (sub_ne_zero.mpr hne)) p hadviceLayout hinstanceLayout
    hquotCommitted hencodes


open Polynomial in
set_option maxHeartbeats 1000000 in
/-- The member-column endpoint with the quotient polynomial *bound*, not free: `hpoly` is the
decoded member polynomial at a designated position — for the deployed instantiation, the combined
quotient-piece commitment the verifier queries in the gate-point set (the `hPieces` folded with
`(xⁿ)`-powers). With it, the relation `hencodes` consumes says the gate numerator over the decoded
columns equals the *committed* quotient times the vanishing polynomial. -/
theorem member_constraint_of_relation_and_batch_hbound [DecidableEq G] [Inhabited G]
    {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {P : G} {b : Fin (2 ^ urs.k) → Fp} {v : Fp}
    {numAdvice numInstance : ℕ}
    (adviceSet : Fin numAdvice → ℕ)
    (hadviceSet : ∀ j, adviceSet j < deployedX4PairCount vk ps ch)
    (adviceMem : ∀ j : Fin numAdvice, Fin (deployedSetQueries vk ps ch (adviceSet j)).length)
    (instanceSet : Fin numInstance → ℕ)
    (hinstanceSet : ∀ j, instanceSet j < deployedX4PairCount vk ps ch)
    (instanceMem : ∀ j : Fin numInstance,
      Fin (deployedSetQueries vk ps ch (instanceSet j)).length)
    (hSet : ℕ) (hhSet : hSet < deployedX4PairCount vk ps ch)
    (hMem : Fin (deployedSetQueries vk ps ch hSet).length)
    (fixedCols : ℕ → Polynomial Fp) (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp)
    (deg : ℕ) (x : Fp)
    {pU pW : Fp} {a : Fin (2 ^ urs.k) → Fp}
    (hrel : IpaRelation urs P b v a)
    (pbatch : OpenedBatchOpenings urs b (x4BatchCommitments urs hk vk ps ch)
      (x4BatchEvals vk ps ch) a pU pW)
    (mdec : ∀ i (hi : i < deployedX4PairCount vk ps ch),
      OpenedMemberDecode urs hk vk ps ch pbatch i hi)
    (hquot : quotientCheck
      (combineGates fixedCols
        (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((mdec (adviceSet j) (hadviceSet j)).cols (adviceMem j))))
        (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((mdec (instanceSet j) (hinstanceSet j)).cols (instanceMem j))))
        y gates) (coeffsToPoly ((mdec hSet hhSet).cols hMem)) deg x)
    (hgood :
      combineGates fixedCols
        (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((mdec (adviceSet j) (hadviceSet j)).cols (adviceMem j))))
        (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((mdec (instanceSet j) (hinstanceSet j)).cols (instanceMem j))))
        y gates ≠ (coeffsToPoly ((mdec hSet hhSet).cols hMem)) * (X ^ deg - 1) →
      (combineGates fixedCols
        (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((mdec (adviceSet j) (hadviceSet j)).cols (adviceMem j))))
        (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((mdec (instanceSet j) (hinstanceSet j)).cols (instanceMem j))))
        y gates - (coeffsToPoly ((mdec hSet hhSet).cols hMem)) * (X ^ deg - 1)).eval x ≠ 0)
    (p : Fin shape.numProofs)
    (hadviceLayout : ∀ j : Fin numAdvice,
      (deployedSetCommIds vk ps ch (adviceSet j)).getD (adviceMem j : ℕ) CommitmentId.vanishingH
        = CommitmentId.adviceCol p (vk.adviceQueryLayout.getD (j : ℕ) (0, 0)).1)
    (hinstanceLayout : ∀ j : Fin numInstance,
      (deployedSetCommIds vk ps ch (instanceSet j)).getD (instanceMem j : ℕ) CommitmentId.vanishingH
        = CommitmentId.instanceCol p (vk.instanceQueryLayout.getD (j : ℕ) (0, 0)).1)
    (hquotLayout : (deployedSetCommIds vk ps ch hSet).getD (hMem : ℕ) CommitmentId.randomPoly
      = CommitmentId.vanishingH)
    {S : Prop}
    (hencodes : ∀ a,
      SnarkRelationWithMemberColumns urs hk vk ps ch P b v p adviceSet hadviceSet adviceMem
        instanceSet hinstanceSet instanceMem fixedCols y gates (coeffsToPoly ((mdec hSet hhSet).cols hMem)) deg pU pW a → S) :
    S :=
  member_constraint_of_relation_and_batch urs hk vk ps ch adviceSet hadviceSet adviceMem
    instanceSet hinstanceSet instanceMem fixedCols y gates (coeffsToPoly ((mdec hSet hhSet).cols hMem)) deg x hrel pbatch mdec
    hquot hgood p hadviceLayout hinstanceLayout ⟨hSet, hhSet, hMem, rfl, hquotLayout⟩ hencodes

end Opened

end Zcash.Snark
