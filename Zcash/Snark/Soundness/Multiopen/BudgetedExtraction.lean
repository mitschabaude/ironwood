import Zcash.Snark.Soundness.Multiopen.ValueCheckX3
import Zcash.Snark.Soundness.Multiopen.FloorBudget

/-!
# The budgeted multiopen extraction (single-path member terminal)

The extraction cores of `Soundness.Multiopen.ValueCheckX3`
(`deployed_value_check_node_binding`/`deployed_member_node_binding`) consume their squeeze floors
*universally quantified over the splice runs* `X1Run`/`X2Run`/`X3Run` — each forking level draws an
injective sample family and needs the next level's floor at every sampled run's base. This module
re-proves the nested extraction in *budgeted* form: the only measure premise is a single **joint
accept floor** `t₁ + t₂ + t₃ + t₄ < μ(J)` over the joint uniform draw of the four fresh challenges,
where `J` is the nested accept event along the *canonical* rewind path. Two devices dissolve the
`∀`-over-runs quantification:

* **Canonical run selectors** (`canonicalX1Run`/`canonicalX2Run`/`canonicalX3Run`): each opened
  accept event existentially carries its accepting splice run; `Classical.choose` fixes a canonical
  one *as a function of the challenge*, before any probability statement. The joint event `J` and
  the extraction then reference the same runs by construction — no per-sample choice remains.
* **Heavy-fiber Markov descent** (`uniformOfFintype_heavy_fiber_lt`, `Soundness.Multiopen.
  FloorBudget`): each level peels its own threshold `tᵢ` off the joint floor, leaving the residual
  floor on every heavy fiber; `exists_injective_accepting_of_measure` forks the heavy set into the
  sample family that level's algebra consumes, and each sample *carries its own inner floor* into
  the next level. The heavy sets have positive measure, so every level self-anchors — the anchor
  premises (`hξ₀`/`hζ₀`/`hx3anchor`) of the `∀`-over-runs cores disappear.

The endpoint `deployed_member_budget` states the audit's combined soundness budget: for the
deployed member decode, *either* the joint accept measure sits within the knowledge-error budget
`Σtᵢ`, *or* the decoded member columns take their claimed evaluations (or a computed
`(g, U, W)`-relation exists). The `∀`-over-runs cores remain in place — this module builds
alongside them; the non-measure premises (`havoid`, `hql`, the member decode) are unchanged except
that `havoid` is only required at the canonical runs.
-/

namespace Zcash.Snark

open Polynomial
open scoped ENNReal
open Classical

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-! ## Canonical run selectors

Each `OpenedX*Accept` event is an existential over its splice run. The *run-accept payload*
definitions below name the body of that existential, so `OpenedX*Accept … = ∃ r, X*RunAccepts … r`
definitionally; the canonical selector is `Classical.choose` on that existential when the event
holds (the honest run otherwise), and its spec lemma returns the payload at the canonical run. -/

/-- The body of `OpenedX2Accept`'s run existential: run `r` accepts the set-separation rewind at
challenge `χ` with a clean forked transcript on its opened commitment. -/
def X2RunAccepts [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (b : Fin (2 ^ urs.k) → Fp) (χ : Fp) (r : X2Run shape G) : Prop :=
  ∃ (z blind : Fp)
    (fs : ForkedTranscript urs hk vk (r.spliced ps) (r.challenges ch χ) b z blind)
    (t : IpaTreeV Fp G urs.k),
    IpaAcceptV urs.g b fs.openedCommitment
      (multiopenValue vk (r.spliced ps) (r.challenges ch χ)) t

/-- The canonical accepting `x₂` splice run at challenge `χ`: `Classical.choose` on the accept
event's run existential when it holds, the honest run otherwise. A *function of the challenge*,
fixed before any probability statement — the joint accept event and the budgeted extraction
reference the same run by construction. -/
noncomputable def canonicalX2Run [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (b : Fin (2 ^ urs.k) → Fp) (χ : Fp) : X2Run shape G :=
  if h : OpenedX2Accept urs hk vk ps ch b χ then
    (show ∃ r : X2Run shape G, X2RunAccepts urs hk vk ps ch b χ r from h).choose
  else honestX2Run ps ch

/-- The canonical `x₂` run carries the accept payload whenever the event holds. -/
theorem canonicalX2Run_accepts [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (b : Fin (2 ^ urs.k) → Fp) {χ : Fp}
    (h : OpenedX2Accept urs hk vk ps ch b χ) :
    X2RunAccepts urs hk vk ps ch b χ (canonicalX2Run urs hk vk ps ch b χ) := by
  rw [canonicalX2Run, dif_pos h]
  exact (show ∃ r : X2Run shape G, X2RunAccepts urs hk vk ps ch b χ r from h).choose_spec

/-- The body of `OpenedX3Accept`'s run existential. -/
def X3RunAccepts [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (b : Fin (2 ^ urs.k) → Fp) (χ : Fp) (r : X3Run shape G) : Prop :=
  ∃ (z blind : Fp)
    (fs : ForkedTranscript urs hk vk (r.spliced ps) (r.challenges ch χ) b z blind)
    (t : IpaTreeV Fp G urs.k),
    IpaAcceptV urs.g b fs.openedCommitment
      (multiopenValue vk (r.spliced ps) (r.challenges ch χ)) t

/-- The canonical accepting `x₃` splice run at challenge `χ`, as `canonicalX2Run`. -/
noncomputable def canonicalX3Run [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (b : Fin (2 ^ urs.k) → Fp) (χ : Fp) : X3Run shape G :=
  if h : OpenedX3Accept urs hk vk ps ch b χ then
    (show ∃ r : X3Run shape G, X3RunAccepts urs hk vk ps ch b χ r from h).choose
  else honestX3Run ps ch

/-- The canonical `x₃` run carries the accept payload whenever the event holds. -/
theorem canonicalX3Run_accepts [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (b : Fin (2 ^ urs.k) → Fp) {χ : Fp}
    (h : OpenedX3Accept urs hk vk ps ch b χ) :
    X3RunAccepts urs hk vk ps ch b χ (canonicalX3Run urs hk vk ps ch b χ) := by
  rw [canonicalX3Run, dif_pos h]
  exact (show ∃ r : X3Run shape G, X3RunAccepts urs hk vk ps ch b χ r from h).choose_spec

/-- The body of `OpenedX1PinnedAccept`'s run existential: run `run` accepts the deployed verifier
at compression challenge `χv` and carries an opened `x₄` batch at its own interpolation base. -/
def X1PinnedRunAccepts [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (χv : Fp) (run : X1Run shape G) : Prop :=
  ∃ (aR : Fin (2 ^ urs.k) → Fp) (pUR pWR : Fp),
    DeployedAccepts urs hk vk (run.spliced ps) (run.challenges ch χv) ∧
    Nonempty (OpenedBatchOpenings urs (evalVector urs.k ((run.challenges ch χv).x3))
      (x4BatchCommitments urs hk vk (run.spliced ps) (run.challenges ch χv))
      (x4BatchEvals vk (run.spliced ps) (run.challenges ch χv)) aR pUR pWR)

/-- The canonical accepting pinned `x₁` splice run at challenge `χv`, as `canonicalX2Run`. -/
noncomputable def canonicalX1Run [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (χv : Fp) : X1Run shape G :=
  if h : OpenedX1PinnedAccept urs hk vk ps ch χv then
    (show ∃ run : X1Run shape G, X1PinnedRunAccepts urs hk vk ps ch χv run from h).choose
  else honestX1Run ps ch

/-- The canonical pinned `x₁` run carries the accept payload whenever the event holds. -/
theorem canonicalX1Run_accepts [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) {χv : Fp} (h : OpenedX1PinnedAccept urs hk vk ps ch χv) :
    X1PinnedRunAccepts urs hk vk ps ch χv (canonicalX1Run urs hk vk ps ch χv) := by
  rw [canonicalX1Run, dif_pos h]
  exact (show ∃ run : X1Run shape G, X1PinnedRunAccepts urs hk vk ps ch χv run from h).choose_spec

/-! ## The canonical-run grid extraction -/

/-- **`openedX3_rewound_batch_eval` at the canonical run.** The single-slot `x₄` floor at the
*canonical* `x₃` run's base — exactly what the joint floor's heavy fiber supplies — replaces the
`∀`-over-`X3Run` floor family: the accept event's run is the canonical one by construction, so the
floor is spent at precisely the run the extraction opens. Same conclusion: one batch whose decoded
column at every slot evaluates at `χ` to the slot's claimed evaluation. -/
theorem openedX3_rewound_batch_eval_canonical [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) {χ : Fp}
    (hprob4 : (deployedX4PairCount vk
          ((canonicalX3Run urs hk vk ps ch (evalVector urs.k χ) χ).spliced ps)
          ((canonicalX3Run urs hk vk ps ch (evalVector urs.k χ) χ).challenges ch χ) : ℝ≥0∞)
          / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
            (OpenedX4Accept urs hk vk
              ((canonicalX3Run urs hk vk ps ch (evalVector urs.k χ) χ).spliced ps)
              ((canonicalX3Run urs hk vk ps ch (evalVector urs.k χ) χ).challenges ch χ)
              (evalVector urs.k χ))))
    (hacc : OpenedX3Accept urs hk vk ps ch (evalVector urs.k χ) χ) :
    ∃ (r : X3Run shape G) (a : Fin (2 ^ urs.k) → Fp) (pU pW : Fp)
      (batch : OpenedBatchOpenings urs (evalVector urs.k χ)
        (x4BatchCommitments urs hk vk (r.spliced ps) (r.challenges ch χ))
        (x4BatchEvals vk (r.spliced ps) (r.challenges ch χ)) a pU pW),
      ∀ j, (openedDecodedCols batch j).eval χ
        = x4BatchEvals vk (r.spliced ps) (r.challenges ch χ) j := by
  obtain ⟨z, blind, fs, t, ht⟩ :=
    canonicalX3Run_accepts urs hk vk ps ch (evalVector urs.k χ) hacc
  obtain ⟨a, ha⟩ := ipaRelation_extract urs (evalVector urs.k χ) fs.openedCommitment
    (multiopenValue vk ((canonicalX3Run urs hk vk ps ch (evalVector urs.k χ) χ).spliced ps)
      ((canonicalX3Run urs hk vk ps ch (evalVector urs.k χ) χ).challenges ch χ)) t ht
  refine ⟨canonicalX3Run urs hk vk ps ch (evalVector urs.k χ) χ, a, fs.pU, fs.pW,
    openedX4Rewind_of_x4Prob_forked urs hk vk
      ((canonicalX3Run urs hk vk ps ch (evalVector urs.k χ) χ).spliced ps)
      ((canonicalX3Run urs hk vk ps ch (evalVector urs.k χ) χ).challenges ch χ) fs ⟨t, ht⟩
      hprob4 a ha, ?_⟩
  intro j
  exact openedDecodedCols_eval_x3 urs hk vk
    ((canonicalX3Run urs hk vk ps ch (evalVector urs.k χ) χ).spliced ps)
    ((canonicalX3Run urs hk vk ps ch (evalVector urs.k χ) χ).challenges ch χ) _ j

end Zcash.Snark
