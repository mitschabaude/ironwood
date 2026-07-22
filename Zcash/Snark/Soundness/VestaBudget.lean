import Zcash.Snark.Soundness.Compose67
import Zcash.Snark.Soundness.Multiopen.BudgetedExtraction

/-!
# The budgeted deployed capstone and the budgeted computed path

`Soundness.Vesta` proves the derived deployed member capstone
(`orchard_verifier_vesta_member_constraint_derived`), whose extraction floors are universally
quantified over the splice runs `X1Run`/`X2Run`/`X3Run`; `Soundness.Multiopen.BudgetedExtraction`
re-proves the member extraction from a single joint accept floor along the canonical rewind path.
This module joins the two ends:

* `orchard_verifier_vesta_member_constraint_budgeted` — the derived capstone with its seven
  run-quantified floor premises (`hξ₀p`/`hprob1p`/`hx2`/`hx3anchor`/`hprob3`/`hprob4` and the
  run-quantified `havoid`) replaced by one joint accept floor `t₁ + (t₂ + t₃ + t₄) <
  μ(memberJointAccept)` at the honest-base thresholds, plus sample avoidance at the canonical runs
  only.
* `member_relation_or_dlr_of_instance_budgeted` / `member_snark_of_instance_budgeted` /
  `orchard_verifier_sound_vesta_budgeted` — the computed path (`Soundness.Compose67`) routed
  through the budgeted capstone: the member decode is *constructed*
  (`openedMemberDecode_of_x1Prob`) and the quotient identity `hquot` is *derived*
  (`quotientCheck_of_claimed` from the member bindings), so neither is a hypothesis. The premises
  that remain are acceptance itself (`hacc0`), the two accept-measure floors (`hprob1`, the joint
  floor `hJ`), sample avoidance at the canonical runs, the gate-structure fingerprint surfaces
  (`hfold`, `hgood`), the layout identities, and the committed-quotient identity — each an honest
  trust surface, none of them extraction data.

The `x₁` floor `hprob1` feeds the member-decode construction and is stated at the honest base; it
follows from the joint floor by the first-coordinate marginal bound, but stays a named hypothesis
because the statement's decode terms carry its proof.
-/

namespace Zcash.Snark

-- Match the instance set `AlgebraicWfProof.multiopen_repr` is stated against (`Soundness.Compose67`
-- and `Forking.Adversary.Algebraic` use the same concrete `Inhabited VestaG`); a binder would be a
-- different instance term, forcing the `multiopenCommitment` fold through `whnf`. Named to avoid an
-- auto-generated-name collision on co-import.
local instance vestaInhabitedVestaBudget : Inhabited VestaG := ⟨0⟩

open Polynomial in
open scoped ENNReal in
open Classical in
set_option maxHeartbeats 4000000 in
/-- **Budgeted deployed member capstone: the floor family priced by one joint accept floor.** The
conclusion of `orchard_verifier_vesta_member_constraint_derived` (`Soundness.Vesta`) — the gate
check runs at the deployed opening challenge `ch.x` on the decoded member columns, with the
columns' claimed evaluations *derived* via the member node binding and `hquot` produced by
`quotientCheck_of_claimed` — from a single joint accept floor per point set:
`t₁(i) + (t₂ + t₃ + t₄) < μ(memberJointAccept)` at the honest-base thresholds
(`deployed_member_node_binding_at_point_budgeted`), in place of the derived capstone's seven
run-quantified floor premises. Sample avoidance (`havoid`) is required only at the canonical runs.

Named assumptions: `hacc0` (the deployed run accepts), `hprob1` (the honest-base `x₁` accept
floor, feeding the member-decode construction), `hJ` (the joint accept floor), `havoid`
(canonical-run sample avoidance), `hfold` (the gate fold at the deployed claimed evaluations — the
gate-structure fingerprint surface), `hgood` (the Schwartz–Zippel surface, producible by
`hgood_of_xProb`), `hadviceLayout`/`hinstanceLayout` (VK query-layout identities),
`hquotCommitted` (the quotient is a committed column), `hencodes` (the member-relation consumer). -/
theorem orchard_verifier_vesta_member_constraint_budgeted {shape : Shape}
    (urs : URS VestaG) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp VestaG) (ps : ProofString shape Fp VestaG)
    (ch : Challenges shape.k Fp)
    (pU pW : Fp)
    {numAdvice numInstance : ℕ}
    (adviceSet : Fin numAdvice → ℕ)
    (hadviceSet : ∀ j, adviceSet j < deployedX4PairCount vk ps ch)
    (adviceMem : ∀ j : Fin numAdvice, Fin (deployedSetQueries vk ps ch (adviceSet j)).length)
    (instanceSet : Fin numInstance → ℕ)
    (hinstanceSet : ∀ j, instanceSet j < deployedX4PairCount vk ps ch)
    (instanceMem : ∀ j : Fin numInstance,
      Fin (deployedSetQueries vk ps ch (instanceSet j)).length)
    (fixedCols : ℕ → Polynomial Fp)
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ)
    {a₀ : Fin (2 ^ urs.k) → Fp}
    (pbatch : OpenedBatchOpenings urs (evalVector urs.k ch.x3)
      (x4BatchCommitments urs hk vk ps ch) (x4BatchEvals vk ps ch) a₀ pU pW)
    (hξcur : pbatch.batchChallenge pbatch.current = ch.x4)
    (hlen : ∀ i, i < deployedX4PairCount vk ps ch
      → 0 < (deployedSetQueries vk ps ch i).length)
    (hprob1 : ∀ i, i < deployedX4PairCount vk ps ch →
      (((deployedSetQueries vk ps ch i).length - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
            (OpenedX1Accept urs hk vk ps ch)))
    (hacc0 : DeployedAccepts urs hk vk ps ch)
    (p : Fin shape.numProofs)
    (hadvLen : ∀ j : Fin numAdvice, (j : ℕ) < vk.adviceQueryLayout.length
      ∧ (j : ℕ) < (List.ofFn (ps.adviceEvals p)).length)
    (hinstLen : ∀ j : Fin numInstance, (j : ℕ) < vk.instanceQueryLayout.length
      ∧ (j : ℕ) < (List.ofFn (ps.instanceEvals p)).length)
    (b₂f : Fp → Fin (2 ^ urs.k) → Fp)
    (hJ : ∀ i, i < deployedX4PairCount vk ps ch →
      (((deployedSetQueries vk ps ch i).length - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
        + (((deployedX4PairCount vk ps ch - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
          + ((max (2 ^ urs.k) (deployedAllPts vk ps ch).card
              + (deployedAllPts vk ps ch).card : ℕ) : ℝ≥0∞) / Fintype.card Fp
          + (deployedX4PairCount vk ps ch : ℝ≥0∞) / Fintype.card Fp)
      < (PMF.uniformOfFintype (Fp × Fp × Fp × Fp)).toOuterMeasure
          (memberJointAccept urs hk vk ps ch b₂f))
    (havoid : ∀ (ξv ζv χv : Fp),
      OpenedX3Accept urs hk vk
        ((canonicalX2Run urs hk vk ((canonicalX1Run urs hk vk ps ch ξv).spliced ps)
            ((canonicalX1Run urs hk vk ps ch ξv).challenges ch ξv) (b₂f ξv) ζv).spliced
          ((canonicalX1Run urs hk vk ps ch ξv).spliced ps))
        ((canonicalX2Run urs hk vk ((canonicalX1Run urs hk vk ps ch ξv).spliced ps)
            ((canonicalX1Run urs hk vk ps ch ξv).challenges ch ξv) (b₂f ξv) ζv).challenges
          ((canonicalX1Run urs hk vk ps ch ξv).challenges ch ξv) ζv)
        (evalVector urs.k χv) χv →
      ∀ k', χv ∉ deployedSetPts vk ((canonicalX1Run urs hk vk ps ch ξv).spliced ps)
        ((canonicalX1Run urs hk vk ps ch ξv).challenges ch ξv) k')
    (hfold : (List.ofFn (fun i : Fin ng =>
        (gates i).eval (fun n => (fixedCols n).eval ch.x)
          (deployedClaimedFeed vk ps ch adviceSet adviceMem vk.adviceQueryLayout)
          (deployedClaimedFeed vk ps ch instanceSet instanceMem vk.instanceQueryLayout))).foldl
          (fun acc v => acc * y + v) 0 = hpoly.eval ch.x * (ch.x ^ deg - 1))
    (hgood :
      combineGates fixedCols
        (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk ps ch pbatch (adviceSet j)
            (hadviceSet j) (hlen _ (hadviceSet j)) (hprob1 _ (hadviceSet j)) hacc0).cols (adviceMem j))))
        (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk ps ch pbatch (instanceSet j)
            (hinstanceSet j) (hlen _ (hinstanceSet j))
            (hprob1 _ (hinstanceSet j)) hacc0).cols (instanceMem j))))
        y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols
        (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk ps ch pbatch (adviceSet j)
            (hadviceSet j) (hlen _ (hadviceSet j)) (hprob1 _ (hadviceSet j)) hacc0).cols (adviceMem j))))
        (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk ps ch pbatch (instanceSet j)
            (hinstanceSet j) (hlen _ (hinstanceSet j))
            (hprob1 _ (hinstanceSet j)) hacc0).cols (instanceMem j))))
        y gates - hpoly * (X ^ deg - 1)).eval ch.x ≠ 0)
    (hadviceLayout : ∀ j : Fin numAdvice,
      (deployedSetCommIds vk ps ch (adviceSet j)).getD (adviceMem j : ℕ) CommitmentId.vanishingH
        = CommitmentId.adviceCol p (vk.adviceQueryLayout.getD (j : ℕ) (0, 0)).1)
    (hinstanceLayout : ∀ j : Fin numInstance,
      (deployedSetCommIds vk ps ch (instanceSet j)).getD (instanceMem j : ℕ) CommitmentId.vanishingH
        = CommitmentId.instanceCol p (vk.instanceQueryLayout.getD (j : ℕ) (0, 0)).1)
    (hquotCommitted : ∃ (hSet : ℕ) (hhSet : hSet < deployedX4PairCount vk ps ch)
        (hMem : Fin (deployedSetQueries vk ps ch hSet).length),
      hpoly = coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk ps ch pbatch hSet hhSet
          (hlen _ hhSet) (hprob1 _ hhSet) hacc0).cols hMem) ∧
      (deployedSetCommIds vk ps ch hSet).getD (hMem : ℕ) CommitmentId.randomPoly
        = CommitmentId.vanishingH)
    {S : Prop}
    (hencodes : ∀ a,
      SnarkRelationWithMemberColumns urs hk vk ps ch
        (deployedCommitment urs hk vk ps ch - pU • urs.u - pW • urs.w)
        (evalVector urs.k ch.x3) (multiopenValue vk ps ch) p adviceSet hadviceSet adviceMem
        instanceSet hinstanceSet instanceMem fixedCols y gates hpoly deg pU pW a → S) :
    S ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  by_cases hrel : HasNontrivialRelation (F := Fp) urs.g urs.u urs.w
  · exact Or.inr hrel
  -- derive `hadvice`: the rotated advice feed's value at `ch.x` is the deployed claimed eval
  have hadvice : ∀ n, (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
      coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk ps ch pbatch (adviceSet j)
        (hadviceSet j) (hlen _ (hadviceSet j)) (hprob1 _ (hadviceSet j)) hacc0).cols
          (adviceMem j))) n).eval ch.x
      = deployedClaimedFeed vk ps ch adviceSet adviceMem vk.adviceQueryLayout n := by
    intro n
    by_cases h : n < numAdvice
    · obtain ⟨q, hqmem, hqid, hqpt⟩ := advice_query_mem_assembleQueries vk ps ch p
        (hadvLen ⟨n, h⟩).1 (hadvLen ⟨n, h⟩).2
      have hltm : ((adviceMem ⟨n, h⟩ : ℕ))
          < (deployedSetCommIds vk ps ch (adviceSet ⟨n, h⟩)).length := by
        rw [deployedSetCommIds_length]
        exact (adviceMem ⟨n, h⟩).isLt
      have hid : (deployedSetCommIds vk ps ch (adviceSet ⟨n, h⟩)).getD ((adviceMem ⟨n, h⟩ : ℕ))
          CommitmentId.vanishingH = q.commId := (hadviceLayout ⟨n, h⟩).trans hqid.symm
      have hpt := deployed_query_point_mem vk ps ch hqmem hltm hid
      rw [hqpt] at hpt
      have hb := deployed_member_node_binding_at_point_budgeted urs hk vk ps ch (adviceSet ⟨n, h⟩)
        (hadviceSet ⟨n, h⟩)
        (openedMemberDecode_of_x1Prob urs hk vk ps ch pbatch (adviceSet ⟨n, h⟩)
          (hadviceSet ⟨n, h⟩) (hlen _ (hadviceSet ⟨n, h⟩)) (hprob1 _ (hadviceSet ⟨n, h⟩)) hacc0)
        b₂f (hJ _ (hadviceSet ⟨n, h⟩)) havoid hpt (adviceMem ⟨n, h⟩)
      rcases hb with hb | hdlr
      swap
      · exact absurd hdlr hrel
      rw [rotatedFeed_eval vk.omega vk.adviceQueryLayout _ h ch.x, hb, deployedClaimedFeed,
        dif_pos h]
    · rw [rotatedFeed_eval_of_ge vk.omega vk.adviceQueryLayout _ (Nat.not_lt.mp h) ch.x,
        deployedClaimedFeed, dif_neg h]
  -- derive `hinstance` symmetrically
  have hinstance : ∀ n, (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
      coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk ps ch pbatch (instanceSet j)
        (hinstanceSet j) (hlen _ (hinstanceSet j)) (hprob1 _ (hinstanceSet j)) hacc0).cols
          (instanceMem j))) n).eval ch.x
      = deployedClaimedFeed vk ps ch instanceSet instanceMem vk.instanceQueryLayout n := by
    intro n
    by_cases h : n < numInstance
    · obtain ⟨q, hqmem, hqid, hqpt⟩ := instance_query_mem_assembleQueries vk ps ch p
        (hinstLen ⟨n, h⟩).1 (hinstLen ⟨n, h⟩).2
      have hltm : ((instanceMem ⟨n, h⟩ : ℕ))
          < (deployedSetCommIds vk ps ch (instanceSet ⟨n, h⟩)).length := by
        rw [deployedSetCommIds_length]
        exact (instanceMem ⟨n, h⟩).isLt
      have hid : (deployedSetCommIds vk ps ch (instanceSet ⟨n, h⟩)).getD
          ((instanceMem ⟨n, h⟩ : ℕ)) CommitmentId.vanishingH = q.commId :=
        (hinstanceLayout ⟨n, h⟩).trans hqid.symm
      have hpt := deployed_query_point_mem vk ps ch hqmem hltm hid
      rw [hqpt] at hpt
      have hb := deployed_member_node_binding_at_point_budgeted urs hk vk ps ch (instanceSet ⟨n, h⟩)
        (hinstanceSet ⟨n, h⟩)
        (openedMemberDecode_of_x1Prob urs hk vk ps ch pbatch (instanceSet ⟨n, h⟩)
          (hinstanceSet ⟨n, h⟩) (hlen _ (hinstanceSet ⟨n, h⟩)) (hprob1 _ (hinstanceSet ⟨n, h⟩))
          hacc0)
        b₂f (hJ _ (hinstanceSet ⟨n, h⟩)) havoid hpt (instanceMem ⟨n, h⟩)
      rcases hb with hb | hdlr
      swap
      · exact absurd hdlr hrel
      rw [rotatedFeed_eval vk.omega vk.instanceQueryLayout _ h ch.x, hb, deployedClaimedFeed,
        dif_pos h]
    · rw [rotatedFeed_eval_of_ge vk.omega vk.instanceQueryLayout _ (Nat.not_lt.mp h) ch.x,
        deployedClaimedFeed, dif_neg h]
  -- the gate check at the deployed opening challenge, from the derived claimed evaluations
  exact orchard_verifier_vesta_member_constraint_deployed_x4 urs hk vk ps ch pU pW adviceSet
    hadviceSet adviceMem instanceSet hinstanceSet instanceMem fixedCols y gates hpoly deg ch.x
    pbatch hξcur hlen hprob1 hacc0
    (quotientCheck_of_claimed fixedCols _ _ y gates hpoly deg ch.x
      (fun n => (fixedCols n).eval ch.x)
      (deployedClaimedFeed vk ps ch adviceSet adviceMem vk.adviceQueryLayout)
      (deployedClaimedFeed vk ps ch instanceSet instanceMem vk.instanceQueryLayout)
      (fun _ => rfl) hadvice hinstance hfold)
    hgood p hadviceLayout hinstanceLayout hquotCommitted hencodes

variable {shape : Shape} {basis : AugmentedIndex (2 ^ shape.k) → VestaG}

open Polynomial in
open scoped ENNReal in
open Classical in
set_option maxHeartbeats 4000000 in
/-- **The budgeted witness tie on the computed path.** `member_relation_or_dlr_of_instance`
(`Soundness.Compose67`) with the member decode *constructed* and `hquot` *derived*: on the
agreement branch the budgeted deployed capstone runs at the algebraic instance's base
`(p.proof.1, chRecord ν)`; on the disagreement branch the two openings of the shared commitment
collide into a computed `(g, u, w)` relation. No `mdec`/`hquot` hypothesis remains — the measure
premises are the honest-base `x₁` floor and the joint accept floor. -/
theorem member_relation_or_dlr_of_instance_budgeted
    {vk : VerifyingKey shape Fp VestaG} (p : AlgebraicWfProof basis vk) (ν : Fin 11 → Fp)
    (cert : AlgebraicDForkCert (F := Fp)
      (augmentedBasis (ursOfAugmentedBasis shape.k basis).g
        (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w) shape.k)
    (hz : ν 10 ≠ 0)
    (hvalid : DeployedForkValid (ursOfAugmentedBasis shape.k basis).g
      (evalVector shape.k (ν 7)) (ursOfAugmentedBasis shape.k basis).u
      (ursOfAugmentedBasis shape.k basis).w (ν 10)
      (commit (ursOfAugmentedBasis shape.k basis)
          (adjustedWitness (p.aMulti ν) p.s
            (multiopenValue vk p.proof.1 (chRecord ν (fun _ => 0))) (ν 9)) +
        (p.multiU ν + ν 9 * p.sU) • (ursOfAugmentedBasis shape.k basis).u +
        (p.multiBlind ν + ν 9 * p.sBlind) • (ursOfAugmentedBasis shape.k basis).w)
      cert.toDForkCert)
    (o : (deployedAlgebraicInstanceOfCert p ν cert hz hvalid).Opening)
    {a₀ : Fin (2 ^ shape.k) → Fp}
    (pbatch : OpenedBatchOpenings (ursOfAugmentedBasis shape.k basis) (evalVector shape.k (ν 7))
      (x4BatchCommitments (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
        (chRecord ν (fun _ => 0)))
      (x4BatchEvals vk p.proof.1 (chRecord ν (fun _ => 0))) a₀ (p.multiU ν) (p.multiBlind ν))
    (hξcur : pbatch.batchChallenge pbatch.current
      = (chRecord ν (fun _ => 0) : Challenges shape.k Fp).x4)
    {numAdvice numInstance : ℕ}
    (adviceSet : Fin numAdvice → ℕ)
    (hadviceSet : ∀ j, adviceSet j
      < deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0)))
    (adviceMem : ∀ j : Fin numAdvice,
      Fin (deployedSetQueries vk p.proof.1 (chRecord ν (fun _ => 0)) (adviceSet j)).length)
    (instanceSet : Fin numInstance → ℕ)
    (hinstanceSet : ∀ j, instanceSet j
      < deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0)))
    (instanceMem : ∀ j : Fin numInstance,
      Fin (deployedSetQueries vk p.proof.1 (chRecord ν (fun _ => 0)) (instanceSet j)).length)
    (fixedCols : ℕ → Polynomial Fp) (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp)
    (hpoly : Polynomial Fp) (deg : ℕ)
    (hlen : ∀ i, i < deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0))
      → 0 < (deployedSetQueries vk p.proof.1 (chRecord ν (fun _ => 0)) i).length)
    (hprob1 : ∀ i, i < deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0)) →
      (((deployedSetQueries vk p.proof.1 (chRecord ν (fun _ => 0)) i).length - 1 : ℕ) : ℝ≥0∞)
          / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
            (OpenedX1Accept (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
              (chRecord ν (fun _ => 0)))))
    (hacc0 : DeployedAccepts (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
      (chRecord ν (fun _ => 0)))
    (pp : Fin shape.numProofs)
    (hadvLen : ∀ j : Fin numAdvice, (j : ℕ) < vk.adviceQueryLayout.length
      ∧ (j : ℕ) < (List.ofFn ((p.proof.1 : ProofString shape Fp VestaG).adviceEvals pp)).length)
    (hinstLen : ∀ j : Fin numInstance, (j : ℕ) < vk.instanceQueryLayout.length
      ∧ (j : ℕ) < (List.ofFn ((p.proof.1 : ProofString shape Fp VestaG).instanceEvals pp)).length)
    (b₂f : Fp → Fin (2 ^ shape.k) → Fp)
    (hJ : ∀ i, i < deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0)) →
      (((deployedSetQueries vk p.proof.1 (chRecord ν (fun _ => 0)) i).length - 1 : ℕ) : ℝ≥0∞)
          / Fintype.card Fp
        + (((deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0)) - 1 : ℕ) : ℝ≥0∞)
            / Fintype.card Fp
          + ((max (2 ^ shape.k)
                (deployedAllPts vk p.proof.1 (chRecord ν (fun _ => 0))).card
              + (deployedAllPts vk p.proof.1 (chRecord ν (fun _ => 0))).card : ℕ) : ℝ≥0∞)
            / Fintype.card Fp
          + (deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0)) : ℝ≥0∞)
            / Fintype.card Fp)
      < (PMF.uniformOfFintype (Fp × Fp × Fp × Fp)).toOuterMeasure
          (memberJointAccept (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
            (chRecord ν (fun _ => 0)) b₂f))
    (havoid : ∀ (ξv ζv χv : Fp),
      OpenedX3Accept (ursOfAugmentedBasis shape.k basis) rfl vk
        ((canonicalX2Run (ursOfAugmentedBasis shape.k basis) rfl vk
            ((canonicalX1Run (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
              (chRecord ν (fun _ => 0)) ξv).spliced p.proof.1)
            ((canonicalX1Run (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
              (chRecord ν (fun _ => 0)) ξv).challenges (chRecord ν (fun _ => 0)) ξv)
            (b₂f ξv) ζv).spliced
          ((canonicalX1Run (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
            (chRecord ν (fun _ => 0)) ξv).spliced p.proof.1))
        ((canonicalX2Run (ursOfAugmentedBasis shape.k basis) rfl vk
            ((canonicalX1Run (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
              (chRecord ν (fun _ => 0)) ξv).spliced p.proof.1)
            ((canonicalX1Run (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
              (chRecord ν (fun _ => 0)) ξv).challenges (chRecord ν (fun _ => 0)) ξv)
            (b₂f ξv) ζv).challenges
          ((canonicalX1Run (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
            (chRecord ν (fun _ => 0)) ξv).challenges (chRecord ν (fun _ => 0)) ξv) ζv)
        (evalVector shape.k χv) χv →
      ∀ k', χv ∉ deployedSetPts vk
        ((canonicalX1Run (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
          (chRecord ν (fun _ => 0)) ξv).spliced p.proof.1)
        ((canonicalX1Run (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
          (chRecord ν (fun _ => 0)) ξv).challenges (chRecord ν (fun _ => 0)) ξv) k')
    (hfold : (List.ofFn (fun i : Fin ng =>
        (gates i).eval
          (fun n => (fixedCols n).eval (chRecord ν (fun _ => 0) : Challenges shape.k Fp).x)
          (deployedClaimedFeed vk p.proof.1 (chRecord ν (fun _ => 0)) adviceSet adviceMem
            vk.adviceQueryLayout)
          (deployedClaimedFeed vk p.proof.1 (chRecord ν (fun _ => 0)) instanceSet instanceMem
            vk.instanceQueryLayout))).foldl
          (fun acc v => acc * y + v) 0
        = hpoly.eval (chRecord ν (fun _ => 0) : Challenges shape.k Fp).x
          * ((chRecord ν (fun _ => 0) : Challenges shape.k Fp).x ^ deg - 1))
    (hgood :
      combineGates fixedCols
        (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob (ursOfAugmentedBasis shape.k basis) rfl vk
            p.proof.1 (chRecord ν (fun _ => 0)) pbatch (adviceSet j)
            (hadviceSet j) (hlen _ (hadviceSet j)) (hprob1 _ (hadviceSet j)) hacc0).cols
              (adviceMem j))))
        (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob (ursOfAugmentedBasis shape.k basis) rfl vk
            p.proof.1 (chRecord ν (fun _ => 0)) pbatch (instanceSet j)
            (hinstanceSet j) (hlen _ (hinstanceSet j)) (hprob1 _ (hinstanceSet j)) hacc0).cols
              (instanceMem j))))
        y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols
        (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob (ursOfAugmentedBasis shape.k basis) rfl vk
            p.proof.1 (chRecord ν (fun _ => 0)) pbatch (adviceSet j)
            (hadviceSet j) (hlen _ (hadviceSet j)) (hprob1 _ (hadviceSet j)) hacc0).cols
              (adviceMem j))))
        (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob (ursOfAugmentedBasis shape.k basis) rfl vk
            p.proof.1 (chRecord ν (fun _ => 0)) pbatch (instanceSet j)
            (hinstanceSet j) (hlen _ (hinstanceSet j)) (hprob1 _ (hinstanceSet j)) hacc0).cols
              (instanceMem j))))
        y gates - hpoly * (X ^ deg - 1)).eval
          (chRecord ν (fun _ => 0) : Challenges shape.k Fp).x ≠ 0)
    (hadviceLayout : ∀ j : Fin numAdvice,
      (deployedSetCommIds vk p.proof.1 (chRecord ν (fun _ => 0)) (adviceSet j)).getD
          (adviceMem j : ℕ) CommitmentId.vanishingH
        = CommitmentId.adviceCol pp (vk.adviceQueryLayout.getD (j : ℕ) (0, 0)).1)
    (hinstanceLayout : ∀ j : Fin numInstance,
      (deployedSetCommIds vk p.proof.1 (chRecord ν (fun _ => 0)) (instanceSet j)).getD
          (instanceMem j : ℕ) CommitmentId.vanishingH
        = CommitmentId.instanceCol pp (vk.instanceQueryLayout.getD (j : ℕ) (0, 0)).1)
    (hquotCommitted : ∃ (hSet : ℕ)
        (hhSet : hSet < deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0)))
        (hMem : Fin (deployedSetQueries vk p.proof.1 (chRecord ν (fun _ => 0)) hSet).length),
      hpoly = coeffsToPoly ((openedMemberDecode_of_x1Prob (ursOfAugmentedBasis shape.k basis) rfl
          vk p.proof.1 (chRecord ν (fun _ => 0)) pbatch hSet hhSet
          (hlen _ hhSet) (hprob1 _ hhSet) hacc0).cols hMem) ∧
      (deployedSetCommIds vk p.proof.1 (chRecord ν (fun _ => 0)) hSet).getD (hMem : ℕ)
          CommitmentId.randomPoly = CommitmentId.vanishingH)
    {S : Prop}
    (hencodes : ∀ a,
      SnarkRelationWithMemberColumns (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
        (chRecord ν (fun _ => 0))
        (deployedCommitment (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
            (chRecord ν (fun _ => 0))
          - p.multiU ν • (ursOfAugmentedBasis shape.k basis).u
          - p.multiBlind ν • (ursOfAugmentedBasis shape.k basis).w)
        (evalVector shape.k (ν 7)) (multiopenValue vk p.proof.1 (chRecord ν (fun _ => 0)))
        pp adviceSet hadviceSet adviceMem instanceSet hinstanceSet instanceMem
        fixedCols y gates hpoly deg (p.multiU ν) (p.multiBlind ν) a → S) :
    S ∨ HasNontrivialRelation (F := Fp) (ursOfAugmentedBasis shape.k basis).g
      (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w := by
  by_cases hae : o.1 = a₀
  · exact orchard_verifier_vesta_member_constraint_budgeted (ursOfAugmentedBasis shape.k basis)
      rfl vk p.proof.1 (chRecord ν (fun _ => 0)) (p.multiU ν) (p.multiBlind ν)
      adviceSet hadviceSet adviceMem instanceSet hinstanceSet instanceMem fixedCols y gates
      hpoly deg pbatch hξcur hlen hprob1 hacc0 pp hadvLen hinstLen b₂f hJ havoid hfold hgood
      hadviceLayout hinstanceLayout hquotCommitted hencodes
  · exact Or.inr (hasNontrivialRelation_of_two_openings (ursOfAugmentedBasis shape.k basis) hae
      ((opening_commit_deployed_of_instance p ν cert hz hvalid o).trans
        (pbatch.ipaRelation_of_x4Current hξcur).1.symm))

open Polynomial in
open scoped ENNReal in
open Classical in
set_option maxHeartbeats 1000000 in
/-- The budgeted `runToSnark`-analogue on the computed path: `member_snark_of_instance`
(`Soundness.Compose67`) with the clean-opening branch routed through the budgeted witness tie, so
no member decode or quotient identity is hypothesised. On the clean-opening branch the budgeted
capstone produces the member SNARK relation (or a binding `HasNontrivialRelation`); on the
relation branch, the algebraic extraction's own `AlgebraicRelationWitness`. -/
noncomputable def member_snark_of_instance_budgeted
    {vk : VerifyingKey shape Fp VestaG} (p : AlgebraicWfProof basis vk) (ν : Fin 11 → Fp)
    (cert : AlgebraicDForkCert (F := Fp)
      (augmentedBasis (ursOfAugmentedBasis shape.k basis).g
        (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w) shape.k)
    (hz : ν 10 ≠ 0)
    (hvalid : DeployedForkValid (ursOfAugmentedBasis shape.k basis).g
      (evalVector shape.k (ν 7)) (ursOfAugmentedBasis shape.k basis).u
      (ursOfAugmentedBasis shape.k basis).w (ν 10)
      (commit (ursOfAugmentedBasis shape.k basis)
          (adjustedWitness (p.aMulti ν) p.s
            (multiopenValue vk p.proof.1 (chRecord ν (fun _ => 0))) (ν 9)) +
        (p.multiU ν + ν 9 * p.sU) • (ursOfAugmentedBasis shape.k basis).u +
        (p.multiBlind ν + ν 9 * p.sBlind) • (ursOfAugmentedBasis shape.k basis).w)
      cert.toDForkCert)
    {a₀ : Fin (2 ^ shape.k) → Fp}
    (pbatch : OpenedBatchOpenings (ursOfAugmentedBasis shape.k basis) (evalVector shape.k (ν 7))
      (x4BatchCommitments (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
        (chRecord ν (fun _ => 0)))
      (x4BatchEvals vk p.proof.1 (chRecord ν (fun _ => 0))) a₀ (p.multiU ν) (p.multiBlind ν))
    (hξcur : pbatch.batchChallenge pbatch.current
      = (chRecord ν (fun _ => 0) : Challenges shape.k Fp).x4)
    {numAdvice numInstance : ℕ}
    (adviceSet : Fin numAdvice → ℕ)
    (hadviceSet : ∀ j, adviceSet j
      < deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0)))
    (adviceMem : ∀ j : Fin numAdvice,
      Fin (deployedSetQueries vk p.proof.1 (chRecord ν (fun _ => 0)) (adviceSet j)).length)
    (instanceSet : Fin numInstance → ℕ)
    (hinstanceSet : ∀ j, instanceSet j
      < deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0)))
    (instanceMem : ∀ j : Fin numInstance,
      Fin (deployedSetQueries vk p.proof.1 (chRecord ν (fun _ => 0)) (instanceSet j)).length)
    (fixedCols : ℕ → Polynomial Fp) (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp)
    (hpoly : Polynomial Fp) (deg : ℕ)
    (hlen : ∀ i, i < deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0))
      → 0 < (deployedSetQueries vk p.proof.1 (chRecord ν (fun _ => 0)) i).length)
    (hprob1 : ∀ i, i < deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0)) →
      (((deployedSetQueries vk p.proof.1 (chRecord ν (fun _ => 0)) i).length - 1 : ℕ) : ℝ≥0∞)
          / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
            (OpenedX1Accept (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
              (chRecord ν (fun _ => 0)))))
    (hacc0 : DeployedAccepts (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
      (chRecord ν (fun _ => 0)))
    (pp : Fin shape.numProofs)
    (hadvLen : ∀ j : Fin numAdvice, (j : ℕ) < vk.adviceQueryLayout.length
      ∧ (j : ℕ) < (List.ofFn ((p.proof.1 : ProofString shape Fp VestaG).adviceEvals pp)).length)
    (hinstLen : ∀ j : Fin numInstance, (j : ℕ) < vk.instanceQueryLayout.length
      ∧ (j : ℕ) < (List.ofFn ((p.proof.1 : ProofString shape Fp VestaG).instanceEvals pp)).length)
    (b₂f : Fp → Fin (2 ^ shape.k) → Fp)
    (hJ : ∀ i, i < deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0)) →
      (((deployedSetQueries vk p.proof.1 (chRecord ν (fun _ => 0)) i).length - 1 : ℕ) : ℝ≥0∞)
          / Fintype.card Fp
        + (((deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0)) - 1 : ℕ) : ℝ≥0∞)
            / Fintype.card Fp
          + ((max (2 ^ shape.k)
                (deployedAllPts vk p.proof.1 (chRecord ν (fun _ => 0))).card
              + (deployedAllPts vk p.proof.1 (chRecord ν (fun _ => 0))).card : ℕ) : ℝ≥0∞)
            / Fintype.card Fp
          + (deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0)) : ℝ≥0∞)
            / Fintype.card Fp)
      < (PMF.uniformOfFintype (Fp × Fp × Fp × Fp)).toOuterMeasure
          (memberJointAccept (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
            (chRecord ν (fun _ => 0)) b₂f))
    (havoid : ∀ (ξv ζv χv : Fp),
      OpenedX3Accept (ursOfAugmentedBasis shape.k basis) rfl vk
        ((canonicalX2Run (ursOfAugmentedBasis shape.k basis) rfl vk
            ((canonicalX1Run (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
              (chRecord ν (fun _ => 0)) ξv).spliced p.proof.1)
            ((canonicalX1Run (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
              (chRecord ν (fun _ => 0)) ξv).challenges (chRecord ν (fun _ => 0)) ξv)
            (b₂f ξv) ζv).spliced
          ((canonicalX1Run (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
            (chRecord ν (fun _ => 0)) ξv).spliced p.proof.1))
        ((canonicalX2Run (ursOfAugmentedBasis shape.k basis) rfl vk
            ((canonicalX1Run (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
              (chRecord ν (fun _ => 0)) ξv).spliced p.proof.1)
            ((canonicalX1Run (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
              (chRecord ν (fun _ => 0)) ξv).challenges (chRecord ν (fun _ => 0)) ξv)
            (b₂f ξv) ζv).challenges
          ((canonicalX1Run (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
            (chRecord ν (fun _ => 0)) ξv).challenges (chRecord ν (fun _ => 0)) ξv) ζv)
        (evalVector shape.k χv) χv →
      ∀ k', χv ∉ deployedSetPts vk
        ((canonicalX1Run (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
          (chRecord ν (fun _ => 0)) ξv).spliced p.proof.1)
        ((canonicalX1Run (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
          (chRecord ν (fun _ => 0)) ξv).challenges (chRecord ν (fun _ => 0)) ξv) k')
    (hfold : (List.ofFn (fun i : Fin ng =>
        (gates i).eval
          (fun n => (fixedCols n).eval (chRecord ν (fun _ => 0) : Challenges shape.k Fp).x)
          (deployedClaimedFeed vk p.proof.1 (chRecord ν (fun _ => 0)) adviceSet adviceMem
            vk.adviceQueryLayout)
          (deployedClaimedFeed vk p.proof.1 (chRecord ν (fun _ => 0)) instanceSet instanceMem
            vk.instanceQueryLayout))).foldl
          (fun acc v => acc * y + v) 0
        = hpoly.eval (chRecord ν (fun _ => 0) : Challenges shape.k Fp).x
          * ((chRecord ν (fun _ => 0) : Challenges shape.k Fp).x ^ deg - 1))
    (hgood :
      combineGates fixedCols
        (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob (ursOfAugmentedBasis shape.k basis) rfl vk
            p.proof.1 (chRecord ν (fun _ => 0)) pbatch (adviceSet j)
            (hadviceSet j) (hlen _ (hadviceSet j)) (hprob1 _ (hadviceSet j)) hacc0).cols
              (adviceMem j))))
        (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob (ursOfAugmentedBasis shape.k basis) rfl vk
            p.proof.1 (chRecord ν (fun _ => 0)) pbatch (instanceSet j)
            (hinstanceSet j) (hlen _ (hinstanceSet j)) (hprob1 _ (hinstanceSet j)) hacc0).cols
              (instanceMem j))))
        y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols
        (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob (ursOfAugmentedBasis shape.k basis) rfl vk
            p.proof.1 (chRecord ν (fun _ => 0)) pbatch (adviceSet j)
            (hadviceSet j) (hlen _ (hadviceSet j)) (hprob1 _ (hadviceSet j)) hacc0).cols
              (adviceMem j))))
        (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob (ursOfAugmentedBasis shape.k basis) rfl vk
            p.proof.1 (chRecord ν (fun _ => 0)) pbatch (instanceSet j)
            (hinstanceSet j) (hlen _ (hinstanceSet j)) (hprob1 _ (hinstanceSet j)) hacc0).cols
              (instanceMem j))))
        y gates - hpoly * (X ^ deg - 1)).eval
          (chRecord ν (fun _ => 0) : Challenges shape.k Fp).x ≠ 0)
    (hadviceLayout : ∀ j : Fin numAdvice,
      (deployedSetCommIds vk p.proof.1 (chRecord ν (fun _ => 0)) (adviceSet j)).getD
          (adviceMem j : ℕ) CommitmentId.vanishingH
        = CommitmentId.adviceCol pp (vk.adviceQueryLayout.getD (j : ℕ) (0, 0)).1)
    (hinstanceLayout : ∀ j : Fin numInstance,
      (deployedSetCommIds vk p.proof.1 (chRecord ν (fun _ => 0)) (instanceSet j)).getD
          (instanceMem j : ℕ) CommitmentId.vanishingH
        = CommitmentId.instanceCol pp (vk.instanceQueryLayout.getD (j : ℕ) (0, 0)).1)
    (hquotCommitted : ∃ (hSet : ℕ)
        (hhSet : hSet < deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0)))
        (hMem : Fin (deployedSetQueries vk p.proof.1 (chRecord ν (fun _ => 0)) hSet).length),
      hpoly = coeffsToPoly ((openedMemberDecode_of_x1Prob (ursOfAugmentedBasis shape.k basis) rfl
          vk p.proof.1 (chRecord ν (fun _ => 0)) pbatch hSet hhSet
          (hlen _ hhSet) (hprob1 _ hhSet) hacc0).cols hMem) ∧
      (deployedSetCommIds vk p.proof.1 (chRecord ν (fun _ => 0)) hSet).getD (hMem : ℕ)
          CommitmentId.randomPoly = CommitmentId.vanishingH)
    {S : Prop}
    (hencodes : ∀ a,
      SnarkRelationWithMemberColumns (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
        (chRecord ν (fun _ => 0))
        (deployedCommitment (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
            (chRecord ν (fun _ => 0))
          - p.multiU ν • (ursOfAugmentedBasis shape.k basis).u
          - p.multiBlind ν • (ursOfAugmentedBasis shape.k basis).w)
        (evalVector shape.k (ν 7)) (multiopenValue vk p.proof.1 (chRecord ν (fun _ => 0)))
        pp adviceSet hadviceSet adviceMem instanceSet hinstanceSet instanceMem
        fixedCols y gates hpoly deg (p.multiU ν) (p.multiBlind ν) a → S) :
    (S ∨ HasNontrivialRelation (F := Fp) (ursOfAugmentedBasis shape.k basis).g
        (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w)
      ⊕' AlgebraicRelationWitness (F := Fp) basis :=
  match (deployedAlgebraicInstanceOfCert p ν cert hz hvalid).run with
  | PSum.inl o =>
      PSum.inl (member_relation_or_dlr_of_instance_budgeted p ν cert hz hvalid o pbatch hξcur
        adviceSet hadviceSet adviceMem instanceSet hinstanceSet instanceMem fixedCols y gates
        hpoly deg hlen hprob1 hacc0 pp hadvLen hinstLen b₂f hJ havoid hfold hgood
        hadviceLayout hinstanceLayout hquotCommitted hencodes)
  | PSum.inr rel => PSum.inr rel

open Polynomial in
open scoped ENNReal in
open Classical in
/-- **Deployed soundness on the computed path, extraction data derived.** The budgeted counterpart
of `orchard_verifier_sound_vesta_computed` (`Soundness.Compose67`): the same
`KnowledgeSoundness.SnarkRelation`-based `S` / `HasNontrivialRelation` / `AlgebraicRelationWitness`
trichotomy, but with the member decode constructed and the quotient identity derived — no
`mdec`/`hquot` hypothesis. What remains hypothesised: the deployed acceptance `hacc0`, the two
accept-measure floors (`hprob1` and the joint floor `hJ`), canonical-run sample avoidance, the
fingerprint surfaces `hfold`/`hgood`, the layout identities, the committed-quotient identity, and
the batch `pbatch` itself (an `x₄`-rewind output; producing it from bare acceptance is the open
composition surface recorded in `Soundness.Multiopen.Decode`). -/
noncomputable def orchard_verifier_sound_vesta_budgeted
    {vk : VerifyingKey shape Fp VestaG} (p : AlgebraicWfProof basis vk) (ν : Fin 11 → Fp)
    (cert : AlgebraicDForkCert (F := Fp)
      (augmentedBasis (ursOfAugmentedBasis shape.k basis).g
        (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w) shape.k)
    (hz : ν 10 ≠ 0)
    (hvalid : DeployedForkValid (ursOfAugmentedBasis shape.k basis).g
      (evalVector shape.k (ν 7)) (ursOfAugmentedBasis shape.k basis).u
      (ursOfAugmentedBasis shape.k basis).w (ν 10)
      (commit (ursOfAugmentedBasis shape.k basis)
          (adjustedWitness (p.aMulti ν) p.s
            (multiopenValue vk p.proof.1 (chRecord ν (fun _ => 0))) (ν 9)) +
        (p.multiU ν + ν 9 * p.sU) • (ursOfAugmentedBasis shape.k basis).u +
        (p.multiBlind ν + ν 9 * p.sBlind) • (ursOfAugmentedBasis shape.k basis).w)
      cert.toDForkCert)
    {a₀ : Fin (2 ^ shape.k) → Fp}
    (pbatch : OpenedBatchOpenings (ursOfAugmentedBasis shape.k basis) (evalVector shape.k (ν 7))
      (x4BatchCommitments (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
        (chRecord ν (fun _ => 0)))
      (x4BatchEvals vk p.proof.1 (chRecord ν (fun _ => 0))) a₀ (p.multiU ν) (p.multiBlind ν))
    (hξcur : pbatch.batchChallenge pbatch.current
      = (chRecord ν (fun _ => 0) : Challenges shape.k Fp).x4)
    {numAdvice numInstance : ℕ}
    (adviceSet : Fin numAdvice → ℕ)
    (hadviceSet : ∀ j, adviceSet j
      < deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0)))
    (adviceMem : ∀ j : Fin numAdvice,
      Fin (deployedSetQueries vk p.proof.1 (chRecord ν (fun _ => 0)) (adviceSet j)).length)
    (instanceSet : Fin numInstance → ℕ)
    (hinstanceSet : ∀ j, instanceSet j
      < deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0)))
    (instanceMem : ∀ j : Fin numInstance,
      Fin (deployedSetQueries vk p.proof.1 (chRecord ν (fun _ => 0)) (instanceSet j)).length)
    (fixedCols : ℕ → Polynomial Fp) (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp)
    (hpoly : Polynomial Fp) (deg : ℕ)
    (hlen : ∀ i, i < deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0))
      → 0 < (deployedSetQueries vk p.proof.1 (chRecord ν (fun _ => 0)) i).length)
    (hprob1 : ∀ i, i < deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0)) →
      (((deployedSetQueries vk p.proof.1 (chRecord ν (fun _ => 0)) i).length - 1 : ℕ) : ℝ≥0∞)
          / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
            (OpenedX1Accept (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
              (chRecord ν (fun _ => 0)))))
    (hacc0 : DeployedAccepts (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
      (chRecord ν (fun _ => 0)))
    (pp : Fin shape.numProofs)
    (hadvLen : ∀ j : Fin numAdvice, (j : ℕ) < vk.adviceQueryLayout.length
      ∧ (j : ℕ) < (List.ofFn ((p.proof.1 : ProofString shape Fp VestaG).adviceEvals pp)).length)
    (hinstLen : ∀ j : Fin numInstance, (j : ℕ) < vk.instanceQueryLayout.length
      ∧ (j : ℕ) < (List.ofFn ((p.proof.1 : ProofString shape Fp VestaG).instanceEvals pp)).length)
    (b₂f : Fp → Fin (2 ^ shape.k) → Fp)
    (hJ : ∀ i, i < deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0)) →
      (((deployedSetQueries vk p.proof.1 (chRecord ν (fun _ => 0)) i).length - 1 : ℕ) : ℝ≥0∞)
          / Fintype.card Fp
        + (((deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0)) - 1 : ℕ) : ℝ≥0∞)
            / Fintype.card Fp
          + ((max (2 ^ shape.k)
                (deployedAllPts vk p.proof.1 (chRecord ν (fun _ => 0))).card
              + (deployedAllPts vk p.proof.1 (chRecord ν (fun _ => 0))).card : ℕ) : ℝ≥0∞)
            / Fintype.card Fp
          + (deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0)) : ℝ≥0∞)
            / Fintype.card Fp)
      < (PMF.uniformOfFintype (Fp × Fp × Fp × Fp)).toOuterMeasure
          (memberJointAccept (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
            (chRecord ν (fun _ => 0)) b₂f))
    (havoid : ∀ (ξv ζv χv : Fp),
      OpenedX3Accept (ursOfAugmentedBasis shape.k basis) rfl vk
        ((canonicalX2Run (ursOfAugmentedBasis shape.k basis) rfl vk
            ((canonicalX1Run (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
              (chRecord ν (fun _ => 0)) ξv).spliced p.proof.1)
            ((canonicalX1Run (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
              (chRecord ν (fun _ => 0)) ξv).challenges (chRecord ν (fun _ => 0)) ξv)
            (b₂f ξv) ζv).spliced
          ((canonicalX1Run (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
            (chRecord ν (fun _ => 0)) ξv).spliced p.proof.1))
        ((canonicalX2Run (ursOfAugmentedBasis shape.k basis) rfl vk
            ((canonicalX1Run (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
              (chRecord ν (fun _ => 0)) ξv).spliced p.proof.1)
            ((canonicalX1Run (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
              (chRecord ν (fun _ => 0)) ξv).challenges (chRecord ν (fun _ => 0)) ξv)
            (b₂f ξv) ζv).challenges
          ((canonicalX1Run (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
            (chRecord ν (fun _ => 0)) ξv).challenges (chRecord ν (fun _ => 0)) ξv) ζv)
        (evalVector shape.k χv) χv →
      ∀ k', χv ∉ deployedSetPts vk
        ((canonicalX1Run (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
          (chRecord ν (fun _ => 0)) ξv).spliced p.proof.1)
        ((canonicalX1Run (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
          (chRecord ν (fun _ => 0)) ξv).challenges (chRecord ν (fun _ => 0)) ξv) k')
    (hfold : (List.ofFn (fun i : Fin ng =>
        (gates i).eval
          (fun n => (fixedCols n).eval (chRecord ν (fun _ => 0) : Challenges shape.k Fp).x)
          (deployedClaimedFeed vk p.proof.1 (chRecord ν (fun _ => 0)) adviceSet adviceMem
            vk.adviceQueryLayout)
          (deployedClaimedFeed vk p.proof.1 (chRecord ν (fun _ => 0)) instanceSet instanceMem
            vk.instanceQueryLayout))).foldl
          (fun acc v => acc * y + v) 0
        = hpoly.eval (chRecord ν (fun _ => 0) : Challenges shape.k Fp).x
          * ((chRecord ν (fun _ => 0) : Challenges shape.k Fp).x ^ deg - 1))
    (hgood :
      combineGates fixedCols
        (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob (ursOfAugmentedBasis shape.k basis) rfl vk
            p.proof.1 (chRecord ν (fun _ => 0)) pbatch (adviceSet j)
            (hadviceSet j) (hlen _ (hadviceSet j)) (hprob1 _ (hadviceSet j)) hacc0).cols
              (adviceMem j))))
        (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob (ursOfAugmentedBasis shape.k basis) rfl vk
            p.proof.1 (chRecord ν (fun _ => 0)) pbatch (instanceSet j)
            (hinstanceSet j) (hlen _ (hinstanceSet j)) (hprob1 _ (hinstanceSet j)) hacc0).cols
              (instanceMem j))))
        y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols
        (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob (ursOfAugmentedBasis shape.k basis) rfl vk
            p.proof.1 (chRecord ν (fun _ => 0)) pbatch (adviceSet j)
            (hadviceSet j) (hlen _ (hadviceSet j)) (hprob1 _ (hadviceSet j)) hacc0).cols
              (adviceMem j))))
        (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob (ursOfAugmentedBasis shape.k basis) rfl vk
            p.proof.1 (chRecord ν (fun _ => 0)) pbatch (instanceSet j)
            (hinstanceSet j) (hlen _ (hinstanceSet j)) (hprob1 _ (hinstanceSet j)) hacc0).cols
              (instanceMem j))))
        y gates - hpoly * (X ^ deg - 1)).eval
          (chRecord ν (fun _ => 0) : Challenges shape.k Fp).x ≠ 0)
    (hadviceLayout : ∀ j : Fin numAdvice,
      (deployedSetCommIds vk p.proof.1 (chRecord ν (fun _ => 0)) (adviceSet j)).getD
          (adviceMem j : ℕ) CommitmentId.vanishingH
        = CommitmentId.adviceCol pp (vk.adviceQueryLayout.getD (j : ℕ) (0, 0)).1)
    (hinstanceLayout : ∀ j : Fin numInstance,
      (deployedSetCommIds vk p.proof.1 (chRecord ν (fun _ => 0)) (instanceSet j)).getD
          (instanceMem j : ℕ) CommitmentId.vanishingH
        = CommitmentId.instanceCol pp (vk.instanceQueryLayout.getD (j : ℕ) (0, 0)).1)
    (hquotCommitted : ∃ (hSet : ℕ)
        (hhSet : hSet < deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0)))
        (hMem : Fin (deployedSetQueries vk p.proof.1 (chRecord ν (fun _ => 0)) hSet).length),
      hpoly = coeffsToPoly ((openedMemberDecode_of_x1Prob (ursOfAugmentedBasis shape.k basis) rfl
          vk p.proof.1 (chRecord ν (fun _ => 0)) pbatch hSet hhSet
          (hlen _ hhSet) (hprob1 _ hhSet) hacc0).cols hMem) ∧
      (deployedSetCommIds vk p.proof.1 (chRecord ν (fun _ => 0)) hSet).getD (hMem : ℕ)
          CommitmentId.randomPoly = CommitmentId.vanishingH)
    {S : Prop}
    (hencodes : ∀ (a : Fin (2 ^ shape.k) → Fp)
        (bo : OpenedBatchOpenings (ursOfAugmentedBasis shape.k basis) (evalVector shape.k (ν 7))
          (x4BatchCommitments (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
            (chRecord ν (fun _ => 0)))
          (x4BatchEvals vk p.proof.1 (chRecord ν (fun _ => 0))) a (p.multiU ν) (p.multiBlind ν))
        (md : ∀ i (hi : i < deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0))),
          OpenedMemberDecode (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
            (chRecord ν (fun _ => 0)) bo i hi),
      SnarkRelation (ursOfAugmentedBasis shape.k basis)
        (deployedCommitment (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
            (chRecord ν (fun _ => 0))
          - p.multiU ν • (ursOfAugmentedBasis shape.k basis).u
          - p.multiBlind ν • (ursOfAugmentedBasis shape.k basis).w)
        (evalVector shape.k (ν 7)) (multiopenValue vk p.proof.1 (chRecord ν (fun _ => 0)))
        (circuitSatViaGates fixedCols
          (fun _ => rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
            coeffsToPoly ((md (adviceSet j) (hadviceSet j)).cols (adviceMem j))))
          (fun _ => rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
            coeffsToPoly ((md (instanceSet j) (hinstanceSet j)).cols (instanceMem j))))
          y gates hpoly deg) a → S) :
    (S ∨ HasNontrivialRelation (F := Fp) (ursOfAugmentedBasis shape.k basis).g
        (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w)
      ⊕' AlgebraicRelationWitness (F := Fp) basis :=
  member_snark_of_instance_budgeted p ν cert hz hvalid pbatch hξcur adviceSet hadviceSet adviceMem
    instanceSet hinstanceSet instanceMem fixedCols y gates hpoly deg hlen hprob1 hacc0 pp
    hadvLen hinstLen b₂f hJ havoid hfold hgood hadviceLayout hinstanceLayout hquotCommitted
    (S := S)
    (fun a hmem => hencodes a hmem.batchOpenings hmem.memberDecode
      (snarkRelation_of_memberColumns hmem))

end Zcash.Snark
