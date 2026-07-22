import Mathlib
import Zcash.Snark.Soundness.Multiopen.ValueCheck
import Zcash.Snark.Soundness.Multiopen.Deployed
import Zcash.Snark.Soundness.Multiopen.Opened

/-!
# The deployed grouping data for the value check

`Soundness.Multiopen.ValueCheck` proved the un-batching core over abstract fixed data. This module
supplies the *deployed* grouping it is instantiated at: the point sets `deployedSetPts` and their
union `deployedAllPts` come from `constructIntermediateSets (assembleQueries vk ps ch)`, and each
set's points sit inside the union (`deployedSetPts_subset`). The instantiation itself is
`deployed_node_binding_of_grid` (`Soundness.Multiopen.ValueCheckX3`), which feeds
`node_binding_of_samples` the run openings acceptance actually supplies; `deployedAllPts`'s
cardinality is also the `x₃` floor threshold of the derived capstone and the floor budget. The
query-point membership bridge `deployed_query_point_mem` and the member↔aggregate eval bridge
`member_aggregate_eval_bridge` below are the grouping-side facts that chain consumes.
-/

namespace Zcash.Snark

open Polynomial

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- The points of deployed point set `j`, as a finite set. -/
noncomputable def deployedSetPts [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (j : ℕ) : Finset Fp :=
  ((constructIntermediateSets (assembleQueries vk ps ch)).points.getD j []).toFinset

/-- The union of all the deployed point sets — the roots of the vanishing polynomial `D`. -/
noncomputable def deployedAllPts [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) :
    Finset Fp :=
  (Finset.range (constructIntermediateSets (assembleQueries vk ps ch)).points.length).biUnion
    (fun j => deployedSetPts vk ps ch j)

/-- Each deployed point set sits inside the union of all points. -/
theorem deployedSetPts_subset [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (j : ℕ) : deployedSetPts vk ps ch j ⊆ deployedAllPts vk ps ch := by
  rcases lt_or_ge j (constructIntermediateSets (assembleQueries vk ps ch)).points.length
    with hj | hj
  · exact Finset.subset_biUnion_of_mem _ (Finset.mem_range.mpr hj)
  · rw [deployedSetPts, List.getD_eq_default _ _ hj]
    simp

/-- **F1: the member↔aggregate `x₁` bridge (eval form).** The `x₄`-slot aggregate column for point set
`i` (`openedDecodedCols` at batch position `count − 1 − i`) evaluated at any `node` is the
`ch.x1`-power fold of its decoded member columns' evaluations. Immediate from the member decode's
`reconstruct` field and `commitGen`'s linearity (`coeffsToPoly_eval` both ways). This is the algebraic
link the x₁ un-batch (F2) runs over. -/
theorem member_aggregate_eval_bridge [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {b a : Fin (2 ^ urs.k) → Fp} {pU pW : Fp}
    (pbatch : OpenedBatchOpenings urs b (x4BatchCommitments urs hk vk ps ch)
      (x4BatchEvals vk ps ch) a pU pW)
    (i : ℕ) (hi : i < deployedX4PairCount vk ps ch)
    (md : OpenedMemberDecode urs hk vk ps ch pbatch i hi) (node : Fp) :
    (openedDecodedCols pbatch ⟨deployedX4PairCount vk ps ch - 1 - i, by omega⟩).eval node
      = ∑ m : Fin (deployedSetQueries vk ps ch i).length,
          ch.x1 ^ (m : ℕ) * (coeffsToPoly (md.cols m)).eval node := by
  rw [openedDecodedCols, coeffsToPoly_eval, md.reconstruct, commitGen_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [commitGen_smul_left, ← coeffsToPoly_eval, smul_eq_mul]

/-- **F4 (deployed): a routed query's point is one of its set's points.** The deployed specialization
of `constructIntermediateSets_point_mem`: if `q` is one of the verifier's opening queries and its
commitment slot names member `m` of deployed point set `si` (`deployedSetCommIds`), then `q`'s
opening point lies in `deployedSetPts vk ps ch si`. This is the bridge the layout hypotheses
(`hadviceLayout`/`hinstanceLayout`) feed the value check: it turns the member's slot identity into
the rotated query point being a genuine node of the set, so the per-set node binding applies there. -/
theorem deployed_query_point_mem [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {q : VerifierQuery shape.k Fp G} (hq : q ∈ assembleQueries vk ps ch)
    {si m : ℕ} {d₀ : CommitmentId}
    (hlt : m < (deployedSetCommIds vk ps ch si).length)
    (hid : (deployedSetCommIds vk ps ch si).getD m d₀ = q.commId) :
    q.point ∈ deployedSetPts vk ps ch si := by
  simp only [deployedSetCommIds] at hlt hid
  rw [deployedSetPts, List.mem_toFinset]
  exact constructIntermediateSets_point_mem (assembleQueries vk ps ch) hq hlt hid

end Zcash.Snark
