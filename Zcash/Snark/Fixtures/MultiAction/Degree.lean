import Zcash.Snark.Fixtures.MultiAction.Fixture
import Zcash.Snark.Soundness.DegreeWalk

/-!
# The captured verifying key's degree budget

The `x`-squeeze schedule constructor (`deployedConstraintXSqueezeSchedule_of_pinned`) takes the
verifying key's degree arithmetic as `ℕ` hypotheses. This module evaluates them at the captured
Post-NU6.3 key.

Take `B = 2047`, which is both the opening degree `2¹¹ − 1` and the selector degree `n − 1`. Every
gate then has `degreeBound ≤ 9`, every permutation chunk width `≤ 7`, and every lookup expression
compresses at `degreeBound ≤ 4`, so the single literal `D = Dq = 20470` dominates every family and
the bad-set term is `(Q + 1) · 20470 / |𝔽|`.
-/

namespace Zcash.Snark.Fixture2

open Zcash.Snark

/-- Every gate of the captured key clears the cap: `degreeBound · 2047 ≤ 20470`
(the largest gate has `degreeBound = 9`). -/
theorem vk_gates_degree_le : ∀ e ∈ vk.gates, e.degreeBound * 2047 ≤ 20470 := by
  native_decide

/-- Every permutation chunk of the captured key has width at most `7` (the chunk length). -/
theorem vk_chunk_width_le : ∀ c ∈ vk.permutationChunks, c.length ≤ 7 := by
  native_decide

/-- Every lookup input expression clears the compression cap (`degreeBound ≤ 4`). -/
theorem vk_lookup_input_degree_le : ∀ l : Fin shape.numLookups,
    ∀ e ∈ vk.lookupInputExprs l, e.degreeBound * 2047 ≤ 8188 := by
  native_decide

/-- Every lookup table expression clears the compression cap (`degreeBound ≤ 1`). -/
theorem vk_lookup_table_degree_le : ∀ l : Fin shape.numLookups,
    ∀ e ∈ vk.lookupTableExprs l, e.degreeBound * 2047 ≤ 8188 := by
  native_decide

/-- The quotient tail of the captured key: `n·d + (2^k − 1) = 2048·8 + 2047 = 18431 ≤ 20470`. -/
theorem vk_quotient_tail_le :
    vk.n * shape.numQuotientPieces + (2 ^ shape.k - 1) ≤ 20470 := by
  native_decide

/-- The selector degree of the captured key: `n − 1 ≤ 2047`. -/
theorem vk_n_pred_le : vk.n - 1 ≤ 2047 := by
  native_decide

/-- The opening degree of the captured key: `2^k − 1 ≤ 2047`. -/
theorem shape_k_pred_le : 2 ^ shape.k - 1 ≤ 2047 := by
  native_decide

end Zcash.Snark.Fixture2
