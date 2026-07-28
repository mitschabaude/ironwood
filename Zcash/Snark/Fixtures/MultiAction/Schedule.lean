import Zcash.Snark.Fixtures.MultiAction.Degree
import Zcash.Snark.Fixtures.MultiAction.StaticChecks
import Zcash.Snark.Soundness.Composition.ScheduleBudget

/-!
# The `x`-squeeze schedule at the captured key

`deployedConstraintXSqueezeSchedule_of_pinned` prices the constraint-difference root set from the
verifying key's degree caps. This module discharges those caps at the captured Post-NU6.3 key
(`Fixtures.MultiAction.Degree`): with `B = 2047`, `W = 7`, `Dc = 8188` and `D = Dq = 20470` every
cap holds, so `epsilonX` is the concrete `20470 / |𝔽|` for any family with the captured key
profile.

Exact leave-one-`x` invariance comes from the family's staged trace; later unbatching challenges
stay free.
-/

namespace Zcash.Snark.Fixture2

open Zcash.Snark
open scoped ENNReal

/-- **The `x`-squeeze schedule at the captured key.** The degree caps are discharged from the
captured verifying key, so `epsilonX` is the concrete `20470 / |𝔽|`. -/
noncomputable def deployedConstraintXSqueezeSchedule_captured
    (family : ComputedDeployedConstraintFSFamily shape)
    (hvk : ∀ basis, CapturedVerifierKeyProfile (family.vk basis)) :
    DeployedConstraintXSqueezeSchedule family.toRootFamily
      ((20470 : ℕ) / (Fintype.card Fp : ℝ≥0∞)) := by
  have hk : 2 ^ shape.k - 1 = 2047 := by norm_num [shape]
  have h := deployedConstraintXSqueezeSchedule_of_pinned family.toRootFamily
    (B := 2047) (W := 7) (Dc := 8188) (D := 20470) (Dq := 20470)
    (by norm_num) shape_k_pred_le
    (fun basis => by rw [(hvk basis).n]; exact vk_n_pred_le)
    (fun basis => by rw [(hvk basis).gates]; exact vk_gates_degree_le)
    (fun basis => by rw [(hvk basis).permutationChunks]; exact vk_chunk_width_le)
    (fun basis => by rw [(hvk basis).lookupInputExprs]; exact vk_lookup_input_degree_le)
    (fun basis => by rw [(hvk basis).lookupTableExprs]; exact vk_lookup_table_degree_le)
    (fun basis => by rw [(hvk basis).n, ← hk]; exact vk_quotient_tail_le)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) family.pinnedX
  simpa using h

end Zcash.Snark.Fixture2
