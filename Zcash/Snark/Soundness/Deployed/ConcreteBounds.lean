import Zcash.Arithmetic
import Zcash.Snark.Soundness.Forking.KnowledgeError

/-!
# Concrete fork-tree knowledge error over the deployed Orchard parameters

Orchard is a single deployed protocol, not an asymptotic family: the verifier runs over the fixed
field `F_p` (`Fintype.card Fp = scalarFieldOrder = PALLAS_BASE_CARD ≈ 2²⁵⁴`) with the captured shape,
whose IPA recursion depth is `k = 11`. This module reads the fork-tree knowledge error off the
deployed parameters as a concrete number.

The `Soundness.Vesta` capstones state their acceptance hypothesis directly against the concrete floor
`3·k/|F_p|` (using `kerr_div_card` to relate it to the recursive `Forking.Tree.kerr` count). This
module records what that floor evaluates to:

* `deployed_forking_knowledge_error` — at any IPA depth `k`, the fork-tree threshold
  `(kerr |F_p| k)/|F_p|ᵏ` equals `3·k/|F_p|`.
* `deployed_forking_knowledge_error_captured` — at the captured Orchard depth `k = 11` it is
  `33/scalarFieldOrder`. With `scalarFieldOrder ≈ 2²⁵⁴` this is `≈ 2⁻²⁴⁹`.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (card_Fp scalarFieldOrder)

open scoped ENNReal

/-- **The deployed fork-tree knowledge error is exactly `3k/|F_p|`.** At any IPA depth `k` the
threshold the Vesta forking capstones compare the accept probability against,
`(kerr |F_p| k)/|F_p|ᵏ`, is the concrete fraction `3·k/|F_p|`. Specialisation of `kerr_div_card` to
the deployed field `F_p`. -/
theorem deployed_forking_knowledge_error (k : ℕ) :
    (kerr (Fintype.card Fp) k : ℝ≥0∞) / Fintype.card (Fin k → Fp)
      = 3 * k / Fintype.card Fp :=
  kerr_div_card (α := Fp) k

/-- The deployed floor at the **captured Orchard depth** `k = 11`: `33/scalarFieldOrder`. Since
`scalarFieldOrder = PALLAS_BASE_CARD ≈ 2²⁵⁴`, this is `≈ 2⁻²⁴⁹` — the concrete soundness error the
fork-tree extraction charges, over the actual deployed parameters. -/
theorem deployed_forking_knowledge_error_captured :
    (kerr (Fintype.card Fp) 11 : ℝ≥0∞) / Fintype.card (Fin 11 → Fp)
      = 33 / (scalarFieldOrder : ℝ≥0∞) := by
  rw [deployed_forking_knowledge_error, card_Fp]
  norm_num

end Zcash.Snark
