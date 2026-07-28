import Zcash.Snark.Soundness.Composition.ActionBudget

/-!
# Shape budget for rewind-free algebraic multiopen roots

The AGM decoder exposes one bad-root event at each deployed multiopen squeeze.  A deliberately
conservative shape-only union bound charges:

* `numPointSets * queryBudget^2` for all `x1` member-at-node identities;
* `numPointSets * queryBudget` for all `x2` set-at-node identities;
* `max (2^k) queryBudget + 2 * queryBudget` for the cleared `x3` identity and collisions;
* `numPointSets + 1` for the `x4` value batch; and
* two linear roots for the recursive IPA `xi`/`z` value shift.

Unlike `actionBudget`, this is a sum of direct root budgets, not a joint-event threshold that must
be fourth-rooted.  The square is intentionally loose but remains negligible at the deployed
parameters and keeps the theorem independent of layout-specific sharing facts.
-/

namespace Zcash.Snark

open scoped ENNReal

/-- A shape-only upper bound for the sum of all pinned AGM root events. -/
noncomputable def algebraicRootBudget (shape : Shape) (k' : Nat) : ENNReal :=
  ((shape.numPointSets * queryBudget shape * queryBudget shape
      + shape.numPointSets * queryBudget shape
      + max (2 ^ k') (queryBudget shape)
      + 2 * queryBudget shape
      + shape.numPointSets + 3 : Nat) : ENNReal) /
    Fintype.card Fp

/-- The algebraic-root budget is monotone in the action count and point-set count when the other
query dimensions are fixed.  This is the linkage needed to use the consensus-maximum captured
shape as an upper bound for every smaller consensus-valid bundle. -/
theorem algebraicRootBudget_mono {shape shape' : Shape} (k' : Nat)
    (hnp : shape.numProofs ≤ shape'.numProofs)
    (hiq : shape.numInstanceQueries = shape'.numInstanceQueries)
    (haq : shape.numAdviceQueries = shape'.numAdviceQueries)
    (hps : shape.numPermutationSets = shape'.numPermutationSets)
    (hlk : shape.numLookups = shape'.numLookups)
    (hfq : shape.numFixedQueries = shape'.numFixedQueries)
    (hpc : shape.numPermutationColumns = shape'.numPermutationColumns)
    (hpts : shape.numPointSets ≤ shape'.numPointSets) :
    algebraicRootBudget shape k' ≤ algebraicRootBudget shape' k' := by
  have hqb := queryBudget_mono hnp hiq haq hps hlk hfq hpc
  rw [algebraicRootBudget, algebraicRootBudget]
  gcongr

end Zcash.Snark
