import Zcash.Snark.Soundness.Multiopen.Opened
import Zcash.Snark.Soundness.Forking.Probability

/-!
# Multiopen floor-failure budget (option-(b), stage 1)

The deployed multiopen value check (`Soundness.Multiopen.ValueCheckX3`, `Soundness.Vesta`) consumes
forking-floor premises `hprob*` of the shape `threshold < measure(accept over the fresh Fp
challenge)` — one per squeeze `x₁`/`x₂`/`x₃`/`x₄`. Each such floor is a lower bound on the deployed
verifier's accept fraction over the single fresh uniform `Fp` challenge that squeeze reprograms
(`Soundness.Forking.reprogramX{1,2,3,4}`, `Soundness.Forking.Rewind`); the honest run witnesses it,
and `exists_injective_accepting_of_measure` turns it into the rewind samples the extraction spends.

This module bounds the *failure* of each floor. Over that single fresh slot, the event "the
deployed run accepts yet the accept-measure sits at or below the threshold" — the negation of the
floor — has probability `≤ threshold` (`squeeze_floor_failure_le`, the failure-side complement of
the counting floor). Specialised to the deployed x₄ predicate this is `openedX4_floor_failure_le`,
the template the other three squeezes reuse verbatim. These per-squeeze failure bounds are the
building blocks of the combined soundness budget (their nested `Fubini` union removes the floor
hypotheses from the computed soundness endpoint).
-/

namespace Zcash.Snark

open scoped ENNReal
open Classical

/-- **Single-squeeze floor-failure bound.** For any single-`Fp`-slot accept predicate `acc` and
threshold `t`, the event "`acc χ` holds but the accept-measure is `≤ t`" — exactly the negation of
the `hprob` floor `t < measure(filter acc)` — has probability `≤ t`. Immediate from
`uniformOfFintype_accept_below_threshold_le` (the threshold condition is `χ`-independent). This is
the reusable core each multiopen squeeze instantiates at its own accept predicate and threshold. -/
theorem squeeze_floor_failure_le (acc : Fp → Prop) [DecidablePred acc] (t : ℝ≥0∞) :
    (PMF.uniformOfFintype Fp).toOuterMeasure
        {χ : Fp | acc χ ∧
          ¬ (t < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter acc))}
      ≤ t := by
  simp only [not_lt]
  exact uniformOfFintype_accept_below_threshold_le acc t

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- **The x₄-squeeze floor-failure bound.** `squeeze_floor_failure_le` at the deployed x₄ accept
predicate `OpenedX4Accept` and threshold `deployedX4PairCount / |Fp|`: over the fresh x₄ challenge
`ξ`, the deployed run accepting while the x₄ rewind accept-measure sits at or below the extraction
threshold — the negation of the terminal's `hprob4` floor — has probability
`≤ deployedX4PairCount / |Fp|`, negligible. `OpenedX4Accept urs hk vk ps ch b : Fp → Prop` is
already the single-slot predicate over the x₄ challenge (its last argument), so this is a direct
instantiation; the x₃/x₂/x₁ squeezes follow the same template at `OpenedX3/X2/X1Accept` and their
own thresholds. -/
theorem openedX4_floor_failure_le [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) (b : Fin (2 ^ urs.k) → Fp) :
    (PMF.uniformOfFintype Fp).toOuterMeasure
        {ξ : Fp | OpenedX4Accept urs hk vk ps ch b ξ ∧
          ¬ ((deployedX4PairCount vk ps ch : ℝ≥0∞) / Fintype.card Fp
              < (PMF.uniformOfFintype Fp).toOuterMeasure
                  (Finset.univ.filter (OpenedX4Accept urs hk vk ps ch b)))}
      ≤ (deployedX4PairCount vk ps ch : ℝ≥0∞) / Fintype.card Fp :=
  squeeze_floor_failure_le (OpenedX4Accept urs hk vk ps ch b) _

end Zcash.Snark
