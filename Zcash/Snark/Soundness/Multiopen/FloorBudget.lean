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

/-- **The x₃-squeeze floor-failure bound.** `squeeze_floor_failure_le` at `OpenedX3Accept` and an
arbitrary threshold `t` (the terminal instantiates `t := (max (2 ^ k) |allPts| + |allPts|)/|Fp|`,
the `hprob3` floor threshold): over the fresh x₃ challenge the deployed run accepting while the x₃
rewind accept-measure sits at or below `t` has probability `≤ t`. Same template as
`openedX4_floor_failure_le`. -/
theorem openedX3_floor_failure_le [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) (b : Fin (2 ^ urs.k) → Fp)
    (t : ℝ≥0∞) :
    (PMF.uniformOfFintype Fp).toOuterMeasure
        {χ : Fp | OpenedX3Accept urs hk vk ps ch b χ ∧
          ¬ (t < (PMF.uniformOfFintype Fp).toOuterMeasure
                  (Finset.univ.filter (OpenedX3Accept urs hk vk ps ch b)))}
      ≤ t :=
  squeeze_floor_failure_le (OpenedX3Accept urs hk vk ps ch b) t

/-- **The x₂-squeeze floor-failure bound.** `squeeze_floor_failure_le` at `OpenedX2Accept` and an
arbitrary threshold `t` (the terminal instantiates `t := (deployedX4PairCount - 1)/|Fp|`, the `hx2`
floor threshold). Same template as `openedX4_floor_failure_le`. -/
theorem openedX2_floor_failure_le [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) (b : Fin (2 ^ urs.k) → Fp)
    (t : ℝ≥0∞) :
    (PMF.uniformOfFintype Fp).toOuterMeasure
        {χ : Fp | OpenedX2Accept urs hk vk ps ch b χ ∧
          ¬ (t < (PMF.uniformOfFintype Fp).toOuterMeasure
                  (Finset.univ.filter (OpenedX2Accept urs hk vk ps ch b)))}
      ≤ t :=
  squeeze_floor_failure_le (OpenedX2Accept urs hk vk ps ch b) t

/-- **The x₁-squeeze floor-failure bound.** `squeeze_floor_failure_le` at `OpenedX1Accept` (which
carries no blinder argument) and an arbitrary threshold `t` (the terminal instantiates
`t := ((deployedSetQueries vk ps ch i).length - 1)/|Fp|`, the per-set `hprob1` floor threshold).
Same template as `openedX4_floor_failure_le`. -/
theorem openedX1_floor_failure_le [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) (t : ℝ≥0∞) :
    (PMF.uniformOfFintype Fp).toOuterMeasure
        {χ : Fp | OpenedX1Accept urs hk vk ps ch χ ∧
          ¬ (t < (PMF.uniformOfFintype Fp).toOuterMeasure
                  (Finset.univ.filter (OpenedX1Accept urs hk vk ps ch)))}
      ≤ t :=
  squeeze_floor_failure_le (OpenedX1Accept urs hk vk ps ch) t

/-- **Nested single-squeeze floor-failure bound (the Fubini composition primitive).** For a family
of single-slot accept predicates `acc b : Fp → Prop` indexed by an outer `Fintype` base `b : B`,
the failure event "the inner run accepts at its fresh slot `x.1` while the inner accept-measure at
that base sits `≤ t`" has probability `≤ t` over the *joint* draw of the inner slot and the outer
base.

This is the crux of whether option-(b) composes: at each fixed outer base `b`, the inner
accept-measure `measure(filter (acc b))` is a constant in the inner slot `x.1`, so
`squeeze_floor_failure_le (acc b) t` bounds the fiber by `t`; `uniformOfFintype_prod_fiber_bound`
then lifts the uniform per-fiber bound to the product. The inner threshold condition never depends
on the inner slot, so no `x.1`-dependence leaks across the lift — the nested `Fubini` is clean. The
deployed squeezes instantiate `acc := OpenedX{2,3,4}Accept` at the base produced by the outer
sampled challenges (via the `reprogramX*` run-determination), with `B` the outer challenge product
`Fp`, `Fp × Fp`, `Fp × Fp × Fp`. -/
theorem nested_squeeze_floor_failure_le {B : Type*} [Fintype B] [Nonempty B]
    (acc : B → Fp → Prop) (t : ℝ≥0∞) :
    (PMF.uniformOfFintype (Fp × B)).toOuterMeasure
        {x : Fp × B | acc x.2 x.1 ∧
          ¬ (t < (PMF.uniformOfFintype Fp).toOuterMeasure
                  (Finset.univ.filter (acc x.2)))}
      ≤ t :=
  uniformOfFintype_prod_fiber_bound
    (fun b => {χ : Fp | acc b χ ∧
        ¬ (t < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter (acc b)))})
    (fun b => squeeze_floor_failure_le (acc b) t)

/-- **Nested single-squeeze floor-failure bound, base-first orientation.** The mirror of
`nested_squeeze_floor_failure_le` for when the outer base is the *first* product coordinate and the
fresh inner slot is the *second* — the shape a squeeze takes when the challenges sampled before it
are packaged on the left. Same composition, via `uniformOfFintype_prod_fiber_bound_right`. -/
theorem nested_squeeze_floor_failure_le_right {A : Type*} [Fintype A] [Nonempty A]
    (acc : A → Fp → Prop) (t : ℝ≥0∞) :
    (PMF.uniformOfFintype (A × Fp)).toOuterMeasure
        {x : A × Fp | acc x.1 x.2 ∧
          ¬ (t < (PMF.uniformOfFintype Fp).toOuterMeasure
                  (Finset.univ.filter (acc x.1)))}
      ≤ t :=
  uniformOfFintype_prod_fiber_bound_right
    (fun a => {χ : Fp | acc a χ ∧
        ¬ (t < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter (acc a)))})
    (fun a => squeeze_floor_failure_le (acc a) t)

/-- **Two-squeeze combined floor-failure budget (the union composes).** Over the joint draw of an
outer challenge (`x.1`) and an inner challenge (`x.2`), the probability that *either* the outer
floor fails (outer accepts but its accept-measure `≤ t₁`) *or* the inner floor fails at the base the
outer challenge determines (inner accepts but its accept-measure `≤ t₂`) is `≤ t₁ + t₂` — the sum of
the two thresholds.

This is the smallest faithful instance of the combined multiopen budget: it shows the per-squeeze
floor-failure bounds (`nested_squeeze_floor_failure_le` for the outer, `_right` for the inner-at-
outer-base) union additively on a *shared* sampling space with no cross term — exactly the
`measure_union_le`-then-`add_le_add` step the full x₁/x₂/x₃/x₄ budget iterates. The four-squeeze
budget is this same union over the nested challenge product; the only additional work is the
product-association reindexing that routes each squeeze's fresh slot to the coordinate its fiber
bound consumes (no further soundness content — the nested Fubini already composes cleanly here). -/
theorem combined_two_floor_failure_le (acc₁ : Fp → Prop) (acc₂ : Fp → Fp → Prop)
    (t₁ t₂ : ℝ≥0∞) :
    (PMF.uniformOfFintype (Fp × Fp)).toOuterMeasure
        ({x : Fp × Fp | acc₁ x.1 ∧
            ¬ (t₁ < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter acc₁))}
          ∪ {x : Fp × Fp | acc₂ x.1 x.2 ∧
            ¬ (t₂ < (PMF.uniformOfFintype Fp).toOuterMeasure
                    (Finset.univ.filter (acc₂ x.1)))})
      ≤ t₁ + t₂ := by
  refine le_trans (MeasureTheory.measure_union_le _ _) (add_le_add ?_ ?_)
  · exact nested_squeeze_floor_failure_le (fun _ : Fp => acc₁) t₁
  · exact nested_squeeze_floor_failure_le_right acc₂ t₂

end Zcash.Snark
