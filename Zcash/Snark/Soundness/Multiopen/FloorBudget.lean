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

/-- **Equiv-invariance of the uniform outer measure.** A measure-preserving relabelling of a finite
sample space leaves the uniform outer measure of a set unchanged: `μ_α (e ⁻¹' T) = μ_β T`. Both
sides are `Nat.card / card`, and an `Equiv` preserves both the numerator (it restricts to a
bijection `e ⁻¹' T ≃ T`) and the denominator (`Fintype.card_congr`). This is what lets each squeeze
route its fresh challenge slot to the coordinate its fiber bound consumes. -/
theorem uniformOfFintype_toOuterMeasure_preimage_equiv {α β : Type*}
    [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] (e : α ≃ β) (T : Set β) :
    (PMF.uniformOfFintype α).toOuterMeasure (e ⁻¹' T)
      = (PMF.uniformOfFintype β).toOuterMeasure T := by
  rw [uniformOfFintype_toOuterMeasure_set, uniformOfFintype_toOuterMeasure_set,
      Fintype.card_congr e]
  congr 1
  exact_mod_cast Nat.card_congr (e.subtypeEquiv (fun _ => Iff.rfl))

/-- **Reindexed single-squeeze floor-failure bound.** `nested_squeeze_floor_failure_le` transported
along a relabelling `e : W ≃ Fp × B` of the full sample space that names the squeeze's fresh slot as
the first coordinate `(e w).1` and its base as `(e w).2`. The failure set is `e ⁻¹'` the primitive's
set, so `uniformOfFintype_toOuterMeasure_preimage_equiv` reduces the bound to the primitive. This is
the general tool the four-squeeze budget applies once per squeeze. -/
theorem floor_failure_reindex_le {W B : Type*} [Fintype W] [Nonempty W] [Fintype B] [Nonempty B]
    (e : W ≃ Fp × B) (acc : B → Fp → Prop) (t : ℝ≥0∞) :
    (PMF.uniformOfFintype W).toOuterMeasure
        {w : W | acc (e w).2 (e w).1 ∧
          ¬ (t < (PMF.uniformOfFintype Fp).toOuterMeasure
                  (Finset.univ.filter (acc (e w).2)))}
      ≤ t := by
  have hset : {w : W | acc (e w).2 (e w).1 ∧
        ¬ (t < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter (acc (e w).2)))}
      = e ⁻¹' {x : Fp × B | acc x.2 x.1 ∧
          ¬ (t < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter (acc x.2)))} := rfl
  rw [hset, uniformOfFintype_toOuterMeasure_preimage_equiv e]
  exact nested_squeeze_floor_failure_le acc t

/-- Relabelling routing the x₂ challenge to the fiber's first coordinate, its predecessors to the
base. -/
def reindexX2 : (Fp × Fp × Fp × Fp) ≃ Fp × (Fp × Fp × Fp) :=
  ⟨fun w => (w.2.1, w.1, w.2.2.1, w.2.2.2), fun p => (p.2.1, p.1, p.2.2.1, p.2.2.2),
    fun _ => rfl, fun _ => rfl⟩

/-- Relabelling routing the x₃ challenge to the fiber's first coordinate, its predecessors to the
base. -/
def reindexX3 : (Fp × Fp × Fp × Fp) ≃ Fp × (Fp × Fp × Fp) :=
  ⟨fun w => (w.2.2.1, w.1, w.2.1, w.2.2.2), fun p => (p.2.1, p.2.2.1, p.1, p.2.2.2),
    fun _ => rfl, fun _ => rfl⟩

/-- Relabelling routing the x₄ challenge to the fiber's first coordinate, its predecessors to the
base. -/
def reindexX4 : (Fp × Fp × Fp × Fp) ≃ Fp × (Fp × Fp × Fp) :=
  ⟨fun w => (w.2.2.2, w.1, w.2.1, w.2.2.1), fun p => (p.2.1, p.2.2.1, p.2.2.2, p.1),
    fun _ => rfl, fun _ => rfl⟩

/-- **Four-squeeze combined floor-failure budget — the unconditional multiopen budget.** Over the
joint uniform draw of the four fresh challenges `w = (x₁, x₂, x₃, x₄)`, the probability that *any* of
the four nested squeeze floors fails — squeeze `i` accepts at its fresh slot yet its accept-measure
at the base the earlier challenges determine sits at or below its threshold `tᵢ` — is bounded by the
sum of the four thresholds `t₁ + t₂ + t₃ + t₄`.

Each squeeze's failure is bounded by `tᵢ` via `floor_failure_reindex_le` (routing that squeeze's
fresh challenge to the fiber's first coordinate and the earlier challenges to the base, through
`reindexX{2,3,4}`), and the four events union additively with no cross term (`measure_union_le`
iterated). This is the combined soundness budget in the sampled-run model: the extraction fails only
inside this event, so the computed-path knowledge error is at most `t₁ + t₂ + t₃ + t₄` plus the AGM
commitment-binding term. Wiring the deployed terminal's `hprob*` floors to instantiate `accᵢ` at
`OpenedX{1,2,3,4}Accept` and the earlier-challenge-determined bases (the `reprogramX*`
run-determination) is the remaining plumbing; the budget arithmetic and its composition are settled
here. -/
theorem combined_floor_failure_le
    (acc₁ : Fp → Prop) (acc₂ : Fp → Fp → Prop)
    (acc₃ : Fp → Fp → Fp → Prop) (acc₄ : Fp → Fp → Fp → Fp → Prop)
    (t₁ t₂ t₃ t₄ : ℝ≥0∞) :
    (PMF.uniformOfFintype (Fp × Fp × Fp × Fp)).toOuterMeasure
        ({w : Fp × Fp × Fp × Fp | acc₁ w.1 ∧
            ¬ (t₁ < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter acc₁))}
          ∪ {w : Fp × Fp × Fp × Fp | acc₂ w.1 w.2.1 ∧
            ¬ (t₂ < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter (acc₂ w.1)))}
          ∪ {w : Fp × Fp × Fp × Fp | acc₃ w.1 w.2.1 w.2.2.1 ∧
            ¬ (t₃ < (PMF.uniformOfFintype Fp).toOuterMeasure
                    (Finset.univ.filter (acc₃ w.1 w.2.1)))}
          ∪ {w : Fp × Fp × Fp × Fp | acc₄ w.1 w.2.1 w.2.2.1 w.2.2.2 ∧
            ¬ (t₄ < (PMF.uniformOfFintype Fp).toOuterMeasure
                    (Finset.univ.filter (acc₄ w.1 w.2.1 w.2.2.1)))})
      ≤ t₁ + t₂ + t₃ + t₄ := by
  refine le_trans (MeasureTheory.measure_union_le _ _) (add_le_add ?_ ?_)
  refine le_trans (MeasureTheory.measure_union_le _ _) (add_le_add ?_ ?_)
  refine le_trans (MeasureTheory.measure_union_le _ _) (add_le_add ?_ ?_)
  · exact nested_squeeze_floor_failure_le (fun _ : Fp × Fp × Fp => acc₁) t₁
  · refine le_of_eq_of_le (congrArg _ ?_)
      (floor_failure_reindex_le reindexX2 (fun b c => acc₂ b.1 c) t₂)
    ext w
    simp only [reindexX2, Equiv.coe_fn_mk, Set.mem_setOf_eq]
  · refine le_of_eq_of_le (congrArg _ ?_)
      (floor_failure_reindex_le reindexX3 (fun b c => acc₃ b.1 b.2.1 c) t₃)
    ext w
    simp only [reindexX3, Equiv.coe_fn_mk, Set.mem_setOf_eq]
  · refine le_of_eq_of_le (congrArg _ ?_)
      (floor_failure_reindex_le reindexX4 (fun b d => acc₄ b.1 b.2.1 b.2.2 d) t₄)
    ext w
    simp only [reindexX4, Equiv.coe_fn_mk, Set.mem_setOf_eq]

/-- **The deployed four-squeeze floor-failure budget (option-(b), stage 3).** The abstract
`combined_floor_failure_le` instantiated at the deployed multiopen accept predicates
`OpenedX{1,2,3,4}Accept`, with each squeeze's base threaded from the earlier sampled challenges by
the adversary's rewind-run strategy `g₁`/`g₂`/`g₃` (the run each sampled challenge determines, via
`Soundness.Forking.reprogramX*`) and the `x₂` blinder `b₂`. Over the joint uniform draw of the four
fresh challenges `w = (x₁, x₂, x₃, x₄)`, the probability that *any* deployed squeeze floor fails —
squeeze `i` accepts at its fresh slot yet the accept-measure at the `g`-determined base sits at or
below its threshold `tᵢ` — is at most `t₁ + t₂ + t₃ + t₄`.

The four failure sets are the exact negations of the deployed terminal's `hprob1`/`hx2`/`hprob3`/
`hprob4` floors (`Soundness.Vesta.orchard_verifier_vesta_member_constraint_derived`) at the
sampled runs:
* `x₁` at the honest base `(ps, ch)` — its floor is base-independent;
* `x₂` at `(g₁ ξ).spliced ps` / `(g₁ ξ).challenges ch ξ` with blinder `b₂ ξ`;
* `x₃` at the `x₂`-rewound base, blinder `evalVector urs.k χ` seeded by the fresh `x₃` slot;
* `x₄` at the `x₃`-rewound base, blinder `evalVector urs.k χ` seeded by the `x₃` challenge (the
  third coordinate), the fresh slot being the `x₄` challenge (the fourth coordinate).

This is a direct application of `combined_floor_failure_le`: the deployed predicates slot into its
abstract `acc₁…acc₄` with the base-threading and blinder-routing lining up definitionally, so the
budget arithmetic is inherited unchanged. The thresholds are left abstract (`t₁…t₄`); the deployed
`hprob*` thresholds (`deployedX4PairCount`/`deployedSetQueries`/`deployedAllPts` at the *sampled*
bases) depend on the run, so relating them to base-independent constants is the residual the terminal
rewiring (stage 4) supplies — it does not affect the union arithmetic settled here. -/
def deployedFloorFailureSet [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (g₁ : Fp → X1Run shape G) (g₂ : Fp → Fp → X2Run shape G) (g₃ : Fp → Fp → Fp → X3Run shape G)
    (b₂ : Fp → Fin (2 ^ urs.k) → Fp) (t₁ t₂ t₃ t₄ : ℝ≥0∞) : Set (Fp × Fp × Fp × Fp) :=
  {w : Fp × Fp × Fp × Fp | OpenedX1Accept urs hk vk ps ch w.1 ∧
      ¬ (t₁ < (PMF.uniformOfFintype Fp).toOuterMeasure
              (Finset.univ.filter (OpenedX1Accept urs hk vk ps ch)))}
    ∪ {w : Fp × Fp × Fp × Fp |
        OpenedX2Accept urs hk vk ((g₁ w.1).spliced ps) ((g₁ w.1).challenges ch w.1)
            (b₂ w.1) w.2.1 ∧
      ¬ (t₂ < (PMF.uniformOfFintype Fp).toOuterMeasure
              (Finset.univ.filter (OpenedX2Accept urs hk vk ((g₁ w.1).spliced ps)
                ((g₁ w.1).challenges ch w.1) (b₂ w.1))))}
    ∪ {w : Fp × Fp × Fp × Fp |
        OpenedX3Accept urs hk vk ((g₂ w.1 w.2.1).spliced ((g₁ w.1).spliced ps))
            ((g₂ w.1 w.2.1).challenges ((g₁ w.1).challenges ch w.1) w.2.1)
            (evalVector urs.k w.2.2.1) w.2.2.1 ∧
      ¬ (t₃ < (PMF.uniformOfFintype Fp).toOuterMeasure
              (Finset.univ.filter (fun χv => OpenedX3Accept urs hk vk
                ((g₂ w.1 w.2.1).spliced ((g₁ w.1).spliced ps))
                ((g₂ w.1 w.2.1).challenges ((g₁ w.1).challenges ch w.1) w.2.1)
                (evalVector urs.k χv) χv)))}
    ∪ {w : Fp × Fp × Fp × Fp |
        OpenedX4Accept urs hk vk
            ((g₃ w.1 w.2.1 w.2.2.1).spliced ((g₂ w.1 w.2.1).spliced ((g₁ w.1).spliced ps)))
            ((g₃ w.1 w.2.1 w.2.2.1).challenges
              ((g₂ w.1 w.2.1).challenges ((g₁ w.1).challenges ch w.1) w.2.1) w.2.2.1)
            (evalVector urs.k w.2.2.1) w.2.2.2 ∧
      ¬ (t₄ < (PMF.uniformOfFintype Fp).toOuterMeasure
              (Finset.univ.filter (OpenedX4Accept urs hk vk
                ((g₃ w.1 w.2.1 w.2.2.1).spliced
                  ((g₂ w.1 w.2.1).spliced ((g₁ w.1).spliced ps)))
                ((g₃ w.1 w.2.1 w.2.2.1).challenges
                  ((g₂ w.1 w.2.1).challenges ((g₁ w.1).challenges ch w.1) w.2.1) w.2.2.1)
                (evalVector urs.k w.2.2.1))))}

/-- **The deployed four-squeeze floor-failure budget (stage 3a).** `combined_floor_failure_le` read
off `deployedFloorFailureSet`: over the joint uniform draw of the four fresh challenges, the deployed
floor-failure event has probability at most `t₁ + t₂ + t₃ + t₄`. -/
theorem deployed_combined_floor_failure_le [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (g₁ : Fp → X1Run shape G) (g₂ : Fp → Fp → X2Run shape G) (g₃ : Fp → Fp → Fp → X3Run shape G)
    (b₂ : Fp → Fin (2 ^ urs.k) → Fp) (t₁ t₂ t₃ t₄ : ℝ≥0∞) :
    (PMF.uniformOfFintype (Fp × Fp × Fp × Fp)).toOuterMeasure
        (deployedFloorFailureSet urs hk vk ps ch g₁ g₂ g₃ b₂ t₁ t₂ t₃ t₄)
      ≤ t₁ + t₂ + t₃ + t₄ :=
  combined_floor_failure_le
    (OpenedX1Accept urs hk vk ps ch)
    (fun ξ ζ => OpenedX2Accept urs hk vk ((g₁ ξ).spliced ps) ((g₁ ξ).challenges ch ξ) (b₂ ξ) ζ)
    (fun ξ ζ χ => OpenedX3Accept urs hk vk ((g₂ ξ ζ).spliced ((g₁ ξ).spliced ps))
        ((g₂ ξ ζ).challenges ((g₁ ξ).challenges ch ξ) ζ) (evalVector urs.k χ) χ)
    (fun ξ ζ χ ω => OpenedX4Accept urs hk vk
        ((g₃ ξ ζ χ).spliced ((g₂ ξ ζ).spliced ((g₁ ξ).spliced ps)))
        ((g₃ ξ ζ χ).challenges ((g₂ ξ ζ).challenges ((g₁ ξ).challenges ch ξ) ζ) χ)
        (evalVector urs.k χ) ω)
    t₁ t₂ t₃ t₄

/-- **The deployed floors hold except on the budget (stage 3b).** Complement of
`deployed_combined_floor_failure_le`: the challenge tuples on which *every* deployed squeeze floor is
satisfied — the "good" event `deployedFloorFailureSetᶜ`, on which each accepting sampled run's floor
`tᵢ < measure(accept)` holds — have probability at least `1 - (t₁ + t₂ + t₃ + t₄)`.

Pure outer-measure arithmetic: `S ∪ Sᶜ = univ` has measure `1`
(`uniformOfFintype_toOuterMeasure_univ`), subadditivity (`measure_union_le`) gives
`1 ≤ μ S + μ Sᶜ`, hence `μ Sᶜ ≥ 1 - μ S ≥ 1 - (t₁+t₂+t₃+t₄)` by the stage-3a bound. This is the form
the terminal rewiring (stage 4) consumes: on the good event, the derived terminal's `hprob*` floor
premises hold at the `g`-determined runs, so the extraction succeeds off a set of measure at most the
budget. -/
theorem deployed_combined_floor_holds [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (g₁ : Fp → X1Run shape G) (g₂ : Fp → Fp → X2Run shape G) (g₃ : Fp → Fp → Fp → X3Run shape G)
    (b₂ : Fp → Fin (2 ^ urs.k) → Fp) (t₁ t₂ t₃ t₄ : ℝ≥0∞) :
    1 - (t₁ + t₂ + t₃ + t₄) ≤
      (PMF.uniformOfFintype (Fp × Fp × Fp × Fp)).toOuterMeasure
        (deployedFloorFailureSet urs hk vk ps ch g₁ g₂ g₃ b₂ t₁ t₂ t₃ t₄)ᶜ := by
  set μ := (PMF.uniformOfFintype (Fp × Fp × Fp × Fp)).toOuterMeasure with hμ
  set S := deployedFloorFailureSet urs hk vk ps ch g₁ g₂ g₃ b₂ t₁ t₂ t₃ t₄ with hS
  have hfail : μ S ≤ t₁ + t₂ + t₃ + t₄ :=
    deployed_combined_floor_failure_le urs hk vk ps ch g₁ g₂ g₃ b₂ t₁ t₂ t₃ t₄
  have hsub : (1 : ℝ≥0∞) ≤ μ S + μ Sᶜ := by
    calc (1 : ℝ≥0∞) = μ (Set.univ : Set (Fp × Fp × Fp × Fp)) :=
          (uniformOfFintype_toOuterMeasure_univ).symm
      _ = μ (S ∪ Sᶜ) := by rw [Set.union_compl_self]
      _ ≤ μ S + μ Sᶜ := MeasureTheory.measure_union_le _ _
  have hgood : (1 : ℝ≥0∞) - μ S ≤ μ Sᶜ := by
    rw [tsub_le_iff_right, add_comm]; exact hsub
  exact le_trans (tsub_le_tsub_left hfail 1) hgood

/-- **Budget → single-path floors (stage 4b bridge).** On the good event
`deployedFloorFailureSetᶜ` each level's squeeze floor holds *conditioned on that level's sampled
accept*: if the sampled run at level `i` accepts, its accept-measure at the `g`-determined base
exceeds the threshold `tᵢ`. This is the per-level de Morgan reading of `w ∉ deployedFloorFailureSet`
(`¬(accᵢ ∧ ¬floorᵢ) = accᵢ → floorᵢ`), and it is exactly the four *single-run* floor facts a
single-path member terminal would consume in place of the current derived terminal's ∀-over-runs
`hx2`/`hprob3`/`hprob4`. Combined with `deployed_combined_floor_holds` (`μ(good) ≥ 1 − Σtᵢ`), this
localises the residual: the only piece still missing for the unconditional deployed budget is a
single-path member terminal — one whose floor premises are these `g`-determined single-run floors
rather than universally quantified over the splice runs `X1Run`/`X2Run`/`X3Run` (which the nested
extraction core `deployed_member_node_binding` currently quantifies over). -/
theorem deployed_singlepath_floor_of_good [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (g₁ : Fp → X1Run shape G) (g₂ : Fp → Fp → X2Run shape G) (g₃ : Fp → Fp → Fp → X3Run shape G)
    (b₂ : Fp → Fin (2 ^ urs.k) → Fp) (t₁ t₂ t₃ t₄ : ℝ≥0∞)
    {w : Fp × Fp × Fp × Fp}
    (hw : w ∉ deployedFloorFailureSet urs hk vk ps ch g₁ g₂ g₃ b₂ t₁ t₂ t₃ t₄) :
    (OpenedX1Accept urs hk vk ps ch w.1 →
        t₁ < (PMF.uniformOfFintype Fp).toOuterMeasure
              (Finset.univ.filter (OpenedX1Accept urs hk vk ps ch)))
    ∧ (OpenedX2Accept urs hk vk ((g₁ w.1).spliced ps) ((g₁ w.1).challenges ch w.1) (b₂ w.1) w.2.1 →
        t₂ < (PMF.uniformOfFintype Fp).toOuterMeasure
              (Finset.univ.filter (OpenedX2Accept urs hk vk ((g₁ w.1).spliced ps)
                ((g₁ w.1).challenges ch w.1) (b₂ w.1))))
    ∧ (OpenedX3Accept urs hk vk ((g₂ w.1 w.2.1).spliced ((g₁ w.1).spliced ps))
          ((g₂ w.1 w.2.1).challenges ((g₁ w.1).challenges ch w.1) w.2.1)
          (evalVector urs.k w.2.2.1) w.2.2.1 →
        t₃ < (PMF.uniformOfFintype Fp).toOuterMeasure
              (Finset.univ.filter (fun χv => OpenedX3Accept urs hk vk
                ((g₂ w.1 w.2.1).spliced ((g₁ w.1).spliced ps))
                ((g₂ w.1 w.2.1).challenges ((g₁ w.1).challenges ch w.1) w.2.1)
                (evalVector urs.k χv) χv)))
    ∧ (OpenedX4Accept urs hk vk
          ((g₃ w.1 w.2.1 w.2.2.1).spliced ((g₂ w.1 w.2.1).spliced ((g₁ w.1).spliced ps)))
          ((g₃ w.1 w.2.1 w.2.2.1).challenges
            ((g₂ w.1 w.2.1).challenges ((g₁ w.1).challenges ch w.1) w.2.1) w.2.2.1)
          (evalVector urs.k w.2.2.1) w.2.2.2 →
        t₄ < (PMF.uniformOfFintype Fp).toOuterMeasure
              (Finset.univ.filter (OpenedX4Accept urs hk vk
                ((g₃ w.1 w.2.1 w.2.2.1).spliced
                  ((g₂ w.1 w.2.1).spliced ((g₁ w.1).spliced ps)))
                ((g₃ w.1 w.2.1 w.2.2.1).challenges
                  ((g₂ w.1 w.2.1).challenges ((g₁ w.1).challenges ch w.1) w.2.1) w.2.2.1)
                (evalVector urs.k w.2.2.1)))) := by
  simp only [deployedFloorFailureSet, Set.mem_union, Set.mem_setOf_eq, not_or, not_and,
    not_not] at hw
  exact ⟨hw.1.1.1, hw.1.1.2, hw.1.2, hw.2⟩

end Zcash.Snark
