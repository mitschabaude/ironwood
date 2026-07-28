import Zcash.Snark.Soundness.Composition.Bridge

/-!
# The unconditional decomposition of the knowledge-error bound

`snarkExtraction_prob_le_of_generatorRO_textbookDL` is conditional on `hExtract` — the assumption
that every clean-opening run already extracts. This module removes it: the failure event splits,
with no hypothesis at all, into the clean-opening failure (already priced) and the
**clean-but-not-extracted** residual, giving the unconditional inequality

  `μ {accept ∧ ¬extracted} ≤ [ clean-opening bound ] + μ {hasCleanOpening ∧ ¬extracted}`

(`snarkExtraction_prob_le_of_generatorRO_textbookDL_decomposed`). The conditionality is now one
quantified term: `hExtract` held exactly when the residual is empty; here it is measured instead.

## What closing the residual needs

`deployed_member_budget` prices a per-base accept event over the four fresh multiopen challenges;
`cleanButNotExtracted` lives over the family's coin space, whose Fiat–Shamir challenges are
functions of the coins. The bridge is a distributional coupling — the shape proven for the IPA
rounds by `roChallenges_ipaRound_uniform` — and a genuine modelling step, not a composition of
existing lemmas. It is deliberately not assumed here: a premise bounding the residual would restate
the conclusion. This legacy decomposition is retained as a generic event identity; the deployed
path now uses direct pinned-root containment instead of the former budgeted-rewinding discharge.
-/

namespace Zcash.Snark

open scoped ENNReal

/-- Match `Algebraic.lean`'s `Inhabited VestaG` value, named to avoid the auto-name clash and the
`whnf` timeouts that a shadowing anonymous instance causes on the composed algebraic-family terms. -/
local instance vestaInhabitedCompositionDecomp : Inhabited VestaG := ⟨0⟩

namespace ComputedAlgebraicFSFamily

variable {shape : Shape}

/-- The **clean-but-not-extracted** residual: runs on which the computed family produced a clean IPA
opening (`hasCleanOpening`) yet the SNARK-extraction predicate `extracted` fails. This is the only
part of the SNARK-extraction failure not already contained in the clean-opening failure
`snarkFailureEvent`. -/
def cleanButNotExtracted (family : ComputedAlgebraicFSFamily shape)
    (extracted : (AugmentedIndex (2 ^ shape.k) → VestaG) → family.Coins → Prop) :
    Set ((AugmentedIndex (2 ^ shape.k) → VestaG) × family.Coins) :=
  {q | family.hasCleanOpening q.1 q.2 ∧ ¬ extracted q.1 q.2}

/-- **The unconditional split.** With no hypothesis, the SNARK-extraction failure is contained in the
union of the clean-opening failure (`snarkFailureEvent`, no clean opening) and the
clean-but-not-extracted residual. Case split on whether a clean opening was produced: with one it is
in the residual (its `¬extracted` is shared); without one it is in the clean-opening failure (its
acceptance is shared — both events use the same `fullAlgebraicAccept` predicate). This is the
hypothesis-free replacement for `snarkExtractionFailureEvent_subset` (which needed `hExtract`). -/
theorem snarkExtractionFailureEvent_subset_union (family : ComputedAlgebraicFSFamily shape)
    (extracted : (AugmentedIndex (2 ^ shape.k) → VestaG) → family.Coins → Prop) :
    family.snarkExtractionFailureEvent extracted
      ⊆ family.snarkFailureEvent ∪ family.cleanButNotExtracted extracted := by
  rintro q ⟨hacc, hnex⟩
  by_cases hclean : family.hasCleanOpening q.1 q.2
  · exact Or.inr ⟨hclean, hnex⟩
  · exact Or.inl ⟨hacc, hclean⟩

end ComputedAlgebraicFSFamily

open ComputedAlgebraicFSFamily in
/-- **The unconditional knowledge-error decomposition.** Without `hExtract`, the measure of
"deployed acceptance but no SNARK extraction" is at most the clean-opening bound plus the measure
of the clean-but-not-extracted residual (set containment and `measure_union_le`). The residual is
the coupling gap recorded in the module docstring — measured, not assumed away. -/
theorem snarkExtraction_prob_le_of_generatorRO_textbookDL_decomposed {shape : Shape}
    {T : Type*} [DecidableEq T] (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ shape.k) → T) (hquery : Function.Injective query)
    (family : ComputedAlgebraicFSFamily shape) {bound : ℝ≥0∞}
    (hDL : TextbookDLWithCoinsAdvantageLE B family.snarkRelationFinder bound)
    (extracted : (AugmentedIndex (2 ^ shape.k) → VestaG) → family.Coins → Prop) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          family.snarkExtractionFailureEvent extracted)
      ≤ ((family.Q + shape.k) * (3 / Fintype.card Fp) +
          (family.Q + 1 : ℕ) * (1 / Fintype.card Fp) +
          (bound + 1 / Fintype.card Fp))
        + (independentProductPMF (orchardGeneratorROSetup query)
            (PMF.uniformOfFintype family.Coins)).toOuterMeasure
              ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
                family.cleanButNotExtracted extracted) := by
  -- Bind the clean-opening bound first, then abbreviate the (shared) outer measure `μ`, so `set` rewrites the
  -- AGM term into the same `μ` shape as the goal. The preimage map is left as the literal it is in
  -- both goal and `hAGM`, avoiding a `set f` whose binder type would thrash elaboration.
  have hAGM := snarkFailure_prob_le_of_generatorRO_textbookDL B hB query hquery family hDL
  set μ := (independentProductPMF (orchardGeneratorROSetup query)
    (PMF.uniformOfFintype family.Coins)).toOuterMeasure with hμ
  refine le_trans (μ.mono (Set.preimage_mono
    (family.snarkExtractionFailureEvent_subset_union extracted))) ?_
  rw [Set.preimage_union]
  exact le_trans (MeasureTheory.measure_union_le _ _) (add_le_add hAGM le_rfl)

end Zcash.Snark
