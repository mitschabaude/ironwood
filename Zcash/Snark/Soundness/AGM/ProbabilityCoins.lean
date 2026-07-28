import Zcash.Snark.Soundness.AGM.Probability

/-!
# Relation-to-DL probability with extractor coins

Carry independent extractor coins through the programmed-basis DL reduction. The experiment,
the counting, and the `bound + 1/|F|` pricing are those of `Soundness.AGM.Probability`; only the
coin space gains the extractor's `ρ`.
-/

open scoped ENNReal
open Classical

namespace Zcash.Snark

variable {F G ρ : Type*} [Field F] [AddCommGroup G] [Module F G]

/-! ## Independent setup and extractor coins -/

/-- Draw from two PMFs independently. -/
noncomputable def independentProductPMF {A B : Type*} (p : PMF A) (q : PMF B) : PMF (A × B) :=
  p.bind fun a => q.map (Prod.mk a)

/-- Mapping the first component commutes with an independent product. -/
theorem independentProductPMF_map_left {A B C : Type*} (p : PMF A) (q : PMF B)
    (f : A → C) :
    (independentProductPMF p q).map (fun x => (f x.1, x.2)) =
      independentProductPMF (p.map f) q := by
  rw [independentProductPMF, PMF.map_bind, independentProductPMF, PMF.bind_map]
  congr 1
  funext a
  rw [PMF.map_comp]
  congr 1

/-- Independent uniform draws are the uniform draw on the product type. -/
theorem independentProductPMF_uniform {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] :
    independentProductPMF (PMF.uniformOfFintype A) (PMF.uniformOfFintype B) =
      PMF.uniformOfFintype (A × B) := by
  apply PMF.ext
  rintro ⟨a, b⟩
  rw [independentProductPMF, PMF.bind_apply, tsum_fintype]
  simp only [PMF.map_apply, PMF.uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul]
  rw [Finset.sum_eq_single a]
  · rw [tsum_eq_single b]
    · rw [if_pos rfl]
      rw [ENNReal.mul_inv (Or.inl (by exact_mod_cast Fintype.card_ne_zero))
        (Or.inl (ENNReal.natCast_ne_top _))]
    · intro b' hb'
      rw [if_neg]
      exact fun h => hb' (Prod.mk.inj h).2.symm
  · intro a' _ ha'
    have hzero : (∑' b' : B, if (a, b) = (a', b') then
        ((Fintype.card B : ℝ≥0∞))⁻¹ else 0) = 0 := ENNReal.tsum_eq_zero.mpr fun b' => by
      rw [if_neg]
      exact fun h => ha' (Prod.mk.inj h).1.symm
    rw [hzero, mul_zero]
  · simp

section Reduction

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype F] [Fintype ρ] [Nonempty ρ] (B : G)

variable (A : (b : ι → G) → ρ → Option (AlgebraicRelationWitness (F := F) b))

/-- Basis scalars and extractor coins on which the computed producer returns a relation. -/
noncomputable def relSetWithCoins : Finset ((ι → F) × ρ) :=
  Finset.univ.filter (fun p => (A (scalarBasis B p.1) p.2).isSome)

/-! ## The programmed experiment with extractor coins

Reduction coins `(z, x, y, c)`: the challenge log, the two programming vectors, and the
extractor's independent coins. -/

/-- The coefficients of the relation returned on presented logs `s` and extractor coins `c`;
zero when none returns. -/
def returnedCoeffsWithCoins (s : ι → F) (c : ρ) : ι → F :=
  (A (scalarBasis B s) c).elim 0 (fun r => r.coeffs)

omit [DecidableEq ι] [Nonempty ι] [Fintype F] [Fintype ρ] [Nonempty ρ] in
/-- `returnedCoeffsWithCoins` reads off the coefficients of the relation actually returned. -/
theorem returnedCoeffsWithCoins_of_eq_some {s : ι → F} {c : ρ}
    {r : AlgebraicRelationWitness (F := F) (scalarBasis B s)}
    (hr : A (scalarBasis B s) c = some r) :
    returnedCoeffsWithCoins B A s c = r.coeffs := by
  simp [returnedCoeffsWithCoins, hr]

/-- A pivot slot where the returned relation has nonzero coefficient; arbitrary when none
returns. -/
noncomputable def pivotSlotWithCoins (s : ι → F) (c : ρ) : ι :=
  (A (scalarBasis B s) c).elim (Classical.arbitrary ι) (fun r => r.exists_nonzero_coeff.choose)

omit [DecidableEq ι] [Fintype F] [Fintype ρ] [Nonempty ρ] in
/-- The pivot slot's coefficient is nonzero whenever a relation returns. -/
theorem returnedCoeffsWithCoins_pivotSlot_ne_zero {s : ι → F} {c : ρ}
    (hsome : (A (scalarBasis B s) c).isSome) :
    returnedCoeffsWithCoins B A s c (pivotSlotWithCoins B A s c) ≠ 0 := by
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hsome
  rw [returnedCoeffsWithCoins_of_eq_some B A hr]
  simp only [pivotSlotWithCoins, hr, Option.elim_some]
  exact r.exists_nonzero_coeff.choose_spec

/-- Programmed coins on which the randomized producer returns a relation. -/
noncomputable def programmedRelSetWithCoins : Finset (F × (ι → F) × (ι → F) × ρ) :=
  Finset.univ.filter (fun t =>
    (A (scalarBasis B (programmedLogs t.1 t.2.1 t.2.2.1)) t.2.2.2).isSome)

/-- Winning coins: the returned relation's component against `y` is nonzero. -/
noncomputable def textbookWinSetWithCoins : Finset (F × (ι → F) × (ι → F) × ρ) :=
  Finset.univ.filter (fun t =>
    (A (scalarBasis B (programmedLogs t.1 t.2.1 t.2.2.1)) t.2.2.2).isSome ∧
      (∑ i, returnedCoeffsWithCoins B A (programmedLogs t.1 t.2.1 t.2.2.1) t.2.2.2 i
          * t.2.2.1 i) ≠ 0)

/-- Failing coins: the returned relation annihilates the challenge programming `y`. -/
noncomputable def missSetWithCoins : Finset (F × (ι → F) × (ι → F) × ρ) :=
  Finset.univ.filter (fun t =>
    (A (scalarBasis B (programmedLogs t.1 t.2.1 t.2.2.1)) t.2.2.2).isSome ∧
      (∑ i, returnedCoeffsWithCoins B A (programmedLogs t.1 t.2.1 t.2.2.1) t.2.2.2 i
          * t.2.2.1 i) = 0)

omit [Nonempty ι] [Nonempty ρ] in
/-- Every relation-producing programmed coin wins or lands in the annihilation hyperplane. -/
theorem programmedRelSetWithCoins_subset_win_union_miss :
    programmedRelSetWithCoins B A ⊆ textbookWinSetWithCoins B A ∪ missSetWithCoins B A := by
  intro t ht
  simp only [programmedRelSetWithCoins, Finset.mem_filter, Finset.mem_univ, true_and] at ht
  rcases eq_or_ne
      (∑ i, returnedCoeffsWithCoins B A (programmedLogs t.1 t.2.1 t.2.2.1) t.2.2.2 i
        * t.2.2.1 i) 0 with h0 | h0
  · exact Finset.mem_union_right _ (by
      simp only [missSetWithCoins, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨ht, h0⟩)
  · exact Finset.mem_union_left _ (by
      simp only [textbookWinSetWithCoins, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨ht, h0⟩)

omit [Nonempty ι] [Nonempty ρ] in
/-- Perfect simulation with extractor coins: for each honest outcome in the relation event, the
programmed coins hitting it are exactly the free choices of `(z, y)`. -/
theorem programmedRelSetWithCoins_card :
    (programmedRelSetWithCoins B A).card =
      (relSetWithCoins B A).card * Fintype.card (F × (ι → F)) := by
  rw [← Finset.card_univ (α := F × (ι → F)), ← Finset.card_product]
  refine Finset.card_bij'
    (fun t _ => ((programmedLogs t.1 t.2.1 t.2.2.1, t.2.2.2), (t.1, t.2.2.1)))
    (fun p _ => (p.2.1, fun i => p.1.1 i - p.2.1 * p.2.2 i, p.2.2, p.1.2))
    ?hi ?hj ?left ?right
  case hi =>
    rintro ⟨z, x, y, c⟩ ht
    simp only [programmedRelSetWithCoins, Finset.mem_filter, Finset.mem_univ, true_and] at ht
    simp only [Finset.mem_product, Finset.mem_univ, and_true]
    simp only [relSetWithCoins, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ht
  case hj =>
    rintro ⟨⟨s, c⟩, z, y⟩ hp
    simp only [Finset.mem_product, Finset.mem_univ, and_true, relSetWithCoins,
      Finset.mem_filter, true_and] at hp
    simp only [programmedRelSetWithCoins, Finset.mem_filter, Finset.mem_univ, true_and]
    have hs : programmedLogs z (fun i => s i - z * y i) y = s := by
      funext i
      simp [programmedLogs]
    rw [hs]
    exact hp
  case left =>
    rintro ⟨z, x, y, c⟩ _
    simp only [Prod.mk.injEq, true_and, and_true]
    funext i
    simp [programmedLogs]
  case right =>
    rintro ⟨⟨s, c⟩, z, y⟩ _
    simp only [Prod.mk.injEq, and_true]
    funext i
    simp [programmedLogs]

omit [Nonempty ρ] in
/-- Annihilation costs at most a `1/|F|` slice of the coins: stash the challenge log in the
returned relation's pivot slot of `y`, which the hyperplane equation recovers. -/
theorem missSetWithCoins_card_le :
    (missSetWithCoins B A).card ≤ Fintype.card ((ι → F) × (ι → F) × ρ) := by
  rw [← Finset.card_univ]
  refine Finset.card_le_card_of_injOn
    (fun t => (programmedLogs t.1 t.2.1 t.2.2.1,
      Function.update t.2.2.1
        (pivotSlotWithCoins B A (programmedLogs t.1 t.2.1 t.2.2.1) t.2.2.2) t.1,
      t.2.2.2))
    (fun _ _ => Finset.mem_univ _) ?_
  rintro ⟨z, x, y, c⟩ ht ⟨z', x', y', c'⟩ ht' heq
  simp only [Finset.mem_coe, missSetWithCoins, Finset.mem_filter, Finset.mem_univ,
    true_and] at ht ht'
  obtain ⟨hsome, hmiss⟩ := ht
  obtain ⟨hsome', hmiss'⟩ := ht'
  dsimp only at heq
  rw [Prod.mk.injEq, Prod.mk.injEq] at heq
  obtain ⟨hs', hupd, hc'⟩ := heq
  have hc : c = c' := hc'
  subst hc
  have hs : programmedLogs z' x' y' = programmedLogs z x y := hs'.symm
  rw [hs] at hsome' hmiss' hupd
  set j := pivotSlotWithCoins B A (programmedLogs z x y) c with hj
  have hz : z = z' := by
    have := congrFun hupd j
    simpa [Function.update_self] using this
  have hyoff : ∀ i, i ≠ j → y i = y' i := by
    intro i hi
    have := congrFun hupd i
    simpa [Function.update_of_ne hi] using this
  have hcj : returnedCoeffsWithCoins B A (programmedLogs z x y) c j ≠ 0 :=
    returnedCoeffsWithCoins_pivotSlot_ne_zero B A hsome
  have hyj : y j = y' j := by
    have h1 : returnedCoeffsWithCoins B A (programmedLogs z x y) c j * y j +
        ∑ i ∈ Finset.univ.erase j,
          returnedCoeffsWithCoins B A (programmedLogs z x y) c i * y i = 0 :=
      (Finset.add_sum_erase Finset.univ
        (fun i => returnedCoeffsWithCoins B A (programmedLogs z x y) c i * y i)
        (Finset.mem_univ j)).trans hmiss
    have h2 : returnedCoeffsWithCoins B A (programmedLogs z x y) c j * y' j +
        ∑ i ∈ Finset.univ.erase j,
          returnedCoeffsWithCoins B A (programmedLogs z x y) c i * y' i = 0 :=
      (Finset.add_sum_erase Finset.univ
        (fun i => returnedCoeffsWithCoins B A (programmedLogs z x y) c i * y' i)
        (Finset.mem_univ j)).trans hmiss'
    have herase : (∑ i ∈ Finset.univ.erase j,
          returnedCoeffsWithCoins B A (programmedLogs z x y) c i * y i)
        = ∑ i ∈ Finset.univ.erase j,
            returnedCoeffsWithCoins B A (programmedLogs z x y) c i * y' i :=
      Finset.sum_congr rfl fun i hi => by
        rw [hyoff i (Finset.ne_of_mem_erase hi)]
    rw [herase] at h1
    exact mul_left_cancel₀ hcj (add_right_cancel (h1.trans h2.symm))
  have hy : y = y' := by
    funext i
    rcases eq_or_ne i j with hi | hi
    · rw [hi]; exact hyj
    · exact hyoff i hi
  have hx : x = x' := by
    funext i
    have := congrFun hs.symm i
    simp only [programmedLogs] at this
    rw [hz, hy] at this
    exact add_right_cancel this
  simp only [Prod.mk.injEq]
  exact ⟨hz, hx, hy, trivial⟩

/-! ## Textbook single-generator DL game -/

/-- A textbook DL bound for the actual randomized relation finder. Its winning coins are those
on which `discreteLogOfChallenge_of_relation`, applied to `programmedEmbedding`, computes the
discrete log of `z • B`. -/
def TextbookDLWithCoinsAdvantageLE (bound : ℝ≥0∞) : Prop :=
  (PMF.uniformOfFintype (F × (ι → F) × (ι → F) × ρ)).toOuterMeasure
      (textbookWinSetWithCoins B A) ≤ bound

/-- Under textbook DL hardness, randomized relation production has probability at most
`bound + 1/|F|` — the tight Jaeger–Tessaro form, with no multiplicative loss. -/
theorem relationWithCoins_prob_le_of_textbookDL {bound : ℝ≥0∞}
    (h : TextbookDLWithCoinsAdvantageLE B A bound) :
    (PMF.uniformOfFintype ((ι → F) × ρ)).toOuterMeasure (relSetWithCoins B A)
      ≤ bound + 1 / Fintype.card F := by
  have hM0 : (Fintype.card ((ι → F) × (ι → F) × ρ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hMtop : (Fintype.card ((ι → F) × (ι → F) × ρ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hC0 : (Fintype.card (F × (ι → F)) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hCtop : (Fintype.card (F × (ι → F)) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hwin : ((textbookWinSetWithCoins B A).card : ℝ≥0∞)
      / Fintype.card (F × (ι → F) × (ι → F) × ρ) ≤ bound := by
    rw [← uniformOfFintype_toOuterMeasure_finset]
    exact h
  have hmiss : ((missSetWithCoins B A).card : ℝ≥0∞)
      / Fintype.card (F × (ι → F) × (ι → F) × ρ) ≤ 1 / Fintype.card F := by
    have hcard : ((missSetWithCoins B A).card : ℝ≥0∞)
        ≤ Fintype.card ((ι → F) × (ι → F) × ρ) := by
      exact_mod_cast missSetWithCoins_card_le B A
    have hN : (Fintype.card (F × (ι → F) × (ι → F) × ρ) : ℝ≥0∞)
        = (Fintype.card ((ι → F) × (ι → F) × ρ) : ℝ≥0∞) * Fintype.card F := by
      push_cast [Fintype.card_prod]
      ring
    calc ((missSetWithCoins B A).card : ℝ≥0∞)
          / Fintype.card (F × (ι → F) × (ι → F) × ρ)
        ≤ (Fintype.card ((ι → F) × (ι → F) × ρ) : ℝ≥0∞)
            / Fintype.card (F × (ι → F) × (ι → F) × ρ) := by gcongr
      _ = 1 / Fintype.card F := by
          rw [hN]
          calc (Fintype.card ((ι → F) × (ι → F) × ρ) : ℝ≥0∞)
                / ((Fintype.card ((ι → F) × (ι → F) × ρ) : ℝ≥0∞) * Fintype.card F)
              = (Fintype.card ((ι → F) × (ι → F) × ρ) : ℝ≥0∞) * 1
                  / ((Fintype.card ((ι → F) × (ι → F) × ρ) : ℝ≥0∞) * Fintype.card F) := by
                rw [mul_one]
            _ = 1 / Fintype.card F := ENNReal.mul_div_mul_left _ _ hM0 hMtop
  have hrel : (PMF.uniformOfFintype ((ι → F) × ρ)).toOuterMeasure (relSetWithCoins B A)
      = ((programmedRelSetWithCoins B A).card : ℝ≥0∞)
          / Fintype.card (F × (ι → F) × (ι → F) × ρ) := by
    rw [uniformOfFintype_toOuterMeasure_finset, programmedRelSetWithCoins_card]
    have hN : (Fintype.card (F × (ι → F) × (ι → F) × ρ) : ℝ≥0∞)
        = (Fintype.card (F × (ι → F)) : ℝ≥0∞) * Fintype.card ((ι → F) × ρ) := by
      push_cast [Fintype.card_prod]
      ring
    rw [hN]
    push_cast
    rw [mul_comm ((relSetWithCoins B A).card : ℝ≥0∞) (Fintype.card (F × (ι → F)) : ℝ≥0∞),
      ENNReal.mul_div_mul_left _ _ hC0 hCtop]
  have hsplit : ((programmedRelSetWithCoins B A).card : ℝ≥0∞)
      ≤ ((textbookWinSetWithCoins B A).card : ℝ≥0∞) + ((missSetWithCoins B A).card : ℝ≥0∞) := by
    exact_mod_cast le_trans
      (Finset.card_le_card (programmedRelSetWithCoins_subset_win_union_miss B A))
      (Finset.card_union_le _ _)
  calc (PMF.uniformOfFintype ((ι → F) × ρ)).toOuterMeasure (relSetWithCoins B A)
      = ((programmedRelSetWithCoins B A).card : ℝ≥0∞)
          / Fintype.card (F × (ι → F) × (ι → F) × ρ) := hrel
    _ ≤ (((textbookWinSetWithCoins B A).card : ℝ≥0∞)
            + ((missSetWithCoins B A).card : ℝ≥0∞))
          / Fintype.card (F × (ι → F) × (ι → F) × ρ) := by gcongr
    _ = ((textbookWinSetWithCoins B A).card : ℝ≥0∞)
            / Fintype.card (F × (ι → F) × (ι → F) × ρ)
          + ((missSetWithCoins B A).card : ℝ≥0∞)
            / Fintype.card (F × (ι → F) × (ι → F) × ρ) := by
        rw [← ENNReal.div_add_div_same]
    _ ≤ bound + 1 / Fintype.card F := add_le_add hwin hmiss

end Reduction

end Zcash.Snark
