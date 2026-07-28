import Mathlib
import Zcash.Snark.Soundness.GoodChallenge
import Zcash.Snark.Soundness.FoldSplit
import Zcash.Snark.Soundness.GrandProductBridge
import Zcash.Snark.Soundness.LookupAssembly
import Zcash.Snark.Soundness.Canonical.LookupSemantics
import Zcash.Snark.Soundness.Canonical.PermutationSemantics
import Zcash.Circuits.Integration.OperationLookups

/-!
# Pricing the new challenge surfaces

The permutation and lookup chain conditions on more challenges than the quotient check's `x`: the
fold split conditions on `y`, the multiset bridge on `β` and `γ`, the tuple decompression on `θ`,
and every telescoped result carries a vanishing-factor escape branch. Each is a root-set event, and
this module prices them all the same way `hgood` is priced — a uniform-challenge measure bound per
event, from `uniformChallenge_badSet` and a root count.

* `uniformChallenge_szBadSet_iUnion_le` — the shared union bound: finitely many root sets, each of
  degree at most `d`, cost at most `N·d / p` together.
* `goodY_failure_measure_le` — the fold split's `y` surface.
* `perm_gamma/beta_failure_measure_le` — the permutation bridge's two surfaces.
* `lookup_gamma/beta_failure_measure_le` — the lookup product bridge's two surfaces.
* `escape_measure_le` — a vanishing-factor branch, as the root set of the product of its factors.
* `theta_failure_measure_le` — the decompression's pairwise `θ` surface.

Sequential conditioning across the squeezes is the same coupling hook `hgood` carries — the data
each root set is built from is pinned in the transcript before its challenge is squeezed (θ after
the advice commitments, β and γ after θ, y after the lookup commitments, x last) — documented with
the deployed constraint decoder's `hfold`/`hgood` surfaces and not re-derived here.

The final section collects the bundle-wide resolver *permutation* prices — the `β` and `γ` surfaces
for every proof's copy argument — alongside the generic and lookup surfaces above, so a single module
carries the whole challenge-pricing story.
-/

-- The terminal API `snarkConstraintsSemanticDeployed_prob_le_of_root_schedule` consumes four
-- explicit bad-event bounds, one for each surface below. A concrete instantiation must obtain those
-- bounds through the sequential-coupling hook above; the compressed-identity capstone deliberately
-- cannot be presented as semantic soundness without them.

namespace Zcash.Snark

open Halo2 Polynomial Finset
open scoped ENNReal

/-- **The shared union bound.** Finitely many root-set events, each of degree at most `d`, together
have measure at most `N·d / p`. -/
theorem uniformChallenge_szBadSet_iUnion_le {ι : Type*} (s : Finset ι) (f : ι → Polynomial Fp)
    (d : ℕ) (hdeg : ∀ i ∈ s, (f i).natDegree ≤ d) :
    uniformChallenge.toOuterMeasure {x : Fp | ∃ i ∈ s, x ∈ szBadSet (f i)}
      ≤ (s.card * d : ℕ) / (Fintype.card Fp : ℝ≥0∞) := by
  have hsub : {x : Fp | ∃ i ∈ s, x ∈ szBadSet (f i)} ⊆ ↑(s.biUnion fun i => szBadSet (f i)) := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := hx
    exact Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨i, hi, hxi⟩)
  calc uniformChallenge.toOuterMeasure {x : Fp | ∃ i ∈ s, x ∈ szBadSet (f i)}
      ≤ uniformChallenge.toOuterMeasure ↑(s.biUnion fun i => szBadSet (f i)) :=
        uniformChallenge.toOuterMeasure.mono hsub
    _ = ((s.biUnion fun i => szBadSet (f i)).card : ℝ≥0∞) / Fintype.card Fp :=
        uniformChallenge_badSet _
    _ ≤ (s.card * d : ℕ) / (Fintype.card Fp : ℝ≥0∞) := by
        gcongr
        calc (s.biUnion fun i => szBadSet (f i)).card
            ≤ ∑ i ∈ s, (szBadSet (f i)).card := Finset.card_biUnion_le
          _ ≤ ∑ _i ∈ s, d := Finset.sum_le_sum fun i hi =>
              le_trans (szBadSet_card_le _) (hdeg i hi)
          _ = s.card * d := by rw [Finset.sum_const, smul_eq_mul]

/-- Out-of-range fold-split witnesses vanish: the residues have degree below `n`, so coefficient
`j ≥ n` folds a list of zeros. -/
theorem foldSplitWitness_eq_zero_of_le {cs : List (Polynomial Fp)} {n j : ℕ} (hn : n ≠ 0)
    (hj : n ≤ j) : foldSplitWitness cs n j = 0 := by
  rw [foldSplitWitness]
  refine (foldPoly_eq_zero_iff _).mpr fun v hv => ?_
  obtain ⟨c, _, rfl⟩ := List.mem_map.mp hv
  refine Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le ?_ hj)
  rcases eq_or_ne (c %ₘ (X ^ n - 1)) 0 with h0 | h0
  · rw [h0, Polynomial.natDegree_zero]
    exact Nat.pos_of_ne_zero hn
  · have hdeg := Polynomial.degree_modByMonic_lt c (monic_X_pow_sub_one hn)
    rw [(Polynomial.natDegree_lt_iff_degree_lt h0)]
    have hXn : ((X : Polynomial Fp) ^ n - 1).degree = (n : WithBot ℕ) := by
      rw [Polynomial.degree_eq_natDegree (monic_X_pow_sub_one hn).ne_zero]
      have h2 : ((X : Polynomial Fp) ^ n - 1).natDegree = n := by
        have h1 : ((X : Polynomial Fp) ^ n - 1) = X ^ n - C 1 := by rw [map_one]
        rw [h1, Polynomial.natDegree_X_pow_sub_C]
      exact_mod_cast congrArg (Nat.cast : ℕ → WithBot ℕ) h2
    rw [← hXn]
    exact hdeg

/-- **The `y` surface priced.** The fold split's bad event — some coefficient witness roots `y` —
costs at most `n·length / p`. -/
theorem goodY_failure_measure_le (cs : List (Polynomial Fp)) {n : ℕ} (hn : n ≠ 0) :
    uniformChallenge.toOuterMeasure
        {y : Fp | ∃ j, y ∈ szBadSet (foldSplitWitness cs n j)}
      ≤ (n * cs.length : ℕ) / (Fintype.card Fp : ℝ≥0∞) := by
  have hset : {y : Fp | ∃ j, y ∈ szBadSet (foldSplitWitness cs n j)}
      = {y : Fp | ∃ j ∈ range n, y ∈ szBadSet (foldSplitWitness cs n j)} := by
    ext y
    simp only [Set.mem_setOf_eq, mem_range]
    constructor
    · rintro ⟨j, hj⟩
      rcases lt_or_ge j n with hlt | hge
      · exact ⟨j, hlt, hj⟩
      · rw [foldSplitWitness_eq_zero_of_le hn hge] at hj
        simp [szBadSet] at hj
    · rintro ⟨j, _, hj⟩
      exact ⟨j, hj⟩
  rw [hset]
  refine le_trans (uniformChallenge_szBadSet_iUnion_le (range n) _ cs.length fun j _ => ?_) ?_
  · rcases eq_or_ne cs [] with rfl | hne
    · simp [foldSplitWitness, foldPoly]
    · have hne' : cs.map (fun c => (c %ₘ (X ^ n - 1)).coeff j) ≠ [] := by simpa using hne
      have hlt := natDegree_foldPoly_lt hne'
      rw [foldSplitWitness]
      simpa using le_of_lt hlt
  · rw [Finset.card_range]

/-- **The permutation `γ` surface priced.** The linear-product difference has degree at most the
cell count, so the bridge's `γ` condition costs at most `|cells| / p`. -/
theorem perm_gamma_failure_measure_le (sp tp : Multiset (Fp × Fp)) (beta : Fp) :
    uniformChallenge.toOuterMeasure
        ↑(szBadSet (linProdDiff (sp.map (fun q => q.1 + q.2 * beta))
          (tp.map (fun q => q.1 + q.2 * beta))))
      ≤ ((max (Multiset.card sp) (Multiset.card tp) : ℕ) : ℝ≥0∞) / Fintype.card Fp := by
  rw [uniformChallenge_badSet]
  gcongr
  refine Nat.cast_le.mpr (le_trans (szBadSet_linProdDiff_card_le _ _) ?_)
  simp only [Multiset.card_map]
  exact le_refl _

/-- Each coefficient of the pair-product difference has degree at most the cell count: the factors
`X + C (encPair q)` carry `β`-degree at most one each. -/
theorem natDegree_coeff_pairProdDiff_le (sp tp : Multiset (Fp × Fp)) (j : ℕ) :
    ((pairProdDiff sp tp).coeff j).natDegree ≤ max (Multiset.card sp) (Multiset.card tp) := by
  have key : ∀ (m : Multiset (Fp × Fp)) (j : ℕ),
      (((m.map (fun q => X + C (encPair q))).prod).coeff j).natDegree ≤ Multiset.card m := by
    intro m
    induction m using Multiset.induction with
    | empty =>
        intro j
        rcases eq_or_ne j 0 with rfl | hj
        · simp
        · simp [Polynomial.coeff_one, hj]
    | cons q m ih =>
        intro j
        rw [Multiset.map_cons, Multiset.prod_cons, add_mul, Polynomial.coeff_add]
        refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
        · rcases j with _ | j'
          · simp [Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero]
          · rw [Polynomial.coeff_X_mul]
            exact le_trans (ih j') (by simp)
        · rw [Polynomial.coeff_C_mul]
          refine le_trans (Polynomial.natDegree_mul_le) ?_
          have hencp : (encPair q).natDegree ≤ 1 := by
            refine le_trans (Polynomial.natDegree_add_le _ _) (max_le (by simp) ?_)
            exact le_trans Polynomial.natDegree_mul_le (by simp)
          calc (encPair q).natDegree + (((m.map (fun q => X + C (encPair q))).prod).coeff j).natDegree
              ≤ 1 + Multiset.card m := Nat.add_le_add hencp (ih j)
            _ = Multiset.card (q ::ₘ m) := by rw [Multiset.card_cons]; omega
  rw [pairProdDiff, Polynomial.coeff_sub]
  refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
  · exact le_trans (key sp j) (le_max_left _ _)
  · exact le_trans (key tp j) (le_max_right _ _)

/-- Out-of-range coefficients of the pair-product difference vanish. -/
theorem pairProdDiff_coeff_eq_zero_of_le (sp tp : Multiset (Fp × Fp)) {j : ℕ}
    (hj : max (Multiset.card sp) (Multiset.card tp) < j) : (pairProdDiff sp tp).coeff j = 0 := by
  have key : ∀ (m : Multiset (Fp × Fp)), Multiset.card m < j →
      ((m.map (fun q => X + C (encPair q))).prod).coeff j = 0 := by
    intro m hm
    refine Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt ?_ hm)
    have hmap : ∀ m : Multiset (Fp × Fp),
        m.map (fun q => X + C (encPair q)) = (m.map encPair).map (fun u => X + C u) := by
      intro m; simp [Multiset.map_map]
    rw [hmap, natDegree_prod_X_add_u]
    simp
  rw [pairProdDiff, Polynomial.coeff_sub,
    key sp (lt_of_le_of_lt (le_max_left _ _) hj), key tp (lt_of_le_of_lt (le_max_right _ _) hj),
    sub_self]

/-- **The permutation `β` surface priced.** Some coefficient of the pair-product difference roots
`β` — at most `(|cells| + 1) · |cells| / p`. -/
theorem perm_beta_failure_measure_le (sp tp : Multiset (Fp × Fp)) :
    uniformChallenge.toOuterMeasure
        {b : Fp | ∃ j, b ∈ szBadSet ((pairProdDiff sp tp).coeff j)}
      ≤ ((max (Multiset.card sp) (Multiset.card tp) + 1)
          * max (Multiset.card sp) (Multiset.card tp) : ℕ) / (Fintype.card Fp : ℝ≥0∞) := by
  set d := max (Multiset.card sp) (Multiset.card tp) with hd
  have hset : {b : Fp | ∃ j, b ∈ szBadSet ((pairProdDiff sp tp).coeff j)}
      = {b : Fp | ∃ j ∈ range (d + 1), b ∈ szBadSet ((pairProdDiff sp tp).coeff j)} := by
    ext b
    simp only [Set.mem_setOf_eq, mem_range]
    constructor
    · rintro ⟨j, hj⟩
      rcases lt_or_ge j (d + 1) with hlt | hge
      · exact ⟨j, hlt, hj⟩
      · rw [pairProdDiff_coeff_eq_zero_of_le sp tp (by omega)] at hj
        simp [szBadSet] at hj
    · rintro ⟨j, _, hj⟩
      exact ⟨j, hj⟩
  rw [hset]
  refine le_trans (uniformChallenge_szBadSet_iUnion_le (range (d + 1)) _ d
    fun j _ => natDegree_coeff_pairProdDiff_le sp tp j) ?_
  simp

/-- The lookup product difference has `γ`-degree bounded by the larger table column. The two input
columns occur only in its coefficients. -/
theorem natDegree_lookupProdDiff_le (a s inp tbl : Multiset Fp) :
    (lookupProdDiff a s inp tbl).natDegree ≤
      max (Multiset.card s) (Multiset.card tbl) := by
  rw [lookupProdDiff]
  refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
  · refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
    exact le_trans (by
      simpa [Multiset.map_map] using
        (natDegree_prod_X_add_u (s.map C)).le) (le_max_left _ _)
  · refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
    exact le_trans (by
      simpa [Multiset.map_map] using
        (natDegree_prod_X_add_u (tbl.map C)).le) (le_max_right _ _)

/-- Out-of-range `γ` coefficients of the lookup product difference vanish. -/
theorem lookupProdDiff_coeff_eq_zero_of_le (a s inp tbl : Multiset Fp) {j : ℕ}
    (hj : max (Multiset.card s) (Multiset.card tbl) < j) :
    (lookupProdDiff a s inp tbl).coeff j = 0 :=
  Polynomial.coeff_eq_zero_of_natDegree_lt
    (lt_of_le_of_lt (natDegree_lookupProdDiff_le a s inp tbl) hj)

/-- Every `γ` coefficient of the lookup product difference has `β`-degree bounded by the larger
input column. The table factors have coefficients that are constant in `β`. -/
theorem natDegree_coeff_lookupProdDiff_le
    (a s inp tbl : Multiset Fp) (j : ℕ) :
    ((lookupProdDiff a s inp tbl).coeff j).natDegree ≤
      max (Multiset.card a) (Multiset.card inp) := by
  have tableCoeff : ∀ (m : Multiset Fp) (j : ℕ),
      (((m.map (fun u => X + C (C u))).prod).coeff j).natDegree ≤ 0 := by
    intro m
    induction m using Multiset.induction with
    | empty =>
        intro j
        rcases eq_or_ne j 0 with rfl | hj
        · simp
        · simp [Polynomial.coeff_one, hj]
    | cons u m ih =>
        intro j
        rw [Multiset.map_cons, Multiset.prod_cons, add_mul, Polynomial.coeff_add]
        refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
        · rcases j with _ | j
          · simp [Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero]
          · rw [Polynomial.coeff_X_mul]
            exact ih j
        · rw [Polynomial.coeff_C_mul]
          exact le_trans (Polynomial.natDegree_C_mul_le _ _) (ih j)
  rw [lookupProdDiff, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
    Polynomial.coeff_C_mul]
  refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
  · refine le_trans Polynomial.natDegree_mul_le ?_
    calc
      ((a.map (fun u => X + C u)).prod).natDegree
          + (((s.map (fun u => X + C (C u))).prod).coeff j).natDegree
        ≤ Multiset.card a + 0 := Nat.add_le_add (by rw [natDegree_prod_X_add_u])
          (tableCoeff s j)
      _ = Multiset.card a := Nat.add_zero _
      _ ≤ max (Multiset.card a) (Multiset.card inp) := le_max_left _ _
  · refine le_trans Polynomial.natDegree_mul_le ?_
    calc
      ((inp.map (fun u => X + C u)).prod).natDegree
          + (((tbl.map (fun u => X + C (C u))).prod).coeff j).natDegree
        ≤ Multiset.card inp + 0 := Nat.add_le_add (by rw [natDegree_prod_X_add_u])
          (tableCoeff tbl j)
      _ = Multiset.card inp := Nat.add_zero _
      _ ≤ max (Multiset.card a) (Multiset.card inp) := le_max_right _ _

/-- **The lookup `γ` surface priced.** Once `β` is fixed, the lookup product difference has one
root per table row at most. -/
theorem lookup_gamma_failure_measure_le
    (a s inp tbl : Multiset Fp) (beta : Fp) :
    uniformChallenge.toOuterMeasure
        ↑(szBadSet ((lookupProdDiff a s inp tbl).map (evalRingHom beta)))
      ≤ (max (Multiset.card s) (Multiset.card tbl) : ℕ) /
          (Fintype.card Fp : ℝ≥0∞) := by
  rw [uniformChallenge_badSet]
  gcongr
  exact_mod_cast le_trans (szBadSet_card_le _)
    (le_trans Polynomial.natDegree_map_le (natDegree_lookupProdDiff_le a s inp tbl))

/-- **The lookup `β` surface priced.** There is one root set for each potentially nonzero
`γ` coefficient, and each such coefficient has degree at most the larger input-column size. -/
theorem lookup_beta_failure_measure_le (a s inp tbl : Multiset Fp) :
    uniformChallenge.toOuterMeasure
        {b : Fp | ∃ j, b ∈ szBadSet ((lookupProdDiff a s inp tbl).coeff j)}
      ≤ ((max (Multiset.card s) (Multiset.card tbl) + 1)
          * max (Multiset.card a) (Multiset.card inp) : ℕ) /
          (Fintype.card Fp : ℝ≥0∞) := by
  set ds := max (Multiset.card s) (Multiset.card tbl) with hds
  set da := max (Multiset.card a) (Multiset.card inp) with hda
  have hset : {b : Fp | ∃ j, b ∈ szBadSet ((lookupProdDiff a s inp tbl).coeff j)}
      = {b : Fp | ∃ j ∈ range (ds + 1),
          b ∈ szBadSet ((lookupProdDiff a s inp tbl).coeff j)} := by
    ext b
    simp only [Set.mem_setOf_eq, mem_range]
    constructor
    · rintro ⟨j, hj⟩
      rcases lt_or_ge j (ds + 1) with hlt | hge
      · exact ⟨j, hlt, hj⟩
      · rw [lookupProdDiff_coeff_eq_zero_of_le a s inp tbl (by omega)] at hj
        simp [szBadSet] at hj
    · rintro ⟨j, _, hj⟩
      exact ⟨j, hj⟩
  rw [hset]
  refine le_trans (uniformChallenge_szBadSet_iUnion_le (range (ds + 1)) _ da
    fun j _ => ?_) ?_
  · simpa [hda] using natDegree_coeff_lookupProdDiff_le a s inp tbl j
  · simp [hds, hda]

/-! ## Resolver-backed lookup challenge families -/

/-- The complete `γ` exclusion for one deployed lookup: the product-difference roots together
with the table-column zero factors used to eliminate the residual running-product branch. -/
noncomputable def resolverLookupGammaBadSet
    {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → Polynomial Fp)
    (p : Fin shape.numProofs) (l : Fin shape.numLookups) (u : ℕ) : Finset Fp :=
  szBadSet ((resolverLookupProductDifference vk ch poly p l u).map
    (evalRingHom ch.beta)) ∪
  lookupColumnZeroBadSet vk.omega
    (lookupTablePolyOfResolver vk ch poly p l) (u + 1)

/-- The complete `β` exclusion for one deployed lookup: every potentially nonzero coefficient of
the product difference together with the input-column zero factors. There are at most `u + 2`
coefficients because the `γ` degree is at most `u + 1`. -/
noncomputable def resolverLookupBetaBadSet
    {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → Polynomial Fp)
    (p : Fin shape.numProofs) (l : Fin shape.numLookups) (u : ℕ) : Finset Fp :=
  ((Finset.range (u + 2)).biUnion fun j =>
    szBadSet ((resolverLookupProductDifference vk ch poly p l u).coeff j)) ∪
  lookupColumnZeroBadSet vk.omega
    (lookupInputPolyOfResolver vk ch poly p l) (u + 1)

/-- Avoiding the two finite bad sets supplies exactly the four challenge facts consumed by one
resolver-backed lookup endpoint. -/
theorem ResolverLookupGoodChallenges.ofBadSets
    {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → Polynomial Fp)
    (p : Fin shape.numProofs) (l : Fin shape.numLookups) (u : ℕ)
    (hgamma : ch.gamma ∉ resolverLookupGammaBadSet vk ch poly p l u)
    (hbeta : ch.beta ∉ resolverLookupBetaBadSet vk ch poly p l u) :
    ResolverLookupGoodChallenges vk ch poly p l u where
  gamma hmem := hgamma (Finset.mem_union_left _ hmem)
  beta j := by
    by_cases hj : j < u + 2
    · intro hmem
      apply hbeta
      rw [resolverLookupBetaBadSet]
      exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
        ⟨j, Finset.mem_range.mpr hj, hmem⟩)
    · have hzero :
          (resolverLookupProductDifference vk ch poly p l u).coeff j = 0 := by
        apply lookupProdDiff_coeff_eq_zero_of_le
        simpa [resolverLookupProductDifference] using (show u + 1 < j by omega)
      simp [hzero, szBadSet]
  inputNonzero hmem := hbeta (by
    rw [resolverLookupBetaBadSet]
    exact Finset.mem_union_right _ hmem)
  tableNonzero hmem := hgamma (by
    rw [resolverLookupGammaBadSet]
    exact Finset.mem_union_right _ hmem)

/-- One deployed lookup's full `γ` exclusion costs at most two values per participating row: one
for multiset recovery and one for the table-column zero factor. -/
theorem resolverLookupGammaBadSet_card_le
    {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → Polynomial Fp)
    (p : Fin shape.numProofs) (l : Fin shape.numLookups) (u : ℕ) :
    (resolverLookupGammaBadSet vk ch poly p l u).card ≤ 2 * (u + 1) := by
  have hroot :
      (szBadSet ((resolverLookupProductDifference vk ch poly p l u).map
        (evalRingHom ch.beta))).card ≤ u + 1 := by
    exact le_trans (szBadSet_card_le _)
      (le_trans Polynomial.natDegree_map_le (by
        simpa [resolverLookupProductDifference] using
          natDegree_lookupProdDiff_le
            (Finset.univ.val.map
              (lookupColumnRows vk.omega (poly (.lookupPermInput p l)) (u + 1)))
            (Finset.univ.val.map
              (lookupColumnRows vk.omega (poly (.lookupPermTable p l)) (u + 1)))
            (Finset.univ.val.map
              (lookupColumnRows vk.omega
                (lookupInputPolyOfResolver vk ch poly p l) (u + 1)))
            (Finset.univ.val.map
              (lookupColumnRows vk.omega
                (lookupTablePolyOfResolver vk ch poly p l) (u + 1)))))
  have hzero :
      (lookupColumnZeroBadSet vk.omega
        (lookupTablePolyOfResolver vk ch poly p l) (u + 1)).card ≤ u + 1 := by
    rw [lookupColumnZeroBadSet]
    simpa using additiveZeroBadSet_card_le
      (lookupColumnRows vk.omega
        (lookupTablePolyOfResolver vk ch poly p l) (u + 1))
  rw [resolverLookupGammaBadSet]
  calc
    (szBadSet ((resolverLookupProductDifference vk ch poly p l u).map
          (evalRingHom ch.beta)) ∪
        lookupColumnZeroBadSet vk.omega
          (lookupTablePolyOfResolver vk ch poly p l) (u + 1)).card
      ≤ (szBadSet ((resolverLookupProductDifference vk ch poly p l u).map
            (evalRingHom ch.beta))).card +
          (lookupColumnZeroBadSet vk.omega
            (lookupTablePolyOfResolver vk ch poly p l) (u + 1)).card := by
        exact Finset.card_union_le _ _
    _ ≤ (u + 1) + (u + 1) := Nat.add_le_add hroot hzero
    _ = 2 * (u + 1) := by omega

/-- Uniform `γ` hits one deployed lookup's complete bad set with probability at most two values
per participating row over the scalar-field size. -/
theorem uniformChallenge_resolverLookupGammaBadSet
    {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → Polynomial Fp)
    (p : Fin shape.numProofs) (l : Fin shape.numLookups) (u : ℕ) :
    uniformChallenge.toOuterMeasure
        (resolverLookupGammaBadSet vk ch poly p l u)
      ≤ (2 * (u + 1) : ℕ) / (Fintype.card Fp : ℝ≥0∞) := by
  rw [uniformChallenge_badSet]
  gcongr
  exact_mod_cast resolverLookupGammaBadSet_card_le vk ch poly p l u

/-- One deployed lookup's full `β` exclusion costs at most
`(u + 2)·(u + 1) + (u + 1) = (u + 3)·(u + 1)` challenge values. -/
theorem resolverLookupBetaBadSet_card_le
    {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → Polynomial Fp)
    (p : Fin shape.numProofs) (l : Fin shape.numLookups) (u : ℕ) :
    (resolverLookupBetaBadSet vk ch poly p l u).card ≤
      (u + 2) * (u + 1) + (u + 1) := by
  have hcoeff : ∀ j,
      (szBadSet ((resolverLookupProductDifference vk ch poly p l u).coeff j)).card
        ≤ u + 1 := by
    intro j
    exact le_trans (szBadSet_card_le _) (by
      simpa [resolverLookupProductDifference] using
        natDegree_coeff_lookupProdDiff_le
          (Finset.univ.val.map
            (lookupColumnRows vk.omega (poly (.lookupPermInput p l)) (u + 1)))
          (Finset.univ.val.map
            (lookupColumnRows vk.omega (poly (.lookupPermTable p l)) (u + 1)))
          (Finset.univ.val.map
            (lookupColumnRows vk.omega
              (lookupInputPolyOfResolver vk ch poly p l) (u + 1)))
          (Finset.univ.val.map
            (lookupColumnRows vk.omega
              (lookupTablePolyOfResolver vk ch poly p l) (u + 1))) j)
  have hzero :
      (lookupColumnZeroBadSet vk.omega
        (lookupInputPolyOfResolver vk ch poly p l) (u + 1)).card ≤ u + 1 := by
    rw [lookupColumnZeroBadSet]
    simpa using additiveZeroBadSet_card_le
      (lookupColumnRows vk.omega
        (lookupInputPolyOfResolver vk ch poly p l) (u + 1))
  rw [resolverLookupBetaBadSet]
  calc
    (((Finset.range (u + 2)).biUnion fun j =>
          szBadSet ((resolverLookupProductDifference vk ch poly p l u).coeff j)) ∪
        lookupColumnZeroBadSet vk.omega
          (lookupInputPolyOfResolver vk ch poly p l) (u + 1)).card
      ≤ ((Finset.range (u + 2)).biUnion fun j =>
          szBadSet ((resolverLookupProductDifference vk ch poly p l u).coeff j)).card +
        (lookupColumnZeroBadSet vk.omega
          (lookupInputPolyOfResolver vk ch poly p l) (u + 1)).card := by
        exact Finset.card_union_le _ _
    _ ≤ (∑ j ∈ Finset.range (u + 2),
          (szBadSet ((resolverLookupProductDifference vk ch poly p l u).coeff j)).card) +
        (u + 1) := Nat.add_le_add Finset.card_biUnion_le hzero
    _ ≤ (∑ _j ∈ Finset.range (u + 2), (u + 1)) + (u + 1) := by
      exact Nat.add_le_add (Finset.sum_le_sum fun j _ => hcoeff j) (le_refl _)
    _ = (u + 2) * (u + 1) + (u + 1) := by simp

/-- Uniform `β` hits one deployed lookup's complete coefficient/zero-factor bad set with the
corresponding root-count probability. -/
theorem uniformChallenge_resolverLookupBetaBadSet
    {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → Polynomial Fp)
    (p : Fin shape.numProofs) (l : Fin shape.numLookups) (u : ℕ) :
    uniformChallenge.toOuterMeasure
        (resolverLookupBetaBadSet vk ch poly p l u)
      ≤ ((u + 2) * (u + 1) + (u + 1) : ℕ) /
          (Fintype.card Fp : ℝ≥0∞) := by
  rw [uniformChallenge_badSet]
  gcongr
  exact_mod_cast resolverLookupBetaBadSet_card_le vk ch poly p l u

/-- The union of all lookup `γ` exclusions in one proof bundle. The challenge is shared by every
proof and lookup argument, so this is the event the transcript squeeze must avoid. -/
noncomputable def allResolverLookupGammaBadSet
    {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → Polynomial Fp) (u : ℕ) : Finset Fp :=
  (Finset.univ : Finset (Fin shape.numProofs × Fin shape.numLookups)).biUnion fun q =>
    resolverLookupGammaBadSet vk ch poly q.1 q.2 u

/-- The union of all lookup `β` exclusions in one proof bundle. -/
noncomputable def allResolverLookupBetaBadSet
    {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → Polynomial Fp) (u : ℕ) : Finset Fp :=
  (Finset.univ : Finset (Fin shape.numProofs × Fin shape.numLookups)).biUnion fun q =>
    resolverLookupBetaBadSet vk ch poly q.1 q.2 u

/-- Avoiding the bundle-wide lookup bad sets supplies the good-challenge record for every proof
and every deployed lookup argument. -/
theorem resolverLookupGoodChallenges_of_not_mem
    {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → Polynomial Fp) (u : ℕ)
    (hgamma : ch.gamma ∉ allResolverLookupGammaBadSet vk ch poly u)
    (hbeta : ch.beta ∉ allResolverLookupBetaBadSet vk ch poly u) :
    ∀ (p : Fin shape.numProofs) (l : Fin shape.numLookups),
      ResolverLookupGoodChallenges vk ch poly p l u := by
  intro p l
  apply ResolverLookupGoodChallenges.ofBadSets
  · intro hmem
    apply hgamma
    exact Finset.mem_biUnion.mpr ⟨(p, l), Finset.mem_univ _, hmem⟩
  · intro hmem
    apply hbeta
    exact Finset.mem_biUnion.mpr ⟨(p, l), Finset.mem_univ _, hmem⟩

/-- The bundle-wide lookup `γ` surface is the number of proof/lookup pairs times the per-argument
two-values-per-row budget. -/
theorem uniformChallenge_allResolverLookupGammaBadSet
    {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → Polynomial Fp) (u : ℕ) :
    uniformChallenge.toOuterMeasure
        (allResolverLookupGammaBadSet vk ch poly u)
      ≤ (shape.numProofs * shape.numLookups * (2 * (u + 1)) : ℕ) /
          (Fintype.card Fp : ℝ≥0∞) := by
  rw [uniformChallenge_badSet]
  gcongr
  rw [allResolverLookupGammaBadSet]
  calc
    ((Finset.univ : Finset (Fin shape.numProofs × Fin shape.numLookups)).biUnion
        fun q => resolverLookupGammaBadSet vk ch poly q.1 q.2 u).card
      ≤ ∑ q ∈ (Finset.univ : Finset (Fin shape.numProofs × Fin shape.numLookups)),
          (resolverLookupGammaBadSet vk ch poly q.1 q.2 u).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _q ∈ (Finset.univ : Finset (Fin shape.numProofs × Fin shape.numLookups)),
          2 * (u + 1) := Finset.sum_le_sum fun q _ =>
            resolverLookupGammaBadSet_card_le vk ch poly q.1 q.2 u
    _ = shape.numProofs * shape.numLookups * (2 * (u + 1)) := by simp

/-- The bundle-wide lookup `β` surface is the number of proof/lookup pairs times the
coefficient-and-zero-factor budget for one argument. -/
theorem uniformChallenge_allResolverLookupBetaBadSet
    {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → Polynomial Fp) (u : ℕ) :
    uniformChallenge.toOuterMeasure
        (allResolverLookupBetaBadSet vk ch poly u)
      ≤ (shape.numProofs * shape.numLookups *
          ((u + 2) * (u + 1) + (u + 1)) : ℕ) /
          (Fintype.card Fp : ℝ≥0∞) := by
  rw [uniformChallenge_badSet]
  gcongr
  rw [allResolverLookupBetaBadSet]
  calc
    ((Finset.univ : Finset (Fin shape.numProofs × Fin shape.numLookups)).biUnion
        fun q => resolverLookupBetaBadSet vk ch poly q.1 q.2 u).card
      ≤ ∑ q ∈ (Finset.univ : Finset (Fin shape.numProofs × Fin shape.numLookups)),
          (resolverLookupBetaBadSet vk ch poly q.1 q.2 u).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _q ∈ (Finset.univ : Finset (Fin shape.numProofs × Fin shape.numLookups)),
          ((u + 2) * (u + 1) + (u + 1)) := Finset.sum_le_sum fun q _ =>
            resolverLookupBetaBadSet_card_le vk ch poly q.1 q.2 u
    _ = shape.numProofs * shape.numLookups *
        ((u + 2) * (u + 1) + (u + 1)) := by simp

/-- **A vanishing-factor escape priced.** The event that some listed factor `v + challenge` vanishes
is the root set of the product `∏ (X + v)`, so it costs at most the factor count over `p`. -/
theorem escape_measure_le (vs : Multiset Fp) :
    uniformChallenge.toOuterMeasure {x : Fp | ∃ v ∈ vs, v + x = 0}
      ≤ (Multiset.card vs : ℝ≥0∞) / Fintype.card Fp := by
  have hsub : {x : Fp | ∃ v ∈ vs, v + x = 0}
      ⊆ ↑(szBadSet ((vs.map (fun v => X + C v)).prod)) := by
    intro x hx
    obtain ⟨v, hv, hvx⟩ := hx
    rw [Finset.mem_coe, mem_szBadSet]
    constructor
    · exact (monic_multiset_prod_of_monic _ _ fun u _ => monic_X_add_C u).ne_zero
    · rw [eval_prod_X_add_u]
      refine Multiset.prod_eq_zero ?_
      refine Multiset.mem_map.mpr ⟨v, hv, ?_⟩
      linear_combination hvx
  calc uniformChallenge.toOuterMeasure {x : Fp | ∃ v ∈ vs, v + x = 0}
      ≤ uniformChallenge.toOuterMeasure ↑(szBadSet ((vs.map (fun v => X + C v)).prod)) :=
        uniformChallenge.toOuterMeasure.mono hsub
    _ ≤ _ := by
        rw [uniformChallenge_badSet]
        gcongr
        calc (szBadSet ((vs.map (fun v => X + C v)).prod)).card
            ≤ ((vs.map (fun v => X + C v)).prod).natDegree := szBadSet_card_le _
          _ ≤ Multiset.card vs := by rw [natDegree_prod_X_add_u]

/-- **The `θ` surface priced.** The pairwise decompression condition over `N` rows of arity at most
`r` costs at most `N²·r / p`. -/
theorem theta_failure_measure_le {N r : ℕ} (inputT tableT : ℕ → List Fp)
    (hlen : ∀ i < N, (inputT i).length ≤ r ∧ (tableT i).length ≤ r) :
    uniformChallenge.toOuterMeasure
        {θ : Fp | ∃ q ∈ range N ×ˢ range N,
          θ ∈ szBadSet (foldPoly (inputT q.1) - foldPoly (tableT q.2))}
      ≤ (N * N * r : ℕ) / (Fintype.card Fp : ℝ≥0∞) := by
  refine le_trans (uniformChallenge_szBadSet_iUnion_le (range N ×ˢ range N)
    (fun q => foldPoly (inputT q.1) - foldPoly (tableT q.2)) r fun q hq => ?_) ?_
  · obtain ⟨h1, h2⟩ := mem_product.mp hq
    refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
    · rcases eq_or_ne (inputT q.1) [] with h | h
      · simp [h, foldPoly]
      · exact le_trans (le_of_lt (natDegree_foldPoly_lt h))
          ((hlen q.1 (mem_range.mp h1)).1)
    · rcases eq_or_ne (tableT q.2) [] with h | h
      · simp [h, foldPoly]
      · exact le_trans (le_of_lt (natDegree_foldPoly_lt h))
          ((hlen q.2 (mem_range.mp h2)).2)
  · simp [mul_assoc]

/-! The operation-level lookup bridge has one `thetaBadSet` per enabled lookup activation (and per
proof assignment). The following family union is the exact finite event a shared `θ` squeeze must
avoid; unlike `theta_failure_measure_le`, it retains the Clean placement and environment needed by
the eventual bridge constructor. -/

/-- The union of the tuple-compression collision sets for an arbitrary finite family of enabled
lookup activations. -/
noncomputable def enabledLookupThetaBadSetFamily
    {ι : Type*} [Fintype ι]
    (place : ι → RegionIndex → ℕ) (env : ι → Environment Fp)
    (lookup : ι → EnabledLookup Fp) : Finset Fp :=
  (Finset.univ : Finset ι).biUnion fun i =>
    (lookup i).thetaBadSet (place i) (env i)

/-- Avoiding the family union supplies the `θ` exclusion for every enabled activation. -/
theorem not_mem_enabledLookupThetaBadSetFamily_iff
    {ι : Type*} [Fintype ι]
    (place : ι → RegionIndex → ℕ) (env : ι → Environment Fp)
    (lookup : ι → EnabledLookup Fp) (theta : Fp) :
    theta ∉ enabledLookupThetaBadSetFamily place env lookup ↔
      ∀ i, theta ∉ (lookup i).thetaBadSet (place i) (env i) := by
  classical
  simp [enabledLookupThetaBadSetFamily]

/-- The family collision set costs the sum of `usableRows × tupleArity` over its activations. -/
theorem enabledLookupThetaBadSetFamily_card_le
    {ι : Type*} [Fintype ι]
    (place : ι → RegionIndex → ℕ) (env : ι → Environment Fp)
    (lookup : ι → EnabledLookup Fp)
    (hlength : ∀ i row, row < (env i).usableRows →
      ((lookup i).inputValues (place i) (env i)).length =
        ((lookup i).tableValues (env i) row).length) :
    (enabledLookupThetaBadSetFamily place env lookup).card ≤
      ∑ i : ι, (env i).usableRows *
        ((lookup i).inputValues (place i) (env i)).length := by
  classical
  rw [enabledLookupThetaBadSetFamily]
  refine le_trans Finset.card_biUnion_le ?_
  exact Finset.sum_le_sum fun i _ =>
    (lookup i).thetaBadSet_card_le (place i) (env i)
      (fun row hrow => hlength i row hrow)

/-- Uniform `θ` hits some activation in a finite enabled-lookup family with probability at most
the sum of the individual row-by-arity budgets. -/
theorem uniformChallenge_enabledLookupThetaBadSetFamily
    {ι : Type*} [Fintype ι]
    (place : ι → RegionIndex → ℕ) (env : ι → Environment Fp)
    (lookup : ι → EnabledLookup Fp)
    (hlength : ∀ i row, row < (env i).usableRows →
      ((lookup i).inputValues (place i) (env i)).length =
        ((lookup i).tableValues (env i) row).length) :
    uniformChallenge.toOuterMeasure
        (enabledLookupThetaBadSetFamily place env lookup)
      ≤ (∑ i : ι, (env i).usableRows *
          ((lookup i).inputValues (place i) (env i)).length : ℕ) /
        (Fintype.card Fp : ℝ≥0∞) := by
  rw [uniformChallenge_badSet]
  gcongr
  exact_mod_cast enabledLookupThetaBadSetFamily_card_le place env lookup hlength

/-! ## Bundle-wide resolver permutation challenge pricing

This section collects the finite bad sets needed to obtain `ResolverPermutationGoodChallenges`
simultaneously for every proof in a bundle, and bounds their uniform-challenge cost. -/

section ResolverPermutation

set_option maxHeartbeats 20000

/-- Both multisets used by a resolver permutation argument contain exactly one entry per
active chunk cell. -/
theorem card_chunkedCellPairs_eq_fintypeCard
    (nc m : ℕ) (width : ℕ → ℕ)
    (value name : ℕ → ℕ → ℕ → Fp) :
    Multiset.card (chunkedCellPairs nc m width value name) =
      Fintype.card (ChunkCell nc m width) := by
  simp [chunkedCellPairs]

/-- The finite `β` exclusion for one resolver-backed permutation argument.  There is one
coefficient root set for each potentially nonzero coefficient of `pairProdDiff`. -/
noncomputable def resolverPermutationBetaBadSet
    {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G)
    (poly : CommitmentId → Polynomial Fp)
    (p : Fin shape.numProofs) (m : ℕ) : Finset Fp :=
  (Finset.range (Fintype.card (ResolverPermutationCell vk poly p m) + 1)).biUnion fun j =>
    szBadSet ((pairProdDiff
      (chunkedCellPairs shape.numPermutationSets m
        (fun c => (ResolverPermutationPairs vk poly p c).length)
        (chunkRowValue vk.omega (ResolverPermutationPairs vk poly p))
        (chunkRowSigmaName vk.omega (ResolverPermutationPairs vk poly p)))
      (chunkedCellPairs shape.numPermutationSets m
        (fun c => (ResolverPermutationPairs vk poly p c).length)
        (chunkRowValue vk.omega (ResolverPermutationPairs vk poly p))
        (chunkRowName vk.omega vk.delta vk.chunkLen))).coeff j)

/-- Avoiding the two per-proof bad sets supplies exactly the good-challenge record consumed by
the resolver permutation endpoint. -/
theorem ResolverPermutationGoodChallenges.ofBadSets
    {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → Polynomial Fp)
    (p : Fin shape.numProofs) (m : ℕ)
    (hgamma : ch.gamma ∉ resolverPermutationGammaBadSet vk ch poly p m)
    (hbeta : ch.beta ∉ resolverPermutationBetaBadSet vk poly p m) :
    ResolverPermutationGoodChallenges vk ch poly p m where
  gamma := hgamma
  beta j := by
    let source :=
      chunkedCellPairs shape.numPermutationSets m
        (fun c => (ResolverPermutationPairs vk poly p c).length)
        (chunkRowValue vk.omega (ResolverPermutationPairs vk poly p))
        (chunkRowSigmaName vk.omega (ResolverPermutationPairs vk poly p))
    let target :=
      chunkedCellPairs shape.numPermutationSets m
        (fun c => (ResolverPermutationPairs vk poly p c).length)
        (chunkRowValue vk.omega (ResolverPermutationPairs vk poly p))
        (chunkRowName vk.omega vk.delta vk.chunkLen)
    let d := Fintype.card (ResolverPermutationCell vk poly p m)
    change ch.beta ∉ szBadSet ((pairProdDiff source target).coeff j)
    by_cases hj : j < d + 1
    · intro hmem
      apply hbeta
      rw [resolverPermutationBetaBadSet]
      exact Finset.mem_biUnion.mpr
        ⟨j, Finset.mem_range.mpr hj, hmem⟩
    · have hsource : Multiset.card source = d := by
        simpa only [source, d] using card_chunkedCellPairs_eq_fintypeCard
          shape.numPermutationSets m
          (fun c => (ResolverPermutationPairs vk poly p c).length)
          (chunkRowValue vk.omega (ResolverPermutationPairs vk poly p))
          (chunkRowSigmaName vk.omega (ResolverPermutationPairs vk poly p))
      have htarget : Multiset.card target = d := by
        simpa only [target, d] using card_chunkedCellPairs_eq_fintypeCard
          shape.numPermutationSets m
          (fun c => (ResolverPermutationPairs vk poly p c).length)
          (chunkRowValue vk.omega (ResolverPermutationPairs vk poly p))
          (chunkRowName vk.omega vk.delta vk.chunkLen)
      have hzero : (pairProdDiff source target).coeff j = 0 := by
        apply pairProdDiff_coeff_eq_zero_of_le
        simp only [hsource, htarget, max_self]
        omega
      rw [hzero]
      simp [szBadSet]

/-- The union of all resolver permutation `γ` exclusions in one proof bundle. -/
noncomputable def allResolverPermutationGammaBadSet
    {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → Polynomial Fp) (m : ℕ) : Finset Fp :=
  (Finset.univ : Finset (Fin shape.numProofs)).biUnion fun p =>
    resolverPermutationGammaBadSet vk ch poly p m

/-- The union of all resolver permutation `β` exclusions in one proof bundle. -/
noncomputable def allResolverPermutationBetaBadSet
    {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G)
    (poly : CommitmentId → Polynomial Fp) (m : ℕ) : Finset Fp :=
  (Finset.univ : Finset (Fin shape.numProofs)).biUnion fun p =>
    resolverPermutationBetaBadSet vk poly p m

/-- Bundle-wide permutation challenge exclusions at one active-row boundary.
This is the verifier-native package consumed by circuit integrations. -/
structure ResolverPermutationChallengeExclusions
    {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → Polynomial Fp) (m : ℕ) : Prop where
  gamma :
    ch.gamma ∉ allResolverPermutationGammaBadSet vk ch poly m
  beta :
    ch.beta ∉ allResolverPermutationBetaBadSet vk poly m

/-- Avoiding the bundle-wide permutation bad sets supplies the good-challenge record for every
proof. -/
theorem resolverPermutationGoodChallenges_of_not_mem
    {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → Polynomial Fp) (m : ℕ)
    (hgamma : ch.gamma ∉ allResolverPermutationGammaBadSet vk ch poly m)
    (hbeta : ch.beta ∉ allResolverPermutationBetaBadSet vk poly m) :
    ∀ p : Fin shape.numProofs,
      ResolverPermutationGoodChallenges vk ch poly p m := by
  intro p
  apply ResolverPermutationGoodChallenges.ofBadSets
  · intro hmem
    apply hgamma
    exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_univ _, hmem⟩
  · intro hmem
    apply hbeta
    exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_univ _, hmem⟩

/-- A bundle exclusion package supplies the per-proof record used by the
permutation semantic endpoint. -/
theorem ResolverPermutationChallengeExclusions.good
    {shape : Shape} {G : Type*}
    {vk : VerifyingKey shape Fp G} {ch : Challenges shape.k Fp}
    {poly : CommitmentId → Polynomial Fp} {m : ℕ}
    (exclusions :
      ResolverPermutationChallengeExclusions vk ch poly m) :
    ∀ p : Fin shape.numProofs,
      ResolverPermutationGoodChallenges vk ch poly p m :=
  resolverPermutationGoodChallenges_of_not_mem
    vk ch poly m exclusions.gamma exclusions.beta

/-- One resolver permutation `γ` exclusion costs at most two challenge values per active
permutation cell: one for multiset recovery and one for source-factor nonvanishing. -/
theorem resolverPermutationGammaBadSet_card_le
    {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → Polynomial Fp)
    (p : Fin shape.numProofs) (m : ℕ) :
    (resolverPermutationGammaBadSet vk ch poly p m).card ≤
      2 * Fintype.card (ResolverPermutationCell vk poly p m) := by
  let source :=
    chunkedCellPairs shape.numPermutationSets m
      (fun c => (ResolverPermutationPairs vk poly p c).length)
      (chunkRowValue vk.omega (ResolverPermutationPairs vk poly p))
      (chunkRowSigmaName vk.omega (ResolverPermutationPairs vk poly p))
  let target :=
    chunkedCellPairs shape.numPermutationSets m
      (fun c => (ResolverPermutationPairs vk poly p c).length)
      (chunkRowValue vk.omega (ResolverPermutationPairs vk poly p))
      (chunkRowName vk.omega vk.delta vk.chunkLen)
  let d := Fintype.card (ResolverPermutationCell vk poly p m)
  have hsource : Multiset.card source = d := by
    simpa only [source, d] using card_chunkedCellPairs_eq_fintypeCard
      shape.numPermutationSets m
      (fun c => (ResolverPermutationPairs vk poly p c).length)
      (chunkRowValue vk.omega (ResolverPermutationPairs vk poly p))
      (chunkRowSigmaName vk.omega (ResolverPermutationPairs vk poly p))
  have htarget : Multiset.card target = d := by
    simpa only [target, d] using card_chunkedCellPairs_eq_fintypeCard
      shape.numPermutationSets m
      (fun c => (ResolverPermutationPairs vk poly p c).length)
      (chunkRowValue vk.omega (ResolverPermutationPairs vk poly p))
      (chunkRowName vk.omega vk.delta vk.chunkLen)
  have hroot :
      (szBadSet (resolverPermutationGammaDifference vk ch poly p m)).card ≤ d := by
    apply le_trans (szBadSet_linProdDiff_card_le _ _)
    simp [source, target, hsource, htarget]
  have hzero :
      (resolverPermutationZeroFactorBadSet vk ch poly p m).card ≤ d := by
    exact additiveZeroBadSet_card_le
      (resolverPermutationFactorOffset vk ch poly p m)
  rw [resolverPermutationGammaBadSet]
  calc
    (szBadSet (resolverPermutationGammaDifference vk ch poly p m) ∪
        resolverPermutationZeroFactorBadSet vk ch poly p m).card
      ≤ (szBadSet (resolverPermutationGammaDifference vk ch poly p m)).card +
          (resolverPermutationZeroFactorBadSet vk ch poly p m).card :=
        Finset.card_union_le _ _
    _ ≤ d + d := Nat.add_le_add hroot hzero
    _ = 2 * d := by omega

/-- One resolver permutation `β` exclusion costs at most `(d + 1)·d`, where `d` is the number
of active permutation cells. -/
theorem resolverPermutationBetaBadSet_card_le
    {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G)
    (poly : CommitmentId → Polynomial Fp)
    (p : Fin shape.numProofs) (m : ℕ) :
    (resolverPermutationBetaBadSet vk poly p m).card ≤
      (Fintype.card (ResolverPermutationCell vk poly p m) + 1) *
        Fintype.card (ResolverPermutationCell vk poly p m) := by
  let source :=
    chunkedCellPairs shape.numPermutationSets m
      (fun c => (ResolverPermutationPairs vk poly p c).length)
      (chunkRowValue vk.omega (ResolverPermutationPairs vk poly p))
      (chunkRowSigmaName vk.omega (ResolverPermutationPairs vk poly p))
  let target :=
    chunkedCellPairs shape.numPermutationSets m
      (fun c => (ResolverPermutationPairs vk poly p c).length)
      (chunkRowValue vk.omega (ResolverPermutationPairs vk poly p))
      (chunkRowName vk.omega vk.delta vk.chunkLen)
  let d := Fintype.card (ResolverPermutationCell vk poly p m)
  have hsource : Multiset.card source = d := by
    simpa only [source, d] using card_chunkedCellPairs_eq_fintypeCard
      shape.numPermutationSets m
      (fun c => (ResolverPermutationPairs vk poly p c).length)
      (chunkRowValue vk.omega (ResolverPermutationPairs vk poly p))
      (chunkRowSigmaName vk.omega (ResolverPermutationPairs vk poly p))
  have htarget : Multiset.card target = d := by
    simpa only [target, d] using card_chunkedCellPairs_eq_fintypeCard
      shape.numPermutationSets m
      (fun c => (ResolverPermutationPairs vk poly p c).length)
      (chunkRowValue vk.omega (ResolverPermutationPairs vk poly p))
      (chunkRowName vk.omega vk.delta vk.chunkLen)
  have hcoeff : ∀ j, (szBadSet ((pairProdDiff source target).coeff j)).card ≤ d := by
    intro j
    exact le_trans (szBadSet_card_le _) (by
      simpa [hsource, htarget] using natDegree_coeff_pairProdDiff_le source target j)
  rw [resolverPermutationBetaBadSet]
  calc
    ((Finset.range (d + 1)).biUnion fun j =>
        szBadSet ((pairProdDiff source target).coeff j)).card
      ≤ ∑ j ∈ Finset.range (d + 1),
          (szBadSet ((pairProdDiff source target).coeff j)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ Finset.range (d + 1), d :=
      Finset.sum_le_sum fun j _ => hcoeff j
    _ = (d + 1) * d := by simp

/-- The bundle-wide permutation `γ` surface is bounded by the sum of the per-proof active-cell
budgets. -/
theorem uniformChallenge_allResolverPermutationGammaBadSet
    {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → Polynomial Fp) (m : ℕ) :
    uniformChallenge.toOuterMeasure
        (allResolverPermutationGammaBadSet vk ch poly m)
      ≤ (∑ p : Fin shape.numProofs,
          (2 * Fintype.card (ResolverPermutationCell vk poly p m) : ℕ)) /
        (Fintype.card Fp : ℝ≥0∞) := by
  rw [uniformChallenge_badSet]
  gcongr
  rw [allResolverPermutationGammaBadSet]
  calc
    ((Finset.univ : Finset (Fin shape.numProofs)).biUnion fun p =>
        resolverPermutationGammaBadSet vk ch poly p m).card
      ≤ ∑ p ∈ (Finset.univ : Finset (Fin shape.numProofs)),
          (resolverPermutationGammaBadSet vk ch poly p m).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ p ∈ (Finset.univ : Finset (Fin shape.numProofs)),
          2 * Fintype.card (ResolverPermutationCell vk poly p m) :=
        Finset.sum_le_sum fun p _ =>
          resolverPermutationGammaBadSet_card_le vk ch poly p m
    _ = ∑ p : Fin shape.numProofs,
          2 * Fintype.card (ResolverPermutationCell vk poly p m) := by simp

/-- The bundle-wide permutation `β` surface is bounded by the sum of the per-proof coefficient
budgets. -/
theorem uniformChallenge_allResolverPermutationBetaBadSet
    {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G)
    (poly : CommitmentId → Polynomial Fp) (m : ℕ) :
    uniformChallenge.toOuterMeasure
        (allResolverPermutationBetaBadSet vk poly m)
      ≤ (∑ p : Fin shape.numProofs,
          ((Fintype.card (ResolverPermutationCell vk poly p m) + 1) *
            Fintype.card (ResolverPermutationCell vk poly p m) : ℕ)) /
        (Fintype.card Fp : ℝ≥0∞) := by
  rw [uniformChallenge_badSet]
  gcongr
  rw [allResolverPermutationBetaBadSet]
  calc
    ((Finset.univ : Finset (Fin shape.numProofs)).biUnion fun p =>
        resolverPermutationBetaBadSet vk poly p m).card
      ≤ ∑ p ∈ (Finset.univ : Finset (Fin shape.numProofs)),
          (resolverPermutationBetaBadSet vk poly p m).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ p ∈ (Finset.univ : Finset (Fin shape.numProofs)),
          (Fintype.card (ResolverPermutationCell vk poly p m) + 1) *
            Fintype.card (ResolverPermutationCell vk poly p m) :=
        Finset.sum_le_sum fun p _ =>
          resolverPermutationBetaBadSet_card_le vk poly p m
    _ = ∑ p : Fin shape.numProofs,
          (Fintype.card (ResolverPermutationCell vk poly p m) + 1) *
            Fintype.card (ResolverPermutationCell vk poly p m) := by simp

end ResolverPermutation

end Zcash.Snark
