import Mathlib
import Zcash.Snark.Soundness.Forking.Oracle
import Zcash.Snark.Soundness.Forking.Tree

/-!
# Probability form of the forking lemma

The deterministic assembly consumes three accepting continuations at each IPA round. This module
proves when such a tree exists: acceptance above the knowledge-error threshold under uniform
challenges forces a full `(3,…,3)` accepting tree.

The main results are:

* `uniformOfFintype_toOuterMeasure_finset`: a finite event under a uniform distribution has
  probability `|E| / |domain|`.
* `extractable_of_prob`: if acceptance exceeds `kerr / |domain|`, an `Extractable` tree exists.

The proof uses the multi-round `kerr` count directly. It does not compound a per-round cubic loss.
`Forking.Oracle` describes the random-oracle idealization, and `Forking.Adversary` supplies the
querying-adversary reduction and query loss.
-/

namespace Zcash.Snark

open scoped ENNReal

variable {α : Type*}

/-- A finite event under the uniform distribution has probability `|E| / |α|`. -/
theorem uniformOfFintype_toOuterMeasure_finset [Fintype α] [Nonempty α] (E : Finset α) :
    (PMF.uniformOfFintype α).toOuterMeasure E = (E.card : ℝ≥0∞) / Fintype.card α := by
  rw [PMF.toOuterMeasure_apply_finset]
  simp only [PMF.uniformOfFintype_apply, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

/-- A bijection maps the uniform distribution on `A` to the uniform distribution on `B`. -/
theorem map_uniformOfFintype_equiv {A B : Type*} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (e : A ≃ B) : (PMF.uniformOfFintype A).map e = PMF.uniformOfFintype B := by
  refine PMF.ext (fun b => ?_)
  rw [PMF.map_apply, tsum_eq_single (e.symm b) (fun a ha => ?_)]
  · simp only [PMF.uniformOfFintype_apply, Equiv.apply_symm_apply, if_pos, Fintype.card_congr e]
  · rw [if_neg]
    intro hb
    exact ha (e.injective ((e.apply_symm_apply b).symm ▸ hb.symm))

/-- Reading a uniform random function at finitely many distinct points gives independent uniform
answers. -/
theorem uniformOfFintype_map_eval_injective {ι T α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq T]
    [Fintype α] [Nonempty α] (φ : ι → T) (hφ : Function.Injective φ) :
    (PMF.uniformOfFintype (↥(Set.range φ) → α)).map (fun O i => O (Equiv.ofInjective φ hφ i))
      = PMF.uniformOfFintype (ι → α) :=
  map_uniformOfFintype_equiv (Equiv.arrowCongr (Equiv.ofInjective φ hφ).symm (Equiv.refl α))

/-- The first component of a uniform draw on `A × B` is uniform on `A`. -/
theorem map_fst_uniformOfFintype {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B] :
    (PMF.uniformOfFintype (A × B)).map Prod.fst = PMF.uniformOfFintype A := by
  classical
  refine PMF.ext fun a => ?_
  rw [PMF.map_apply, tsum_fintype, PMF.uniformOfFintype_apply]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  rw [ENNReal.mul_inv (Or.inl (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))
      (Or.inl (ENNReal.natCast_ne_top _)),
    mul_comm ((Fintype.card A : ℝ≥0∞))⁻¹ ((Fintype.card B : ℝ≥0∞))⁻¹, ← mul_assoc,
    ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
      (ENNReal.natCast_ne_top _), one_mul]

/-- Reading a uniform table at distinct points gives a uniform answer vector. -/
theorem uniformOfFintype_map_precomp_injective {ι T F : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype T] [DecidableEq T] [Fintype F] [Nonempty F]
    (φ : ι → T) (hφ : Function.Injective φ) :
    (PMF.uniformOfFintype (T → F)).map (fun O => O ∘ φ) = PMF.uniformOfFintype (ι → F) := by
  have hsplit : (fun O : T → F => O ∘ φ)
      = (fun O' : ↥(Set.range φ) → F => fun i => O' (Equiv.ofInjective φ hφ i))
        ∘ Prod.fst
        ∘ (Equiv.piEquivPiSubtypeProd (fun t => t ∈ Set.range φ) (fun _ => F)) := by
    funext O
    rfl
  rw [hsplit, ← PMF.map_comp, ← PMF.map_comp,
    map_uniformOfFintype_equiv (Equiv.piEquivPiSubtypeProd (fun t => t ∈ Set.range φ) (fun _ => F)),
    map_fst_uniformOfFintype, uniformOfFintype_map_eval_injective φ hφ]

/-- A set's uniform measure is its counting fraction. -/
theorem uniformOfFintype_toOuterMeasure_set {α : Type*} [Fintype α] [Nonempty α] (s : Set α) :
    (PMF.uniformOfFintype α).toOuterMeasure s = (Nat.card s : ℝ≥0∞) / Fintype.card α := by
  classical
  rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card',
    ← uniformOfFintype_toOuterMeasure_finset, Set.coe_toFinset]

open Classical in
/-- A uniform product inherits a bound that holds on every first-coordinate fiber. -/
theorem uniformOfFintype_prod_fiber_bound {A B : Type*} [Fintype A] [Fintype B] [Nonempty A]
    [Nonempty B] (S : B → Set A) {β : ℝ≥0∞}
    (hS : ∀ b, (PMF.uniformOfFintype A).toOuterMeasure (S b) ≤ β) :
    (PMF.uniformOfFintype (A × B)).toOuterMeasure {x : A × B | x.1 ∈ S x.2} ≤ β := by
  rw [uniformOfFintype_toOuterMeasure_set]
  have hcard : (Nat.card {x : A × B | x.1 ∈ S x.2}) = ∑ b : B, Nat.card (S b) := by
    rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card', Set.toFinset_setOf,
      Finset.card_filter, Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card', ← Finset.card_filter]
    congr 1
    ext a
    simp [Set.mem_toFinset]
  have hfib : ∀ b : B, ((Nat.card (S b) : ℕ) : ℝ≥0∞) ≤ β * Fintype.card A := by
    intro b
    have h := hS b
    rw [uniformOfFintype_toOuterMeasure_set, ENNReal.div_le_iff
      (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)] at h
    exact h
  rw [ENNReal.div_le_iff (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) (ENNReal.natCast_ne_top _),
    hcard]
  push_cast
  calc (∑ b : B, ((Nat.card (S b) : ℕ) : ℝ≥0∞))
      ≤ ∑ _b : B, β * Fintype.card A := Finset.sum_le_sum fun b _ => hfib b
    _ = Fintype.card B * (β * Fintype.card A) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = β * ((Fintype.card A : ℝ≥0∞) * Fintype.card B) := by ring
    _ = β * (Fintype.card (A × B)) := by rw [Fintype.card_prod]; push_cast; ring

open Classical in
/-- The symmetric Fubini bound, with the second coordinate chosen by the first. -/
theorem uniformOfFintype_prod_fiber_bound_right {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (S : A → Set B) {β : ℝ≥0∞}
    (hS : ∀ a, (PMF.uniformOfFintype B).toOuterMeasure (S a) ≤ β) :
    (PMF.uniformOfFintype (A × B)).toOuterMeasure {x : A × B | x.2 ∈ S x.1} ≤ β := by
  rw [uniformOfFintype_toOuterMeasure_set]
  have hcard : (Nat.card {x : A × B | x.2 ∈ S x.1}) = ∑ a : A, Nat.card (S a) := by
    rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card', Set.toFinset_setOf,
      Finset.card_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card', ← Finset.card_filter]
    congr 1
    ext b
    simp [Set.mem_toFinset]
  have hfib : ∀ a : A, ((Nat.card (S a) : ℕ) : ℝ≥0∞) ≤ β * Fintype.card B := by
    intro a
    have h := hS a
    rw [uniformOfFintype_toOuterMeasure_set, ENNReal.div_le_iff
      (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)] at h
    exact h
  rw [ENNReal.div_le_iff (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
    (ENNReal.natCast_ne_top _), hcard]
  push_cast
  calc (∑ a : A, ((Nat.card (S a) : ℕ) : ℝ≥0∞))
      ≤ ∑ _a : A, β * Fintype.card B := Finset.sum_le_sum fun a _ => hfib a
    _ = Fintype.card A * (β * Fintype.card B) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = β * ((Fintype.card A : ℝ≥0∞) * Fintype.card B) := by ring
    _ = β * Fintype.card (A × B) := by rw [Fintype.card_prod]; push_cast; ring

/-- Unread oracle coordinates remain uniform after choosing a target from the other coordinates. -/
theorem uniformOfFintype_fresh_read_bound {ι T F X : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype T] [DecidableEq T] [Fintype F] [Nonempty F]
    (φ : ι → T) (hφ : Function.Injective φ)
    (choice : ({t : T // ¬ t ∈ Set.range φ} → F) → X)
    (S : X → Set (ι → F)) {β : ℝ≥0∞}
    (hS : ∀ x, (PMF.uniformOfFintype (ι → F)).toOuterMeasure (S x) ≤ β) :
    (PMF.uniformOfFintype (T → F)).toOuterMeasure
      {O : T → F | (fun i => O (φ i)) ∈ S (choice (fun t => O t.1))} ≤ β := by
  have he : {O : T → F | (fun i => O (φ i)) ∈ S (choice (fun t => O t.1))}
      = (Equiv.piEquivPiSubtypeProd (fun t => t ∈ Set.range φ) (fun _ => F)) ⁻¹'
          {y : ({t : T // t ∈ Set.range φ} → F) × ({t : T // ¬ t ∈ Set.range φ} → F) |
            (fun i => y.1 (Equiv.ofInjective φ hφ i)) ∈ S (choice y.2)} := rfl
  rw [he, ← PMF.toOuterMeasure_map_apply,
    map_uniformOfFintype_equiv (Equiv.piEquivPiSubtypeProd (fun t => t ∈ Set.range φ) (fun _ => F))]
  refine uniformOfFintype_prod_fiber_bound
    (fun b => {a : {t : T // t ∈ Set.range φ} → F |
      (fun i => a (Equiv.ofInjective φ hφ i)) ∈ S (choice b)}) (fun b => ?_)
  have hpre : {a : {t : T // t ∈ Set.range φ} → F |
      (fun i => a (Equiv.ofInjective φ hφ i)) ∈ S (choice b)}
      = (fun (a : {t : T // t ∈ Set.range φ} → F) (i : ι) => a (Equiv.ofInjective φ hφ i)) ⁻¹'
          S (choice b) := rfl
  beta_reduce
  rw [hpre, ← PMF.toOuterMeasure_map_apply, uniformOfFintype_map_eval_injective φ hφ]
  exact hS (choice b)

/-- Uniform measure of a rectangle: the product of the sides' measures. -/
theorem uniformOfFintype_toOuterMeasure_prod {A B : Type*} [Fintype A] [Fintype B] [Nonempty A]
    [Nonempty B] (s : Set A) (t : Set B) :
    (PMF.uniformOfFintype (A × B)).toOuterMeasure (s ×ˢ t)
      = (PMF.uniformOfFintype A).toOuterMeasure s * (PMF.uniformOfFintype B).toOuterMeasure t := by
  rw [uniformOfFintype_toOuterMeasure_set, uniformOfFintype_toOuterMeasure_set,
    uniformOfFintype_toOuterMeasure_set, Nat.card_coe_set_eq, Nat.card_coe_set_eq,
    Nat.card_coe_set_eq, Set.ncard_prod, Fintype.card_prod]
  push_cast
  rw [ENNReal.mul_div_mul_comm (Or.inl (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))
    (Or.inl (ENNReal.natCast_ne_top _))]

/-- Uniform measure of the whole space is `1`. -/
theorem uniformOfFintype_toOuterMeasure_univ {α : Type*} [Fintype α] [Nonempty α] :
    (PMF.uniformOfFintype α).toOuterMeasure (Set.univ : Set α) = 1 := by
  rw [uniformOfFintype_toOuterMeasure_set, Nat.card_coe_set_eq, Set.ncard_univ,
    Nat.card_eq_fintype_card, ENNReal.div_self (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
      (ENNReal.natCast_ne_top _)]

/-- Uniform measure of a singleton: `1 / |α|`. -/
theorem uniformOfFintype_toOuterMeasure_singleton {α : Type*} [Fintype α] [Nonempty α] (a : α) :
    (PMF.uniformOfFintype α).toOuterMeasure {a} = 1 / Fintype.card α := by
  rw [uniformOfFintype_toOuterMeasure_set, Nat.card_coe_set_eq, Set.ncard_singleton, Nat.cast_one]

/-- Reading one point of a uniform table gives a uniform value. -/
theorem map_eval_uniformOfFintype {T F : Type*} [Fintype T] [DecidableEq T] [Fintype F]
    [Nonempty F] (t : T) :
    (PMF.uniformOfFintype (T → F)).map (fun O => O t) = PMF.uniformOfFintype F := by
  have h : (fun O : T → F => O t)
      = (Equiv.funUnique {x : T // x = t} F)
        ∘ Prod.fst
        ∘ (Equiv.piEquivPiSubtypeProd (fun x => x = t) (fun _ => F)) := by
    funext O; rfl
  rw [h, ← PMF.map_comp, ← PMF.map_comp,
    map_uniformOfFintype_equiv (Equiv.piEquivPiSubtypeProd (fun x => x = t) (fun _ => F)),
    map_fst_uniformOfFintype, map_uniformOfFintype_equiv (Equiv.funUnique {x : T // x = t} F)]

/-- A uniform table's answer at one point has the uniform marginal. -/
theorem uniformOfFintype_point_measure {T F : Type*} [Fintype T] [DecidableEq T] [Fintype F]
    [Nonempty F] (t : T) (s : Set F) :
    (PMF.uniformOfFintype (T → F)).toOuterMeasure {O : T → F | O t ∈ s}
      = (PMF.uniformOfFintype F).toOuterMeasure s := by
  have h : {O : T → F | O t ∈ s} = (fun O : T → F => O t) ⁻¹' s := rfl
  rw [h, ← PMF.toOuterMeasure_map_apply, map_eval_uniformOfFintype]

/-- Conditioning an update-invariant event on `O t = u` costs `1/|F|`. -/
theorem uniformOfFintype_cond_point {T F : Type*} [Fintype T] [DecidableEq T] [Fintype F]
    [Nonempty F] (t : T) (u : F) (E : Set (T → F))
    (hE : ∀ (O : T → F) (v : F), Function.update O t v ∈ E ↔ O ∈ E) :
    (PMF.uniformOfFintype (T → F)).toOuterMeasure {O : T → F | O t = u ∧ O ∈ E}
      = (PMF.uniformOfFintype (T → F)).toOuterMeasure E / Fintype.card F := by
  set e := Equiv.piSplitAt t (fun _ : T => F) with he
  have hsymm : ∀ (O : T → F) (v : F), e.symm (v, (e O).2) = Function.update O t v := by
    intro O v
    funext j
    by_cases hj : j = t
    · subst hj; simp [he, Equiv.piSplitAt, Function.update]
    · simp [he, Equiv.piSplitAt, Function.update, hj]
  have hEinv : ∀ (O : T → F) (v : F), (e.symm (v, (e O).2) ∈ E) ↔ O ∈ E := by
    intro O v; rw [hsymm]; exact hE O v
  have h1 : {O : T → F | O t = u ∧ O ∈ E}
      = e ⁻¹' (({u} : Set F) ×ˢ {g | e.symm (u, g) ∈ E}) := by
    ext O
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff, Set.mem_setOf_eq]
    exact ⟨fun ⟨hu, hO⟩ => ⟨hu, (hEinv O u).mpr hO⟩, fun ⟨hu, hO⟩ => ⟨hu, (hEinv O u).mp hO⟩⟩
  have h2 : E = e ⁻¹' ((Set.univ : Set F) ×ˢ {g | e.symm (u, g) ∈ E}) := by
    ext O
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and, Set.mem_setOf_eq]
    exact (hEinv O u).symm
  rw [h1, ← PMF.toOuterMeasure_map_apply, map_uniformOfFintype_equiv e,
    uniformOfFintype_toOuterMeasure_prod, uniformOfFintype_toOuterMeasure_singleton]
  conv_rhs => rw [h2, ← PMF.toOuterMeasure_map_apply, map_uniformOfFintype_equiv e,
    uniformOfFintype_toOuterMeasure_prod, uniformOfFintype_toOuterMeasure_univ]
  rw [one_mul, one_div, div_eq_mul_inv, mul_comm]

open Classical in
/-- Bound the expected size of a table-chosen set by its uniform-measure bound. -/
theorem sum_point_mem_measure_le {T F : Type*} [Fintype T] [DecidableEq T] [Fintype F]
    [Nonempty F] (S : (T → F) → Set F) {ε : ℝ≥0∞}
    (hS : ∀ O, (PMF.uniformOfFintype F).toOuterMeasure (S O) ≤ ε) :
    (∑ u : F, (PMF.uniformOfFintype (T → F)).toOuterMeasure {O : T → F | u ∈ S O})
      ≤ ε * Fintype.card F := by
  have hcount : (∑ u : F, (Nat.card {O : T → F | u ∈ S O} : ℝ≥0∞))
      = ∑ O : T → F, (Nat.card (S O) : ℝ≥0∞) := by
    norm_cast
    calc (∑ u : F, Nat.card {O : T → F | u ∈ S O})
        = ∑ u : F, (Finset.univ.filter (fun O : T → F => u ∈ S O)).card := by
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card', Set.toFinset_setOf]
      _ = ∑ u : F, ∑ O : T → F, if u ∈ S O then 1 else 0 := by
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [Finset.card_filter]
      _ = ∑ O : T → F, ∑ u : F, if u ∈ S O then 1 else 0 := Finset.sum_comm
      _ = ∑ O : T → F, Nat.card (S O) := by
          refine Finset.sum_congr rfl fun O _ => ?_
          rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card',
            show (S O).toFinset = Finset.univ.filter (fun u => u ∈ S O) from by
              ext u; simp [Set.mem_toFinset],
            Finset.card_filter]
  have hper : ∀ O : T → F, (Nat.card (S O) : ℝ≥0∞) ≤ ε * Fintype.card F := by
    intro O
    have h := hS O
    rw [uniformOfFintype_toOuterMeasure_set, ENNReal.div_le_iff
      (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)] at h
    exact h
  calc (∑ u : F, (PMF.uniformOfFintype (T → F)).toOuterMeasure {O : T → F | u ∈ S O})
      = ∑ u : F, (Nat.card {O : T → F | u ∈ S O} : ℝ≥0∞) / Fintype.card (T → F) := by
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [uniformOfFintype_toOuterMeasure_set]
    _ = (∑ u : F, (Nat.card {O : T → F | u ∈ S O} : ℝ≥0∞)) / Fintype.card (T → F) := by
        simp only [div_eq_mul_inv, Finset.sum_mul]
    _ = (∑ O : T → F, (Nat.card (S O) : ℝ≥0∞)) / Fintype.card (T → F) := by rw [hcount]
    _ ≤ (∑ _O : T → F, ε * Fintype.card F) / Fintype.card (T → F) := by
        gcongr with O _
        exact hper O
    _ = (Fintype.card (T → F) * (ε * Fintype.card F)) / Fintype.card (T → F) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = ε * Fintype.card F := by
        rw [mul_comm ((Fintype.card (T → F) : ℝ≥0∞)),
          ENNReal.mul_div_cancel_right (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
            (ENNReal.natCast_ne_top _)]

/-- An update-blind set contains `O t` with at most its uniform-measure bound. -/
theorem uniformOfFintype_point_mem_blind_le {T F : Type*} [Fintype T] [DecidableEq T] [Fintype F]
    [Nonempty F] (t : T) (S : (T → F) → Set F)
    (hblind : ∀ (O : T → F) (v : F), S (Function.update O t v) = S O) {ε : ℝ≥0∞}
    (hS : ∀ O, (PMF.uniformOfFintype F).toOuterMeasure (S O) ≤ ε) :
    (PMF.uniformOfFintype (T → F)).toOuterMeasure {O : T → F | O t ∈ S O} ≤ ε := by
  have hsub : {O : T → F | O t ∈ S O}
      ⊆ ⋃ u : F, {O : T → F | O t = u ∧ O ∈ {O' : T → F | u ∈ S O'}} := by
    intro O hO
    exact Set.mem_iUnion.mpr ⟨O t, rfl, hO⟩
  refine le_trans (MeasureTheory.measure_mono hsub) ?_
  refine le_trans (MeasureTheory.measure_iUnion_le _) ?_
  rw [tsum_fintype]
  have hper : ∀ u : F, (PMF.uniformOfFintype (T → F)).toOuterMeasure
      {O : T → F | O t = u ∧ O ∈ {O' : T → F | u ∈ S O'}}
      = (PMF.uniformOfFintype (T → F)).toOuterMeasure {O' : T → F | u ∈ S O'}
          / Fintype.card F := by
    intro u
    refine uniformOfFintype_cond_point t u _ fun O v => ?_
    simp only [Set.mem_setOf_eq, hblind O v]
  calc (∑ u : F, (PMF.uniformOfFintype (T → F)).toOuterMeasure
        {O : T → F | O t = u ∧ O ∈ {O' : T → F | u ∈ S O'}})
      = (∑ u : F, (PMF.uniformOfFintype (T → F)).toOuterMeasure {O' : T → F | u ∈ S O'})
          / Fintype.card F := by
        simp only [div_eq_mul_inv, Finset.sum_mul]
        exact Finset.sum_congr rfl fun u _ => by rw [hper u, div_eq_mul_inv]
    _ ≤ (ε * Fintype.card F) / Fintype.card F := by
        gcongr
        exact sum_point_mem_measure_le S hS
    _ = ε := ENNReal.mul_div_cancel_right (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
        (ENNReal.natCast_ne_top _)

/-- Uniform measure of a set inside three points is at most `3 / |α|`. -/
theorem uniformOfFintype_toOuterMeasure_triple_le {α : Type*} [Fintype α] [Nonempty α]
    {s : Set α} {x a b : α} (hs : s ⊆ {x, a, b}) :
    (PMF.uniformOfFintype α).toOuterMeasure s ≤ 3 / Fintype.card α := by
  refine le_trans (MeasureTheory.measure_mono hs) ?_
  rw [uniformOfFintype_toOuterMeasure_set]
  gcongr
  have h1 : ({x, a, b} : Set α).ncard ≤ 3 := by
    refine le_trans (Set.ncard_insert_le _ _) ?_
    have h2 : ({a, b} : Set α).ncard ≤ 2 :=
      le_trans (Set.ncard_insert_le _ _) (by simp [Set.ncard_singleton])
    omega
  rw [Nat.card_coe_set_eq]
  exact_mod_cast h1

/-- If uniform acceptance exceeds the `kerr` probability, a full accepting fork tree exists. -/
theorem extractable_of_prob [Fintype α] [DecidableEq α] [Zero α] [Nonempty α] {d : ℕ}
    (acc : (Fin d → α) → Prop) [DecidablePred acc]
    (h : (kerr (Fintype.card α) d : ℝ≥0∞) / Fintype.card (Fin d → α)
       < (PMF.uniformOfFintype (Fin d → α)).toOuterMeasure (Finset.univ.filter acc)) :
    Extractable acc := by
  apply extractable_of_kerr_lt
  by_contra hle
  push Not at hle
  have hmono : (PMF.uniformOfFintype (Fin d → α)).toOuterMeasure (Finset.univ.filter acc)
      ≤ (kerr (Fintype.card α) d : ℝ≥0∞) / Fintype.card (Fin d → α) := by
    rw [uniformOfFintype_toOuterMeasure_finset]
    gcongr
  exact absurd h (not_lt.mpr hmono)

/-- Finite `ℝ≥0∞` Cauchy–Schwarz for the local forking bound. -/
theorem ennreal_sq_sum_le_card_mul_sum_sq {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞)
    (hf : ∀ i ∈ s, f i ≠ ∞) :
    (∑ i ∈ s, f i) ^ 2 ≤ s.card * ∑ i ∈ s, (f i) ^ 2 := by
  have hsum : (∑ i ∈ s, f i) ≠ ∞ := (ENNReal.sum_lt_top.mpr (fun i hi => (hf i hi).lt_top)).ne
  have hsq : (∑ i ∈ s, (f i) ^ 2) ≠ ∞ :=
    (ENNReal.sum_lt_top.mpr (fun i hi => (ENNReal.pow_ne_top (hf i hi)).lt_top)).ne
  rw [← ENNReal.toReal_le_toReal (ENNReal.pow_ne_top hsum)
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hsq),
    ENNReal.toReal_pow, ENNReal.toReal_sum hf, ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_sum (fun i hi => ENNReal.pow_ne_top (hf i hi))]
  simp_rw [ENNReal.toReal_pow]
  exact sq_sum_le_card_mul_sum_sq

/-- Split accepting ordered pairs into distinct and diagonal pairs. -/
theorem acc_pair_card {F : Type*} [Fintype F] [DecidableEq F] (P : F → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card * (Finset.univ.filter P).card
      = (Finset.univ.filter (fun p : F × F => P p.1 ∧ P p.2 ∧ p.1 ≠ p.2)).card
        + (Finset.univ.filter P).card := by
  set A := Finset.univ.filter P with hA
  have hoff : (Finset.univ.filter (fun p : F × F => P p.1 ∧ P p.2 ∧ p.1 ≠ p.2)) = A.offDiag := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_offDiag, hA]
  have hle : A.card ≤ A.card * A.card := by
    rcases Nat.eq_zero_or_pos A.card with h0 | h0
    · simp [h0]
    · exact Nat.le_mul_of_pos_left _ h0
  rw [hoff, Finset.offDiag_card]
  exact (Nat.sub_add_cancel hle).symm

/-- Counting form of the local `ε² − ε/N` forking bound. -/
theorem forking_card_bound {Ψ F : Type*} [Fintype Ψ] [Fintype F] [DecidableEq F]
    (acc : Ψ → F → Prop) [∀ ψ, DecidablePred (acc ψ)] :
    (∑ ψ : Ψ, (Finset.univ.filter (acc ψ)).card) ^ 2
      ≤ Fintype.card Ψ
          * ((∑ ψ : Ψ,
                (Finset.univ.filter (fun p : F × F => acc ψ p.1 ∧ acc ψ p.2 ∧ p.1 ≠ p.2)).card)
              + ∑ ψ : Ψ, (Finset.univ.filter (acc ψ)).card) := by
  set E : Ψ → ℕ := fun ψ => (Finset.univ.filter (acc ψ)).card with hE
  set D : Ψ → ℕ :=
    fun ψ => (Finset.univ.filter (fun p : F × F => acc ψ p.1 ∧ acc ψ p.2 ∧ p.1 ≠ p.2)).card with hD
  have hsq : ∀ ψ, E ψ * E ψ = D ψ + E ψ := fun ψ => acc_pair_card (acc ψ)
  have hsum : (∑ ψ : Ψ, E ψ * E ψ) = (∑ ψ : Ψ, D ψ) + ∑ ψ : Ψ, E ψ := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun ψ _ => hsq ψ
  have hcs : ((∑ ψ : Ψ, E ψ : ℕ) : ℝ≥0∞) ^ 2
      ≤ (Fintype.card Ψ : ℝ≥0∞) * ∑ ψ : Ψ, ((E ψ : ℝ≥0∞)) ^ 2 := by
    have h := ennreal_sq_sum_le_card_mul_sum_sq (Finset.univ : Finset Ψ) (fun ψ => (E ψ : ℝ≥0∞))
      (fun _ _ => ENNReal.natCast_ne_top _)
    rw [Finset.card_univ] at h
    rw [Nat.cast_sum]
    exact h
  have hcast : (∑ ψ : Ψ, ((E ψ : ℝ≥0∞)) ^ 2) = ((∑ ψ : Ψ, D ψ) + ∑ ψ : Ψ, E ψ : ℕ) := by
    rw [← hsum]
    push_cast
    exact Finset.sum_congr rfl fun ψ _ => by rw [sq]
  rw [hcast] at hcs
  have hfin : ((∑ ψ : Ψ, E ψ) ^ 2 : ℕ)
      ≤ (Fintype.card Ψ * ((∑ ψ : Ψ, D ψ) + ∑ ψ : Ψ, E ψ) : ℕ) := by
    exact_mod_cast hcs
  simpa [hE, hD] using hfin

/-- Count of accepting `(state, challenge)` pairs as a sum over states. -/
theorem card_acc_pairs {Ψ F : Type*} [Fintype Ψ] [Fintype F] (acc : Ψ → F → Prop)
    [∀ ψ, DecidablePred (acc ψ)] :
    Nat.card {x : Ψ × F | acc x.1 x.2} = ∑ ψ : Ψ, (Finset.univ.filter (acc ψ)).card := by
  rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card', Set.toFinset_setOf,
    Finset.card_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  rw [Finset.card_filter]

/-- Count of distinct-accepting challenge pairs (per state) as a sum over states. -/
theorem card_acc_distinct {Ψ F : Type*} [Fintype Ψ] [Fintype F] [DecidableEq F]
    (acc : Ψ → F → Prop) [∀ ψ, DecidablePred (acc ψ)] :
    Nat.card {x : Ψ × F × F | acc x.1 x.2.1 ∧ acc x.1 x.2.2 ∧ x.2.1 ≠ x.2.2}
      = ∑ ψ : Ψ,
          (Finset.univ.filter (fun p : F × F => acc ψ p.1 ∧ acc ψ p.2 ∧ p.1 ≠ p.2)).card := by
  rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card', Set.toFinset_setOf,
    Finset.card_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  rw [Finset.card_filter]

/-- **Local forking, measure form.** Two independent challenges at one state are distinct and both
accepting with probability at least `ε² − ε/N`. -/
theorem forking_measure_bound {Ψ F : Type*} [Fintype Ψ] [Nonempty Ψ] [Fintype F] [Nonempty F]
    [DecidableEq F] (acc : Ψ → F → Prop) [∀ ψ, DecidablePred (acc ψ)] :
    ((PMF.uniformOfFintype (Ψ × F)).toOuterMeasure {x : Ψ × F | acc x.1 x.2}) ^ 2
      ≤ (PMF.uniformOfFintype (Ψ × F × F)).toOuterMeasure
          {x : Ψ × F × F | acc x.1 x.2.1 ∧ acc x.1 x.2.2 ∧ x.2.1 ≠ x.2.2}
        + (PMF.uniformOfFintype (Ψ × F)).toOuterMeasure {x : Ψ × F | acc x.1 x.2}
            / Fintype.card F := by
  set Nψ : ℝ≥0∞ := (Fintype.card Ψ : ℝ≥0∞) with hNψ
  set Nf : ℝ≥0∞ := (Fintype.card F : ℝ≥0∞) with hNf
  set E : ℕ := ∑ ψ : Ψ, (Finset.univ.filter (acc ψ)).card with hEdef
  set D : ℕ :=
    ∑ ψ : Ψ, (Finset.univ.filter (fun p : F × F => acc ψ p.1 ∧ acc ψ p.2 ∧ p.1 ≠ p.2)).card
    with hDdef
  have hcard_bound : E ^ 2 ≤ Fintype.card Ψ * (D + E) := forking_card_bound acc
  have hψ0 : Nψ ≠ 0 := by rw [hNψ]; exact_mod_cast Fintype.card_ne_zero
  have hf0 : Nf ≠ 0 := by rw [hNf]; exact_mod_cast Fintype.card_ne_zero
  simp only [uniformOfFintype_toOuterMeasure_set]
  rw [card_acc_pairs, card_acc_distinct, ← hEdef, ← hDdef]
  simp only [Fintype.card_prod]
  push_cast
  rw [← hNψ, ← hNf]
  have hden : Nψ * Nf ≠ 0 := mul_ne_zero hψ0 hf0
  have hL : ((E : ℝ≥0∞) / (Nψ * Nf)) ^ 2 ≠ ∞ :=
    ENNReal.pow_ne_top (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hden)
  have hR : (D : ℝ≥0∞) / (Nψ * (Nf * Nf)) + (E : ℝ≥0∞) / (Nψ * Nf) / Nf ≠ ∞ :=
    ENNReal.add_ne_top.mpr
      ⟨ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (mul_ne_zero hψ0 (mul_ne_zero hf0 hf0)),
       ENNReal.div_ne_top (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hden) hf0⟩
  rw [← ENNReal.toReal_le_toReal hL hR,
    ENNReal.toReal_add
      (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (mul_ne_zero hψ0 (mul_ne_zero hf0 hf0)))
      (ENNReal.div_ne_top (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hden) hf0),
    ENNReal.toReal_pow, ENNReal.toReal_div, ENNReal.toReal_div, ENNReal.toReal_div,
    ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul]
  rw [hNψ, hNf, ENNReal.toReal_natCast, ENNReal.toReal_natCast, ENNReal.toReal_natCast,
    ENNReal.toReal_natCast]
  have hnψ : (0 : ℝ) < (Fintype.card Ψ : ℝ) := by exact_mod_cast Fintype.card_pos
  have hnf : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have hcard_real : ((E : ℝ)) ^ 2
      ≤ (Fintype.card Ψ : ℝ) * ((D : ℝ) + (E : ℝ)) := by exact_mod_cast hcard_bound
  rw [div_pow, div_div,
    show (Fintype.card Ψ : ℝ) * Fintype.card F * Fintype.card F
        = Fintype.card Ψ * (Fintype.card F * Fintype.card F) from by ring,
    ← add_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right hcard_real
      (show (0 : ℝ) ≤ (Fintype.card Ψ : ℝ) * ((Fintype.card F : ℝ) * (Fintype.card F : ℝ)) from by
        positivity),
    hnψ, hnf]

open scoped ENNReal in
/-- **The single-squeeze forking count.** If one accepting challenge is in hand and the accept event's
uniform measure beats `n / |α|`, then `n + 1` pairwise-distinct accepting challenges exist, with the given
one in slot `0`. The one-challenge analogue of `extractable_of_prob` (there the event is a whole round
*vector* and beating `kerr` forces the `(3,…,3)` tree; here beating `n/|α|` forces `n` rewound accepting
values beside the current one) — the counting core of the multiopen `x₄` rewinding
(`Soundness.Multiopen.Deployed`). -/
theorem exists_injective_accepting_of_measure {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
    {acc : α → Prop} [DecidablePred acc] {x₀ : α} (hx₀ : acc x₀)
    (hprob : (n : ℝ≥0∞) / Fintype.card α
      < (PMF.uniformOfFintype α).toOuterMeasure (Finset.univ.filter acc)) :
    ∃ ξ : Fin (n + 1) → α, Function.Injective ξ ∧ ξ 0 = x₀ ∧ ∀ r, acc (ξ r) := by
  have hcard : n < (Finset.univ.filter acc).card := by
    by_contra hle
    push Not at hle
    have hmono : (PMF.uniformOfFintype α).toOuterMeasure (Finset.univ.filter acc)
        ≤ (n : ℝ≥0∞) / Fintype.card α := by
      rw [uniformOfFintype_toOuterMeasure_finset]
      exact ENNReal.div_le_div_right (by exact_mod_cast hle) _
    exact absurd hprob (not_lt.mpr hmono)
  have hx₀mem : x₀ ∈ Finset.univ.filter acc := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx₀⟩
  have herase : n ≤ ((Finset.univ.filter acc).erase x₀).card := by
    rw [Finset.card_erase_of_mem hx₀mem]
    omega
  obtain ⟨S, hS, hScard⟩ := Finset.exists_subset_card_eq herase
  let f : Fin n → α := fun i => (S.equivFin.symm (Fin.cast hScard.symm i) : α)
  have hfinj : Function.Injective f := fun i j hij => by
    have h1 := S.equivFin.symm.injective (Subtype.val_injective hij)
    exact Fin.val_injective (by simpa using congrArg Fin.val h1)
  have hfS : ∀ i, f i ∈ S := fun i => (S.equivFin.symm (Fin.cast hScard.symm i)).2
  refine ⟨Fin.cons x₀ f, ?_, rfl, ?_⟩
  · refine (Fin.cons_injective_iff).mpr ⟨?_, hfinj⟩
    rintro ⟨i, hfi⟩
    exact Finset.ne_of_mem_erase (hS (hfS i)) hfi
  · intro r
    cases r using Fin.cases with
    | zero => simpa using hx₀
    | succ i =>
        have hmem := hS (hfS i)
        have := Finset.mem_of_mem_erase hmem
        simpa using (Finset.mem_filter.mp this).2

open scoped ENNReal in
/-- **The single-squeeze forking count, off a bad set.** The avoidance-strengthened
`exists_injective_accepting_of_measure`: paying `bad.card / |α|` on top of the `n / |α|` sampling
floor buys `n + 1` pairwise-distinct accepting values that additionally miss `bad` altogether.
Counting, not a union bound: beating `(n + bad.card) / |α|` forces `n + bad.card < #{acc}`, so
`#({acc} \ bad) > n` whatever `bad` is.

This is what turns a sample-avoidance hypothesis into a budget line. The multiopen grid needs its
interpolation challenges off the opened set points (else the cleared-denominator core divides by a
vanishing `∏(χ − p)`), and an accepting run does *not* supply that: at a colliding challenge the
verifier's `(x₃ − p)⁻¹` is `0⁻¹ = 0`, so the check degenerates rather than failing. Charging
`|allPts| / |α|` for the collisions and sampling off `allPts` discharges the hypothesis outright.

No anchor is needed — unlike `exists_injective_accepting_of_measure`, which threads a given
accepting value into slot `0`, the floor alone is what produces the family here. -/
theorem exists_injective_accepting_avoiding_of_measure {α : Type*} [Fintype α] [DecidableEq α]
    [Nonempty α] {n : ℕ} {acc : α → Prop} [DecidablePred acc] (bad : Finset α)
    (hprob : ((n + bad.card : ℕ) : ℝ≥0∞) / Fintype.card α
      < (PMF.uniformOfFintype α).toOuterMeasure (Finset.univ.filter acc)) :
    ∃ ξ : Fin (n + 1) → α, Function.Injective ξ ∧ ∀ r, acc (ξ r) ∧ ξ r ∉ bad := by
  have hcard : n + bad.card < (Finset.univ.filter acc).card := by
    by_contra hle
    push Not at hle
    have hmono : (PMF.uniformOfFintype α).toOuterMeasure (Finset.univ.filter acc)
        ≤ ((n + bad.card : ℕ) : ℝ≥0∞) / Fintype.card α := by
      rw [uniformOfFintype_toOuterMeasure_finset]
      exact ENNReal.div_le_div_right (by exact_mod_cast hle) _
    exact absurd hprob (not_lt.mpr hmono)
  have hsd : n + 1 ≤ ((Finset.univ.filter acc) \ bad).card := by
    have := Finset.le_card_sdiff bad (Finset.univ.filter acc)
    omega
  obtain ⟨S, hS, hScard⟩ := Finset.exists_subset_card_eq hsd
  refine ⟨fun i => (S.equivFin.symm (Fin.cast hScard.symm i) : α), ?_, ?_⟩
  · intro i j hij
    have h1 := S.equivFin.symm.injective (Subtype.val_injective hij)
    exact Fin.val_injective (by simpa using congrArg Fin.val h1)
  · intro r
    have hmem := hS (S.equivFin.symm (Fin.cast hScard.symm r)).2
    rw [Finset.mem_sdiff] at hmem
    exact ⟨(Finset.mem_filter.mp hmem.1).2, hmem.2⟩

open scoped ENNReal in
/-- **The single-squeeze forking *failure* bound** — the failure-side complement of
`exists_injective_accepting_of_measure`. Over one fresh uniform challenge `χ`, the event "`acc χ` holds
yet the accept measure sits at or below the threshold `t`" has measure `≤ t`: the threshold condition is
`χ`-independent, so the event is either all of `{χ | acc χ}` (when the measure `≤ t`, whence its measure
`≤ t`) or empty. This is the counting core turning each multiopen squeeze's `hprob` floor into a bounded
failure probability. -/
theorem uniformOfFintype_accept_below_threshold_le {α : Type*} [Fintype α] [Nonempty α]
    [DecidableEq α] (acc : α → Prop) [DecidablePred acc] (t : ℝ≥0∞) :
    (PMF.uniformOfFintype α).toOuterMeasure
        {χ : α | acc χ ∧ (PMF.uniformOfFintype α).toOuterMeasure (Finset.univ.filter acc) ≤ t}
      ≤ t := by
  by_cases h : (PMF.uniformOfFintype α).toOuterMeasure (Finset.univ.filter acc) ≤ t
  · have hset : {χ : α | acc χ ∧
        (PMF.uniformOfFintype α).toOuterMeasure (Finset.univ.filter acc) ≤ t}
        = {χ : α | acc χ} := by
      ext χ
      simp only [Set.mem_setOf_eq, and_iff_left_iff_imp]
      intro _; exact h
    have hcoe : {χ : α | acc χ} = (↑(Finset.univ.filter acc) : Set α) := by
      ext χ; simp [Finset.coe_filter]
    rw [hset, hcoe]
    exact h
  · have hset : {χ : α | acc χ ∧
        (PMF.uniformOfFintype α).toOuterMeasure (Finset.univ.filter acc) ≤ t} = ∅ := by
      ext χ
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro _; exact h
    rw [hset]; simp

end Zcash.Snark
