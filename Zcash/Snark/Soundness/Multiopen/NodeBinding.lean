import Zcash.Snark.Soundness.Multiopen.Claimed
import Zcash.Snark.Soundness.Multiopen.ValueCheckDeployed

/-!
# F3: the deployed `x₃` value bridge

The multiopen value check binds each decoded aggregate column to its claimed interpolation. The
counting-floor core (`Soundness.Multiopen.Claimed.claimedEval_of_x3Prob`) already turns an `x₃`
accept measure plus a per-accepting-run *consistency* — the decoded column reproduces the deployed
`r`-value at the accepting interpolation challenge — into the node binding: at each rotated set
point, the aggregate column's value is the claimed evaluation.

Two routes to that instantiation once lived here. The *aggregate route* fixed the decoded column to
the fingerprinted `x₄`-slot aggregate for point set `j` and the accept event to `OpenedX3Accept`,
leaving the per-run consistency `hconsistent` — equivalently the inner `hx2cons` — as an open
obligation. It was abandoned (`X2Run` re-sends `q′` across `x₂`-rewinds, so there is no fixed-`q′`
anchor at `x₂` to discharge `hx2cons` against) and has been removed.

The *fixed-`q′` route* anchored on the `q′` absorbed before `x₃`
(`openedDecodedCols_top_eval_x3`), discharging `hconsistent`/`hx2cons` end-to-end from the accept
floors. Its node-binding chain has been removed: every rung concluded an ∃-closed binding disjunct,
which a prime-order group satisfies unconditionally and so cannot be charged to DLOG. The deployed
capstones now take the rewind-free AGM route, which returns explicit augmented-basis coefficients
on disagreement; what remains here is the grid and decode apparatus that route reads.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (Msm Msm.zero)

-- The deployed grouping definitions appear inside index types, so a defeq check on an index can
-- pull the whole `constructIntermediateSets (assembleQueries …)` computation through `whnf`.
-- Sealing them keeps those checks syntactic; the proofs below use their equation lemmas.
attribute [local irreducible] deployedSetQueries deployedSetCommIds deployedX4PairCount
  x4BatchCommitments x4BatchEvals

open Polynomial
open scoped ENNReal
open Classical

variable {G : Type*} [AddCommGroup G] [Module Fp G]










/-- The product over a distinct point list's *indices* equals the product over its point *finset* —
the `hsamp` denominator's product-shape conversion (`∏ over range length` ↔ `∏ over deployedSetPts`). -/
theorem prod_range_getD_eq_toFinset {l : List Fp} (hnd : l.Nodup) (χ : Fp) :
    (∏ m ∈ Finset.range l.length, (χ - l.getD m 0)) = ∏ p ∈ l.toFinset, (χ - p) := by
  rw [← Fin.prod_univ_eq_prod_range (fun m => χ - l.getD m 0) l.length]
  refine Finset.prod_bij (fun (i : Fin l.length) _ => l.get i) ?_ ?_ ?_ ?_
  · intro i _; exact List.mem_toFinset.mpr (List.get_mem l i)
  · intro i _ i' _ h
    exact (List.nodup_iff_injective_get.mp hnd) (by simpa using h)
  · intro p hp
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp hp)
    exact ⟨i, Finset.mem_univ _, hi⟩
  · intro i _
    simp [List.get_eq_getElem, i.isLt]

/-- Inverse form of the product-shape conversion. -/
theorem prod_inv_range_getD_eq_toFinset {l : List Fp} (hnd : l.Nodup) (χ : Fp) :
    (∏ m ∈ Finset.range l.length, (χ - l.getD m 0)⁻¹) = (∏ p ∈ l.toFinset, (χ - p))⁻¹ := by
  rw [← prod_range_getD_eq_toFinset hnd χ, ← Finset.prod_inv_distrib]

/-- **`hsamp` from the value-check power form (reversed convention).** The per-`x₂`-value multiopen
identity in exactly the shape `node_binding_of_samples` consumes, set index reversed (`ζʲ` pairs
with `sets.reverse.getD j`, resolving the power/index convention gap): given the run's opening and
the field identifications, the value expands to `∑ⱼ ζʲ (colⱼ − rⱼ)(χ)·(∏ p∈pts j, (χ − p))⁻¹`.
Pure algebra over `multiopenEval_powerForm`. -/
theorem hsamp_of_multiopenEval_reversed {numSets : ℕ}
    (sets : List (List Fp × List Fp × Fp)) (hlen : sets.length = numSets)
    (col r : Fin numSets → Polynomial Fp) (pts : Fin numSets → Finset Fp)
    (ζ χ qv : Fp)
    (hqv : qv = multiopenEval ζ χ sets)
    (hnd : ∀ j : Fin numSets, (sets.reverse.getD (j : ℕ) ([], [], 0)).1.Nodup)
    (hpts : ∀ j : Fin numSets, (sets.reverse.getD (j : ℕ) ([], [], 0)).1.toFinset = pts j)
    (hu : ∀ j : Fin numSets, (col j).eval χ = (sets.reverse.getD (j : ℕ) ([], [], 0)).2.2)
    (hr : ∀ j : Fin numSets, (r j).eval χ
        = lagrangeEval χ (sets.reverse.getD (j : ℕ) ([], [], 0)).1
            (sets.reverse.getD (j : ℕ) ([], [], 0)).2.1) :
    qv = ∑ j : Fin numSets, ζ ^ (j : ℕ) * (col j - r j).eval χ * (∏ p ∈ pts j, (χ - p))⁻¹ := by
  rw [hqv, multiopenEval_powerForm, hlen, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [eval_sub, hu j, hr j, ← hpts j, ← prod_inv_range_getD_eq_toFinset (hnd j) χ]
  ring


/-- The deployed multiopen value-check `sets` (halo2 `setsForEval`): per point set, its points, the
`x₁`-compressed evaluation vector, and the prover's claimed set evaluation `multiopenUⱼ`. This is the
list `deployedBaseEval` feeds `multiopenEval`; naming it lets the value check's field identifications
be stated. -/
noncomputable def deployedSetsForEval [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) :
    List (List Fp × List Fp × Fp) :=
  let grouped := constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)
  let compressed := (grouped.sets.zip grouped.points).map (fun sp => compressSet ch.x1 sp.1 sp.2.length)
  ((grouped.points.zip (compressed.map Prod.snd)).zip (List.ofFn ps.multiopenU)).map
    (fun p => (p.1.1, p.1.2, p.2))

omit [AddCommGroup G] [Module Fp G] in
/-- `deployedBaseEval` is `multiopenEval` over `deployedSetsForEval` — definitional. -/
theorem deployedBaseEval_eq_multiopenEval [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) :
    deployedBaseEval vk instanceCommitment ps ch = multiopenEval ch.x2 ch.x3 (deployedSetsForEval vk instanceCommitment ps ch) := rfl

omit [AddCommGroup G] [Module Fp G] in
/-- **Shape alignment: the value-check `sets` has exactly `deployedX4PairCount` entries.** Both reduce
to `min(min(gsets.length, gpoints.length), numPointSets)` — the grouping's set count clipped to the
prover's claimed-eval count — so no `= shape.numPointSets` fact is needed. This lets the deployed
value check be instantiated at `numSets := deployedX4PairCount`. -/
theorem deployedSetsForEval_length [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) :
    (deployedSetsForEval vk instanceCommitment ps ch).length = deployedX4PairCount vk instanceCommitment ps ch := by
  have hsp := constructIntermediateSets_points_length (assembleQueries vk instanceCommitment ps ch)
  simp only [deployedSetsForEval, deployedX4PairCount, deployedX4Pairs, deployedX4Qs,
    List.length_map, List.length_zip, List.length_ofFn]
  omega

omit [AddCommGroup G] [Module Fp G] in
/-- The `j`-th value-check set's point list is grouping point set `j`'s points — so its finset is
`deployedSetPts j`. The points-field identification for the grid openings. -/
theorem deployedSetsForEval_getD_points [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {k : ℕ} (hk : k < deployedX4PairCount vk instanceCommitment ps ch) :
    ((deployedSetsForEval vk instanceCommitment ps ch).getD k ([], [], 0)).1
      = (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD k [] := by
  have hlen := deployedSetsForEval_length vk instanceCommitment ps ch
  have hsp := constructIntermediateSets_points_length (assembleQueries vk instanceCommitment ps ch)
  have hcount : deployedX4PairCount vk instanceCommitment ps ch
      ≤ (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.length := by
    simp only [deployedX4PairCount, deployedX4Pairs, deployedX4Qs, List.length_map,
      List.length_zip, List.length_ofFn]
    omega
  rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact hk),
    List.getD_eq_getElem _ _ (by omega)]
  simp only [deployedSetsForEval, List.getElem_map, List.getElem_zip]

omit [AddCommGroup G] [Module Fp G] in
/-- The `j`-th value-check set's point finset is exactly `deployedSetPts j` — the `hpts`
field-identification for the grid openings. -/
theorem deployedSetsForEval_getD_toFinset [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {k : ℕ} (hk : k < deployedX4PairCount vk instanceCommitment ps ch) :
    ((deployedSetsForEval vk instanceCommitment ps ch).getD k ([], [], 0)).1.toFinset = deployedSetPts vk instanceCommitment ps ch k := by
  rw [deployedSetsForEval_getD_points vk instanceCommitment ps ch hk, deployedSetPts]

omit [AddCommGroup G] [Module Fp G] in
/-- The `j`-th value-check set's point list is duplicate-free — the `hnd` field-identification for
the grid openings, via `constructIntermediateSets_points_nodup`. -/
theorem deployedSetsForEval_getD_nodup [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {k : ℕ} (hk : k < deployedX4PairCount vk instanceCommitment ps ch) :
    ((deployedSetsForEval vk instanceCommitment ps ch).getD k ([], [], 0)).1.Nodup := by
  rw [deployedSetsForEval_getD_points vk instanceCommitment ps ch hk]
  exact constructIntermediateSets_points_nodup _ _

omit [AddCommGroup G] [Module Fp G] in
/-- The `reverse`d value-check `sets`, at index `k`, reads grouping set `numSets − 1 − k`'s point
list — the reversed index the `multiopenEval` power convention pairs `x₂^k` with. -/
theorem deployedSetsForEval_reverse_getD_points [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {k : ℕ} (hk : k < deployedX4PairCount vk instanceCommitment ps ch) :
    ((deployedSetsForEval vk instanceCommitment ps ch).reverse.getD k ([], [], 0)).1
      = (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD
          (deployedX4PairCount vk instanceCommitment ps ch - 1 - k) [] := by
  have hlen := deployedSetsForEval_length vk instanceCommitment ps ch
  have htup : (deployedSetsForEval vk instanceCommitment ps ch).reverse.getD k ([], [], 0)
      = (deployedSetsForEval vk instanceCommitment ps ch).getD (deployedX4PairCount vk instanceCommitment ps ch - 1 - k) ([], [], 0) := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_reverse (by rw [hlen]; exact hk), hlen]
  rw [htup]
  exact deployedSetsForEval_getD_points vk instanceCommitment ps ch (by omega)

omit [AddCommGroup G] [Module Fp G] in
/-- The reversed value-check set's point finset is `deployedSetPts (numSets − 1 − k)` — the `hpts`
field-ID at the reversed indexing. -/
theorem deployedSetsForEval_reverse_getD_toFinset [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {k : ℕ} (hk : k < deployedX4PairCount vk instanceCommitment ps ch) :
    ((deployedSetsForEval vk instanceCommitment ps ch).reverse.getD k ([], [], 0)).1.toFinset
      = deployedSetPts vk instanceCommitment ps ch (deployedX4PairCount vk instanceCommitment ps ch - 1 - k) := by
  rw [deployedSetsForEval_reverse_getD_points vk instanceCommitment ps ch hk, deployedSetPts]

omit [AddCommGroup G] [Module Fp G] in
/-- The reversed value-check set's point list is `Nodup` — the `hnd` field-ID at the reversed
indexing. -/
theorem deployedSetsForEval_reverse_getD_nodup [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {k : ℕ} (hk : k < deployedX4PairCount vk instanceCommitment ps ch) :
    ((deployedSetsForEval vk instanceCommitment ps ch).reverse.getD k ([], [], 0)).1.Nodup := by
  rw [deployedSetsForEval_reverse_getD_points vk instanceCommitment ps ch hk]
  exact constructIntermediateSets_points_nodup _ _

omit [AddCommGroup G] [Module Fp G] in
/-- The reversed value-check set's claimed-eval (`u`) field at index `k` is the batch eval slot `k`
(`x4BatchEvals`) — the `u`-field counterpart of `deployedSetsForEval_reverse_getD_points`. Both reduce
to the prover's claimed set eval `multiopenU` at position `count − 1 − k`: `deployedSetsForEval`'s
`.2.2` and `deployedX4Pairs`'s `.2` are the same `List.ofFn ps.multiopenU` component. This is the
identity matching `x4BatchEvals` values to `(sets s t).reverse.getD j |>.2.2`. -/
theorem deployedSetsForEval_reverse_getD_u [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {k : ℕ} (hk : k < deployedX4PairCount vk instanceCommitment ps ch) :
    ((deployedSetsForEval vk instanceCommitment ps ch).reverse.getD k ([], [], 0)).2.2
      = x4BatchEvals vk instanceCommitment ps ch ⟨k, Nat.lt_succ_of_lt hk⟩ := by
  have hlenS := deployedSetsForEval_length vk instanceCommitment ps ch
  have hlenP : (deployedX4Pairs vk instanceCommitment ps ch).length = deployedX4PairCount vk instanceCommitment ps ch :=
    (deployedX4PairCount_eq vk instanceCommitment ps ch).symm
  have hik : deployedX4PairCount vk instanceCommitment ps ch - 1 - k < deployedX4PairCount vk instanceCommitment ps ch := by omega
  -- per-index: both the value-check set's u-field and the batch pair's eval are `multiopenU[i]`
  have key : ((deployedSetsForEval vk instanceCommitment ps ch).getD
        (deployedX4PairCount vk instanceCommitment ps ch - 1 - k) ([], [], 0)).2.2
      = ((deployedX4Pairs vk instanceCommitment ps ch).getD
        (deployedX4PairCount vk instanceCommitment ps ch - 1 - k) (Msm.zero shape.k Fp G, 0)).2 := by
    rw [List.getD_eq_getElem _ _ (by rw [hlenS]; exact hik),
        List.getD_eq_getElem _ _ (by rw [hlenP]; exact hik)]
    simp only [deployedSetsForEval, deployedX4Pairs, List.getElem_map, List.getElem_zip]
  -- reduce `x4BatchEvals ⟨k⟩` (k < count) and both reverses to forward `getD (count−1−k)`
  rw [x4BatchEvals]
  simp only [hk, if_true]
  rw [List.getD_eq_getElem?_getD (l := (deployedSetsForEval vk instanceCommitment ps ch).reverse),
      List.getElem?_reverse (by rw [hlenS]; exact hk), hlenS,
      ← List.getD_eq_getElem?_getD,
      List.getD_eq_getElem?_getD (l := (deployedX4Pairs vk instanceCommitment ps ch).reverse),
      List.getElem?_reverse (by rw [hlenP]; exact hk), hlenP,
      ← List.getD_eq_getElem?_getD]
  exact key












/-- A coefficient-vector polynomial has degree below its length: each summand `C aᵢ · Xⁱ` has
`natDegree ≤ i < n`. The decoded batch columns (`openedDecodedCols`) are `coeffsToPoly` of
`Fin (2 ^ k)` vectors, so their degree is below `2 ^ k`. -/
theorem coeffsToPoly_natDegree_lt {n : ℕ} (hn : 0 < n) (a : Fin n → Fp) :
    (coeffsToPoly a).natDegree < n := by
  have hle : (coeffsToPoly a).natDegree ≤ n - 1 := by
    rw [coeffsToPoly]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun i _ => ?_)
    calc (Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)).natDegree
        ≤ (Polynomial.X ^ (i : ℕ) : Polynomial Fp).natDegree :=
          Polynomial.natDegree_C_mul_le _ _
      _ = (i : ℕ) := Polynomial.natDegree_X_pow _
      _ ≤ n - 1 := by have := i.isLt; omega
  omega

/-- The `r`-interpolant's degree is at most the node count — the `≤` form of
`lagrangePoly_natDegree_lt`, covering the empty point list (where the interpolant is `0`). -/
theorem lagrangePoly_natDegree_le {points evals : List Fp}
    (hnode : Function.Injective (fun i : Fin points.length => points[i])) :
    (lagrangePoly points evals).natDegree ≤ points.length := by
  rcases Nat.eq_zero_or_pos points.length with h0 | hpos
  · haveI : IsEmpty (Fin points.length) := by rw [h0]; exact Fin.isEmpty
    rw [lagrangePoly, Finset.univ_eq_empty, Lagrange.interpolate_empty,
      Polynomial.natDegree_zero]
    exact Nat.zero_le _
  · exact le_of_lt (lagrangePoly_natDegree_lt hpos hnode)

/-- The vanishing polynomial's degree is at most its point count. -/
theorem vanishingProd_natDegree_le (pts : Finset Fp) :
    (vanishingProd pts).natDegree ≤ pts.card := by
  rw [vanishingProd]
  calc (∏ p ∈ pts, (X - C p)).natDegree
      ≤ ∑ p ∈ pts, (X - C p).natDegree := Polynomial.natDegree_prod_le _ _
    _ = pts.card := by simp

/-- The complementary product's degree is at most the full point count. -/
theorem coProd_natDegree_le (all pts : Finset Fp) :
    (coProd all pts).natDegree ≤ all.card :=
  le_trans (vanishingProd_natDegree_le _) (Finset.card_le_card Finset.sdiff_subset)



/-! ## F2: the `x₁` member un-batch -/

/-- **The compression fold's evaluation accumulator, generically.** Over the raw fold
state (accumulator `ev`, running power `pw`): each member `m` contributes its claimed-eval list
scaled by the running `x₁`-power, so the folded entry at any in-range point index is the starting
entry plus `pw` times the `x₁`-power fold of the members' claimed evaluations at that index. The
member eval lists must carry one entry per set point (`hlens`) for the `zip` not to truncate. -/
theorem compressSet_evals_foldl {k' : ℕ} {F G' : Type*} [Field F]
    (x1 : F) (sq : List (CommitmentRef k' F G' × List F))
    (d₀ : CommitmentRef k' F G' × List F) {np idx : ℕ} (hidx : idx < np)
    (hlens : ∀ qc ∈ sq, qc.2.length = np) :
    ∀ (msm : Msm k' F G') (ev : List F) (pw : F), ev.length = np →
      (sq.foldl (fun (st : Msm k' F G' × List F × F) qc =>
          (accumulateCommitment st.2.2 qc.1 st.1,
           (st.2.1.zip qc.2).map (fun e => e.1 + e.2 * st.2.2),
           st.2.2 * x1)) (msm, ev, pw)).2.1.getD idx 0
        = ev.getD idx 0
          + pw * (∑ m ∈ Finset.range sq.length,
              x1 ^ m * ((sq.getD m d₀).2.getD idx 0)) := by
  induction sq with
  | nil => intro msm ev pw hev; simp
  | cons qc sq ih =>
      intro msm ev pw hev
      rw [List.foldl_cons]
      dsimp only
      have hqclen : qc.2.length = np := hlens qc (List.mem_cons_self ..)
      have hevlen' : ((ev.zip qc.2).map (fun e => e.1 + e.2 * pw)).length = np := by
        rw [List.length_map, List.length_zip, hev, hqclen, min_self]
      rw [ih (fun qc' hqc' => hlens qc' (List.mem_cons_of_mem _ hqc')) _ _ _ hevlen']
      have hentry : ((ev.zip qc.2).map (fun e => e.1 + e.2 * pw)).getD idx 0
          = ev.getD idx 0 + qc.2.getD idx 0 * pw := by
        rw [List.getD_eq_getElem _ _ (by rw [hevlen']; exact hidx),
          List.getD_eq_getElem _ _ (by rw [hev]; exact hidx),
          List.getD_eq_getElem _ _ (by rw [hqclen]; exact hidx)]
        simp [List.getElem_zip]
      rw [hentry, List.length_cons, Finset.sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, one_mul, mul_add,
        Finset.mul_sum]
      rw [show (∑ m ∈ Finset.range sq.length,
            pw * x1 * (x1 ^ m * ((sq.getD m d₀).2.getD idx 0)))
          = ∑ m ∈ Finset.range sq.length,
            pw * (x1 ^ (m + 1) * ((sq.getD m d₀).2.getD idx 0)) from
        Finset.sum_congr rfl (fun m _ => by ring)]
      ring

/-- **The compressed set evaluations are the `x₁`-power folds of the member evaluations (F2 stage
A).** At any in-range point index, `compressSet`'s evaluation vector entry is
`∑ₘ x₁^m · (member m's claimed eval at that point)`. -/
theorem compressSet_snd_getD {k' : ℕ} {F G' : Type*} [Field F]
    (x1 : F) (sq : List (CommitmentRef k' F G' × List F))
    (d₀ : CommitmentRef k' F G' × List F) {np idx : ℕ} (hidx : idx < np)
    (hlens : ∀ qc ∈ sq, qc.2.length = np) :
    (compressSet x1 sq np).2.getD idx 0
      = ∑ m ∈ Finset.range sq.length, x1 ^ m * ((sq.getD m d₀).2.getD idx 0) := by
  have h := compressSet_evals_foldl x1 sq d₀ hidx hlens (Msm.zero k' F G')
    (List.replicate np (0 : F)) 1 (by simp)
  simp only [compressSet]
  rw [h, List.getD_eq_getElem _ _ (by rw [List.length_replicate]; exact hidx),
    List.getElem_replicate, one_mul, zero_add]

omit [AddCommGroup G] [Module Fp G] in
/-- The `k`-th value-check set's compressed evaluation vector is `compressSet`'s — the evals-field
identification for the deployed sets (the `.2.1` companion of `deployedSetsForEval_getD_points`). -/
theorem deployedSetsForEval_getD_evals [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {k : ℕ} (hk : k < deployedX4PairCount vk instanceCommitment ps ch) :
    ((deployedSetsForEval vk instanceCommitment ps ch).getD k ([], [], 0)).2.1
      = (compressSet ch.x1 (deployedSetQueries vk instanceCommitment ps ch k)
          ((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD k []).length).2 := by
  have hsp := constructIntermediateSets_points_length (assembleQueries vk instanceCommitment ps ch)
  have hcnt : deployedX4PairCount vk instanceCommitment ps ch
      ≤ (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.length := by
    simp only [deployedX4PairCount, deployedX4Pairs, deployedX4Qs, List.length_map,
      List.length_zip, List.length_ofFn]
    omega
  have hzip : k < ((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).sets.zip
      (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points).length := by
    rw [List.length_zip]
    omega
  have hpts : k < (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.length := by
    omega
  rw [List.getD_eq_getElem _ _ (by rw [deployedSetsForEval_length]; exact hk)]
  simp only [deployedSetsForEval, List.getElem_map, List.getElem_zip]
  simp only [deployedSetQueries]
  rw [List.getD_eq_getElem _ _ hzip, List.getD_eq_getElem _ _ hpts]
  simp only [List.getElem_zip]



/-! ### `deployedAllPts` splice-invariance

The union of all deployed point sets — whose cardinality is the `x₃` (`hprob3`) threshold in the
derived terminal — is built entirely from `constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)`
(`deployedAllPts`/`deployedSetPts`, `ValueCheckDeployed`), so it inherits the `assembleQueries`
seal (`x{1,2,3,4}Run_assembleQueries`, `Deployed`) verbatim: the rewound base's point union — hence
its cardinality — is the honest one. Together with `x{1,2,3,4}Run_pairCount`/`_setQueries` (already
in `Deployed`), this shows *every* deployed threshold is a splice-invariant structural constant, the
enabling fact for reading the run-indexed floors off the base-independent budget. -/










omit [AddCommGroup G] [Module Fp G] in
/-- **`hql` discharged: each routed member of a deployed point set claims one evaluation per set
point** (`constructIntermediateSets_eval_length` at the deployed queries). This closes the
one structural bookkeeping premise the per-member value check needs. -/
theorem deployedSetQueries_eval_length [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (i : ℕ) :
    ∀ qc ∈ deployedSetQueries vk instanceCommitment ps ch i,
      qc.2.length
        = ((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i []).length := by
  intro qc hqc
  refine constructIntermediateSets_eval_length (assembleQueries vk instanceCommitment ps ch) i qc ?_
  simpa only [deployedSetQueries, constructIntermediateSets_zip_sets_getD] using hqc



/-! ## F5: the rotated-point member binding and the derived gate feed -/

/-- The rotated gate feed's value at the gate point is the member column's value at the rotated
query point: `rotatedFeed` composes the column with `ω^rot·X`, so evaluation at `x` lands at
`ω^rot·x = rotateOmega ω x rot`. -/
theorem rotatedFeed_eval {n : ℕ} (omega : Fp) (layout : List (ℕ × ℤ))
    (col : Fin n → Polynomial Fp) {j : ℕ} (hj : j < n) (x : Fp) :
    (rotatedFeed omega layout col j).eval x
      = (col ⟨j, hj⟩).eval (rotateOmega omega x (layout.getD j (0, 0)).2) := by
  simp only [rotatedFeed, finFn, dif_pos hj, Polynomial.eval_comp, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, rotateOmega]
  exact congrArg (fun t => Polynomial.eval t (col ⟨j, hj⟩))
    (mul_comm (omega ^ (layout.getD j (0, 0)).2) x)

/-- Out of the layout's range the rotated feed is the zero polynomial. -/
theorem rotatedFeed_eval_of_ge {n : ℕ} (omega : Fp) (layout : List (ℕ × ℤ))
    (col : Fin n → Polynomial Fp) {j : ℕ} (hj : n ≤ j) (x : Fp) :
    (rotatedFeed omega layout col j).eval x = 0 := by
  simp only [rotatedFeed, finFn, dif_neg (Nat.not_lt.mpr hj), Polynomial.eval_zero]






end Zcash.Snark
