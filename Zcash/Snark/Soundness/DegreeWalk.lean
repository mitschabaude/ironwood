import Zcash.Snark.Soundness.Constraints

/-!
# Degree accounting for the combined constraint polynomial

The good-challenge term prices the squeeze bad set at `εx`, the Schwartz–Zippel measure of the
combined constraint difference. This module walks the constraint builders and bounds that
difference's `natDegree` by an explicit `D`, giving `εx = D / |𝔽|`.

The walk covers a syntactic degree per gate expression (`Expr.degreeBound`), per-member bounds for
the permutation and lookup values, the `acc·y + v` fold, and the pre-`x` quotient tail. Throughout,
`B` bounds every polynomial input and the caller supplies a `D` dominating each family's product
depth times `B`.
-/

namespace Zcash.Snark

open Polynomial

/-- Syntactic degree of a gate expression, counting column leaves per multiplicative branch:
leaves are `1`, products add, sums take the max. Evaluated at column polynomials of degree `≤ B`,
the gate's polynomial has degree `≤ degreeBound · B` (`natDegree_eval_map_C_le`). -/
def Expr.degreeBound {F : Type*} : Expr F → ℕ
  | .constant _ => 0
  | .fixed _ => 1
  | .advice _ => 1
  | .instance _ => 1
  | .negated a => a.degreeBound
  | .sum a b => max a.degreeBound b.degreeBound
  | .product a b => a.degreeBound + b.degreeBound
  | .scaled a _ => a.degreeBound

/-- A gate expression with scalar constants, evaluated at column polynomials of degree `≤ B`, has
degree at most `degreeBound · B`: constants contribute nothing, leaves one column each, products
add. -/
theorem natDegree_eval_map_C_le {B : ℕ} {fx av inst : ℕ → Polynomial Fp}
    (hfx : ∀ i, (fx i).natDegree ≤ B) (hav : ∀ i, (av i).natDegree ≤ B)
    (hinst : ∀ i, (inst i).natDegree ≤ B) (e : Expr Fp) :
    ((e.map Polynomial.C).eval fx av inst).natDegree ≤ e.degreeBound * B := by
  induction e with
  | constant c => simp [Expr.map, Expr.eval, Expr.degreeBound]
  | fixed i => simpa [Expr.map, Expr.eval, Expr.degreeBound] using hfx i
  | advice i => simpa [Expr.map, Expr.eval, Expr.degreeBound] using hav i
  | «instance» i => simpa [Expr.map, Expr.eval, Expr.degreeBound] using hinst i
  | negated a ih => simpa [Expr.map, Expr.eval, Expr.degreeBound, natDegree_neg] using ih
  | sum a b iha ihb =>
      refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_)
      · exact le_trans iha (Nat.mul_le_mul_right B (le_max_left _ _))
      · exact le_trans ihb (Nat.mul_le_mul_right B (le_max_right _ _))
  | product a b iha ihb =>
      refine le_trans (natDegree_mul_le) ?_
      rw [Expr.degreeBound, add_mul]
      exact Nat.add_le_add iha ihb
  | scaled a c ih =>
      refine le_trans (natDegree_mul_le) ?_
      simpa [Expr.map, Expr.degreeBound] using ih

/-- The `θ`-compression of a list of gate expressions keeps the members' degree bound: the fold
`acc·θ + e` never multiplies two columns. -/
theorem natDegree_compressExprs_le {B D : ℕ} {fx av inst : ℕ → Polynomial Fp}
    (hfx : ∀ i, (fx i).natDegree ≤ B) (hav : ∀ i, (av i).natDegree ≤ B)
    (hinst : ∀ i, (inst i).natDegree ≤ B) (theta : Fp) (exprs : List (Expr Fp))
    (hD : ∀ e ∈ exprs, e.degreeBound * B ≤ D) :
    (compressExprs fx av inst (Polynomial.C theta) (exprs.map (Expr.map Polynomial.C))).natDegree
      ≤ D := by
  rw [compressExprs]
  suffices h : ∀ acc : Polynomial Fp, acc.natDegree ≤ D →
      ((exprs.map (Expr.map Polynomial.C)).foldl
        (fun acc e => acc * Polynomial.C theta + e.eval fx av inst) acc).natDegree ≤ D by
    exact h 0 (by simp)
  induction exprs with
  | nil => intro acc hacc; simpa using hacc
  | cons e t ih =>
      intro acc hacc
      rw [List.map_cons, List.foldl_cons]
      refine ih (fun e' he' => hD e' (List.mem_cons_of_mem _ he')) _
        (le_trans (natDegree_add_le _ _) (max_le ?_ ?_))
      · exact le_trans natDegree_mul_le (by simpa using hacc)
      · exact le_trans (natDegree_eval_map_C_le hfx hav hinst e)
          (hD e (List.mem_cons_self ..))

/-- One chunk step's degree: the two running products carry one factor of degree `≤ B` per
column plus the carrier, and the switch-off multiplies one more selector — `(W + 2)·B` for chunk
width `≤ W`. -/
theorem natDegree_permChunk_le {B W : ℕ} (hB : 1 ≤ B)
    (beta gamma delta : Fp) (chunkLen chunkIndex : ℕ)
    (set : PermSetEval (Polynomial Fp)) (pairs : List (Polynomial Fp × Polynomial Fp))
    (lLast lBlind : Polynomial Fp)
    (hev : set.eval.natDegree ≤ B) (hnext : set.nextEval.natDegree ≤ B)
    (hpairs : ∀ p ∈ pairs, p.1.natDegree ≤ B ∧ p.2.natDegree ≤ B)
    (hlen : pairs.length ≤ W)
    (hll : lLast.natDegree ≤ B) (hlb : lBlind.natDegree ≤ B) :
    (permChunkExpression (Polynomial.C beta) (Polynomial.C gamma) Polynomial.X
      (Polynomial.C delta) chunkLen chunkIndex set pairs lLast lBlind).natDegree
      ≤ (W + 2) * B := by
  have hprod : ∀ f : ℕ → Polynomial Fp, (∀ j ∈ Finset.range pairs.length, (f j).natDegree ≤ B) →
      (∏ j ∈ Finset.range pairs.length, f j).natDegree ≤ W * B := by
    intro f hf
    refine le_trans (natDegree_prod_le _ _) (le_trans (Finset.sum_le_card_nsmul _ _ B hf) ?_)
    simpa [smul_eq_mul] using Nat.mul_le_mul_right B hlen
  have hmem : ∀ j ∈ Finset.range pairs.length, pairs.getD j (0, 0) ∈ pairs := by
    intro j hj
    rw [List.getD_eq_getElem _ _ (Finset.mem_range.mp hj)]
    exact List.getElem_mem _
  rw [permChunkExpression_eq]
  refine le_trans natDegree_mul_le ?_
  have hsel : ((1 : Polynomial Fp) - (lLast + lBlind)).natDegree ≤ B :=
    le_trans (natDegree_sub_le _ _)
      (max_le (by simp) (le_trans (natDegree_add_le _ _) (max_le hll hlb)))
  refine le_trans (Nat.add_le_add ?_ hsel)
    (show B + W * B + B ≤ (W + 2) * B by ring_nf; omega)
  -- the product difference: each side is carrier · ∏ factors
  refine le_trans (natDegree_sub_le _ _) (max_le ?_ ?_)
  · refine le_trans natDegree_mul_le (Nat.add_le_add hnext (hprod _ ?_))
    intro j hj
    refine le_trans (natDegree_add_le _ _) (max_le (le_trans (natDegree_add_le _ _)
      (max_le ((hpairs _ (hmem j hj)).1) ?_)) (by simp))
    exact le_trans natDegree_mul_le
      (by simpa using (hpairs _ (hmem j hj)).2)
  · refine le_trans natDegree_mul_le (Nat.add_le_add hev (hprod _ ?_))
    intro j hj
    have heq : (Polynomial.C beta * Polynomial.X * Polynomial.C delta ^ (chunkIndex * chunkLen)
        * Polynomial.C delta ^ j : Polynomial Fp)
        = Polynomial.C (beta * delta ^ (chunkIndex * chunkLen) * delta ^ j) * Polynomial.X := by
      simp only [Polynomial.C_mul, Polynomial.C_pow]
      ring
    refine le_trans (natDegree_add_le _ _) (max_le (le_trans (natDegree_add_le _ _)
      (max_le ((hpairs _ (hmem j hj)).1) ?_)) (by simp))
    rw [heq]
    exact le_trans (natDegree_C_mul_le _ _) (le_trans natDegree_X_le hB)

/-- Every permutation constraint value has degree at most `D`, for `D` dominating `3·B` (the
boundary and chaining rules) and `(W + 2)·B` (the chunk steps). -/
theorem natDegree_permutationExpressions_le {B W D : ℕ} (hB : 1 ≤ B)
    (sets : List (PermSetEval (Polynomial Fp)))
    (chunks : List (PermSetEval (Polynomial Fp) × List (Polynomial Fp × Polynomial Fp)))
    (beta gamma delta : Fp) (chunkLen : ℕ) (l0 lLast lBlind : Polynomial Fp)
    (hsets : ∀ s ∈ sets, s.eval.natDegree ≤ B ∧ (s.lastEval.getD 0).natDegree ≤ B)
    (hchunks : ∀ c ∈ chunks, (c.1.eval.natDegree ≤ B ∧ c.1.nextEval.natDegree ≤ B)
      ∧ c.2.length ≤ W ∧ ∀ p ∈ c.2, p.1.natDegree ≤ B ∧ p.2.natDegree ≤ B)
    (hl0 : l0.natDegree ≤ B) (hll : lLast.natDegree ≤ B) (hlb : lBlind.natDegree ≤ B)
    (h3 : 3 * B ≤ D) (hWD : (W + 2) * B ≤ D) :
    ∀ q ∈ permutationExpressions sets chunks (Polynomial.C beta) (Polynomial.C gamma)
      Polynomial.X (Polynomial.C delta) chunkLen l0 lLast lBlind, q.natDegree ≤ D := by
  intro q hq
  rw [permutationExpressions] at hq
  rcases List.mem_append.mp hq with hq' | hq'
  · rcases List.mem_append.mp hq' with hq'' | hq''
    · rcases List.mem_append.mp hq'' with hh | hh
      · -- the start rule
        rcases hhead : sets.head? with _ | first
        · rw [hhead] at hh; simp at hh
        · rw [hhead] at hh
          rcases List.mem_singleton.mp hh with rfl
          have hfirst := hsets first (List.mem_of_mem_head? (by rw [hhead]; rfl))
          refine le_trans natDegree_mul_le (le_trans (Nat.add_le_add hl0
            (le_trans (natDegree_sub_le _ _) (max_le (by simp) hfirst.1))) (by omega))
      · -- the end rule
        rcases hlast : sets.getLast? with _ | last
        · rw [hlast] at hh; simp at hh
        · rw [hlast] at hh
          rcases List.mem_singleton.mp hh with rfl
          have hl := hsets last (List.mem_of_getLast? hlast)
          have h2B : (last.eval ^ 2 - last.eval).natDegree ≤ 2 * B :=
            le_trans (natDegree_sub_le _ _) (max_le
              (le_trans natDegree_pow_le (Nat.mul_le_mul_left 2 hl.1))
              (le_trans hl.1 (by omega)))
          exact le_trans natDegree_mul_le (le_trans (Nat.add_le_add h2B hll) (by omega))
    · -- the chaining rule
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq''
      obtain ⟨hp1, hp2⟩ := List.of_mem_zip hp
      have h1 := hsets p.1 (List.mem_of_mem_drop hp1)
      have h2 := hsets p.2 hp2
      refine le_trans natDegree_mul_le (le_trans (Nat.add_le_add (le_trans
        (natDegree_sub_le _ _) (max_le h1.1 h2.2)) hl0) (by omega))
  · -- the chunk steps
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq'
    exact le_trans (natDegree_permChunk_le hB beta gamma delta chunkLen p.1 p.2.1 p.2.2
      lLast lBlind (hchunks p.2 (List.of_mem_zip hp).2).1.1
      (hchunks p.2 (List.of_mem_zip hp).2).1.2
      (hchunks p.2 (List.of_mem_zip hp).2).2.2
      (hchunks p.2 (List.of_mem_zip hp).2).2.1 hll hlb) hWD

/-- Every lookup constraint value has degree at most `D`, for `D` dominating `4·B` (the
product-and-shuffle rules) and `2·B + 2·Dc` (the compressed step rule), where `Dc` bounds the
compressed input/table expressions. -/
theorem natDegree_lookupExpressions_le {B Dc D : ℕ}
    {fx av inst : ℕ → Polynomial Fp}
    (hfx : ∀ i, (fx i).natDegree ≤ B) (hav : ∀ i, (av i).natDegree ≤ B)
    (hinst : ∀ i, (inst i).natDegree ≤ B)
    (le : LookupEval (Polynomial Fp)) (inputExprs tableExprs : List (Expr Fp))
    (theta beta gamma : Fp) (l0 lLast lBlind : Polynomial Fp)
    (hle : le.productEval.natDegree ≤ B ∧ le.productNextEval.natDegree ≤ B
      ∧ le.permutedInputEval.natDegree ≤ B ∧ le.permutedInputInvEval.natDegree ≤ B
      ∧ le.permutedTableEval.natDegree ≤ B)
    (hin : ∀ e ∈ inputExprs, e.degreeBound * B ≤ Dc)
    (htab : ∀ e ∈ tableExprs, e.degreeBound * B ≤ Dc)
    (hl0 : l0.natDegree ≤ B) (hll : lLast.natDegree ≤ B) (hlb : lBlind.natDegree ≤ B)
    (h4 : 4 * B ≤ D) (hcomp : 2 * B + 2 * Dc ≤ D) :
    ∀ q ∈ lookupExpressions le (inputExprs.map (Expr.map Polynomial.C))
      (tableExprs.map (Expr.map Polynomial.C)) fx av inst (Polynomial.C theta)
      (Polynomial.C beta) (Polynomial.C gamma) l0 lLast lBlind, q.natDegree ≤ D := by
  obtain ⟨hp, hpn, hpi, hpiv, hpt⟩ := hle
  have hactive : ((1 : Polynomial Fp) - (lLast + lBlind)).natDegree ≤ B :=
    le_trans (natDegree_sub_le _ _)
      (max_le (by simp) (le_trans (natDegree_add_le _ _) (max_le hll hlb)))
  intro q hq
  simp only [lookupExpressions, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · -- the start rule
    refine le_trans natDegree_mul_le (le_trans (Nat.add_le_add hl0 (le_trans
      (natDegree_sub_le _ _) (max_le (by simp) hp))) (by omega))
  · -- the end rule
    have h2B : (le.productEval ^ 2 - le.productEval).natDegree ≤ 2 * B :=
      le_trans (natDegree_sub_le _ _) (max_le
        (le_trans natDegree_pow_le (Nat.mul_le_mul_left 2 hp)) (le_trans hp (by omega)))
    exact le_trans natDegree_mul_le (le_trans (Nat.add_le_add hll h2B) (by omega))
  · -- the step rule
    have hleft : (le.productNextEval * (le.permutedInputEval + Polynomial.C beta)
        * (le.permutedTableEval + Polynomial.C gamma)).natDegree ≤ 3 * B := by
      refine le_trans natDegree_mul_le (le_trans (Nat.add_le_add (le_trans natDegree_mul_le
        (Nat.add_le_add hpn (le_trans (natDegree_add_le _ _) (max_le hpi (by simp)))))
        (le_trans (natDegree_add_le _ _) (max_le hpt (by simp)))) (by omega))
    have hright : (le.productEval
        * (compressExprs fx av inst (Polynomial.C theta)
            (inputExprs.map (Expr.map Polynomial.C)) + Polynomial.C beta)
        * (compressExprs fx av inst (Polynomial.C theta)
            (tableExprs.map (Expr.map Polynomial.C)) + Polynomial.C gamma)).natDegree
        ≤ B + 2 * Dc := by
      refine le_trans natDegree_mul_le (le_trans (Nat.add_le_add (le_trans natDegree_mul_le
        (Nat.add_le_add hp (le_trans (natDegree_add_le _ _) (max_le
          (natDegree_compressExprs_le hfx hav hinst theta inputExprs hin) (by simp)))))
        (le_trans (natDegree_add_le _ _) (max_le
          (natDegree_compressExprs_le hfx hav hinst theta tableExprs htab) (by simp))))
        (by omega))
    have hdiff := le_trans (natDegree_sub_le _ _) (max_le_max hleft hright)
    exact le_trans natDegree_mul_le (le_trans (Nat.add_le_add hdiff hactive) (by omega))
  · -- the permuted-columns start rule
    exact le_trans natDegree_mul_le (le_trans (Nat.add_le_add hl0 (le_trans
      (natDegree_sub_le _ _) (max_le hpi hpt))) (by omega))
  · -- the permuted-columns run rule
    refine le_trans natDegree_mul_le (le_trans (Nat.add_le_add (le_trans natDegree_mul_le
      (Nat.add_le_add (le_trans (natDegree_sub_le _ _) (max_le hpi hpt))
        (le_trans (natDegree_sub_le _ _) (max_le hpi hpiv)))) hactive) (by omega))

/-- Every polynomial constraint value across the sub-proofs has degree at most `D`. The cap `D`
must dominate each family: the gates' `degreeBound · B`, the permutation rules' `3·B` and
`(W + 2)·B`, and the lookup rules' `4·B` and `2·B + 2·Dc`. -/
theorem natDegree_constraintPolys_le {np : ℕ} {B W Dc D : ℕ} (hB : 1 ≤ B)
    (fixedCols : ℕ → Polynomial Fp) (adviceCols instanceCols : Fin np → ℕ → Polynomial Fp)
    (gates : List (Expr Fp))
    (sets : Fin np → List (PermSetEval (Polynomial Fp)))
    (chunks : Fin np → List (PermSetEval (Polynomial Fp) × List (Polynomial Fp × Polynomial Fp)))
    (lookups : Fin np → List (LookupEval (Polynomial Fp) × List (Expr Fp) × List (Expr Fp)))
    (beta gamma delta theta : Fp) (chunkLen : ℕ) (l0 lLast lBlind : Polynomial Fp)
    (hfx : ∀ i, (fixedCols i).natDegree ≤ B)
    (hav : ∀ p i, (adviceCols p i).natDegree ≤ B)
    (hinst : ∀ p i, (instanceCols p i).natDegree ≤ B)
    (hgates : ∀ e ∈ gates, e.degreeBound * B ≤ D)
    (hsets : ∀ p, ∀ s ∈ sets p, s.eval.natDegree ≤ B ∧ (s.lastEval.getD 0).natDegree ≤ B)
    (hchunks : ∀ p, ∀ c ∈ chunks p, (c.1.eval.natDegree ≤ B ∧ c.1.nextEval.natDegree ≤ B)
      ∧ c.2.length ≤ W ∧ ∀ pr ∈ c.2, pr.1.natDegree ≤ B ∧ pr.2.natDegree ≤ B)
    (hlooks : ∀ p, ∀ lk ∈ lookups p,
      (lk.1.productEval.natDegree ≤ B ∧ lk.1.productNextEval.natDegree ≤ B
        ∧ lk.1.permutedInputEval.natDegree ≤ B ∧ lk.1.permutedInputInvEval.natDegree ≤ B
        ∧ lk.1.permutedTableEval.natDegree ≤ B)
      ∧ (∀ e ∈ lk.2.1, e.degreeBound * B ≤ Dc) ∧ (∀ e ∈ lk.2.2, e.degreeBound * B ≤ Dc))
    (hl0 : l0.natDegree ≤ B) (hll : lLast.natDegree ≤ B) (hlb : lBlind.natDegree ≤ B)
    (h3 : 3 * B ≤ D) (hWD : (W + 2) * B ≤ D) (h4 : 4 * B ≤ D) (hcomp : 2 * B + 2 * Dc ≤ D) :
    ∀ q ∈ constraintPolys fixedCols adviceCols instanceCols gates sets chunks lookups
      beta gamma delta theta chunkLen l0 lLast lBlind, q.natDegree ≤ D := by
  intro q hq
  rw [constraintPolys, allConstraints] at hq
  obtain ⟨l, hl, hql⟩ := List.mem_flatten.mp hq
  obtain ⟨p, rfl⟩ := List.mem_ofFn.mp hl
  rw [subProofConstraints] at hql
  rcases List.mem_append.mp hql with hg | hg
  · rcases List.mem_append.mp hg with hg' | hg'
    · -- a gate
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hg'
      obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp he
      exact le_trans (natDegree_eval_map_C_le hfx (hav p) (hinst p) e₀) (hgates e₀ he₀)
    · -- a permutation rule
      exact natDegree_permutationExpressions_le hB (sets p) (chunks p) beta gamma delta
        chunkLen l0 lLast lBlind (hsets p) (hchunks p) hl0 hll hlb h3 hWD _ hg'
  · -- a lookup rule
    obtain ⟨l', hl', hql'⟩ := List.mem_flatten.mp hg
    obtain ⟨lk', hlk', rfl⟩ := List.mem_map.mp hl'
    obtain ⟨lk, hlk, rfl⟩ := List.mem_map.mp hlk'
    exact natDegree_lookupExpressions_le hfx (hav p) (hinst p) lk.1 lk.2.1 lk.2.2
      theta beta gamma l0 lLast lBlind (hlooks p lk hlk).1 (hlooks p lk hlk).2.1
      (hlooks p lk hlk).2.2 hl0 hll hlb h4 hcomp _ hql'

/-- The `acc·y + v` fold preserves the members' degree cap: `y` is a scalar. -/
theorem natDegree_foldByY_le {D : ℕ} (y : Fp) (ps : List (Polynomial Fp))
    (hps : ∀ q ∈ ps, q.natDegree ≤ D) :
    (ps.foldl (fun acc p => acc * Polynomial.C y + p) 0).natDegree ≤ D := by
  suffices h : ∀ acc : Polynomial Fp, acc.natDegree ≤ D →
      (ps.foldl (fun acc p => acc * Polynomial.C y + p) acc).natDegree ≤ D by
    exact h 0 (by simp)
  induction ps with
  | nil => intro acc hacc; simpa using hacc
  | cons p t ih =>
      intro acc hacc
      rw [List.foldl_cons]
      refine ih (fun q hq => hps q (List.mem_cons_of_mem _ hq)) _
        (le_trans (natDegree_add_le _ _) (max_le (le_trans natDegree_mul_le (by simpa using hacc))
          (hps p (List.mem_cons_self ..))))

/-- **The combined constraint numerator's degree cap.** With every column feed, carrier and
selector of degree `≤ B` and the cap `D` dominating each constraint family, the full `y`-fold has
degree at most `D`. -/
theorem natDegree_combineConstraints_le {np : ℕ} {B W Dc D : ℕ} (hB : 1 ≤ B)
    (fixedCols : ℕ → Polynomial Fp) (adviceCols instanceCols : Fin np → ℕ → Polynomial Fp)
    (gates : List (Expr Fp))
    (sets : Fin np → List (PermSetEval (Polynomial Fp)))
    (chunks : Fin np → List (PermSetEval (Polynomial Fp) × List (Polynomial Fp × Polynomial Fp)))
    (lookups : Fin np → List (LookupEval (Polynomial Fp) × List (Expr Fp) × List (Expr Fp)))
    (beta gamma delta theta y : Fp) (chunkLen : ℕ) (l0 lLast lBlind : Polynomial Fp)
    (hfx : ∀ i, (fixedCols i).natDegree ≤ B)
    (hav : ∀ p i, (adviceCols p i).natDegree ≤ B)
    (hinst : ∀ p i, (instanceCols p i).natDegree ≤ B)
    (hgates : ∀ e ∈ gates, e.degreeBound * B ≤ D)
    (hsets : ∀ p, ∀ s ∈ sets p, s.eval.natDegree ≤ B ∧ (s.lastEval.getD 0).natDegree ≤ B)
    (hchunks : ∀ p, ∀ c ∈ chunks p, (c.1.eval.natDegree ≤ B ∧ c.1.nextEval.natDegree ≤ B)
      ∧ c.2.length ≤ W ∧ ∀ pr ∈ c.2, pr.1.natDegree ≤ B ∧ pr.2.natDegree ≤ B)
    (hlooks : ∀ p, ∀ lk ∈ lookups p,
      (lk.1.productEval.natDegree ≤ B ∧ lk.1.productNextEval.natDegree ≤ B
        ∧ lk.1.permutedInputEval.natDegree ≤ B ∧ lk.1.permutedInputInvEval.natDegree ≤ B
        ∧ lk.1.permutedTableEval.natDegree ≤ B)
      ∧ (∀ e ∈ lk.2.1, e.degreeBound * B ≤ Dc) ∧ (∀ e ∈ lk.2.2, e.degreeBound * B ≤ Dc))
    (hl0 : l0.natDegree ≤ B) (hll : lLast.natDegree ≤ B) (hlb : lBlind.natDegree ≤ B)
    (h3 : 3 * B ≤ D) (hWD : (W + 2) * B ≤ D) (h4 : 4 * B ≤ D) (hcomp : 2 * B + 2 * Dc ≤ D) :
    (combineConstraints fixedCols adviceCols instanceCols gates sets chunks lookups
      beta gamma delta theta y chunkLen l0 lLast lBlind).natDegree ≤ D := by
  rw [combineConstraints]
  exact natDegree_foldByY_le y _ (natDegree_constraintPolys_le hB fixedCols adviceCols
    instanceCols gates sets chunks lookups beta gamma delta theta chunkLen l0 lLast lBlind
    hfx hav hinst hgates hsets hchunks hlooks hl0 hll hlb h3 hWD h4 hcomp)

end Zcash.Snark
