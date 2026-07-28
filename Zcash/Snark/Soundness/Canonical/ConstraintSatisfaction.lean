import Mathlib
import Zcash.Snark.Soundness.Constraints
import Zcash.Snark.Soundness.FoldSplit
import Zcash.Snark.Soundness.KnowledgeSoundness

/-!
# The full polynomial constraint system, by argument

`constraintPolys` is intentionally a flat list because that is what the verifier folds by `y`.
Semantic consumers need the inverse view: custom gates, permutation constraints, and lookup
constraints for a selected sub-proof. This module packages the polynomial inputs once and proves
the membership facts that recover those three families from the flat deployed list.
-/

namespace Zcash.Snark

open Polynomial

/-- The data from which the deployed polynomial constraint list is assembled. Packaging it keeps
downstream semantic statements from repeating the full `constraintPolys` argument list. -/
structure ConstraintPolyModel (np : ℕ) where
  fixedCols : ℕ → Polynomial Fp
  adviceCols : Fin np → ℕ → Polynomial Fp
  instanceCols : Fin np → ℕ → Polynomial Fp
  gates : List (Expr Fp)
  sets : Fin np → List (PermSetEval (Polynomial Fp))
  chunks : Fin np →
    List (PermSetEval (Polynomial Fp) × List (Polynomial Fp × Polynomial Fp))
  lookups : Fin np →
    List (LookupEval (Polynomial Fp) × List (Expr Fp) × List (Expr Fp))
  beta : Fp
  gamma : Fp
  delta : Fp
  theta : Fp
  chunkLen : ℕ
  l0 : Polynomial Fp
  lLast : Polynomial Fp
  lBlind : Polynomial Fp

namespace ConstraintPolyModel

/-- One sub-proof's lifted custom-gate constraints. -/
noncomputable def gateConstraints {np : ℕ} (M : ConstraintPolyModel np) (p : Fin np) :
    List (Polynomial Fp) :=
  (M.gates.map (Expr.map C)).map
    (fun g => g.eval M.fixedCols (M.adviceCols p) (M.instanceCols p))

/-- One sub-proof's permutation constraints. -/
noncomputable def permutationConstraints {np : ℕ} (M : ConstraintPolyModel np) (p : Fin np) :
    List (Polynomial Fp) :=
  permutationExpressions (M.sets p) (M.chunks p) (C M.beta) (C M.gamma) X (C M.delta)
    M.chunkLen M.l0 M.lLast M.lBlind

/-- One sub-proof's lookup constraints. -/
noncomputable def lookupConstraints {np : ℕ} (M : ConstraintPolyModel np) (p : Fin np) :
    List (Polynomial Fp) :=
  ((M.lookups p).map fun lk =>
    lookupExpressions lk.1 (lk.2.1.map (Expr.map C)) (lk.2.2.map (Expr.map C))
      M.fixedCols (M.adviceCols p) (M.instanceCols p)
      (C M.theta) (C M.beta) (C M.gamma) M.l0 M.lLast M.lBlind).flatten

/-- One sub-proof's constraints, split into the same three consecutive families as the verifier. -/
noncomputable def subProofConstraints {np : ℕ} (M : ConstraintPolyModel np) (p : Fin np) :
    List (Polynomial Fp) :=
  M.gateConstraints p ++ M.permutationConstraints p ++ M.lookupConstraints p

/-- The complete flat constraint list across all sub-proofs. -/
noncomputable def constraints {np : ℕ} (M : ConstraintPolyModel np) : List (Polynomial Fp) :=
  (List.ofFn fun p => M.subProofConstraints p).flatten

/-- The packaged list is definitionally the existing deployed polynomial builder. -/
theorem constraints_eq_constraintPolys {np : ℕ} (M : ConstraintPolyModel np) :
    M.constraints =
      constraintPolys M.fixedCols M.adviceCols M.instanceCols M.gates M.sets M.chunks M.lookups
        M.beta M.gamma M.delta M.theta M.chunkLen M.l0 M.lLast M.lBlind := by
  unfold constraints constraintPolys allConstraints
  congr 2
  funext p
  unfold ConstraintPolyModel.subProofConstraints gateConstraints permutationConstraints
    lookupConstraints Zcash.Snark.subProofConstraints
  simp [List.map_map, Function.comp_def]

/--
The capstone constraint identity specialized to one packaged polynomial model.

The witness vector is retained because it is part of the extracted IPA relation,
but the model's columns are already canonically decoded and therefore do not vary
with that vector.
-/
def CircuitSat {np k : ℕ} (M : ConstraintPolyModel np)
    (y : Fp) (hpoly : Polynomial Fp) (deg : ℕ)
    (a : Fin (2 ^ k) → Fp) : Prop :=
  circuitSatViaConstraints M.fixedCols
    (fun _ => M.adviceCols) (fun _ => M.instanceCols)
    M.gates M.sets M.chunks M.lookups
    M.beta M.gamma M.delta M.theta y M.chunkLen
    M.l0 M.lLast M.lBlind hpoly deg a

/-- A member of one sub-proof's list is a member of the deployed flat list. -/
theorem mem_constraints_of_mem_subProof {np : ℕ} (M : ConstraintPolyModel np) (p : Fin np)
    {c : Polynomial Fp} (hc : c ∈ M.subProofConstraints p) : c ∈ M.constraints := by
  refine List.mem_flatten.mpr ⟨M.subProofConstraints p, ?_, hc⟩
  exact List.mem_ofFn.mpr ⟨p, rfl⟩

/-- A lifted custom gate occurs in the deployed flat list. -/
theorem gate_mem_constraints {np : ℕ} (M : ConstraintPolyModel np) (p : Fin np)
    {c : Polynomial Fp} (hc : c ∈ M.gateConstraints p) : c ∈ M.constraints :=
  M.mem_constraints_of_mem_subProof p (by simp [subProofConstraints, hc])

/-- A permutation constraint occurs in the deployed flat list. -/
theorem permutation_mem_constraints {np : ℕ} (M : ConstraintPolyModel np) (p : Fin np)
    {c : Polynomial Fp} (hc : c ∈ M.permutationConstraints p) : c ∈ M.constraints :=
  M.mem_constraints_of_mem_subProof p (by simp [subProofConstraints, hc])

/-- A lookup constraint occurs in the deployed flat list. -/
theorem lookup_mem_constraints {np : ℕ} (M : ConstraintPolyModel np) (p : Fin np)
    {c : Polynomial Fp} (hc : c ∈ M.lookupConstraints p) : c ∈ M.constraints :=
  M.mem_constraints_of_mem_subProof p (by simp [subProofConstraints, hc])

/-- A member of one selected lookup's five-expression list occurs in that sub-proof's lookup
family. -/
theorem lookupExpression_mem_lookupConstraints {np : ℕ} (M : ConstraintPolyModel np) (p : Fin np)
    {lk : LookupEval (Polynomial Fp) × List (Expr Fp) × List (Expr Fp)}
    (hlk : lk ∈ M.lookups p) {c : Polynomial Fp}
    (hc : c ∈ lookupExpressions lk.1 (lk.2.1.map (Expr.map C)) (lk.2.2.map (Expr.map C))
      M.fixedCols (M.adviceCols p) (M.instanceCols p)
      (C M.theta) (C M.beta) (C M.gamma) M.l0 M.lLast M.lBlind) :
    c ∈ M.lookupConstraints p := by
  refine List.mem_flatten.mpr ⟨_, ?_, hc⟩
  exact List.mem_map.mpr ⟨lk, hlk, rfl⟩

end ConstraintPolyModel

/-- Full polynomial constraint satisfaction, separated into the three semantic argument families.
Each field says that every member of that family vanishes on the size-`n` evaluation domain. -/
structure ConstraintSatisfaction {np : ℕ} (M : ConstraintPolyModel np) (n : ℕ) : Prop where
  gates : ∀ p c, c ∈ M.gateConstraints p → (X ^ n - 1 : Polynomial Fp) ∣ c
  permutation : ∀ p c, c ∈ M.permutationConstraints p → (X ^ n - 1 : Polynomial Fp) ∣ c
  lookups : ∀ p c, c ∈ M.lookupConstraints p → (X ^ n - 1 : Polynomial Fp) ∣ c

/-- Divisibility of every member of the flat deployed list gives full, family-separated
constraint satisfaction. This is the direct consumer of `constraints_dvd_of_good_y`. -/
theorem ConstraintSatisfaction.of_all {np n : ℕ} (M : ConstraintPolyModel np)
    (hall : ∀ c ∈ M.constraints, (X ^ n - 1 : Polynomial Fp) ∣ c) :
    ConstraintSatisfaction M n where
  gates p c hc := hall c (M.gate_mem_constraints p hc)
  permutation p c hc := hall c (M.permutation_mem_constraints p hc)
  lookups p c hc := hall c (M.lookup_mem_constraints p hc)

/--
Split the capstone's single folded constraint identity into the
family-separated satisfaction record used by the semantic bridge.

The only additional premise is the explicit `y`-good event: no coefficient
witness for a constraint hidden by the fold vanishes at `y`.
-/
theorem ConstraintSatisfaction.of_circuitSatViaConstraints
    {np k n : ℕ} (M : ConstraintPolyModel np)
    (y : Fp) (hpoly : Polynomial Fp)
    (a : Fin (2 ^ k) → Fp)
    (hn : n ≠ 0)
    (hsat : M.CircuitSat y hpoly n a)
    (hgoodY : ∀ j,
      y ∉ szBadSet (foldSplitWitness M.constraints n j)) :
    ConstraintSatisfaction M n := by
  apply ConstraintSatisfaction.of_all M
  apply constraints_dvd_of_good_y M.constraints hpoly hn
  · rw [M.constraints_eq_constraintPolys]
    exact hsat
  · exact hgoodY

/-- Use full satisfaction on a member of one selected lookup's five constraints. -/
theorem ConstraintSatisfaction.lookupExpression {np n : ℕ} {M : ConstraintPolyModel np}
    (h : ConstraintSatisfaction M n) (p : Fin np)
    {lk : LookupEval (Polynomial Fp) × List (Expr Fp) × List (Expr Fp)}
    (hlk : lk ∈ M.lookups p) {c : Polynomial Fp}
    (hc : c ∈ lookupExpressions lk.1 (lk.2.1.map (Expr.map C)) (lk.2.2.map (Expr.map C))
      M.fixedCols (M.adviceCols p) (M.instanceCols p)
      (C M.theta) (C M.beta) (C M.gamma) M.l0 M.lLast M.lBlind) :
    (X ^ n - 1 : Polynomial Fp) ∣ c :=
  h.lookups p c (M.lookupExpression_mem_lookupConstraints p hlk hc)

/-! ## Named members of the permutation list -/

/-- The first permutation running product's start constraint is in `permutationExpressions`. -/
theorem permutation_start_mem {F : Type*} [CommRing F]
    (sets : List (PermSetEval F)) (chunks : List (PermSetEval F × List (F × F)))
    (beta gamma x delta : F) (chunkLen : ℕ) (l0 lLast lBlind : F)
    {first : PermSetEval F} (hfirst : sets.head? = some first) :
    l0 * (1 - first.eval) ∈
      permutationExpressions sets chunks beta gamma x delta chunkLen l0 lLast lBlind := by
  simp [permutationExpressions, hfirst]

/-- The final permutation running product's Boolean end constraint is in
`permutationExpressions`. -/
theorem permutation_end_mem {F : Type*} [CommRing F]
    (sets : List (PermSetEval F)) (chunks : List (PermSetEval F × List (F × F)))
    (beta gamma x delta : F) (chunkLen : ℕ) (l0 lLast lBlind : F)
    {last : PermSetEval F} (hlast : sets.getLast? = some last) :
    (last.eval ^ 2 - last.eval) * lLast ∈
      permutationExpressions sets chunks beta gamma x delta chunkLen l0 lLast lBlind := by
  simp [permutationExpressions, hlast]

/-- An adjacent pair of permutation sets contributes its inter-set chain constraint. -/
theorem permutation_chain_mem {F : Type*} [CommRing F]
    (sets : List (PermSetEval F)) (chunks : List (PermSetEval F × List (F × F)))
    (beta gamma x delta : F) (chunkLen : ℕ) (l0 lLast lBlind : F)
    {current previous : PermSetEval F}
    (hpair : (current, previous) ∈ (sets.drop 1).zip sets) :
    (current.eval - previous.lastEval.getD 0) * l0 ∈
      permutationExpressions sets chunks beta gamma x delta chunkLen l0 lLast lBlind := by
  simp only [permutationExpressions, List.mem_append]
  exact Or.inl (Or.inr (List.mem_map.mpr ⟨_, hpair, rfl⟩))

/-- A chunk contributes its deployed `permChunkExpression`. -/
theorem permutation_step_mem {F : Type*} [CommRing F]
    (sets : List (PermSetEval F)) (chunks : List (PermSetEval F × List (F × F)))
    (beta gamma x delta : F) (chunkLen : ℕ) (l0 lLast lBlind : F)
    {chunkIndex : ℕ} {chunk : PermSetEval F × List (F × F)}
    (hchunk : (chunkIndex, chunk) ∈ (List.range chunks.length).zip chunks) :
    permChunkExpression beta gamma x delta chunkLen chunkIndex chunk.1 chunk.2 lLast lBlind ∈
      permutationExpressions sets chunks beta gamma x delta chunkLen l0 lLast lBlind := by
  simp only [permutationExpressions, List.mem_append]
  exact Or.inr (List.mem_map.mpr ⟨_, hchunk, rfl⟩)

/-! ## Named members of each lookup list -/

theorem lookup_start_mem {F : Type*} [CommRing F] (le : LookupEval F)
    (inputExprs tableExprs : List (Expr F)) (fixed advice instanceFeed : ℕ → F)
    (theta beta gamma l0 lLast lBlind : F) :
    l0 * (1 - le.productEval) ∈
      lookupExpressions le inputExprs tableExprs fixed advice instanceFeed
        theta beta gamma l0 lLast lBlind := by
  simp [lookupExpressions]

theorem lookup_end_mem {F : Type*} [CommRing F] (le : LookupEval F)
    (inputExprs tableExprs : List (Expr F)) (fixed advice instanceFeed : ℕ → F)
    (theta beta gamma l0 lLast lBlind : F) :
    lLast * (le.productEval ^ 2 - le.productEval) ∈
      lookupExpressions le inputExprs tableExprs fixed advice instanceFeed
        theta beta gamma l0 lLast lBlind := by
  simp [lookupExpressions]

theorem lookup_product_step_mem {F : Type*} [CommRing F] (le : LookupEval F)
    (inputExprs tableExprs : List (Expr F)) (fixed advice instanceFeed : ℕ → F)
    (theta beta gamma l0 lLast lBlind : F) :
    (le.productNextEval * (le.permutedInputEval + beta) * (le.permutedTableEval + gamma)
      - le.productEval * (compressExprs fixed advice instanceFeed theta inputExprs + beta)
        * (compressExprs fixed advice instanceFeed theta tableExprs + gamma))
        * (1 - (lLast + lBlind)) ∈
      lookupExpressions le inputExprs tableExprs fixed advice instanceFeed
        theta beta gamma l0 lLast lBlind := by
  simp [lookupExpressions]

theorem lookup_run_start_mem {F : Type*} [CommRing F] (le : LookupEval F)
    (inputExprs tableExprs : List (Expr F)) (fixed advice instanceFeed : ℕ → F)
    (theta beta gamma l0 lLast lBlind : F) :
    l0 * (le.permutedInputEval - le.permutedTableEval) ∈
      lookupExpressions le inputExprs tableExprs fixed advice instanceFeed
        theta beta gamma l0 lLast lBlind := by
  simp [lookupExpressions]

theorem lookup_run_step_mem {F : Type*} [CommRing F] (le : LookupEval F)
    (inputExprs tableExprs : List (Expr F)) (fixed advice instanceFeed : ℕ → F)
    (theta beta gamma l0 lLast lBlind : F) :
    (le.permutedInputEval - le.permutedTableEval)
      * (le.permutedInputEval - le.permutedInputInvEval)
      * (1 - (lLast + lBlind)) ∈
      lookupExpressions le inputExprs tableExprs fixed advice instanceFeed
        theta beta gamma l0 lLast lBlind := by
  simp [lookupExpressions]

/-! ## A selected lookup's five constraints from full satisfaction -/

/-- Full satisfaction supplies a selected lookup's running-product start constraint. -/
theorem ConstraintSatisfaction.lookupStart {np n : ℕ} {M : ConstraintPolyModel np}
    (h : ConstraintSatisfaction M n) (p : Fin np)
    {lk : LookupEval (Polynomial Fp) × List (Expr Fp) × List (Expr Fp)}
    (hlk : lk ∈ M.lookups p) :
    (X ^ n - 1 : Polynomial Fp) ∣ M.l0 * (1 - lk.1.productEval) :=
  h.lookupExpression p hlk (lookup_start_mem ..)

/-- Full satisfaction supplies a selected lookup's running-product end constraint. -/
theorem ConstraintSatisfaction.lookupEnd {np n : ℕ} {M : ConstraintPolyModel np}
    (h : ConstraintSatisfaction M n) (p : Fin np)
    {lk : LookupEval (Polynomial Fp) × List (Expr Fp) × List (Expr Fp)}
    (hlk : lk ∈ M.lookups p) :
    (X ^ n - 1 : Polynomial Fp) ∣
      M.lLast * (lk.1.productEval ^ 2 - lk.1.productEval) :=
  h.lookupExpression p hlk (lookup_end_mem ..)

/-- Full satisfaction supplies a selected lookup's product-step constraint. -/
theorem ConstraintSatisfaction.lookupProductStep {np n : ℕ} {M : ConstraintPolyModel np}
    (h : ConstraintSatisfaction M n) (p : Fin np)
    {lk : LookupEval (Polynomial Fp) × List (Expr Fp) × List (Expr Fp)}
    (hlk : lk ∈ M.lookups p) :
    (X ^ n - 1 : Polynomial Fp) ∣
      (lk.1.productNextEval * (lk.1.permutedInputEval + C M.beta)
          * (lk.1.permutedTableEval + C M.gamma)
        - lk.1.productEval
          * (compressExprs M.fixedCols (M.adviceCols p) (M.instanceCols p) (C M.theta)
              (lk.2.1.map (Expr.map C)) + C M.beta)
          * (compressExprs M.fixedCols (M.adviceCols p) (M.instanceCols p) (C M.theta)
              (lk.2.2.map (Expr.map C)) + C M.gamma))
        * (1 - (M.lLast + M.lBlind)) :=
  h.lookupExpression p hlk (lookup_product_step_mem ..)

/-- Full satisfaction supplies a selected lookup's first-row run constraint. -/
theorem ConstraintSatisfaction.lookupRunStart {np n : ℕ} {M : ConstraintPolyModel np}
    (h : ConstraintSatisfaction M n) (p : Fin np)
    {lk : LookupEval (Polynomial Fp) × List (Expr Fp) × List (Expr Fp)}
    (hlk : lk ∈ M.lookups p) :
    (X ^ n - 1 : Polynomial Fp) ∣
      M.l0 * (lk.1.permutedInputEval - lk.1.permutedTableEval) :=
  h.lookupExpression p hlk (lookup_run_start_mem ..)

/-- Full satisfaction supplies a selected lookup's repeat-or-match run constraint. -/
theorem ConstraintSatisfaction.lookupRunStep {np n : ℕ} {M : ConstraintPolyModel np}
    (h : ConstraintSatisfaction M n) (p : Fin np)
    {lk : LookupEval (Polynomial Fp) × List (Expr Fp) × List (Expr Fp)}
    (hlk : lk ∈ M.lookups p) :
    (X ^ n - 1 : Polynomial Fp) ∣
      (lk.1.permutedInputEval - lk.1.permutedTableEval)
        * (lk.1.permutedInputEval - lk.1.permutedInputInvEval)
        * (1 - (M.lLast + M.lBlind)) :=
  h.lookupExpression p hlk (lookup_run_step_mem ..)

end Zcash.Snark
