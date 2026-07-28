import Zcash.Snark.Soundness.Composition.DeployedConstraintContainment
import Zcash.Snark.Soundness.DegreeWalk

/-!
# Pricing the deployed `x`-squeeze schedule

`DeployedConstraintXSqueezeSchedule` asks two things of the constraint-difference root set: a
uniform measure bound (`measure_le`) and invariance under reprogramming the run's own `x` answer
(`pinned`).

The measure half is discharged here. Every committed carrier is a point polynomial, a rotation of
one, or a Lagrange selector, so the degree walk caps the difference at `max D Dq` and its
Schwartz–Zippel set at `max D Dq / |𝔽|`. Root witnesses at one oracle table share the family's own
outcome, so the set collapses across fork tapes and the bound covers all of it.

The pinning half is derived, not assumed: a captured family carries a
`DeployedConstraintXOnlineTrace` and the equation follows from its query log. That computation may
read later challenges, so no classical truth-table adapter sits on the executable path.
-/

namespace Zcash.Snark

open Polynomial
open scoped ENNReal

/-! ## Degree bounds for the committed carriers -/

/-- Rotation preserves a degree bound: composing with `C w · X` rescales `X`. -/
theorem natDegree_comp_rotate_le (col : Polynomial Fp) (w : Fp) {B : ℕ}
    (h : col.natDegree ≤ B) :
    (col.comp (Polynomial.C w * Polynomial.X)).natDegree ≤ B := by
  refine le_trans natDegree_comp_le ?_
  calc col.natDegree * (Polynomial.C w * Polynomial.X).natDegree
      ≤ B * 1 := Nat.mul_le_mul h (le_trans (natDegree_C_mul_le _ _) natDegree_X_le)
    _ = B := mul_one B

/-- A rotated feed keeps its columns' degree bound. -/
theorem natDegree_rotatedFeed_le {n : ℕ} (omega : Fp) (layout : List (ℕ × ℤ))
    (col : Fin n → Polynomial Fp) {B : ℕ} (h : ∀ j, (col j).natDegree ≤ B) (i : ℕ) :
    (rotatedFeed omega layout col i).natDegree ≤ B := by
  rw [rotatedFeed, finFn]
  split
  · exact natDegree_comp_rotate_le _ _ (h _)
  · simp

/-- The Lagrange basis polynomial has degree below the domain size. -/
theorem natDegree_lagrangeBasisPoly_le (omega : Fp) (n : ℕ) (i : ℤ) :
    (lagrangeBasisPoly omega n i).natDegree ≤ n - 1 := by
  rw [lagrangeBasisPoly]
  refine le_trans (natDegree_C_mul_le _ _) (natDegree_sum_le_of_forall_le _ _ ?_)
  intro k hk
  refine le_trans (natDegree_C_mul_le _ _) ?_
  rw [natDegree_X_pow]
  have := Finset.mem_range.mp hk
  omega

/-- A fold of sums keeps the members' degree bound. -/
theorem natDegree_foldl_add_le {B : ℕ} (ps : List (Polynomial Fp))
    (h : ∀ q ∈ ps, q.natDegree ≤ B) :
    (ps.foldl (· + ·) 0).natDegree ≤ B := by
  suffices h' : ∀ acc : Polynomial Fp, acc.natDegree ≤ B →
      (ps.foldl (· + ·) acc).natDegree ≤ B by
    exact h' 0 (by simp)
  induction ps with
  | nil => intro acc hacc; simpa using hacc
  | cons p t ih =>
      intro acc hacc
      rw [List.foldl_cons]
      exact ih (fun q hq => h q (List.mem_cons_of_mem _ hq)) _
        (le_trans (natDegree_add_le _ _) (max_le hacc (h p (List.mem_cons_self ..))))

/-- The pre-`x` quotient against the vanishing factor: `d` pieces of degree `≤ Bq`, each shifted
by `n` per slot, and the `Xⁿ − 1` factor — `n·d + Bq` in total. -/
theorem natDegree_preXQuotient_mul_le {d : ℕ} (n : ℕ) (hp : Fin d → Polynomial Fp) {Bq : ℕ}
    (h : ∀ j, (hp j).natDegree ≤ Bq) :
    (preXQuotient n hp * (Polynomial.X ^ n - 1)).natDegree ≤ n * d + Bq := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [preXQuotient]
  · obtain ⟨d', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hd)
    refine le_trans natDegree_mul_le ?_
    have h1 : (preXQuotient n hp).natDegree ≤ n * d' + Bq := by
      rw [preXQuotient]
      refine natDegree_sum_le_of_forall_le _ _ ?_
      intro i _
      refine le_trans natDegree_mul_le ?_
      rw [natDegree_X_pow]
      exact Nat.add_le_add (Nat.mul_le_mul_left n (Nat.lt_succ_iff.mp i.isLt)) (h i)
    have h2 : ((Polynomial.X : Polynomial Fp) ^ n - 1).natDegree ≤ n :=
      le_trans (natDegree_sub_le _ _) (max_le (by simp) (by simp))
    refine le_trans (Nat.add_le_add h1 h2) ?_
    rw [Nat.mul_succ]
    omega

/-- **The committed constraint difference's degree cap.** With every point polynomial and
quotient piece of degree `≤ B`, the selector degree `n − 1 ≤ B`, and the caps `D`/`Dq` dominating
the constraint families and the quotient tail, the pre-`x` constraint difference has degree at
most `max D Dq`. -/
theorem natDegree_committedPreXConstraintDifference_le {G : Type*} [Inhabited G]
    {shape : Shape} (poly : G → Polynomial Fp)
    (piecePoly : Fin shape.numQuotientPieces → Polynomial Fp)
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {B W Dc D Dq : ℕ} (hB : 1 ≤ B)
    (hpoly : ∀ g, (poly g).natDegree ≤ B)
    (hpiece : ∀ j, (piecePoly j).natDegree ≤ B)
    (hnB : vk.n - 1 ≤ B)
    (hgates : ∀ e ∈ vk.gates, e.degreeBound * B ≤ D)
    (hW : ∀ c ∈ vk.permutationChunks, c.length ≤ W)
    (hlin : ∀ l : Fin shape.numLookups, ∀ e ∈ vk.lookupInputExprs l, e.degreeBound * B ≤ Dc)
    (hltab : ∀ l : Fin shape.numLookups, ∀ e ∈ vk.lookupTableExprs l, e.degreeBound * B ≤ Dc)
    (hq : vk.n * shape.numQuotientPieces + B ≤ Dq)
    (h3 : 3 * B ≤ D) (hWD : (W + 2) * B ≤ D) (h4 : 4 * B ≤ D)
    (hcomp : 2 * B + 2 * Dc ≤ D) :
    (committedPreXConstraintDifference poly piecePoly vk instanceCommitment ps ch).natDegree
      ≤ max D Dq := by
  have hfeed : ∀ q i, (committedAdviceFeed poly vk ps q i).natDegree ≤ B := fun q i =>
    natDegree_rotatedFeed_le _ _ _ (fun _ => hpoly _) i
  have hfix : ∀ i, (committedFixedFeed poly vk i).natDegree ≤ B := fun i =>
    natDegree_rotatedFeed_le _ _ _ (fun _ => hpoly _) i
  have hinstF : ∀ q i, (committedInstanceFeed poly vk instanceCommitment q i).natDegree ≤ B :=
    fun q i => natDegree_rotatedFeed_le _ _ _ (fun _ => hpoly _) i
  have hcommon : ∀ c, (committedPermCommonFeed poly vk c).natDegree ≤ B := by
    intro c
    rw [committedPermCommonFeed]
    split
    · exact hpoly _
    · simp
  rw [committedPreXConstraintDifference]
  refine le_trans (natDegree_sub_le _ _) (max_le_max ?_ ?_)
  · refine natDegree_combineConstraints_le hB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      hfix hfeed hinstF hgates ?_ ?_ ?_
      (le_trans (natDegree_lagrangeBasisPoly_le _ _ _) hnB)
      (le_trans (natDegree_lagrangeBasisPoly_le _ _ _) hnB) ?_ h3 hWD h4 hcomp
    · -- permutation-set carriers
      intro p s hs
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hs
      dsimp only
      refine ⟨hpoly _, ?_⟩
      rcases (ps.permutationSetEvals p j).lastEval with _ | le
      · simp
      · simp only [Option.map_some, Option.getD_some]
        split
        · exact natDegree_comp_rotate_le _ _ (hpoly _)
        · simp
    · -- permutation chunks
      intro p c hc
      obtain ⟨sc, hsc, rfl⟩ := List.mem_map.mp hc
      obtain ⟨s1, s2⟩ := sc
      obtain ⟨hs1, hs2⟩ := List.of_mem_zip hsc
      dsimp only
      refine ⟨?_, ?_, ?_⟩
      · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hs1
        exact ⟨hpoly _, natDegree_comp_rotate_le _ _ (hpoly _)⟩
      · simpa using hW _ hs2
      · intro pr hpr
        obtain ⟨cr, -, hpr'⟩ := List.mem_map.mp hpr
        rw [← hpr']
        obtain ⟨cref, cc⟩ := cr
        refine ⟨?_, hcommon _⟩
        rcases cref with i | i | i
        · exact hfeed _ _
        · exact hfix _
        · exact hinstF _ _
    · -- lookup carriers
      intro p lk hlk
      obtain ⟨l, rfl⟩ := List.mem_ofFn.mp hlk
      exact ⟨⟨hpoly _, natDegree_comp_rotate_le _ _ (hpoly _), hpoly _,
        natDegree_comp_rotate_le _ _ (hpoly _), hpoly _⟩, hlin l, hltab l⟩
    · -- the blind selector: a fold of Lagrange polynomials
      refine natDegree_foldl_add_le _ ?_
      intro q hq'
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hq'
      exact le_trans (natDegree_lagrangeBasisPoly_le _ _ _) hnB
  · -- the quotient tail
    rw [committedPreXQuotient]
    exact le_trans (natDegree_preXQuotient_mul_le _ _ hpiece) hq

/-! ## The deployed constraint difference, collapsed across fork tapes -/

variable {shape : Shape}

local instance vestaInhabitedScheduleBudget : Inhabited VestaG := ⟨0⟩

/-- The deployed constraint difference's degree cap: the point polynomials and quotient pieces
are coordinate polynomials of degree below the basis size `2^k`. -/
theorem natDegree_deployedConstraintDifferenceOfRoot_le
    (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (coins : family.toFamily.Coins)
    (root : DeployedRootDecodeWitness family basis coins)
    {B W Dc D Dq : ℕ} (hB : 1 ≤ B) (hkB : 2 ^ shape.k - 1 ≤ B)
    (hnB : (family.vk basis).n - 1 ≤ B)
    (hgates : ∀ e ∈ (family.vk basis).gates, e.degreeBound * B ≤ D)
    (hW : ∀ c ∈ (family.vk basis).permutationChunks, c.length ≤ W)
    (hlin : ∀ l : Fin shape.numLookups,
      ∀ e ∈ (family.vk basis).lookupInputExprs l, e.degreeBound * B ≤ Dc)
    (hltab : ∀ l : Fin shape.numLookups,
      ∀ e ∈ (family.vk basis).lookupTableExprs l, e.degreeBound * B ≤ Dc)
    (hq : (family.vk basis).n * shape.numQuotientPieces + B ≤ Dq)
    (h3 : 3 * B ≤ D) (hWD : (W + 2) * B ≤ D) (h4 : 4 * B ≤ D)
    (hcomp : 2 * B + 2 * Dc ≤ D) :
    (deployedConstraintDifferenceOfRoot family basis coins root).natDegree ≤ max D Dq := by
  rw [deployedConstraintDifferenceOfRoot]
  refine natDegree_committedPreXConstraintDifference_le _ _ _ _ _ _ hB
    (fun g => ?_) (fun j => ?_) hnB hgates hW hlin hltab hq h3 hWD h4 hcomp
  · rw [deployedConstraintPointPolynomial, onlinePointPolynomial]
    have h := coeffsToPoly_natDegree_lt (n := 2 ^ shape.k) (by positivity)
      (onlinePointCoordinates (deployedConstraintSource family basis
        (deployedRootRunOutput family basis coins) root.batchWitness) g).1
    omega
  · have h := coeffsToPoly_natDegree_lt (n := 2 ^ shape.k) (by positivity)
      (deployedConstraintPieceCoordinates family basis
        (deployedRootRunOutput family basis coins) root.batchWitness j).1
    omega

/-- Root witnesses at the same oracle table carry the same batch data: both are pinned to the
family's own outcome at that table, so the constraint difference does not depend on the fork
tape or the witness choice. -/
theorem deployedConstraintDifference_witness_congr
    (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    {O : BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp}
    {tape tape' : RecursiveForkTape Fp shape.k}
    (root : DeployedRootDecodeWitness family basis (O, tape))
    (root' : DeployedRootDecodeWitness family basis (O, tape')) :
    deployedConstraintDifferenceOfRoot family basis (O, tape) root
      = deployedConstraintDifferenceOfRoot family basis (O, tape') root' := by
  have hbw : root.batchWitness = root'.batchWitness :=
    PSum.inl.inj (root.outcome_eq.symm.trans root'.outcome_eq)
  rw [deployedConstraintDifferenceOfRoot, deployedConstraintDifferenceOfRoot, hbw]

/-- **The exact constraint-difference root set's measure.** The set collapses across fork tapes
to one Schwartz–Zippel set, priced by the degree cap. -/
theorem deployedConstraintXBadSet_measure_le
    (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    {D : ℕ}
    (hdeg : ∀ (tape : RecursiveForkTape Fp shape.k)
      (root : DeployedRootDecodeWitness family basis (O, tape)),
      (deployedConstraintDifferenceOfRoot family basis (O, tape) root).natDegree ≤ D) :
    (PMF.uniformOfFintype Fp).toOuterMeasure (deployedConstraintXBadSet family basis O)
      ≤ (D : ℝ≥0∞) / (Fintype.card Fp : ℝ≥0∞) := by
  by_cases h : ∃ tape : RecursiveForkTape Fp shape.k,
      Nonempty (DeployedRootDecodeWitness family basis (O, tape))
  · obtain ⟨tape₀, ⟨root₀⟩⟩ := h
    have hsub : deployedConstraintXBadSet family basis O
        ⊆ ↑(szBadSet (deployedConstraintDifferenceOfRoot family basis (O, tape₀) root₀)) := by
      rintro x ⟨tape, root, hx⟩
      rwa [deployedConstraintDifference_witness_congr family basis root root₀] at hx
    refine le_trans ((PMF.uniformOfFintype Fp).toOuterMeasure.mono hsub) ?_
    refine le_trans (uniformChallenge_szBadSet _) ?_
    gcongr
    exact_mod_cast hdeg tape₀ root₀
  · have hempty : deployedConstraintXBadSet family basis O = ∅ := by
      ext x
      simp only [deployedConstraintXBadSet, Set.mem_setOf_eq, Set.mem_empty_iff_false,
        iff_false, not_exists]
      intro tape root _
      exact h ⟨tape, ⟨root⟩⟩
    simp [hempty]

/-! ## The schedule, priced -/

/-- **The deployed `x`-squeeze schedule from the degree caps.** The pricing half is discharged
outright at `epsilonX = max D Dq / |𝔽|`. This generic constructor consumes the derived
pinning equation; captured deployed families obtain it from `DeployedConstraintXOnlineTrace`. -/
def deployedConstraintXSqueezeSchedule_of_pinned
    (family : ComputedDeployedRootFSFamily shape)
    {B W Dc D Dq : ℕ} (hB : 1 ≤ B) (hkB : 2 ^ shape.k - 1 ≤ B)
    (hnB : ∀ basis, (family.vk basis).n - 1 ≤ B)
    (hgates : ∀ basis, ∀ e ∈ (family.vk basis).gates, e.degreeBound * B ≤ D)
    (hW : ∀ basis, ∀ c ∈ (family.vk basis).permutationChunks, c.length ≤ W)
    (hlin : ∀ basis, ∀ l : Fin shape.numLookups,
      ∀ e ∈ (family.vk basis).lookupInputExprs l, e.degreeBound * B ≤ Dc)
    (hltab : ∀ basis, ∀ l : Fin shape.numLookups,
      ∀ e ∈ (family.vk basis).lookupTableExprs l, e.degreeBound * B ≤ Dc)
    (hq : ∀ basis, (family.vk basis).n * shape.numQuotientPieces + B ≤ Dq)
    (h3 : 3 * B ≤ D) (hWD : (W + 2) * B ≤ D) (h4 : 4 * B ≤ D)
    (hcomp : 2 * B + 2 * Dc ≤ D)
    (hpinned : DeployedConstraintXPinning family) :
    DeployedConstraintXSqueezeSchedule family
      ((max D Dq : ℕ) / (Fintype.card Fp : ℝ≥0∞)) where
  measure_le basis O :=
    deployedConstraintXBadSet_measure_le family basis O (fun tape root =>
      natDegree_deployedConstraintDifferenceOfRoot_le family basis (O, tape) root hB hkB
        (hnB basis) (hgates basis) (hW basis) (hlin basis) (hltab basis) (hq basis)
        h3 hWD h4 hcomp)
  pinned := hpinned

/-- A stronger convenience constructor deriving exact pinning from strict prefix determination. -/
def deployedConstraintXSqueezeSchedule_of_prefixDetermined
    (family : ComputedDeployedRootFSFamily shape)
    (hcausal : DeployedConstraintXPrefixDetermined family)
    {B W Dc D Dq : ℕ} (hB : 1 ≤ B) (hkB : 2 ^ shape.k - 1 ≤ B)
    (hnB : ∀ basis, (family.vk basis).n - 1 ≤ B)
    (hgates : ∀ basis, ∀ e ∈ (family.vk basis).gates, e.degreeBound * B ≤ D)
    (hW : ∀ basis, ∀ c ∈ (family.vk basis).permutationChunks, c.length ≤ W)
    (hlin : ∀ basis, ∀ l : Fin shape.numLookups,
      ∀ e ∈ (family.vk basis).lookupInputExprs l, e.degreeBound * B ≤ Dc)
    (hltab : ∀ basis, ∀ l : Fin shape.numLookups,
      ∀ e ∈ (family.vk basis).lookupTableExprs l, e.degreeBound * B ≤ Dc)
    (hq : ∀ basis, (family.vk basis).n * shape.numQuotientPieces + B ≤ Dq)
    (h3 : 3 * B ≤ D) (hWD : (W + 2) * B ≤ D) (h4 : 4 * B ≤ D)
    (hcomp : 2 * B + 2 * Dc ≤ D) :
    DeployedConstraintXSqueezeSchedule family
      ((max D Dq : ℕ) / (Fintype.card Fp : ℝ≥0∞)) :=
  deployedConstraintXSqueezeSchedule_of_pinned family hB hkB hnB hgates hW hlin hltab hq
    h3 hWD h4 hcomp (deployedConstraintXPinning_of_prefixDetermined family hcausal)

end Zcash.Snark
