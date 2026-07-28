import Mathlib
import Zcash.Snark.Soundness.Main
import Zcash.Snark.Soundness.Forking.Rewind
import Zcash.Snark.Soundness.Multiopen.Opened
import Zcash.Snark.Soundness.Multiopen.ValueCheckDeployed
import Zcash.Snark.Soundness.Multiopen.NodeBinding
import Zcash.Snark.Soundness.Forking.KnowledgeError
import CompElliptic.Curves.Pasta
import CompElliptic.Curves.PastaOrder

/-!
# Vesta instantiation: the verifier group at the deployed curve

The soundness theorems of `Zcash.Snark.Soundness.Main` are proven for an abstract
`Fp`-module `G`. Here `G` is pinned to the actual Vesta curve `SWPoint Vesta.curve` (`y² = x³ + 5`),
whose group law CompElliptic/mathlib have already proven (associativity transported from
`WeierstrassCurve.Affine.Point`). The deployed Orchard verifier runs over Vesta, so these theorems are
the concrete-curve forms of the abstract capstones.

## The setting

The only structure the `Fp`-action needs that the curve does not already carry is the Vesta group
order: every point is `p`-torsion (`p = scalarFieldOrder`). Given that, `AddCommGroup.zmodModule`
turns the curve into an `Fp`-module and the abstract theorems specialize to Vesta.

## Assumptions

* **The Vesta group order.** CompElliptic's `Pasta.Vesta.card_eq` supplies
  `Nat.card VestaG = scalarFieldOrder`, from which `vestaOrder` proves that every point is annihilated
  by the scalar-field order. This does not require a caller-supplied hypothesis, but `card_eq` is a
  closed computation certified with `native_decide`; concrete Vesta endpoints inherit that pinned
  compiler-trust axiom.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (Msm Msm.evalNat_eq_eval scalarFieldOrder)

-- The deployed grouping definitions appear inside index types, so a defeq check on an index can
-- pull the whole `constructIntermediateSets (assembleQueries …)` computation through `whnf`.
-- Sealing them keeps those checks syntactic; the proofs below use their equation lemmas.
attribute [local irreducible] deployedSetQueries deployedSetCommIds deployedX4PairCount
  x4BatchCommitments x4BatchEvals

open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass CompElliptic.CurveOrder

/-- The deployed verifier group `E_q`, concretely `SWPoint Vesta.curve`: the points of `y² = x³ + 5`. -/
abbrev VestaG := SWPoint Vesta.curve

/-- The Vesta group-order proposition: every Vesta point is `p`-torsion for
`p = scalarFieldOrder`. `vestaOrder` supplies it from CompElliptic's pinned point-count result, and
`vestaFpModule` consumes it through `Fact`. -/
abbrev VestaOrder : Prop := ∀ P : VestaG, (scalarFieldOrder : ℕ) • P = 0

/-- Derive the Vesta group-order proposition from CompElliptic's `Pasta.Vesta.card_eq` and the fact
that a finite group is annihilated by its cardinality. The theorem has no explicit hypothesis, but
inherits `card_eq`'s pinned `native_decide` axiom. -/
theorem vestaOrder : VestaOrder := by
  intro P
  have hcard : Nat.card VestaG = scalarFieldOrder := Vesta.card_eq
  rw [← hcard]
  exact addOrderOf_dvd_iff_nsmul_eq_zero.mp (addOrderOf_dvd_natCard P)

/-- Install the Vesta order proved by `vestaOrder` as the `Fact` used by the `Fp`-module instance. -/
instance : Fact VestaOrder := ⟨vestaOrder⟩

/-- Given the Vesta group order (`Fact VestaOrder`), the curve is an `Fp`-module
(`AddCommGroup.zmodModule` on the `p`-torsion). Conditional — it fires only when the order `Fact`
is in scope; this file installs that fact via `vestaOrder`. Computable (curve addition and the
`ZMod`-action both are), so the break reductions stay plain `def`s at the concrete curve. -/
instance vestaFpModule [h : Fact VestaOrder] : Module Fp VestaG :=
  AddCommGroup.zmodModule h.out

/-- **The concrete-to-abstract MSM bridge at Vesta.** `Msm.evalNat_eq_eval` specialised to
`SWPoint Vesta.curve`: the pinned Vesta group order supplies the `Fp`-module structure
unconditionally (via `vestaFpModule`, as for the capstones below), so the executable natural-scalar
evaluation the concrete fixtures compute (`capturedMsm.evalNat`, `(assemble ..).evalNat`) coincides
with the module-theoretic `eval` the soundness capstones consume. So the fixtures' `evalNat = 0`
checks *are* the `eval = 0` acceptance condition of the abstract verifier, not merely an analogous
computation. -/
theorem Msm.evalNat_eq_eval_vesta (urs : URS VestaG)
    (m : Msm urs.k Fp VestaG) : m.evalNat urs = m.eval urs :=
  Msm.evalNat_eq_eval urs m

def NontrivialRelation.ofUnopenedForkVesta [DecidableEq VestaG]
    [Inhabited VestaG]
    {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp VestaG) (instanceCommitment : Fin shape.numProofs → ℕ → VestaG)
    (ps : ProofString shape Fp VestaG) (ch : Challenges shape.k Fp)
    {b : Fin (2 ^ urs.k) → Fp} {z blind : Fp} (hz : z ≠ 0)
    (fs : ForkedTranscript urs hk vk instanceCommitment ps ch b z blind)
    (hne : ¬ IpaAcceptV urs.g b fs.openedCommitment (multiopenValue vk instanceCommitment ps ch)
      (projTree fs.tree)) :
    NontrivialRelation (F := Fp) urs.g urs.u urs.w :=
  NontrivialRelation.ofUnopenedFork urs hk vk instanceCommitment ps ch hz fs hne

open Polynomial in
/-- **Deployed opening and constraint over Vesta, given a clean fork.**
`orchard_verifier_deployed_constraint_of_forked` specialised to `SWPoint Vesta.curve`: the opening
for the declared `fs.openedCommitment` and the pinned `multiopenValue`, and `circuitSat` (concrete
`circuitSatViaGates`) from the verifier's gate point-check `hquot` lifted by Schwartz–Zippel
(`hgood`). The `Fp`-module comes from the pinned Vesta point-count result. `hquot`/`hgood` share
`hcirc`'s unsatisfiable shape (see the section note in `Soundness.Main`). -/
theorem orchard_verifier_vesta_constraint_of_forked [DecidableEq VestaG] [Inhabited VestaG]
    {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp VestaG) (instanceCommitment : Fin shape.numProofs → ℕ → VestaG)
    (ps : ProofString shape Fp VestaG) (ch : Challenges shape.k Fp)
    {b : Fin (2 ^ urs.k) → Fp} {z blind : Fp}
    (fixedCols : ℕ → Polynomial Fp)
    (decodeAdvice decodeInstance : (Fin (2 ^ urs.k) → Fp) → (ℕ → Polynomial Fp))
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ) (x : Fp)
    (fs : ForkedTranscript urs hk vk instanceCommitment ps ch b z blind)
    (hclean : IpaAcceptV urs.g b fs.openedCommitment (multiopenValue vk instanceCommitment ps ch)
      (projTree fs.tree))
    (hquot : ∀ a, IpaRelation urs fs.openedCommitment b
      (multiopenValue vk instanceCommitment ps ch) a →
      quotientCheck (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates) hpoly deg x)
    (hgood : ∀ a, IpaRelation urs fs.openedCommitment b
      (multiopenValue vk instanceCommitment ps ch) a →
      combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates
        - hpoly * (X ^ deg - 1)).eval x ≠ 0)
    {S : Prop}
    (hencodes : ∀ a, SnarkRelation urs fs.openedCommitment b (multiopenValue vk instanceCommitment ps ch)
      (circuitSatViaGates fixedCols decodeAdvice decodeInstance y gates hpoly deg) a → S) :
    S :=
  orchard_verifier_deployed_constraint_of_forked urs hk vk instanceCommitment ps ch fixedCols
    decodeAdvice decodeInstance y gates hpoly deg x fs hclean hquot hgood hencodes

/-- The powers evaluation vector has leading entry `1` (`evalVector k x 0 = x⁰ = 1`), discharging the IPA's
`hb0` structural fact at the concrete deployed `b = evalVector`. -/
theorem evalVector_zero {F : Type*} [Field F] (k : ℕ) (x : F) : evalVector k x 0 = 1 := by
  simp [evalVector]

/-- The IPA witness after folding in the value term and synthetic blinder. -/
def adjustedWitness {k : ℕ} (aMulti s : Fin (2 ^ k) → Fp) (v ξ : Fp) : Fin (2 ^ k) → Fp :=
  aMulti - Pi.single 0 v + ξ • s

/-- The adjusted witness commits to halo2's adjusted commitment — `hP` holds by linearity, not by assumption. -/
theorem commit_adjustedWitness {G : Type*} [AddCommGroup G] [Module Fp G] (urs : URS G)
    (aMulti s : Fin (2 ^ urs.k) → Fp) (v ξ : Fp) :
    commit urs (adjustedWitness aMulti s v ξ) = commit urs aMulti - v • urs.g 0 + ξ • commit urs s := by
  have csub : ∀ a a' : Fin (2 ^ urs.k) → Fp, commit urs (a - a') = commit urs a - commit urs a' := by
    intro a a'; simp only [commit, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
  rw [adjustedWitness, commit_add, csub, commit_single, commit_smul]

open scoped ENNReal in
/-- A nonzero blinding shift vanishes for at most a `1 / |Fp|` fraction of uniform `ξ` challenges. -/
theorem blinder_value_recovery_badSet {k : ℕ} (s : Fin (2 ^ k) → Fp) (xEval : Fp)
    (hδ : innerProduct s (evalVector k xEval) ≠ 0) :
    uniformChallenge.toOuterMeasure
        (Finset.univ.filter (fun ξ : Fp => ξ * innerProduct s (evalVector k xEval) = 0))
      ≤ 1 / (Fintype.card Fp : ℝ≥0∞) :=
  blinder_shift_badSet_measure (innerProduct s (evalVector k xEval)) 0 hδ

/-- The single-entry value term in the adjusted commitment is `-v • g 0`. -/
theorem sum_getD_single {k : ℕ} {G : Type*} [AddCommGroup G] [Module Fp G] (gg : Fin (2 ^ k) → G)
    (v : Fp) :
    (∑ i, ([-v].getD i.val 0 : Fp) • gg i) = -v • gg 0 := by
  rw [Finset.sum_eq_single (0 : Fin (2 ^ k))]
  · simp
  · intro i _ hi
    have hival : i.val ≠ 0 := Fin.val_ne_zero_iff.mpr hi
    rw [List.getD_eq_default, zero_smul]
    simp only [List.length_cons, List.length_nil, Nat.zero_add]
    omega
  · intro h; exact absurd (Finset.mem_univ _) h
open Polynomial in
open scoped ENNReal in
open Classical in
/-- **Deployed decoded constraint, per fork, batch produced by `x₄` rewinding.** The circuit is
checked on columns decoded from the opened `x₄` batch over the deployed aggregates, not through
free decode functions; the batch is derived from the fork's clean transcript and the `x₄` accept
measure (`openedX4Rewind_of_x4Prob_forked`). `hquot`/`hgood` are stated once, for the canonical
decode at the transcript's own extracted witness — the satisfiable shape (quantifying over every
opening is vacuous at a nontrivial kernel; see `Multiopen.Decode`'s scope section). -/
theorem orchard_verifier_vesta_decoded_constraint_of_forked_x4 [DecidableEq VestaG]
    [Inhabited VestaG] {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp VestaG) (instanceCommitment : Fin shape.numProofs → ℕ → VestaG) (ps : ProofString shape Fp VestaG)
    (ch : Challenges shape.k Fp)
    {b : Fin (2 ^ urs.k) → Fp} {z blind : Fp}
    {numAdvice numInstance : ℕ}
    (adviceIndex : Fin numAdvice → Fin (deployedX4PairCount vk instanceCommitment ps ch + 1))
    (instanceIndex : Fin numInstance → Fin (deployedX4PairCount vk instanceCommitment ps ch + 1))
    (fixedCols : ℕ → Polynomial Fp)
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ) (x : Fp)
    (fs : ForkedTranscript urs hk vk instanceCommitment ps ch b z blind)
    (hclean : IpaAcceptV urs.g b fs.openedCommitment (multiopenValue vk instanceCommitment ps ch)
      (projTree fs.tree))
    (hprob4 : ((deployedX4PairCount vk instanceCommitment ps ch : ℝ≥0∞)) / Fintype.card Fp
      < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
          (OpenedX4Accept urs hk vk instanceCommitment ps ch b)))
    (hquot : quotientCheck
        (combineGates fixedCols
          (selectedPolys (openedDecodedCols (openedX4Rewind_of_x4Prob_forked urs hk vk instanceCommitment ps ch fs
            ⟨projTree fs.tree, hclean⟩ hprob4 (ipaRelation_extract urs b fs.openedCommitment (multiopenValue vk instanceCommitment ps ch)
            (projTree fs.tree) hclean).1
          (ipaRelation_extract urs b fs.openedCommitment (multiopenValue vk instanceCommitment ps ch)
            (projTree fs.tree) hclean).2)) adviceIndex)
          (selectedPolys (openedDecodedCols (openedX4Rewind_of_x4Prob_forked urs hk vk instanceCommitment ps ch fs
            ⟨projTree fs.tree, hclean⟩ hprob4 (ipaRelation_extract urs b fs.openedCommitment (multiopenValue vk instanceCommitment ps ch)
            (projTree fs.tree) hclean).1
          (ipaRelation_extract urs b fs.openedCommitment (multiopenValue vk instanceCommitment ps ch)
            (projTree fs.tree) hclean).2)) instanceIndex)
          y gates) hpoly deg x)
    (hgood :
      combineGates fixedCols
          (selectedPolys (openedDecodedCols (openedX4Rewind_of_x4Prob_forked urs hk vk instanceCommitment ps ch fs
            ⟨projTree fs.tree, hclean⟩ hprob4 (ipaRelation_extract urs b fs.openedCommitment (multiopenValue vk instanceCommitment ps ch)
            (projTree fs.tree) hclean).1
          (ipaRelation_extract urs b fs.openedCommitment (multiopenValue vk instanceCommitment ps ch)
            (projTree fs.tree) hclean).2)) adviceIndex)
          (selectedPolys (openedDecodedCols (openedX4Rewind_of_x4Prob_forked urs hk vk instanceCommitment ps ch fs
            ⟨projTree fs.tree, hclean⟩ hprob4 (ipaRelation_extract urs b fs.openedCommitment (multiopenValue vk instanceCommitment ps ch)
            (projTree fs.tree) hclean).1
          (ipaRelation_extract urs b fs.openedCommitment (multiopenValue vk instanceCommitment ps ch)
            (projTree fs.tree) hclean).2)) instanceIndex)
          y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols
          (selectedPolys (openedDecodedCols (openedX4Rewind_of_x4Prob_forked urs hk vk instanceCommitment ps ch fs
            ⟨projTree fs.tree, hclean⟩ hprob4 (ipaRelation_extract urs b fs.openedCommitment (multiopenValue vk instanceCommitment ps ch)
            (projTree fs.tree) hclean).1
          (ipaRelation_extract urs b fs.openedCommitment (multiopenValue vk instanceCommitment ps ch)
            (projTree fs.tree) hclean).2)) adviceIndex)
          (selectedPolys (openedDecodedCols (openedX4Rewind_of_x4Prob_forked urs hk vk instanceCommitment ps ch fs
            ⟨projTree fs.tree, hclean⟩ hprob4 (ipaRelation_extract urs b fs.openedCommitment (multiopenValue vk instanceCommitment ps ch)
            (projTree fs.tree) hclean).1
          (ipaRelation_extract urs b fs.openedCommitment (multiopenValue vk instanceCommitment ps ch)
            (projTree fs.tree) hclean).2)) instanceIndex)
          y gates - hpoly * (X ^ deg - 1)).eval x ≠ 0)
    {S : Prop}
    (hencodes : ∀ a cols,
      SnarkRelationWithOpenedColumns urs fs.openedCommitment b (multiopenValue vk instanceCommitment ps ch)
        (x4BatchCommitments urs hk vk instanceCommitment ps ch) (x4BatchEvals vk instanceCommitment ps ch) adviceIndex instanceIndex
        fixedCols y gates hpoly deg fs.pU fs.pW a cols → S) :
    S :=
  opened_constraint_of_relation_and_batch (x4BatchCommitments urs hk vk instanceCommitment ps ch)
    (x4BatchEvals vk instanceCommitment ps ch) adviceIndex instanceIndex fixedCols y gates hpoly deg x
    (ipaRelation_extract urs b fs.openedCommitment (multiopenValue vk instanceCommitment ps ch)
            (projTree fs.tree) hclean).2
    (openedX4Rewind_of_x4Prob_forked urs hk vk instanceCommitment ps ch fs
            ⟨projTree fs.tree, hclean⟩ hprob4 (ipaRelation_extract urs b fs.openedCommitment (multiopenValue vk instanceCommitment ps ch)
            (projTree fs.tree) hclean).1
          (ipaRelation_extract urs b fs.openedCommitment (multiopenValue vk instanceCommitment ps ch)
            (projTree fs.tree) hclean).2)
    hquot hgood hencodes

end Zcash.Snark
