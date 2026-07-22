import Mathlib
import Zcash.Snark.Soundness.Main
import Zcash.Snark.Soundness.Forking.Probability
import Zcash.Snark.Soundness.Multiopen.Decode

/-!
# Compatibility layer for the multiopen decode reconstruction

`fs-adversary` carries the augmented binding reduction as *computed data*
(`NontrivialRelation`, `NontrivialRelation.ofDeployedTree`), whereas the multiopen-decode
development (`Multiopen/Decode.lean`, `Multiopen/Deployed.lean`, `Multiopen/DecodeFixture.lean`)
was written against the *propositional* interface `HasNontrivialRelation` / `deployed_to_acceptV`.

This module re-exposes that propositional interface on top of the structure-based API, ports the
`Msm` evaluation spine lemmas the decode proofs need (`Msm.eval_{zero,scale,add}`), and states the
decoded-column constraint bridges
(`hasNontrivialRelation_of_two_openings`, `decoded_constraint_of_relation_and_batch`,
`decoded_constraint_of_opening_or_relation`).
-/

namespace Zcash.Snark

namespace Msm

/-- The zero MSM evaluates to the group identity. -/
theorem eval_zero {F G : Type*} [Field F] [AddCommGroup G] [Module F G] (urs : URS G) :
    (Msm.zero urs.k F G).eval urs = 0 := by
  simp [eval, zero]

/-- Scaling an MSM scales its evaluation. -/
theorem eval_scale {F G : Type*} [Field F] [AddCommGroup G] [Module F G]
    (urs : URS G) (c : F) (m : Msm urs.k F G) :
    (m.scale c).eval urs = c • m.eval urs := by
  simp only [eval, scale, smul_add, Finset.smul_sum, List.smul_sum, List.map_map,
    Function.comp_def, mul_smul]

/-- Adding two MSMs adds their evaluations. -/
theorem eval_add {F G : Type*} [Field F] [AddCommGroup G] [Module F G]
    (urs : URS G) (m₁ m₂ : Msm urs.k F G) :
    (m₁.add m₂).eval urs = m₁.eval urs + m₂.eval urs := by
  simp only [eval, add, add_smul, Finset.sum_add_distrib, List.map_append, List.sum_append]
  abel

end Msm

section Binding

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- A nontrivial discrete-log relation among the augmented generators `(g, U, W)`: scalars `(a, α, β)`
not all zero with `⟨a, g⟩ + α • U + β • W = 0`. Such a relation always *exists* in a prime-order group;
the content of the reduction below is that breaking binding *produces* one, which DLR hardness forbids. -/
def HasNontrivialRelation {n : ℕ} (g : Fin n → G) (U W : G) : Prop :=
  ∃ (a : Fin n → F) (α β : F), (a ≠ 0 ∨ α ≠ 0 ∨ β ≠ 0) ∧ commitGen g a + α • U + β • W = 0

/-- Bridge from `fs-adversary`'s computed `NontrivialRelation` datum to the propositional
`HasNontrivialRelation`. `commitGen g a` is `∑ i, a i • g i` by definition, so the structure's
`relation` field is the required equation. -/
theorem HasNontrivialRelation.of_nontrivialRelation {n : ℕ} {g : Fin n → G} {U W : G}
    (r : NontrivialRelation (F := F) g U W) : HasNontrivialRelation (F := F) g U W :=
  ⟨r.a, r.α, r.β, r.nontrivial, by simpa [commitGen] using r.relation⟩

/-- The deployed recursion peels to the clean `IpaAcceptV`, or exhibits a nontrivial relation.
Propositional form of `NontrivialRelation.ofDeployedTree`: either the clean IPA transcript accepts,
or the structure-based constructor (fed the negation) yields a relation datum, which
`of_nontrivialRelation` demotes to the `HasNontrivialRelation` branch. Binding enters only as that
branch — the reduction, not an assumed independence. -/
theorem deployed_to_acceptV {U W : G} {z : F} (hz : z ≠ 0)
    {d : ℕ} (g : Fin (2 ^ d) → G) (b : Fin (2 ^ d) → F) (P : G) (v blind : F)
    (t : DeployedIpaTreeV F G d) (h : DeployedIpaAcceptV g b U W z P v blind t) :
    IpaAcceptV g b P v (projTree t) ∨ HasNontrivialRelation (F := F) g U W := by
  classical
  by_cases hacc : IpaAcceptV g b P v (projTree t)
  · exact Or.inl hacc
  · exact Or.inr (HasNontrivialRelation.of_nontrivialRelation
      (NontrivialRelation.ofDeployedTree hz g b P v blind t h hacc))

end Binding

section Decoded

variable {G : Type*} [AddCommGroup G] [Module Fp G]

theorem hasNontrivialRelation_of_two_openings (urs : URS G) {a a' : Fin (2 ^ urs.k) → Fp}
    (hne : a ≠ a') (hcollision : commit urs a = commit urs a') :
    HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  refine ⟨a - a', 0, 0, Or.inl (sub_ne_zero.mpr hne), ?_⟩
  have hsub : commitGen (F := Fp) urs.g (a - a') = commit urs a - commit urs a' := by
    simp only [commit, commitGen, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
  rw [hsub, hcollision]
  simp

open Polynomial in
/-- Turn a final multiopen relation plus same-witness batch rewinds into the decoded-column SNARK
relation. This is the terminal constraint-side bridge used by the probability/AGM capstones: the circuit is
checked on columns recovered from the verifier-opened multiopen relation, not through an arbitrary
`decodeAdvice`/`decodeInstance` function. `hquot`/`hgood` are stated for the canonical decode
`decodedCols hbatch` — the family this proof constructs — and are dischargeable only with `x` the opened
point (see the scope section in the module docstring). -/
theorem decoded_constraint_of_relation_and_batch {urs : URS G} {P : G}
    {b : Fin (2 ^ urs.k) → Fp} {v : Fp}
    {numColumns numAdvice numInstance : ℕ}
    (columnCommitments : Fin numColumns → G) (columnEvals : Fin numColumns → Fp)
    (adviceIndex : Fin numAdvice → Fin numColumns) (instanceIndex : Fin numInstance → Fin numColumns)
    (fixedCols : ℕ → Polynomial Fp)
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ) (x : Fp)
    {a : Fin (2 ^ urs.k) → Fp}
    (hrel : IpaRelation urs P b v a)
    (hbatch : BatchOpeningsForWitness urs b columnCommitments columnEvals a)
    (hquot : quotientCheck
      (combineGates fixedCols (selectedPolys (decodedCols hbatch) adviceIndex)
        (selectedPolys (decodedCols hbatch) instanceIndex) y gates) hpoly deg x)
    (hgood : combineGates fixedCols (selectedPolys (decodedCols hbatch) adviceIndex)
        (selectedPolys (decodedCols hbatch) instanceIndex) y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols (selectedPolys (decodedCols hbatch) adviceIndex)
        (selectedPolys (decodedCols hbatch) instanceIndex) y gates
          - hpoly * (X ^ deg - 1)).eval x ≠ 0)
    {S : Prop}
    (hencodes : ∀ a cols,
      SnarkRelationWithDecodedColumns urs P b v columnCommitments columnEvals adviceIndex instanceIndex
        fixedCols y gates hpoly deg a cols → S) :
    S := by
  have hsat : circuitSatViaGates fixedCols
      (selectedPolysDecode (k := urs.k) (decodedCols hbatch) adviceIndex)
      (selectedPolysDecode (k := urs.k) (decodedCols hbatch) instanceIndex) y gates hpoly deg a :=
    circuitSatViaGates_of_check fixedCols
      (selectedPolysDecode (k := urs.k) (decodedCols hbatch) adviceIndex)
      (selectedPolysDecode (k := urs.k) (decodedCols hbatch) instanceIndex) y gates hpoly deg a x
      hquot hgood
  exact hencodes a (decodedCols hbatch)
    { opens := hrel
      batchOpenings := hbatch
      decodedColumns := decodedCols_spec hbatch
      satisfiesCircuit := hsat }

open Polynomial in
/-- Lift an opening-or-DLR terminal capstone to the decoded-column constraint endpoint, provided the
multiopen batch rewinding output is available for the final relation witness. Conditional interface: the
batch family is assumed via `MultiopenRewindForRelation` (see its docstring), and `hquot`/`hgood` are
stated for the canonical decode of the batch supplied at each relation witness. Reduction-shaped:
quantifying `hquot ∧ hgood` over every opening is jointly unsatisfiable once the commitment kernel is
nontrivial (see the scope section of `Soundness.Multiopen.Decode`); the live capstones pin the
witness. -/
theorem decoded_constraint_of_opening_or_relation {urs : URS G} {P : G}
    {b : Fin (2 ^ urs.k) → Fp} {v : Fp}
    {numColumns numAdvice numInstance : ℕ}
    (columnCommitments : Fin numColumns → G) (columnEvals : Fin numColumns → Fp)
    (adviceIndex : Fin numAdvice → Fin numColumns) (instanceIndex : Fin numInstance → Fin numColumns)
    (fixedCols : ℕ → Polynomial Fp)
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ) (x : Fp)
    (hopening : (∃ a, IpaRelation urs P b v a) ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w)
    (hbatch : MultiopenRewindForRelation urs P b v columnCommitments columnEvals)
    (hquot : ∀ a (hrel : IpaRelation urs P b v a),
      quotientCheck
        (combineGates fixedCols (selectedPolys (decodedCols (hbatch a hrel)) adviceIndex)
          (selectedPolys (decodedCols (hbatch a hrel)) instanceIndex) y gates) hpoly deg x)
    (hgood : ∀ a (hrel : IpaRelation urs P b v a),
      combineGates fixedCols (selectedPolys (decodedCols (hbatch a hrel)) adviceIndex)
          (selectedPolys (decodedCols (hbatch a hrel)) instanceIndex) y gates
        ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols (selectedPolys (decodedCols (hbatch a hrel)) adviceIndex)
          (selectedPolys (decodedCols (hbatch a hrel)) instanceIndex) y gates
        - hpoly * (X ^ deg - 1)).eval x ≠ 0)
    {S : Prop}
    (hencodes : ∀ a cols,
      SnarkRelationWithDecodedColumns urs P b v columnCommitments columnEvals adviceIndex instanceIndex
        fixedCols y gates hpoly deg a cols → S) :
    S ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  rcases hopening with ⟨a, hrel⟩ | hrel
  · exact Or.inl (decoded_constraint_of_relation_and_batch columnCommitments columnEvals adviceIndex
      instanceIndex fixedCols y gates hpoly deg x hrel (hbatch a hrel) (hquot a hrel) (hgood a hrel)
      hencodes)
  · exact Or.inr hrel

end Decoded

end Zcash.Snark
