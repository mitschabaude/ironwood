import Zcash.Snark.Soundness.Vesta
import Zcash.Snark.Soundness.Forking.Adversary.Algebraic
import Zcash.Snark.Soundness.AGM.Capstone

/-!
# Issue #67: composing the algebraic forking extraction with the deployed decoded capstone

`Soundness.Forking.Adversary.Algebraic` proves the clean-opening branch of the algebraic forking
family (`runToSnark`, bounded by `snarkFailure_prob_le_of_*`); `Soundness.Vesta` proves the deployed
decoded capstone (`orchard_verifier_vesta_member_constraint_derived`). The two are architecturally
disjoint — one runs over an adversary-produced `AlgebraicWfProof` at oracle-derived challenges
`chRecord ν`, the other over a deployed `(vk, ps, ch)` run. This module builds the identification
bridge #67 needs on the *computed path*: the algebraic instance's clean `Opening` — an `IpaRelation`
at `commit … aMulti` — is exactly the `IpaRelation` at the deployed opened commitment
`deployedCommitment − pU•u − pW•w` the capstone consumes, once `AlgebraicWfProof.multiopen_repr`
rewrites the commitment and the honest value shift `z⁻¹·vU − ξ·⟨s,b⟩` is discharged.
-/

namespace Zcash.Snark

-- Match the instance set `AlgebraicWfProof.multiopen_repr` is stated against
-- (`Forking.Adversary.Algebraic` uses the same concrete `Inhabited VestaG`); a local `[Inhabited]`
-- binder would be a *different* instance term, forcing the `multiopenCommitment` fold through `whnf`.
-- Named (not anonymous) to avoid an auto-generated-name collision with the identical
-- `local instance` in `Forking.Adversary.Provenance` when both are imported into `TrustBoundary`.
local instance vestaInhabitedCompose67 : Inhabited VestaG := ⟨0⟩

variable {shape : Shape} {basis : AugmentedIndex (2 ^ shape.k) → VestaG}

/-- `deployedCommitment` at the split URS unfolds to `multiopenCommitment`: definitional (the `hk`
cast is `rfl` on `ursOfAugmentedBasis`, whose `.k` is `shape.k`). Isolated so downstream terms match
`AlgebraicWfProof.multiopen_repr`'s `multiopenCommitment` without forcing the fold through `whnf`. -/
theorem deployedCommitment_eq_multiopen
    (vk : VerifyingKey shape Fp VestaG) (ps : ProofString shape Fp VestaG)
    (ch : Challenges shape.k Fp) :
    deployedCommitment (ursOfAugmentedBasis shape.k basis) rfl vk ps ch
      = multiopenCommitment (ursOfAugmentedBasis shape.k basis).g
          (ursOfAugmentedBasis shape.k basis).w (ursOfAugmentedBasis shape.k basis).u vk ps ch :=
  rfl

/-- **The g-span representation of the multiopen commitment (P-identification).** The algebraic
proof's aggregate witness `aMulti ν` commits to `multiopenCommitment − multiU•u − multiBlind•w`:
immediate from `AlgebraicWfProof.multiopen_repr`. -/
theorem commit_aMulti_eq_multiopen
    {vk : VerifyingKey shape Fp VestaG} (p : AlgebraicWfProof basis vk) (ν : Fin 11 → Fp) :
    commit (ursOfAugmentedBasis shape.k basis) (p.aMulti ν)
      = multiopenCommitment (ursOfAugmentedBasis shape.k basis).g
          (ursOfAugmentedBasis shape.k basis).w (ursOfAugmentedBasis shape.k basis).u
          vk p.algebraicProof.erase (chRecord ν (fun _ => 0))
        - p.multiU ν • (ursOfAugmentedBasis shape.k basis).u
        - p.multiBlind ν • (ursOfAugmentedBasis shape.k basis).w := by
  have h := p.multiopen_repr ν
  rw [sub_sub, eq_sub_iff_add_eq, ← add_assoc]
  exact h

/-- **The algebraic clean opening is an `IpaRelation` at the identified commitment/value (the #67
bridge, abstract form).** A clean `Opening` of a `DeployedAlgebraicForkingInstance` `x` is an
`IpaRelation` at `commit … x.aMulti`, base `x.b`, value `x.v + z⁻¹·vU − ξ·⟨s,b⟩`. Given the
P-identification `hP` (`commit x.aMulti = P`), the value identification `hv` (`x.v = v`), and the
honest shift-vanishing `hshift`, that opening's witness satisfies `IpaRelation urs P x.b v`. -/
theorem ipaRelation_of_opening
    {P : VestaG} {v : Fp}
    (x : DeployedAlgebraicForkingInstance (G := VestaG) shape.k basis)
    (hP : commit (ursOfAugmentedBasis shape.k basis) x.aMulti = P)
    (hv : x.v = v)
    (hshift : x.z⁻¹ * x.vU - x.ξ * innerProduct x.s x.b = 0)
    (o : x.Opening) :
    IpaRelation (ursOfAugmentedBasis shape.k basis) P x.b v o.1 := by
  obtain ⟨hcommit, hval⟩ := o.2
  refine ⟨hcommit.trans hP, ?_⟩
  rw [hval, add_sub_assoc, hshift, add_zero, hv]

set_option maxHeartbeats 1000000 in
/-- **The bridge at the constructed instance.** `ipaRelation_of_opening` at
`deployedAlgebraicInstanceOfCert p ν cert hz hvalid`, with `P` the deployed opened commitment
`deployedCommitment − multiU•u − multiBlind•w` and `v = multiopenValue`. `hP` is discharged by
`commit_aMulti_eq_multiopen` (through `deployedCommitment_eq_multiopen`); `hv` is `rfl` (the instance's
`v` field); `hshift` is the honest-instance condition (`vU = 0` and the `ξ·⟨s,b⟩` term vanishing),
carried as a premise. This is the exact `IpaRelation` shape `OpenedBatchOpenings.ipaRelation_of_x4Current`
and the deployed member capstone consume. -/
theorem ipaRelation_deployed_of_instance
    {vk : VerifyingKey shape Fp VestaG} (p : AlgebraicWfProof basis vk) (ν : Fin 11 → Fp)
    (cert : AlgebraicDForkCert (F := Fp)
      (augmentedBasis (ursOfAugmentedBasis shape.k basis).g
        (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w) shape.k)
    (hz : ν 10 ≠ 0)
    (hvalid : DeployedForkValid (ursOfAugmentedBasis shape.k basis).g
      (evalVector shape.k (ν 7)) (ursOfAugmentedBasis shape.k basis).u
      (ursOfAugmentedBasis shape.k basis).w (ν 10)
      (commit (ursOfAugmentedBasis shape.k basis)
          (adjustedWitness (p.aMulti ν) p.s
            (multiopenValue vk p.proof.1 (chRecord ν (fun _ => 0))) (ν 9)) +
        (p.multiU ν + ν 9 * p.sU) • (ursOfAugmentedBasis shape.k basis).u +
        (p.multiBlind ν + ν 9 * p.sBlind) • (ursOfAugmentedBasis shape.k basis).w)
      cert.toDForkCert)
    (hshift : (ν 10)⁻¹ * (p.multiU ν + ν 9 * p.sU)
        - ν 9 * innerProduct p.s (evalVector shape.k (ν 7)) = 0)
    (o : (deployedAlgebraicInstanceOfCert p ν cert hz hvalid).Opening) :
    IpaRelation (ursOfAugmentedBasis shape.k basis)
      (deployedCommitment (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
            (chRecord ν (fun _ => 0))
        - p.multiU ν • (ursOfAugmentedBasis shape.k basis).u
        - p.multiBlind ν • (ursOfAugmentedBasis shape.k basis).w)
      (evalVector shape.k (ν 7)) (multiopenValue vk p.proof.1 (chRecord ν (fun _ => 0))) o.1 :=
  ipaRelation_of_opening (deployedAlgebraicInstanceOfCert p ν cert hz hvalid)
    (by
      simp only [deployedAlgebraicInstanceOfCert]
      rw [deployedCommitment_eq_multiopen,
        show (p.proof.1 : ProofString shape Fp VestaG) = p.algebraicProof.erase from rfl]
      exact commit_aMulti_eq_multiopen p ν)
    rfl hshift o

open Polynomial in
open Classical in
set_option maxHeartbeats 1000000 in
/-- **G3 witness-tie: the algebraic clean opening feeds the deployed member capstone.** Mirroring the
legacy forking constraint (`orchard_verifier_vesta_forking_constraint_deployed_x4`), the deployed
batch `pbatch` supplies its own opening `hrel₀` (`ipaRelation_of_x4Current`) at witness `a₀`, and the
algebraic instance's clean opening `o` supplies a second opening of the *same* commitment
`deployedCommitment − multiU•u − multiBlind•w` at witness `o.1` (`ipaRelation_deployed_of_instance`).
Either the two witnesses agree — and `member_constraint_of_relation_and_batch` produces the member
SNARK relation — or they collide on `commit` with distinct witnesses, yielding a nontrivial `(g,u,w)`
relation (`hasNontrivialRelation_of_two_openings`). This ties the deployed batch's witness to the
#56-extracted witness, so the SNARK relation the capstone concludes is about the extracted opening
(or binding breaks). The member-capstone gate data (`hquot`/`hgood`/layout/`hquotCommitted`/`mdec`)
is carried as premises — it is the deployed gate check, produced separately by the F5 machinery. -/
theorem member_relation_or_dlr_of_instance
    {vk : VerifyingKey shape Fp VestaG} (p : AlgebraicWfProof basis vk) (ν : Fin 11 → Fp)
    (cert : AlgebraicDForkCert (F := Fp)
      (augmentedBasis (ursOfAugmentedBasis shape.k basis).g
        (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w) shape.k)
    (hz : ν 10 ≠ 0)
    (hvalid : DeployedForkValid (ursOfAugmentedBasis shape.k basis).g
      (evalVector shape.k (ν 7)) (ursOfAugmentedBasis shape.k basis).u
      (ursOfAugmentedBasis shape.k basis).w (ν 10)
      (commit (ursOfAugmentedBasis shape.k basis)
          (adjustedWitness (p.aMulti ν) p.s
            (multiopenValue vk p.proof.1 (chRecord ν (fun _ => 0))) (ν 9)) +
        (p.multiU ν + ν 9 * p.sU) • (ursOfAugmentedBasis shape.k basis).u +
        (p.multiBlind ν + ν 9 * p.sBlind) • (ursOfAugmentedBasis shape.k basis).w)
      cert.toDForkCert)
    (hshift : (ν 10)⁻¹ * (p.multiU ν + ν 9 * p.sU)
        - ν 9 * innerProduct p.s (evalVector shape.k (ν 7)) = 0)
    (o : (deployedAlgebraicInstanceOfCert p ν cert hz hvalid).Opening)
    {a₀ : Fin (2 ^ shape.k) → Fp}
    (pbatch : OpenedBatchOpenings (ursOfAugmentedBasis shape.k basis) (evalVector shape.k (ν 7))
      (x4BatchCommitments (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
        (chRecord ν (fun _ => 0)))
      (x4BatchEvals vk p.proof.1 (chRecord ν (fun _ => 0))) a₀ (p.multiU ν) (p.multiBlind ν))
    (hξcur : pbatch.batchChallenge pbatch.current
      = (chRecord ν (fun _ => 0) : Challenges shape.k Fp).x4)
    {numAdvice numInstance : ℕ}
    (adviceSet : Fin numAdvice → ℕ)
    (hadviceSet : ∀ j, adviceSet j
      < deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0)))
    (adviceMem : ∀ j : Fin numAdvice,
      Fin (deployedSetQueries vk p.proof.1 (chRecord ν (fun _ => 0)) (adviceSet j)).length)
    (instanceSet : Fin numInstance → ℕ)
    (hinstanceSet : ∀ j, instanceSet j
      < deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0)))
    (instanceMem : ∀ j : Fin numInstance,
      Fin (deployedSetQueries vk p.proof.1 (chRecord ν (fun _ => 0)) (instanceSet j)).length)
    (fixedCols : ℕ → Polynomial Fp) (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp)
    (hpoly : Polynomial Fp) (deg : ℕ) (xpt : Fp)
    (mdec : ∀ i (hi : i < deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0))),
      OpenedMemberDecode (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
        (chRecord ν (fun _ => 0)) pbatch i hi)
    (hquot : quotientCheck
      (combineGates fixedCols
        (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((mdec (adviceSet j) (hadviceSet j)).cols (adviceMem j))))
        (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((mdec (instanceSet j) (hinstanceSet j)).cols (instanceMem j))))
        y gates) hpoly deg xpt)
    (hgood :
      combineGates fixedCols
        (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((mdec (adviceSet j) (hadviceSet j)).cols (adviceMem j))))
        (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((mdec (instanceSet j) (hinstanceSet j)).cols (instanceMem j))))
        y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols
        (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((mdec (adviceSet j) (hadviceSet j)).cols (adviceMem j))))
        (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((mdec (instanceSet j) (hinstanceSet j)).cols (instanceMem j))))
        y gates - hpoly * (X ^ deg - 1)).eval xpt ≠ 0)
    (pp : Fin shape.numProofs)
    (hadviceLayout : ∀ j : Fin numAdvice,
      (deployedSetCommIds vk p.proof.1 (chRecord ν (fun _ => 0)) (adviceSet j)).getD
          (adviceMem j : ℕ) CommitmentId.vanishingH
        = CommitmentId.adviceCol pp (vk.adviceQueryLayout.getD (j : ℕ) (0, 0)).1)
    (hinstanceLayout : ∀ j : Fin numInstance,
      (deployedSetCommIds vk p.proof.1 (chRecord ν (fun _ => 0)) (instanceSet j)).getD
          (instanceMem j : ℕ) CommitmentId.vanishingH
        = CommitmentId.instanceCol pp (vk.instanceQueryLayout.getD (j : ℕ) (0, 0)).1)
    (hquotCommitted : ∃ (hSet : ℕ)
        (hhSet : hSet < deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0)))
        (hMem : Fin (deployedSetQueries vk p.proof.1 (chRecord ν (fun _ => 0)) hSet).length),
      hpoly = coeffsToPoly ((mdec hSet hhSet).cols hMem) ∧
      (deployedSetCommIds vk p.proof.1 (chRecord ν (fun _ => 0)) hSet).getD (hMem : ℕ)
          CommitmentId.randomPoly = CommitmentId.vanishingH)
    {S : Prop}
    (hencodes : ∀ a,
      SnarkRelationWithMemberColumns (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
        (chRecord ν (fun _ => 0))
        (deployedCommitment (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
            (chRecord ν (fun _ => 0))
          - p.multiU ν • (ursOfAugmentedBasis shape.k basis).u
          - p.multiBlind ν • (ursOfAugmentedBasis shape.k basis).w)
        (evalVector shape.k (ν 7)) (multiopenValue vk p.proof.1 (chRecord ν (fun _ => 0)))
        pp adviceSet hadviceSet adviceMem instanceSet hinstanceSet instanceMem
        fixedCols y gates hpoly deg (p.multiU ν) (p.multiBlind ν) a → S) :
    S ∨ HasNontrivialRelation (F := Fp) (ursOfAugmentedBasis shape.k basis).g
      (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w := by
  have hrel₀ := pbatch.ipaRelation_of_x4Current hξcur
  have hrel' := ipaRelation_deployed_of_instance p ν cert hz hvalid hshift o
  by_cases hae : o.1 = a₀
  · exact Or.inl (member_constraint_of_relation_and_batch (ursOfAugmentedBasis shape.k basis) rfl
      vk p.proof.1 (chRecord ν (fun _ => 0)) adviceSet hadviceSet adviceMem instanceSet hinstanceSet
      instanceMem fixedCols y gates hpoly deg xpt hrel₀ pbatch mdec hquot hgood pp hadviceLayout
      hinstanceLayout hquotCommitted hencodes)
  · exact Or.inr (hasNontrivialRelation_of_two_openings (ursOfAugmentedBasis shape.k basis) hae
      (hrel'.1.trans hrel₀.1.symm))

open Polynomial in
open Classical in
set_option maxHeartbeats 1000000 in
/-- **G3 completion: the runToSnark-analogue on the computed path.** Matching the algebraic
instance's `run` (`runToSnark`'s clean-opening/relation dichotomy): on the clean-opening branch, the
witness-tie `member_relation_or_dlr_of_instance` produces the member SNARK relation (or a binding
`HasNontrivialRelation`); on the relation branch, the algebraic extraction's own
`AlgebraicRelationWitness`. Unlike `runToSnark` — whose `hcirc` admits no DL escape and whose
`hencodes` is at the raw `commit … aMulti` shape — this matches `run` directly, so the member
capstone's binding disjunct threads out cleanly and the deployed opened-commitment shape is used
throughout. The bounded probability of the non-clean branch is `snarkFailure_prob_le_of_*` (#56),
attached in the G4 step. -/
noncomputable def member_snark_of_instance
    {vk : VerifyingKey shape Fp VestaG} (p : AlgebraicWfProof basis vk) (ν : Fin 11 → Fp)
    (cert : AlgebraicDForkCert (F := Fp)
      (augmentedBasis (ursOfAugmentedBasis shape.k basis).g
        (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w) shape.k)
    (hz : ν 10 ≠ 0)
    (hvalid : DeployedForkValid (ursOfAugmentedBasis shape.k basis).g
      (evalVector shape.k (ν 7)) (ursOfAugmentedBasis shape.k basis).u
      (ursOfAugmentedBasis shape.k basis).w (ν 10)
      (commit (ursOfAugmentedBasis shape.k basis)
          (adjustedWitness (p.aMulti ν) p.s
            (multiopenValue vk p.proof.1 (chRecord ν (fun _ => 0))) (ν 9)) +
        (p.multiU ν + ν 9 * p.sU) • (ursOfAugmentedBasis shape.k basis).u +
        (p.multiBlind ν + ν 9 * p.sBlind) • (ursOfAugmentedBasis shape.k basis).w)
      cert.toDForkCert)
    (hshift : (ν 10)⁻¹ * (p.multiU ν + ν 9 * p.sU)
        - ν 9 * innerProduct p.s (evalVector shape.k (ν 7)) = 0)
    {a₀ : Fin (2 ^ shape.k) → Fp}
    (pbatch : OpenedBatchOpenings (ursOfAugmentedBasis shape.k basis) (evalVector shape.k (ν 7))
      (x4BatchCommitments (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
        (chRecord ν (fun _ => 0)))
      (x4BatchEvals vk p.proof.1 (chRecord ν (fun _ => 0))) a₀ (p.multiU ν) (p.multiBlind ν))
    (hξcur : pbatch.batchChallenge pbatch.current
      = (chRecord ν (fun _ => 0) : Challenges shape.k Fp).x4)
    {numAdvice numInstance : ℕ}
    (adviceSet : Fin numAdvice → ℕ)
    (hadviceSet : ∀ j, adviceSet j
      < deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0)))
    (adviceMem : ∀ j : Fin numAdvice,
      Fin (deployedSetQueries vk p.proof.1 (chRecord ν (fun _ => 0)) (adviceSet j)).length)
    (instanceSet : Fin numInstance → ℕ)
    (hinstanceSet : ∀ j, instanceSet j
      < deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0)))
    (instanceMem : ∀ j : Fin numInstance,
      Fin (deployedSetQueries vk p.proof.1 (chRecord ν (fun _ => 0)) (instanceSet j)).length)
    (fixedCols : ℕ → Polynomial Fp) (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp)
    (hpoly : Polynomial Fp) (deg : ℕ) (xpt : Fp)
    (mdec : ∀ i (hi : i < deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0))),
      OpenedMemberDecode (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
        (chRecord ν (fun _ => 0)) pbatch i hi)
    (hquot : quotientCheck
      (combineGates fixedCols
        (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((mdec (adviceSet j) (hadviceSet j)).cols (adviceMem j))))
        (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((mdec (instanceSet j) (hinstanceSet j)).cols (instanceMem j))))
        y gates) hpoly deg xpt)
    (hgood :
      combineGates fixedCols
        (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((mdec (adviceSet j) (hadviceSet j)).cols (adviceMem j))))
        (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((mdec (instanceSet j) (hinstanceSet j)).cols (instanceMem j))))
        y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols
        (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((mdec (adviceSet j) (hadviceSet j)).cols (adviceMem j))))
        (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((mdec (instanceSet j) (hinstanceSet j)).cols (instanceMem j))))
        y gates - hpoly * (X ^ deg - 1)).eval xpt ≠ 0)
    (pp : Fin shape.numProofs)
    (hadviceLayout : ∀ j : Fin numAdvice,
      (deployedSetCommIds vk p.proof.1 (chRecord ν (fun _ => 0)) (adviceSet j)).getD
          (adviceMem j : ℕ) CommitmentId.vanishingH
        = CommitmentId.adviceCol pp (vk.adviceQueryLayout.getD (j : ℕ) (0, 0)).1)
    (hinstanceLayout : ∀ j : Fin numInstance,
      (deployedSetCommIds vk p.proof.1 (chRecord ν (fun _ => 0)) (instanceSet j)).getD
          (instanceMem j : ℕ) CommitmentId.vanishingH
        = CommitmentId.instanceCol pp (vk.instanceQueryLayout.getD (j : ℕ) (0, 0)).1)
    (hquotCommitted : ∃ (hSet : ℕ)
        (hhSet : hSet < deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0)))
        (hMem : Fin (deployedSetQueries vk p.proof.1 (chRecord ν (fun _ => 0)) hSet).length),
      hpoly = coeffsToPoly ((mdec hSet hhSet).cols hMem) ∧
      (deployedSetCommIds vk p.proof.1 (chRecord ν (fun _ => 0)) hSet).getD (hMem : ℕ)
          CommitmentId.randomPoly = CommitmentId.vanishingH)
    {S : Prop}
    (hencodes : ∀ a,
      SnarkRelationWithMemberColumns (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
        (chRecord ν (fun _ => 0))
        (deployedCommitment (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
            (chRecord ν (fun _ => 0))
          - p.multiU ν • (ursOfAugmentedBasis shape.k basis).u
          - p.multiBlind ν • (ursOfAugmentedBasis shape.k basis).w)
        (evalVector shape.k (ν 7)) (multiopenValue vk p.proof.1 (chRecord ν (fun _ => 0)))
        pp adviceSet hadviceSet adviceMem instanceSet hinstanceSet instanceMem
        fixedCols y gates hpoly deg (p.multiU ν) (p.multiBlind ν) a → S) :
    (S ∨ HasNontrivialRelation (F := Fp) (ursOfAugmentedBasis shape.k basis).g
        (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w)
      ⊕' AlgebraicRelationWitness (F := Fp) basis :=
  match (deployedAlgebraicInstanceOfCert p ν cert hz hvalid).run with
  | PSum.inl o =>
      PSum.inl (member_relation_or_dlr_of_instance p ν cert hz hvalid hshift o pbatch hξcur
        adviceSet hadviceSet adviceMem instanceSet hinstanceSet instanceMem fixedCols y gates
        hpoly deg xpt mdec hquot hgood pp hadviceLayout hinstanceLayout hquotCommitted hencodes)
  | PSum.inr rel => PSum.inr rel

/-- **The computed member relation yields the `KnowledgeSoundness.SnarkRelation` (G5 bridge).** The
`SnarkRelationWithMemberColumns` the composition produces projects onto the plain `SnarkRelation`
(`Soundness.KnowledgeSoundness`) at `circuitSat := circuitSatViaGates …` on the decoded member
columns: its `opens` field is the IPA opening and its `satisfiesCircuit` field is exactly the gate
check. This is the payload `ExtractableFromAcceptance` (`Soundness.Main`) *assumed* — an `IpaRelation`
together with circuit satisfaction — now delivered on the computed path, so the bridge is retired. -/
theorem snarkRelation_of_memberColumns {G : Type*} [AddCommGroup G] [Module Fp G]
    [DecidableEq G] [Inhabited G] {shp : Shape} {urs : URS G} {hk : shp.k = urs.k}
    {vk : VerifyingKey shp Fp G} {ps : ProofString shp Fp G} {ch : Challenges shp.k Fp}
    {P : G} {b : Fin (2 ^ urs.k) → Fp} {v : Fp} {pp : Fin shp.numProofs}
    {numAdvice numInstance : ℕ} {adviceSet : Fin numAdvice → ℕ}
    {hadviceSet : ∀ j, adviceSet j < deployedX4PairCount vk ps ch}
    {adviceMem : ∀ j : Fin numAdvice, Fin (deployedSetQueries vk ps ch (adviceSet j)).length}
    {instanceSet : Fin numInstance → ℕ}
    {hinstanceSet : ∀ j, instanceSet j < deployedX4PairCount vk ps ch}
    {instanceMem : ∀ j : Fin numInstance,
      Fin (deployedSetQueries vk ps ch (instanceSet j)).length}
    {fixedCols : ℕ → Polynomial Fp} {y : Fp} {ng : ℕ} {gates : Fin ng → Expr Fp}
    {hpoly : Polynomial Fp} {deg : ℕ} {pU pW : Fp} {a : Fin (2 ^ urs.k) → Fp}
    (hmem : SnarkRelationWithMemberColumns urs hk vk ps ch P b v pp adviceSet hadviceSet adviceMem
      instanceSet hinstanceSet instanceMem fixedCols y gates hpoly deg pU pW a) :
    SnarkRelation urs P b v
      (circuitSatViaGates fixedCols
        (fun _ => rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((hmem.memberDecode (adviceSet j) (hadviceSet j)).cols (adviceMem j))))
        (fun _ => rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((hmem.memberDecode (instanceSet j) (hinstanceSet j)).cols (instanceMem j))))
        y gates hpoly deg) a :=
  ⟨hmem.opens, hmem.satisfiesCircuit⟩

open Polynomial in
/-- **#67 G5: deployed soundness on the computed path — `ExtractableFromAcceptance` retired.** The
computed counterpart of `orchard_verifier_sound_vesta_conditional` (`Soundness.Vesta`): it concludes
the same `KnowledgeSoundness.SnarkRelation`-based `S`, but from the algebraic forking instance and the
deployed gate data — with **no `ExtractableFromAcceptance` hypothesis**. On the clean-opening branch
the extracted witness both opens the deployed commitment and satisfies the member gate check
(`member_snark_of_instance` composed with `snarkRelation_of_memberColumns`); on the non-clean branch
the algebraic family returns a computed DL relation (`AlgebraicRelationWitness`). Unlike the legacy
conditional endpoints, `circuitSat` is not a free parameter — it is the concrete gate check on the
decoded member columns, so `hencodes` quantifies over the batch/decode the computed path produces.
This supersedes `orchard_verifier_sound_conditional`/`orchard_verifier_sound_vesta_conditional` and
their assumed bridge `ExtractableFromAcceptance` (`Soundness.Main`). -/
noncomputable def orchard_verifier_sound_vesta_computed
    {vk : VerifyingKey shape Fp VestaG} (p : AlgebraicWfProof basis vk) (ν : Fin 11 → Fp)
    (cert : AlgebraicDForkCert (F := Fp)
      (augmentedBasis (ursOfAugmentedBasis shape.k basis).g
        (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w) shape.k)
    (hz : ν 10 ≠ 0)
    (hvalid : DeployedForkValid (ursOfAugmentedBasis shape.k basis).g
      (evalVector shape.k (ν 7)) (ursOfAugmentedBasis shape.k basis).u
      (ursOfAugmentedBasis shape.k basis).w (ν 10)
      (commit (ursOfAugmentedBasis shape.k basis)
          (adjustedWitness (p.aMulti ν) p.s
            (multiopenValue vk p.proof.1 (chRecord ν (fun _ => 0))) (ν 9)) +
        (p.multiU ν + ν 9 * p.sU) • (ursOfAugmentedBasis shape.k basis).u +
        (p.multiBlind ν + ν 9 * p.sBlind) • (ursOfAugmentedBasis shape.k basis).w)
      cert.toDForkCert)
    (hshift : (ν 10)⁻¹ * (p.multiU ν + ν 9 * p.sU)
        - ν 9 * innerProduct p.s (evalVector shape.k (ν 7)) = 0)
    {a₀ : Fin (2 ^ shape.k) → Fp}
    (pbatch : OpenedBatchOpenings (ursOfAugmentedBasis shape.k basis) (evalVector shape.k (ν 7))
      (x4BatchCommitments (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
        (chRecord ν (fun _ => 0)))
      (x4BatchEvals vk p.proof.1 (chRecord ν (fun _ => 0))) a₀ (p.multiU ν) (p.multiBlind ν))
    (hξcur : pbatch.batchChallenge pbatch.current
      = (chRecord ν (fun _ => 0) : Challenges shape.k Fp).x4)
    {numAdvice numInstance : ℕ}
    (adviceSet : Fin numAdvice → ℕ)
    (hadviceSet : ∀ j, adviceSet j
      < deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0)))
    (adviceMem : ∀ j : Fin numAdvice,
      Fin (deployedSetQueries vk p.proof.1 (chRecord ν (fun _ => 0)) (adviceSet j)).length)
    (instanceSet : Fin numInstance → ℕ)
    (hinstanceSet : ∀ j, instanceSet j
      < deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0)))
    (instanceMem : ∀ j : Fin numInstance,
      Fin (deployedSetQueries vk p.proof.1 (chRecord ν (fun _ => 0)) (instanceSet j)).length)
    (fixedCols : ℕ → Polynomial Fp) (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp)
    (hpoly : Polynomial Fp) (deg : ℕ) (xpt : Fp)
    (mdec : ∀ i (hi : i < deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0))),
      OpenedMemberDecode (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
        (chRecord ν (fun _ => 0)) pbatch i hi)
    (hquot : quotientCheck
      (combineGates fixedCols
        (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((mdec (adviceSet j) (hadviceSet j)).cols (adviceMem j))))
        (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((mdec (instanceSet j) (hinstanceSet j)).cols (instanceMem j))))
        y gates) hpoly deg xpt)
    (hgood :
      combineGates fixedCols
        (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((mdec (adviceSet j) (hadviceSet j)).cols (adviceMem j))))
        (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((mdec (instanceSet j) (hinstanceSet j)).cols (instanceMem j))))
        y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols
        (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((mdec (adviceSet j) (hadviceSet j)).cols (adviceMem j))))
        (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((mdec (instanceSet j) (hinstanceSet j)).cols (instanceMem j))))
        y gates - hpoly * (X ^ deg - 1)).eval xpt ≠ 0)
    (pp : Fin shape.numProofs)
    (hadviceLayout : ∀ j : Fin numAdvice,
      (deployedSetCommIds vk p.proof.1 (chRecord ν (fun _ => 0)) (adviceSet j)).getD
          (adviceMem j : ℕ) CommitmentId.vanishingH
        = CommitmentId.adviceCol pp (vk.adviceQueryLayout.getD (j : ℕ) (0, 0)).1)
    (hinstanceLayout : ∀ j : Fin numInstance,
      (deployedSetCommIds vk p.proof.1 (chRecord ν (fun _ => 0)) (instanceSet j)).getD
          (instanceMem j : ℕ) CommitmentId.vanishingH
        = CommitmentId.instanceCol pp (vk.instanceQueryLayout.getD (j : ℕ) (0, 0)).1)
    (hquotCommitted : ∃ (hSet : ℕ)
        (hhSet : hSet < deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0)))
        (hMem : Fin (deployedSetQueries vk p.proof.1 (chRecord ν (fun _ => 0)) hSet).length),
      hpoly = coeffsToPoly ((mdec hSet hhSet).cols hMem) ∧
      (deployedSetCommIds vk p.proof.1 (chRecord ν (fun _ => 0)) hSet).getD (hMem : ℕ)
          CommitmentId.randomPoly = CommitmentId.vanishingH)
    {S : Prop}
    (hencodes : ∀ (a : Fin (2 ^ shape.k) → Fp)
        (bo : OpenedBatchOpenings (ursOfAugmentedBasis shape.k basis) (evalVector shape.k (ν 7))
          (x4BatchCommitments (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
            (chRecord ν (fun _ => 0)))
          (x4BatchEvals vk p.proof.1 (chRecord ν (fun _ => 0))) a (p.multiU ν) (p.multiBlind ν))
        (md : ∀ i (hi : i < deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0))),
          OpenedMemberDecode (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
            (chRecord ν (fun _ => 0)) bo i hi),
      SnarkRelation (ursOfAugmentedBasis shape.k basis)
        (deployedCommitment (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
            (chRecord ν (fun _ => 0))
          - p.multiU ν • (ursOfAugmentedBasis shape.k basis).u
          - p.multiBlind ν • (ursOfAugmentedBasis shape.k basis).w)
        (evalVector shape.k (ν 7)) (multiopenValue vk p.proof.1 (chRecord ν (fun _ => 0)))
        (circuitSatViaGates fixedCols
          (fun _ => rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
            coeffsToPoly ((md (adviceSet j) (hadviceSet j)).cols (adviceMem j))))
          (fun _ => rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
            coeffsToPoly ((md (instanceSet j) (hinstanceSet j)).cols (instanceMem j))))
          y gates hpoly deg) a → S) :
    (S ∨ HasNontrivialRelation (F := Fp) (ursOfAugmentedBasis shape.k basis).g
        (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w)
      ⊕' AlgebraicRelationWitness (F := Fp) basis :=
  member_snark_of_instance p ν cert hz hvalid hshift pbatch hξcur adviceSet hadviceSet adviceMem
    instanceSet hinstanceSet instanceMem fixedCols y gates hpoly deg xpt mdec hquot hgood pp
    hadviceLayout hinstanceLayout hquotCommitted
    (S := S)
    (fun a hmem => hencodes a hmem.batchOpenings hmem.memberDecode
      (snarkRelation_of_memberColumns hmem))

/-! ## G4 — the quantitative knowledge-error bound (conditional)

The `#56` clean-opening failure `snarkFailureEvent` is already bounded
(`snarkFailure_prob_le_of_generatorRO_textbookDL`). On every clean-opening run the composition
`member_snark_of_instance` (G3) delivers `SnarkRelation ∨ DL` *given the deployed gate data*
(`pbatch`/`mdec`/`hquot`/`hgood`/layout). So the SNARK-extraction failure is contained in the
clean-opening failure and inherits the same bound — **conditional on the gate data discharging on
clean openings** (`hExtract`).

This condition is not removable here: it is the disjoint-halves gap (#67 scope). The deployed gate
data is produced by the #18 deployed forking floors (`openedMemberDecode_of_x1Prob`/`openedX4Rewind`),
a *separate* probabilistic account, and **no failure-probability bound exists over the deployed accept
measures** (`OpenedX1/X2/X3/X4Accept`) — they occur only as measure-lower-bound premises. Removing
`hExtract` requires bounding the multiopen-decode failure and unioning it with the AGM bound:
substantive new content, the genuine remaining core of #67's quantitative clause. -/

namespace ComputedAlgebraicFSFamily

variable {shape : Shape}

/-- The SNARK-extraction-failure event: full deployed acceptance with no successful SNARK extraction
`extracted`. `extracted` is the composition's per-run conclusion (`SnarkRelation ∨ DL`), delivered on
the clean-opening branch by `member_snark_of_instance` given the deployed gate data. -/
def snarkExtractionFailureEvent (family : ComputedAlgebraicFSFamily shape)
    (extracted : (AugmentedIndex (2 ^ shape.k) → VestaG) → family.Coins → Prop) :
    Set ((AugmentedIndex (2 ^ shape.k) → VestaG) × family.Coins) :=
  {q | fsWinsFull (family.adversary q.1) (fullAlgebraicAccept q.1 (family.vk q.1))
      (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) q.2.1 ∧
    ¬ extracted q.1 q.2}

/-- If every clean-opening run yields the extraction, the SNARK-extraction failure is contained in
the clean-opening failure `snarkFailureEvent`. -/
theorem snarkExtractionFailureEvent_subset (family : ComputedAlgebraicFSFamily shape)
    (extracted : (AugmentedIndex (2 ^ shape.k) → VestaG) → family.Coins → Prop)
    (hExtract : ∀ basis coins, family.hasCleanOpening basis coins → extracted basis coins) :
    family.snarkExtractionFailureEvent extracted ⊆ family.snarkFailureEvent := by
  rintro q ⟨hacc, hnex⟩
  exact ⟨hacc, fun hclean => hnex (hExtract q.1 q.2 hclean)⟩

end ComputedAlgebraicFSFamily

open scoped ENNReal in
open ComputedAlgebraicFSFamily in
/-- **#67 G4: conditional knowledge-soundness bound.** The measure of "deployed acceptance but no
SNARK extraction" inherits the `#56` clean-opening bound
`(Q+k)·3/|Fp| + (Q+1)/|Fp| + |basis|·ε`, **conditional on `hExtract`** — that every clean-opening run
delivers the extraction (which `member_snark_of_instance` supplies given the deployed gate data). By
set-containment (`snarkExtractionFailureEvent_subset`) + outer-measure monotonicity, so the concrete
AGM bound transfers verbatim. `hExtract` is the honest disjoint-halves gap: discharging it family-wide
needs a failure-probability bound over the deployed accept measures, which does not exist (the #18
floors are measure-lower-bound premises only). -/
theorem snarkExtraction_prob_le_of_generatorRO_textbookDL {shape : Shape}
    {T : Type*} [DecidableEq T] (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ shape.k) → T) (hquery : Function.Injective query)
    (family : ComputedAlgebraicFSFamily shape) {bound : ℝ≥0∞}
    (hDL : TextbookDLWithCoinsAdvantageLE B family.snarkRelationFinder bound)
    (extracted : (AugmentedIndex (2 ^ shape.k) → VestaG) → family.Coins → Prop)
    (hExtract : ∀ basis coins, family.hasCleanOpening basis coins → extracted basis coins) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          family.snarkExtractionFailureEvent extracted)
      ≤ (family.Q + shape.k) * (3 / Fintype.card Fp) +
        (family.Q + 1 : ℕ) * (1 / Fintype.card Fp) +
        Fintype.card (AugmentedIndex (2 ^ shape.k)) * bound :=
  le_trans
    ((independentProductPMF (orchardGeneratorROSetup query)
        (PMF.uniformOfFintype family.Coins)).toOuterMeasure.mono
      (Set.preimage_mono (family.snarkExtractionFailureEvent_subset extracted hExtract)))
    (snarkFailure_prob_le_of_generatorRO_textbookDL B hB query hquery family hDL)

/-- **Instance provenance (G4 Piece A).** Whenever the computed family's `instanceAttempt` yields an
instance `x`, that `x` is a `deployedAlgebraicInstanceOfCert` of a concrete `AlgebraicWfProof p`,
oracle-scalar vector `ν`, and certificate — the structural inverse of `computedDeployedAlgebraicInstance`
(which returns `some` only on the cert-found, `ν 10 ≠ 0` branch). This exposes the `AlgebraicWfProof`
behind a clean-opening instance, the datum any future unconditional-bound reconciliation needs to hand
the deployed member capstone. It does NOT, on its own, produce the deployed batch `pbatch`/`mdec` — those
require the multiopen `x₄`/`x₁` rewinds (a distinct probabilistic account), which a single proof cannot
furnish (`OpenedBatchOpenings` needs an injective multi-challenge batch). -/
theorem instanceAttempt_provenance
    (family : ComputedAlgebraicFSFamily shape) (coins : family.Coins)
    {x : DeployedAlgebraicForkingInstance (G := VestaG) shape.k basis}
    (h : (family.instanceAttempt basis coins).output = some x) :
    ∃ (p : AlgebraicWfProof basis (family.vk basis)) (ν : Fin 11 → Fp)
      (cert : AlgebraicDForkCert (F := Fp)
        (augmentedBasis (ursOfAugmentedBasis shape.k basis).g
          (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w) shape.k)
      (hz : ν 10 ≠ 0)
      (hvalid : DeployedForkValid (ursOfAugmentedBasis shape.k basis).g
        (evalVector shape.k (ν 7)) (ursOfAugmentedBasis shape.k basis).u
        (ursOfAugmentedBasis shape.k basis).w (ν 10)
        (commit (ursOfAugmentedBasis shape.k basis)
            (adjustedWitness (p.aMulti ν) p.s
              (multiopenValue (family.vk basis) p.proof.1 (chRecord ν (fun _ => 0))) (ν 9)) +
          (p.multiU ν + ν 9 * p.sU) • (ursOfAugmentedBasis shape.k basis).u +
          (p.multiBlind ν + ν 9 * p.sBlind) • (ursOfAugmentedBasis shape.k basis).w)
        cert.toDForkCert),
      x = deployedAlgebraicInstanceOfCert p ν cert hz hvalid := by
  simp only [ComputedAlgebraicFSFamily.instanceAttempt,
    computedDeployedAlgebraicInstanceFromTape, computedDeployedAlgebraicInstance] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact ⟨_, _, _, _, _, (Option.some.inj h).symm⟩
    · exact absurd h (by simp)

open scoped ENNReal in
open Classical in
/-- **The x₁ single-slot floor failure bound (#67 G7 stage 2).** `uniformOfFintype_accept_below_threshold_le`
instantiated at the deployed `x₁` accept event: the measure of the `x₁` compression challenges where the
deployed run accepts yet the `x₁` accept measure sits at or below `t` is `≤ t`. This bounds the failure of
the derived terminal's `hprob1`/`hprob1p` floors, which are single-slot over the fixed honest `(ps, ch)`.
The `hx2`/`hprob3`/`hprob4` floors are ∀-quantified over the run structures `X1/X2/X3Run`, which carry NO
`Fintype` instance, so their failure event is an existential over a non-finite adversarial type — not a
uniform-measure event this bound (or any single-slot count) can reach. -/
theorem openedX1_floor_failure_le (urs : URS VestaG) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp VestaG) (ps : ProofString shape Fp VestaG)
    (ch : Challenges shape.k Fp) (t : ℝ≥0∞) :
    (PMF.uniformOfFintype Fp).toOuterMeasure
        {χv : Fp | OpenedX1Accept urs hk vk ps ch χv ∧
          (PMF.uniformOfFintype Fp).toOuterMeasure
              (Finset.univ.filter (OpenedX1Accept urs hk vk ps ch)) ≤ t}
      ≤ t :=
  uniformOfFintype_accept_below_threshold_le (OpenedX1Accept urs hk vk ps ch) t

end Zcash.Snark
