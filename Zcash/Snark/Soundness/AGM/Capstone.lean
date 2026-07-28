import Zcash.Snark.Soundness.AGM.Peel
import Zcash.Snark.Soundness.AGM.Prover
import Zcash.Snark.Soundness.Forking.Rewind

/-!
# Deployed AGM opening or relation

`Soundness.AGM.Peel` computes a relation from algebraic prover data. This module returns either a
multiopen IPA opening or an explicit relation; no coefficients are chosen from an existential.

## The boundary with the Fiat–Shamir/forking layer

Once the transcript and its representations are supplied, both result branches are computed data.
The Fiat–Shamir/forking layer must provide those inputs and connect its acceptance probability to
this execution. `deployedAlgebraicRelationWitness` returns the relation type used by the DL proof.

The vectors in `hP` use only `g`. Real halo2 commitments are blinded, so the Vesta endpoints first
remove their declared `U` and `W` components. The algebraic prover supplies representations of those
adjusted points.
-/

namespace Zcash.Snark

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- Compute a deployed IPA opening or relation from an algebraic fork certificate.

Erasing the coefficients gives the certificate checked by `DeployedForkValid`. The relation branch
uses the form expected by the programmed-basis DL reduction. -/
def deployedAlgebraicForkingRelation [DecidableEq G] [Inhabited G] (urs : URS G)
    (b : Fin (2 ^ urs.k) → Fp) (v ξ z blind : Fp) (aMulti aDep s : Fin (2 ^ urs.k) → Fp)
    (cert : AlgebraicDForkCert (F := Fp) (augmentedBasis urs.g urs.u urs.w) urs.k)
    (hz : z ≠ 0) (hb0 : b 0 = 1)
    (hP : commit urs aDep = commit urs aMulti - v • urs.g 0 + ξ • commit urs s)
    (hvalid : DeployedForkValid urs.g b urs.u urs.w z
      (commit urs aDep + (z * 0) • urs.u + blind • urs.w) cert.toDForkCert) :
    (Σ' a, IpaRelation urs (commit urs aMulti) b (v - ξ * innerProduct s b) a)
      ⊕' AlgebraicRelationWitness (F := Fp) (augmentedBasis urs.g urs.u urs.w) :=
  match deployed_forking_relation urs b v ξ z blind aMulti aDep s cert.toDForkCert hz hb0 hP hvalid with
  | PSum.inl hopen => PSum.inl hopen
  | PSum.inr hrel =>
      PSum.inr (AugmentedRelationWitness.toAlgebraicRelationWitness hrel)

/-- `deployedAlgebraicForkingRelation` with a declared `U` coefficient `vU`. This shifts the
opened value by `z⁻¹·vU`. -/
def deployedAlgebraicForkingRelation_shifted [DecidableEq G] [Inhabited G] (urs : URS G)
    (b : Fin (2 ^ urs.k) → Fp) (v ξ z vU blind : Fp) (aMulti aDep s : Fin (2 ^ urs.k) → Fp)
    (cert : AlgebraicDForkCert (F := Fp) (augmentedBasis urs.g urs.u urs.w) urs.k)
    (hz : z ≠ 0) (hb0 : b 0 = 1)
    (hP : commit urs aDep = commit urs aMulti - v • urs.g 0 + ξ • commit urs s)
    (hvalid : DeployedForkValid urs.g b urs.u urs.w z
      (commit urs aDep + vU • urs.u + blind • urs.w) cert.toDForkCert) :
    (Σ' a, IpaRelation urs (commit urs aMulti) b (v + z⁻¹ * vU - ξ * innerProduct s b) a)
      ⊕' AlgebraicRelationWitness (F := Fp) (augmentedBasis urs.g urs.u urs.w) :=
  match deployed_forking_relation_shifted urs b v ξ z vU blind aMulti aDep s cert.toDForkCert
      hz hb0 hP hvalid with
  | PSum.inl hopen => PSum.inl hopen
  | PSum.inr hrel =>
      PSum.inr (AugmentedRelationWitness.toAlgebraicRelationWitness hrel)

/-- Run the deployed certificate, then the programmed-basis DL reduction: an IPA opening, the
challenge `C`'s discrete log, or proof that the returned relation's component against the
programming is zero. -/
def deployedAlgebraicForkingProgrammed [DecidableEq G] [Inhabited G] (urs : URS G)
    (B C : G)
    (embedding : ProgrammedBasisEmbedding (F := Fp) B C (augmentedBasis urs.g urs.u urs.w))
    (b : Fin (2 ^ urs.k) → Fp) (v ξ z blind : Fp) (aMulti aDep s : Fin (2 ^ urs.k) → Fp)
    (cert : AlgebraicDForkCert (F := Fp) (augmentedBasis urs.g urs.u urs.w) urs.k)
    (hz : z ≠ 0) (hb0 : b 0 = 1)
    (hP : commit urs aDep = commit urs aMulti - v • urs.g 0 + ξ • commit urs s)
    (hvalid : DeployedForkValid urs.g b urs.u urs.w z
      (commit urs aDep + (z * 0) • urs.u + blind • urs.w) cert.toDForkCert) :
    (Σ' a, IpaRelation urs (commit urs aMulti) b (v - ξ * innerProduct s b) a)
      ⊕' ProgrammedRelationOutcome (F := Fp) B C (augmentedBasis urs.g urs.u urs.w)
          embedding.y :=
  match deployedAlgebraicForkingRelation urs b v ξ z blind aMulti aDep s cert hz hb0 hP hvalid with
  | PSum.inl hopen => PSum.inl hopen
  | PSum.inr hrel => PSum.inr (programmedExtractOrMiss B C embedding hrel)

/-! ## Concrete relation producer for the probability experiment -/

/-- Inputs for the deployed algebraic kernel on one augmented basis. `vU` is the commitment's
declared `U` coefficient; honest proofs have `vU = 0`. -/
structure DeployedAlgebraicForkingInstance (k : ℕ)
    (basis : AugmentedIndex (2 ^ k) → G) where
  b : Fin (2 ^ k) → Fp
  v : Fp
  ξ : Fp
  z : Fp
  vU : Fp
  blind : Fp
  aMulti : Fin (2 ^ k) → Fp
  aDep : Fin (2 ^ k) → Fp
  s : Fin (2 ^ k) → Fp
  cert : AlgebraicDForkCert (F := Fp)
    (augmentedBasis (ursOfAugmentedBasis k basis).g
      (ursOfAugmentedBasis k basis).u (ursOfAugmentedBasis k basis).w) k
  hz : z ≠ 0
  hb0 : b 0 = 1
  hP : commit (ursOfAugmentedBasis k basis) aDep =
    commit (ursOfAugmentedBasis k basis) aMulti - v • (ursOfAugmentedBasis k basis).g 0 +
      ξ • commit (ursOfAugmentedBasis k basis) s
  hvalid : DeployedForkValid (ursOfAugmentedBasis k basis).g b
    (ursOfAugmentedBasis k basis).u (ursOfAugmentedBasis k basis).w z
    (commit (ursOfAugmentedBasis k basis) aDep + vU • (ursOfAugmentedBasis k basis).u +
      blind • (ursOfAugmentedBasis k basis).w) cert.toDForkCert

namespace DeployedAlgebraicForkingInstance

/-- The opening returned by one deployed instance. Its value is shifted by `z⁻¹·vU`; for an
honest instance `vU = 0`. -/
abbrev Opening {k : ℕ} {basis : AugmentedIndex (2 ^ k) → G}
    (x : DeployedAlgebraicForkingInstance (G := G) k basis) : Type _ :=
  Σ' a, IpaRelation (ursOfAugmentedBasis k basis)
    (commit (ursOfAugmentedBasis k basis) x.aMulti) x.b
    (x.v + x.z⁻¹ * x.vU - x.ξ * innerProduct x.s x.b) a

/-- Run one deployed instance and return its opening or relation on the supplied basis. -/
def run [DecidableEq G] {k : ℕ} {basis : AugmentedIndex (2 ^ k) → G}
    (x : DeployedAlgebraicForkingInstance (G := G) k basis) :
    x.Opening ⊕' AlgebraicRelationWitness (F := Fp) basis := by
  letI : Inhabited G := ⟨0⟩
  cases deployedAlgebraicForkingRelation_shifted (ursOfAugmentedBasis k basis) x.b x.v x.ξ x.z
      x.vU x.blind x.aMulti x.aDep x.s x.cert x.hz x.hb0 x.hP x.hvalid with
  | inl hopen => exact PSum.inl hopen
  | inr hrel =>
      rw [augmentedBasis_ursOfAugmentedBasis] at hrel
      exact PSum.inr hrel

/-- Whether running this instance returns the relation branch. -/
def ProducesRelation [DecidableEq G] {k : ℕ} {basis : AugmentedIndex (2 ^ k) → G}
    (x : DeployedAlgebraicForkingInstance (G := G) k basis) : Prop :=
  ∃ r, x.run = PSum.inr r

/-- Preserve a relation or turn a distinct opening into a commitment-collision relation. -/
def relationOfRun [DecidableEq G] {k : ℕ} {basis : AugmentedIndex (2 ^ k) → G}
    (x : DeployedAlgebraicForkingInstance (G := G) k basis)
    (run : x.Opening ⊕' AlgebraicRelationWitness (F := Fp) basis) :
    Option (AlgebraicRelationWitness (F := Fp) basis) :=
  match run with
  | PSum.inr hrel => some hrel
  | PSum.inl hopen =>
      if hne : hopen.1 = x.aMulti then none
      else
        some (augmentedBasis_ursOfAugmentedBasis k basis ▸
          (relationWitnessOfCollision (ursOfAugmentedBasis k basis) hne
            hopen.2.1).augment (ursOfAugmentedBasis k basis).u (ursOfAugmentedBasis k basis).w)

/-- Return the explicit relation from a relation or distinct-opening branch. -/
def runRelation [DecidableEq G] {k : ℕ} {basis : AugmentedIndex (2 ^ k) → G}
    (x : DeployedAlgebraicForkingInstance (G := G) k basis) :
    Option (AlgebraicRelationWitness (F := Fp) basis) :=
  x.relationOfRun x.run

/-- A value mismatch makes every kernel outcome yield a relation. -/
theorem relationOfRun_isSome_of_mismatch [DecidableEq G] {k : ℕ}
    {basis : AugmentedIndex (2 ^ k) → G}
    (x : DeployedAlgebraicForkingInstance (G := G) k basis)
    (run : x.Opening ⊕' AlgebraicRelationWitness (F := Fp) basis)
    (hmm : innerProduct x.aMulti x.b ≠ x.v + x.z⁻¹ * x.vU - x.ξ * innerProduct x.s x.b) :
    (x.relationOfRun run).isSome := by
  cases run with
  | inr hrel => rfl
  | inl hopen =>
      have hne : ¬ hopen.1 = x.aMulti := fun heq => hmm (heq ▸ hopen.2.2)
      simp only [relationOfRun, dif_neg hne, Option.isSome_some]

/-- A binding mismatch makes `runRelation` return an explicit relation. -/
theorem runRelation_isSome_of_mismatch [DecidableEq G] {k : ℕ}
    {basis : AugmentedIndex (2 ^ k) → G}
    (x : DeployedAlgebraicForkingInstance (G := G) k basis)
    (hmm : innerProduct x.aMulti x.b ≠ x.v + x.z⁻¹ * x.vU - x.ξ * innerProduct x.s x.b) :
    x.runRelation.isSome :=
  relationOfRun_isSome_of_mismatch x x.run hmm

end DeployedAlgebraicForkingInstance

/-- Whether the supplied instance for this basis exists and returns a relation. -/
def deployedAlgebraicRelationProduced [DecidableEq G] {k : ℕ}
    (instances : ∀ basis : AugmentedIndex (2 ^ k) → G,
      Option (DeployedAlgebraicForkingInstance (G := G) k basis))
    (basis : AugmentedIndex (2 ^ k) → G) : Prop :=
  ∃ x, instances basis = some x ∧ x.ProducesRelation

/-- Bases on which the supplied instance computes a relation. -/
def deployedAlgebraicRelationEvent [DecidableEq G] {k : ℕ}
    (instances : ∀ basis : AugmentedIndex (2 ^ k) → G,
      Option (DeployedAlgebraicForkingInstance (G := G) k basis)) :
    Set (AugmentedIndex (2 ^ k) → G) :=
  { basis | deployedAlgebraicRelationProduced instances basis }

/-- The relation finder used by the probability proof.

It runs the supplied instance for each basis and returns only its computed relation branch. Missing
instances and valid openings return `none`. -/
def deployedAlgebraicRelationFinder [DecidableEq G] {k : ℕ}
    (instances : ∀ basis : AugmentedIndex (2 ^ k) → G,
      Option (DeployedAlgebraicForkingInstance (G := G) k basis)) :
    (basis : AugmentedIndex (2 ^ k) → G) →
      Option (AlgebraicRelationWitness (F := Fp) basis) :=
  fun basis =>
    match instances basis with
    | none => none
    | some x =>
      match x.run with
      | PSum.inl _ => none
      | PSum.inr hrel => some hrel

/-- The finder succeeds exactly when the supplied instance returns a relation. -/
theorem deployedAlgebraicRelationFinder_isSome_iff [DecidableEq G] {k : ℕ}
    (instances : ∀ basis : AugmentedIndex (2 ^ k) → G,
      Option (DeployedAlgebraicForkingInstance (G := G) k basis))
    (basis : AugmentedIndex (2 ^ k) → G) :
    (deployedAlgebraicRelationFinder instances basis).isSome ↔
      deployedAlgebraicRelationProduced instances basis := by
  unfold deployedAlgebraicRelationProduced deployedAlgebraicRelationFinder
  cases hinst : instances basis with
  | none => simp
  | some x =>
    cases hrun : x.run with
    | inl hopen => simp [DeployedAlgebraicForkingInstance.ProducesRelation, hrun]
    | inr hrel => simp [DeployedAlgebraicForkingInstance.ProducesRelation, hrun]

/-- Compute an IPA opening or explicit relation from an accepting deployed algebraic tree. -/
def deployedAlgebraicRelation [DecidableEq G] [Inhabited G] (urs : URS G)
    (b : Fin (2 ^ urs.k) → Fp) (v ξ z blind : Fp) (aMulti aDep s : Fin (2 ^ urs.k) → Fp)
    (t : DeployedIpaTreeV Fp G urs.k) (hz : z ≠ 0) (hb0 : b 0 = 1)
    (hP : commit urs aDep = commit urs aMulti - v • urs.g 0 + ξ • commit urs s)
    (ht : AlgebraicDeployedAcceptV urs.g b urs.u urs.w z (commit urs aDep) 0 blind t) :
    (Σ' a, IpaRelation urs (commit urs aMulti) b (v - ξ * innerProduct s b) a)
      ⊕' AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w := by
  cases deployedToAcceptVWitness hz urs.g b (commit urs aDep) 0 blind t ht with
  | inl hclean =>
    obtain ⟨a, ha⟩ := ipaRelation_extract urs b (commit urs aDep) 0 (projTree t) hclean
    have h1 := ipaRelation_unshift urs (commit urs aDep + v • urs.g 0) b v a hb0
      (by rw [add_sub_cancel_right]; exact ha)
    have h2 : commit urs aDep + v • urs.g 0 = commit urs aMulti + ξ • commit urs s := by
      rw [hP]; abel
    rw [h2] at h1
    exact PSum.inl ⟨_, ipaRelation_unblind_value urs (commit urs aMulti) b v ξ s _ h1⟩
  | inr hrel => exact PSum.inr hrel

/-- As `deployedAlgebraicRelation`, with the relation converted for the probability proof. -/
def deployedAlgebraicRelationWitness [DecidableEq G] [Inhabited G] (urs : URS G)
    (b : Fin (2 ^ urs.k) → Fp) (v ξ z blind : Fp) (aMulti aDep s : Fin (2 ^ urs.k) → Fp)
    (t : DeployedIpaTreeV Fp G urs.k) (hz : z ≠ 0) (hb0 : b 0 = 1)
    (hP : commit urs aDep = commit urs aMulti - v • urs.g 0 + ξ • commit urs s)
    (ht : AlgebraicDeployedAcceptV urs.g b urs.u urs.w z (commit urs aDep) 0 blind t) :
    (Σ' a, IpaRelation urs (commit urs aMulti) b (v - ξ * innerProduct s b) a)
      ⊕' AlgebraicRelationWitness (F := Fp) (augmentedBasis urs.g urs.u urs.w) :=
  match deployedAlgebraicRelation urs b v ξ z blind aMulti aDep s t hz hb0 hP ht with
  | PSum.inl hopen => PSum.inl hopen
  | PSum.inr r => PSum.inr r.toAlgebraicRelationWitness

end Zcash.Snark
