import Zcash.Snark.Soundness.AGM.OnlineMultiopen
import Zcash.Snark.Soundness.AGM.DeployedMultiopen
import Zcash.Snark.Soundness.AGM.RepresentationDecode
import Zcash.Snark.Soundness.Composition.Bridge

/-!
# Decode deployed `x4` columns from the adversary's AGM coordinate function

Varying only `x4` in the ghost representation function of `AlgebraicWfProof` and applying the
offline decoder recovers represented `x4` columns without an additional accepting execution.
This file proves only the algebraic decode; `CanonicalOnlineMultiopenCoordinates` pins the
construction, while `DeployedRootOnlineTrace` supplies the query-chronology condition used to
derive squeeze invariance.
-/

namespace Zcash.Snark

open Classical

local instance vestaInhabitedCoordinateDecode : Inhabited VestaG := ⟨0⟩

variable {shape : Shape} {basis : AugmentedIndex (2 ^ shape.k) -> VestaG}

attribute [local irreducible] deployedX4PairCount x4BatchCommitments

/-- Change only the deployed `x4` slot (pre-IPA squeeze index 8). -/
def updateX4Answer (nu : Fin 11 -> Fp) (x4 : Fp) : Fin 11 -> Fp :=
  Function.update nu (8 : Fin 11) x4

/-- Local structure extensionality; `Challenges` does not export an `[ext]` theorem. -/
private theorem challenges_ext {k : Nat} {F : Type*} {c1 c2 : Challenges k F}
    (hTheta : c1.theta = c2.theta) (hBeta : c1.beta = c2.beta)
    (hGamma : c1.gamma = c2.gamma) (hY : c1.y = c2.y) (hX : c1.x = c2.x)
    (hX1 : c1.x1 = c2.x1) (hX2 : c1.x2 = c2.x2) (hX3 : c1.x3 = c2.x3)
    (hX4 : c1.x4 = c2.x4) (hXi : c1.xi = c2.xi) (hZ : c1.z = c2.z)
    (hRounds : c1.ipaRound = c2.ipaRound) : c1 = c2 := by
  cases c1
  cases c2
  simp_all

/-- Updating the `x4` answer updates exactly the `x4` field of the challenge record. -/
theorem chRecord_updateX4Answer {k : Nat} (nu : Fin 11 -> Fp) (rounds : Fin k -> Fp)
    (x4 : Fp) :
    chRecord (updateX4Answer nu x4) rounds = {chRecord nu rounds with x4 := x4} := by
  apply challenges_ext <;> simp [chRecord, updateX4Answer, Function.update]

/-- If the replacement is the current answer, `updateX4Answer` is the original vector. -/
theorem updateX4Answer_eq_self {nu : Fin 11 -> Fp} {x4 : Fp} (h : x4 = nu 8) :
    updateX4Answer nu x4 = nu := by
  funext j
  by_cases hj : j = (8 : Fin 11)
  · subst j
    simp [updateX4Answer, h]
  · simp [updateX4Answer, Function.update, hj]

/-- The representations stored in `AlgebraicWfProof`, evaluated offline at distinct `x4` values,
form a representation family for the exact deployed `x4` columns. -/
noncomputable def deployedX4RepresentationFamily
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs -> Nat -> VestaG}
    (p : AlgebraicWfProof basis vk instanceCommitment) (nu : Fin 11 -> Fp)
    (points : Fin (deployedX4PairCount vk instanceCommitment p.proof.1
      (chRecord nu (fun _ => 0)) + 1) -> Fp)
    (hpoints : Function.Injective points)
    (current : Fin (deployedX4PairCount vk instanceCommitment p.proof.1
      (chRecord nu (fun _ => 0)) + 1))
    (hcurrent : points current = nu 8) :
    AlgebraicPowerRepresentationFamily (ursOfAugmentedBasis shape.k basis)
      (x4BatchCommitments (ursOfAugmentedBasis shape.k basis) rfl vk instanceCommitment p.proof.1
        (chRecord nu (fun _ => 0)))
      (p.aMulti nu) (p.multiU nu) (p.multiBlind nu) (nu 8) := by
  let urs := ursOfAugmentedBasis shape.k basis
  let ch : Challenges shape.k Fp := chRecord nu (fun _ : Fin shape.k => 0)
  refine
    { points := points
      pointsInjective := hpoints
      represented := fun r => p.aMulti (updateX4Answer nu (points r))
      representedU := fun r => p.multiU (updateX4Answer nu (points r))
      representedW := fun r => p.multiBlind (updateX4Answer nu (points r))
      current := current
      currentPoint := hcurrent
      currentRepresented := ?_
      currentU := ?_
      currentW := ?_
      commitment := ?_ }
  · rw [updateX4Answer_eq_self hcurrent]
  · rw [updateX4Answer_eq_self hcurrent]
  · rw [updateX4Answer_eq_self hcurrent]
  · intro r
    let nuR := updateX4Answer nu (points r)
    calc
      commit urs (p.aMulti nuR) + p.multiU nuR • urs.u + p.multiBlind nuR • urs.w =
          multiopenCommitment urs.g urs.w urs.u vk instanceCommitment p.proof.1
            (chRecord nuR (fun _ => 0)) := p.multiopen_repr nuR
      _ = deployedCommitment urs rfl vk instanceCommitment p.proof.1
          (chRecord nuR (fun _ => 0)) :=
        (deployedCommitment_eq_multiopen vk instanceCommitment p.proof.1
          (chRecord nuR (fun _ => 0))).symm
      _ = deployedCommitment urs rfl vk instanceCommitment p.proof.1
          {ch with x4 := points r} := by
        rw [chRecord_updateX4Answer]
      _ = ∑ i : Fin (deployedX4PairCount vk instanceCommitment p.proof.1 ch + 1),
          points r ^ (i : Nat) •
            x4BatchCommitments urs rfl vk instanceCommitment p.proof.1 ch i :=
        deployedCommitment_x4_batch urs rfl vk instanceCommitment p.proof.1 ch (points r)

/-- Decode the exact deployed `x4` algebraic power batch directly from the adversary's AGM
representation function. -/
noncomputable def deployedX4BatchOfRepresentations
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs -> Nat -> VestaG}
    (p : AlgebraicWfProof basis vk instanceCommitment) (nu : Fin 11 -> Fp)
    (points : Fin (deployedX4PairCount vk instanceCommitment p.proof.1
      (chRecord nu (fun _ => 0)) + 1) -> Fp)
    (hpoints : Function.Injective points)
    (current : Fin (deployedX4PairCount vk instanceCommitment p.proof.1
      (chRecord nu (fun _ => 0)) + 1))
    (hcurrent : points current = nu 8) :
    AlgebraicPowerBatch (ursOfAugmentedBasis shape.k basis)
      (x4BatchCommitments (ursOfAugmentedBasis shape.k basis) rfl vk instanceCommitment p.proof.1
        (chRecord nu (fun _ => 0)))
      (p.aMulti nu) (p.multiU nu) (p.multiBlind nu) (nu 8) :=
  (deployedX4RepresentationFamily p nu points hpoints current hcurrent).decode

/-- Feed the decoded representation columns and the recursive IPA opening directly into the
rewind-free `x4` commitment/value connector.  Compared with
`deployedX4AlgebraicBatchAndValueOrRelation`, this discharges both the represented-column premise
and the aggregate commitment equation from `AlgebraicWfProof` itself. -/
noncomputable def deployedX4BatchAndValueOfRepresentationsOrRelation
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs -> Nat -> VestaG}
    (p : AlgebraicWfProof basis vk instanceCommitment) (nu : Fin 11 -> Fp)
    (points : Fin (deployedX4PairCount vk instanceCommitment p.proof.1
      (chRecord nu (fun _ => 0)) + 1) -> Fp)
    (hpoints : Function.Injective points)
    (current : Fin (deployedX4PairCount vk instanceCommitment p.proof.1
      (chRecord nu (fun _ => 0)) + 1))
    (hcurrent : points current = nu 8)
    (openingWitness : Fin (2 ^ shape.k) -> Fp)
    (hopeningCommit : commit (ursOfAugmentedBasis shape.k basis) openingWitness =
      commit (ursOfAugmentedBasis shape.k basis) (p.aMulti nu))
    (hz : nu 10 ≠ 0)
    (hshifted : commitGen (evalVector shape.k (nu 7)) openingWitness =
      multiopenValue vk instanceCommitment p.proof.1 (chRecord nu (fun _ => 0)) +
        (nu 10)⁻¹ * (p.multiU nu + nu 9 * p.sU) -
          nu 9 * commitGen (evalVector shape.k (nu 7)) p.s)
    (hgoodXi : nu 9 ∉ szBadSet
      (ipaShiftXiPolynomial
        (commitGen (evalVector shape.k (nu 7)) (p.aMulti nu) -
          multiopenValue vk instanceCommitment p.proof.1 (chRecord nu (fun _ => 0)))
        (commitGen (evalVector shape.k (nu 7)) p.s)))
    (hgoodZ : nu 10 ∉ szBadSet
      (ipaShiftZPolynomial
        (commitGen (evalVector shape.k (nu 7)) (p.aMulti nu) -
          multiopenValue vk instanceCommitment p.proof.1 (chRecord nu (fun _ => 0)))
        (p.multiU nu) p.sU (commitGen (evalVector shape.k (nu 7)) p.s) (nu 9))) :
    (Σ' _batch : AlgebraicPowerBatch (ursOfAugmentedBasis shape.k basis)
        (x4BatchCommitments (ursOfAugmentedBasis shape.k basis) rfl vk instanceCommitment p.proof.1
          (chRecord nu (fun _ => 0)))
        (p.aMulti nu) (p.multiU nu) (p.multiBlind nu) (nu 8),
      commitGen (evalVector shape.k (nu 7)) (p.aMulti nu) =
        multiopenValue vk instanceCommitment p.proof.1 (chRecord nu (fun _ => 0))) ⊕'
      AugmentedRelationWitness (F := Fp)
        (ursOfAugmentedBasis shape.k basis).g
        (ursOfAugmentedBasis shape.k basis).u
        (ursOfAugmentedBasis shape.k basis).w := by
  let urs := ursOfAugmentedBasis shape.k basis
  let ch : Challenges shape.k Fp := chRecord nu (fun _ : Fin shape.k => 0)
  let batch := deployedX4BatchOfRepresentations p nu points hpoints current hcurrent
  let cols : AlgebraicColumnRepresentations urs
      (x4BatchCommitments urs rfl vk instanceCommitment p.proof.1 ch) :=
    { coeffs := batch.coeffs
      uComp := batch.uComp
      wComp := batch.wComp
      commitment := batch.commitment }
  have haggregate : commit urs (p.aMulti nu) + p.multiU nu • urs.u +
      p.multiBlind nu • urs.w =
        deployedCommitment urs rfl vk instanceCommitment p.proof.1 ch := by
    rw [deployedCommitment_eq_multiopen]
    exact p.multiopen_repr nu
  exact deployedX4AlgebraicBatchAndValueOrRelation urs rfl vk instanceCommitment p.proof.1 ch cols
    (p.aMulti nu) (p.multiU nu) (p.multiBlind nu) haggregate openingWitness p.s p.sU
    (evalVector shape.k (nu 7)) hopeningCommit hz hshifted hgoodXi hgoodZ

end Zcash.Snark
