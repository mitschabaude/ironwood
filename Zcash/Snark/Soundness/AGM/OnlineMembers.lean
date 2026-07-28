import Zcash.Snark.Soundness.AGM.DeployedCoordinateDecode
import Zcash.Snark.Soundness.AGM.DeployedX1

/-!
# Prefix-covered deployed member representations

The within-set `x1` batch consists of actual query commitments.  Each such commitment must resolve
to either a prover-emitted algebraic point fixed before `x1`, or a verifier-fixed represented
point.  This file states that concrete coverage predicate and turns it into the exact
`AlgebraicColumnRepresentations` consumed by `deployedX1AlgebraicBatchOrRelation`.
-/

namespace Zcash.Snark

open Classical

local instance vestaInhabitedOnlineMembers : Inhabited VestaG := ⟨0⟩

variable {shape : Shape} {basis : AugmentedIndex (2 ^ shape.k) -> VestaG}

attribute [local irreducible] deployedSetQueries deployedX4PairCount
  deployedSetMemberCommitments

/-- A commitment reference is covered by online representations: a plain point is present
directly, while an MSM has representations for every appended point it combines. -/
def CommitmentRefCovered
    (source : List (AlgebraicPoint (F := Fp) basis)) :
    CommitmentRef shape.k Fp VestaG -> Prop
  | .point P => ∃ ap ∈ source, ap.point = P
  | .msm m => ∀ pr ∈ m.other, ∃ ap ∈ source, ap.point = pr.2

/-- Every query commitment routed into a deployed point set is structurally covered by the online
multiopen source.  This includes MSM-valued references such as the folded vanishing-`h`
commitment; their evaluated group point need not itself appear as a source point. -/
def DeployedMembersCovered
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (aps : AlgebraicProofString shape basis)
    (fixed : List (AlgebraicPoint (F := Fp) basis)) : Prop :=
  forall nu : Fin 11 -> Fp,
    forall i : Nat, i < deployedX4PairCount vk instanceCommitment aps.erase
        (chRecord nu (fun _ => 0)) ->
      forall m : Fin (deployedSetQueries vk instanceCommitment aps.erase
        (chRecord nu (fun _ => 0)) i).length,
        CommitmentRefCovered (aps.preX1AssemblySource fixed)
          ((deployedSetQueries vk instanceCommitment aps.erase
            (chRecord nu (fun _ => 0)) i).getD (m : Nat) (.point 0, [])).1

/-- AGM coordinates for the group value of one structurally covered commitment reference. -/
structure CoveredCommitmentRepresentation
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (c : CommitmentRef shape.k Fp VestaG) where
  coeffs : Fin (2 ^ shape.k) -> Fp
  uComp : Fp
  wComp : Fp
  commitment :
    commit (ursOfAugmentedBasis shape.k basis) coeffs +
        uComp • (ursOfAugmentedBasis shape.k basis).u +
        wComp • (ursOfAugmentedBasis shape.k basis).w =
      c.eval (ursOfAugmentedBasis shape.k basis)

/-- Deterministic coordinates of the first online representation of a point, with zero as an
unreachable default for uncovered points.  `preX1AssemblySource` orders prover and fixed
pre-`x` representations before `qPrime`, so these coordinates are fixed before the `x` squeeze. -/
def onlinePointCoordinates (source : List (AlgebraicPoint (F := Fp) basis)) (P : VestaG) :
    (Fin (2 ^ shape.k) -> Fp) × Fp × Fp :=
  match source.find? (fun ap => ap.point = P) with
  | some ap => (ap.gPart, ap.coeffs AugmentedIndex.u, ap.coeffs AugmentedIndex.w)
  | none => (0, 0, 0)

/-- Polynomial carried by the deterministic online representation of a point. -/
noncomputable def onlinePointPolynomial
    (source : List (AlgebraicPoint (F := Fp) basis)) (P : VestaG) : Polynomial Fp :=
  coeffsToPoly (onlinePointCoordinates source P).1

/-- Resolve a covered point by deterministic list lookup, or combine the representations carried
by an MSM-valued commitment reference. -/
def coveredCommitmentRepresentation
    (source : List (AlgebraicPoint (F := Fp) basis))
    (c : CommitmentRef shape.k Fp VestaG)
    (hcovered : CommitmentRefCovered source c) :
    CoveredCommitmentRepresentation basis c := by
  cases c with
  | point P =>
      have H : (source.find? (fun ap => ap.point = P)).isSome := by
        rw [List.find?_isSome]
        obtain ⟨ap, hapSource, hapPoint⟩ := hcovered
        exact ⟨ap, hapSource, by simp [hapPoint]⟩
      let ap := (source.find? (fun candidate => candidate.point = P)).get H
      have hapPoint : ap.point = P := by
        have hsome := List.find?_some (Option.some_get H).symm
        simpa [ap] using hsome
      refine
        { coeffs := ap.gPart
          uComp := ap.coeffs AugmentedIndex.u
          wComp := ap.coeffs AugmentedIndex.w
          commitment := ?_ }
      simpa only [CommitmentRef.eval] using
        (AlgebraicPoint.point_eq_components ap).symm.trans hapPoint
  | msm m =>
      let represented := RepresentedMsm.ofCoveredList m source hcovered
      refine
        { coeffs := m.gScalars + repsGPart represented.reps
          uComp := m.uScalar + repsU represented.reps
          wComp := m.wScalar + repsW represented.reps
          commitment := ?_ }
      simpa only [CommitmentRef.eval] using
        (Msm.eval_repr m represented.reps represented.covers).symm

/-- Point coverage makes `coveredCommitmentRepresentation` use the deterministic online
coordinates above. -/
theorem coveredCommitmentRepresentation_point_coordinates
    (source : List (AlgebraicPoint (F := Fp) basis)) (P : VestaG)
    (hcovered : CommitmentRefCovered source (.point P)) :
    let represented := coveredCommitmentRepresentation source (.point P) hcovered
    (represented.coeffs, represented.uComp, represented.wComp) =
      onlinePointCoordinates source P := by
  have H : (source.find? (fun ap => ap.point = P)).isSome := by
    rw [List.find?_isSome]
    obtain ⟨ap, hapSource, hapPoint⟩ := hcovered
    exact ⟨ap, hapSource, by simp [hapPoint]⟩
  obtain ⟨ap, hap⟩ := Option.isSome_iff_exists.mp H
  simp only [coveredCommitmentRepresentation, onlinePointCoordinates, hap]
  rfl

/-- The deterministic coordinates open every covered point. -/
theorem onlinePointCoordinates_commitment
    (source : List (AlgebraicPoint (F := Fp) basis)) (P : VestaG)
    (hcovered : CommitmentRefCovered source (.point P)) :
    commit (ursOfAugmentedBasis shape.k basis) (onlinePointCoordinates source P).1 +
        (onlinePointCoordinates source P).2.1 • (ursOfAugmentedBasis shape.k basis).u +
        (onlinePointCoordinates source P).2.2 • (ursOfAugmentedBasis shape.k basis).w = P := by
  let represented := coveredCommitmentRepresentation source (.point P) hcovered
  have hcoords := coveredCommitmentRepresentation_point_coordinates source P hcovered
  have hopen := represented.commitment
  simp only [CommitmentRef.eval] at hopen
  rw [← hcoords]
  exact hopen

/-- Transport the deterministic point coordinates across equality of commitment references. -/
theorem coveredCommitmentRepresentation_coeffs_of_eq_point
    (source : List (AlgebraicPoint (F := Fp) basis))
    (c : CommitmentRef shape.k Fp VestaG) (hcovered : CommitmentRefCovered source c)
    (P : VestaG) (hP : c = .point P) :
    (coveredCommitmentRepresentation source c hcovered).coeffs =
      (onlinePointCoordinates source P).1 := by
  subst c
  have hcoords := coveredCommitmentRepresentation_point_coordinates source P hcovered
  simpa only using congrArg (fun r => r.1) hcoords

/-- Resolve each covered deployed member commitment to the augmented AGM coordinates carried by
its source point. -/
def deployedMemberRepresentationsOfCovered
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs → Nat → VestaG}
    (p : AlgebraicWfProof basis vk instanceCommitment)
    (fixed : List (AlgebraicPoint (F := Fp) basis))
    (hcovered : DeployedMembersCovered vk instanceCommitment p.algebraicProof fixed)
    (nu : Fin 11 -> Fp) (i : Nat)
    (hi : i < deployedX4PairCount vk instanceCommitment p.proof.1
      (chRecord nu (fun _ => 0))) :
    AlgebraicColumnRepresentations (ursOfAugmentedBasis shape.k basis)
      (deployedSetMemberCommitments (ursOfAugmentedBasis shape.k basis) rfl
        vk instanceCommitment p.proof.1 (chRecord nu (fun _ => 0)) i) := by
  let memberRef : Fin (deployedSetQueries vk instanceCommitment p.proof.1
      (chRecord nu (fun _ => 0)) i).length -> CommitmentRef shape.k Fp VestaG :=
    fun m => ((deployedSetQueries vk instanceCommitment p.proof.1
      (chRecord nu (fun _ => 0)) i).getD (m : Nat) (.point 0, [])).1
  let represented : forall m, CoveredCommitmentRepresentation basis (memberRef m) :=
    fun m => coveredCommitmentRepresentation
      (p.algebraicProof.preX1AssemblySource fixed) (memberRef m)
      (hcovered nu i hi m)
  refine
    { coeffs := fun m => (represented m).coeffs
      uComp := fun m => (represented m).uComp
      wComp := fun m => (represented m).wComp
      commitment := ?_ }
  intro m
  simpa only [memberRef, deployedSetMemberCommitments_apply] using
    (represented m).commitment

/-- At a plain commitment reference, the deployed member coordinates are the deterministic online
point coordinates. -/
theorem deployedMemberRepresentationsOfCovered_coeffs_point
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs → Nat → VestaG}
    (p : AlgebraicWfProof basis vk instanceCommitment)
    (fixed : List (AlgebraicPoint (F := Fp) basis))
    (hcovered : DeployedMembersCovered vk instanceCommitment p.algebraicProof fixed)
    (nu : Fin 11 -> Fp) (i : Nat)
    (hi : i < deployedX4PairCount vk instanceCommitment p.proof.1
      (chRecord nu (fun _ => 0)))
    (m : Fin (deployedSetQueries vk instanceCommitment p.proof.1
      (chRecord nu (fun _ => 0)) i).length) (P : VestaG)
    (hP : ((deployedSetQueries vk instanceCommitment p.proof.1
      (chRecord nu (fun _ => 0)) i).getD (m : Nat) (.point 0, [])).1 = .point P) :
    (deployedMemberRepresentationsOfCovered p fixed hcovered nu i hi).coeffs m =
      (onlinePointCoordinates (p.algebraicProof.preX1AssemblySource fixed) P).1 := by
  let source := p.algebraicProof.preX1AssemblySource fixed
  let memberRef : Fin (deployedSetQueries vk instanceCommitment p.proof.1
      (chRecord nu (fun _ => 0)) i).length -> CommitmentRef shape.k Fp VestaG :=
    fun j => ((deployedSetQueries vk instanceCommitment p.proof.1
      (chRecord nu (fun _ => 0)) i).getD (j : Nat) (.point 0, [])).1
  change (coveredCommitmentRepresentation source (memberRef m)
      (hcovered nu i hi m)).coeffs = _
  have href : memberRef m = .point P := hP
  exact coveredCommitmentRepresentation_coeffs_of_eq_point source (memberRef m)
    (hcovered nu i hi m) P href

/-- A routed member uses exactly the deterministic covered representation of its commitment
reference, including the two augmented coordinates.  Coverage proofs occur only in erased fields,
so they cannot alter these components. -/
theorem deployedMemberRepresentationsOfCovered_components
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs → Nat → VestaG}
    (p : AlgebraicWfProof basis vk instanceCommitment)
    (fixed : List (AlgebraicPoint (F := Fp) basis))
    (hcovered : DeployedMembersCovered vk instanceCommitment p.algebraicProof fixed)
    (nu : Fin 11 -> Fp) (i : Nat)
    (hi : i < deployedX4PairCount vk instanceCommitment p.proof.1
      (chRecord nu (fun _ => 0)))
    (m : Fin (deployedSetQueries vk instanceCommitment p.proof.1
      (chRecord nu (fun _ => 0)) i).length)
    (c : CommitmentRef shape.k Fp VestaG)
    (hc : ((deployedSetQueries vk instanceCommitment p.proof.1
      (chRecord nu (fun _ => 0)) i).getD (m : Nat) (.point 0, [])).1 = c)
    (cCovered : CommitmentRefCovered
      (p.algebraicProof.preX1AssemblySource fixed) c) :
    let member := deployedMemberRepresentationsOfCovered p fixed hcovered nu i hi
    let represented := coveredCommitmentRepresentation
      (p.algebraicProof.preX1AssemblySource fixed) c cCovered
    member.coeffs m = represented.coeffs ∧ member.uComp m = represented.uComp ∧
      member.wComp m = represented.wComp := by
  subst c
  change _ = (coveredCommitmentRepresentation _ _ cCovered).coeffs ∧
    _ = (coveredCommitmentRepresentation _ _ cCovered).uComp ∧
    _ = (coveredCommitmentRepresentation _ _ cCovered).wComp
  have hproof : hcovered nu i hi m = cCovered := Subsingleton.elim _ _
  cases hproof
  exact ⟨rfl, rfl, rfl⟩

/-- The exact deployed within-set `x1` batch, obtained from online-covered member coordinates.
Any mismatch with the already decoded `x4` aggregate is returned as an explicit augmented-basis
relation. -/
noncomputable def deployedX1BatchOfCoveredOrRelation
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs → Nat → VestaG}
    (p : AlgebraicWfProof basis vk instanceCommitment)
    (fixed : List (AlgebraicPoint (F := Fp) basis))
    (hcovered : DeployedMembersCovered vk instanceCommitment p.algebraicProof fixed)
    (nu : Fin 11 -> Fp)
    (x4Batch : AlgebraicPowerBatch (ursOfAugmentedBasis shape.k basis)
      (x4BatchCommitments (ursOfAugmentedBasis shape.k basis) rfl vk instanceCommitment p.proof.1
        (chRecord nu (fun _ => 0)))
      (p.aMulti nu) (p.multiU nu) (p.multiBlind nu) (nu 8))
    (i : Nat) (hi : i < deployedX4PairCount vk instanceCommitment p.proof.1
      (chRecord nu (fun _ => 0))) :
    AlgebraicPowerBatch (ursOfAugmentedBasis shape.k basis)
        (deployedSetMemberCommitments (ursOfAugmentedBasis shape.k basis) rfl
          vk instanceCommitment p.proof.1 (chRecord nu (fun _ => 0)) i)
        (x4Batch.coeffs ⟨deployedX4PairCount vk instanceCommitment p.proof.1
          (chRecord nu (fun _ => 0)) - 1 - i, by omega⟩)
        (x4Batch.uComp ⟨deployedX4PairCount vk instanceCommitment p.proof.1
          (chRecord nu (fun _ => 0)) - 1 - i, by omega⟩)
        (x4Batch.wComp ⟨deployedX4PairCount vk instanceCommitment p.proof.1
          (chRecord nu (fun _ => 0)) - 1 - i, by omega⟩)
        (nu 5) ⊕'
      AugmentedRelationWitness (F := Fp)
        (ursOfAugmentedBasis shape.k basis).g
        (ursOfAugmentedBasis shape.k basis).u
        (ursOfAugmentedBasis shape.k basis).w :=
  deployedX1AlgebraicBatchOrRelation (ursOfAugmentedBasis shape.k basis) rfl
    vk instanceCommitment p.proof.1 (chRecord nu (fun _ => 0)) x4Batch i hi
    (deployedMemberRepresentationsOfCovered p fixed hcovered nu i hi)

/-- Provenance-preserving covered-member unbatch used by the deployed root capstone. -/
def deployedX1BatchOfCoveredWithSourceOrRelation
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs → Nat → VestaG}
    (p : AlgebraicWfProof basis vk instanceCommitment)
    (fixed : List (AlgebraicPoint (F := Fp) basis))
    (hcovered : DeployedMembersCovered vk instanceCommitment p.algebraicProof fixed)
    (nu : Fin 11 -> Fp)
    (x4Batch : AlgebraicPowerBatch (ursOfAugmentedBasis shape.k basis)
      (x4BatchCommitments (ursOfAugmentedBasis shape.k basis) rfl vk instanceCommitment p.proof.1
        (chRecord nu (fun _ => 0)))
      (p.aMulti nu) (p.multiU nu) (p.multiBlind nu) (nu 8))
    (i : Nat) (hi : i < deployedX4PairCount vk instanceCommitment p.proof.1
      (chRecord nu (fun _ => 0))) :
    AlgebraicPowerBatchWithSource (ursOfAugmentedBasis shape.k basis)
        (deployedMemberRepresentationsOfCovered p fixed hcovered nu i hi)
        (x4Batch.coeffs ⟨deployedX4PairCount vk instanceCommitment p.proof.1
          (chRecord nu (fun _ => 0)) - 1 - i, by omega⟩)
        (x4Batch.uComp ⟨deployedX4PairCount vk instanceCommitment p.proof.1
          (chRecord nu (fun _ => 0)) - 1 - i, by omega⟩)
        (x4Batch.wComp ⟨deployedX4PairCount vk instanceCommitment p.proof.1
          (chRecord nu (fun _ => 0)) - 1 - i, by omega⟩)
        (nu 5) ⊕'
      AugmentedRelationWitness (F := Fp)
        (ursOfAugmentedBasis shape.k basis).g
        (ursOfAugmentedBasis shape.k basis).u
        (ursOfAugmentedBasis shape.k basis).w :=
  deployedX1AlgebraicBatchWithSourceOrRelation (ursOfAugmentedBasis shape.k basis) rfl
    vk instanceCommitment p.proof.1 (chRecord nu (fun _ => 0)) x4Batch i hi
    (deployedMemberRepresentationsOfCovered p fixed hcovered nu i hi)

/-! ## Smart construction from represented online proof data -/

/-- The data an online algebraic prover must return before canonical multiopen coordinates are
assembled.  The aggregate representation itself is deliberately absent: `toAlgebraicWfProof`
computes it from the represented commitments and the verifier's MSM. -/
structure OnlineMemberProofData
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs -> Nat -> VestaG}
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (fixed : List (AlgebraicPoint (F := Fp) basis)) where
  algebraicProof : AlgebraicProofString shape basis
  wellFormed : PsWellFormed algebraicProof.erase
  assemblyCovered : MultiopenAssemblyCovered vk instanceCommitment algebraicProof fixed
  membersCovered : DeployedMembersCovered vk instanceCommitment algebraicProof fixed

/-- Assemble the only accepted aggregate coordinates from online represented proof data. -/
noncomputable def OnlineMemberProofData.toAlgebraicWfProof
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs -> Nat -> VestaG}
    {basis : AugmentedIndex (2 ^ shape.k) -> VestaG}
    {fixed : List (AlgebraicPoint (F := Fp) basis)}
    (data : OnlineMemberProofData (vk := vk) (instanceCommitment := instanceCommitment)
      basis fixed) :
    AlgebraicWfProof basis vk instanceCommitment :=
  AlgebraicWfProof.ofOnlineMultiopenRepresented data.algebraicProof data.wellFormed
    fixed data.assemblyCovered

/-- Add the exact deployed-member coverage evidence to the online multiopen family.  Keeping this
as a second refinement avoids changing the existing computed-family API while the tighter path is
developed. -/
structure ComputedOnlineMemberFSFamily (shape : Shape)
    extends ComputedOnlineMultiopenFSFamily shape where
  membersCovered : forall basis O,
    DeployedMembersCovered (vk basis) (instanceCommitment basis)
      ((adversary basis).run O).algebraicProof
      (fixedRepresentations basis)

namespace ComputedOnlineMemberFSFamily

/-- Forget only member-coverage evidence. -/
abbrev toOnlineFamily (family : ComputedOnlineMemberFSFamily shape) :
    ComputedOnlineMultiopenFSFamily shape := family.toComputedOnlineMultiopenFSFamily

/-- Forget all tighter multiopen evidence. -/
abbrev toFamily (family : ComputedOnlineMemberFSFamily shape) :
    ComputedAlgebraicFSFamily shape := family.toOnlineFamily.toFamily

/-- Build the refined family from an adversary that returns represented proof data.  This is the
concrete adapter for the online AGM interface: `aMulti`, `multiU`, and `multiBlind` are generated by
`ofOnlineMultiopenRepresented`, so the canonical-coordinate and member-coverage fields are derived
rather than separately postulated. -/
noncomputable def ofProofData
    (init : List (TranscriptElt Fp VestaG))
    (vk : (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) ->
      VerifyingKey shape Fp VestaG)
    (instanceCommitment : (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) ->
      Fin shape.numProofs -> Nat -> VestaG)
    (fixed : (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) ->
      List (AlgebraicPoint (F := Fp) basis))
    (adversary : (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) ->
      OracleComp
        (BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k)) Fp
        (OnlineMemberProofData (vk := vk basis)
          (instanceCommitment := instanceCommitment basis) basis (fixed basis)))
    (Q : Nat) (queryBound : forall basis, (adversary basis).QueryBound Q) :
    ComputedOnlineMemberFSFamily shape where
  init := init
  vk := vk
  instanceCommitment := instanceCommitment
  adversary := fun basis => (adversary basis).bind fun data =>
    .pure data.toAlgebraicWfProof
  Q := Q
  queryBound := fun basis => OracleComp.queryBound_bind (queryBound basis)
    (fun _ => .pure _ 0) |>.mono (by omega)
  fixedRepresentations := fixed
  canonical := by
    intro basis O
    simp only [OracleComp.run_bind, OracleComp.run_pure]
    exact AlgebraicWfProof.ofOnlineMultiopenRepresented_canonical
      ((adversary basis).run O).algebraicProof
      ((adversary basis).run O).wellFormed (fixed basis)
      ((adversary basis).run O).assemblyCovered
  membersCovered := by
    intro basis O
    simpa only [OracleComp.run_bind, OracleComp.run_pure,
      OnlineMemberProofData.toAlgebraicWfProof,
      AlgebraicWfProof.ofOnlineMultiopenRepresented] using
      ((adversary basis).run O).membersCovered

end ComputedOnlineMemberFSFamily

end Zcash.Snark
