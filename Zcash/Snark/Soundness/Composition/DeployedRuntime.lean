import Zcash.Snark.Soundness.Composition.DeployedAcceptance
import Zcash.Snark.Soundness.Forking.WithReads

/-!
# Runtime helpers for deployed algebraic extraction

This module contains only the challenge-read wrapper and deployed-acceptance bookkeeping shared by
the rewind-free root containment.  In particular, it does not define or import the historical
four-level accepting-multiopen containment.
-/

namespace Zcash.Snark

open Classical
open ComputedAlgebraicFSFamily

local instance vestaInhabitedDeployedRuntime : Inhabited VestaG := ⟨0⟩

variable {shape : Shape}

/-- A fiber bound for an arbitrary independent product. -/
theorem independentProductPMF_fiber_bound {A B : Type*} (p : PMF A) (q : PMF B)
    (S : A → Set B) {beta : ENNReal} (hS : ∀ a, q.toOuterMeasure (S a) ≤ beta) :
    (independentProductPMF p q).toOuterMeasure {x : A × B | x.2 ∈ S x.1} ≤ beta := by
  rw [independentProductPMF, PMF.toOuterMeasure_bind_apply]
  calc ∑' a, p a * (q.map (Prod.mk a)).toOuterMeasure {x : A × B | x.2 ∈ S x.1}
      = ∑' a, p a * q.toOuterMeasure (S a) := by
        refine tsum_congr fun a => ?_
        have hpre : (Prod.mk a) ⁻¹' {x : A × B | x.2 ∈ S x.1} = S a := by
          ext b
          simp only [Set.mem_preimage, Set.mem_setOf_eq]
        rw [PMF.toOuterMeasure_map_apply, hpre]
    _ ≤ ∑' a, p a * beta := ENNReal.tsum_le_tsum fun a => mul_le_mul_right (hS a) _
    _ = (∑' a, p a) * beta := by rw [ENNReal.tsum_mul_right]
    _ = beta := by rw [PMF.tsum_coe, one_mul]

/-- The algebraic adversary together with all eleven pre-IPA and `k` IPA-round oracle reads.
Irreducibility keeps dependent witness indices stable during equality elimination; proofs that need
the implementation unfold it explicitly. -/
@[irreducible] def wrappedAdversary (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) :
    OracleComp (BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k)) Fp
      (AlgebraicWfProof basis (family.vk basis) (family.instanceCommitment basis) ×
        (Fin (11 + shape.k) → Fp)) :=
  (family.adversary basis).withReads
    (fun p => Fin.append (algebraicFullPrefixesPre family.init p)
      (algebraicFullPrefixes family.init p))

/-- The challenge record encoded by a wrapped output. -/
def wrappedRecord {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs → Nat → VestaG}
    (pnu : AlgebraicWfProof basis vk instanceCommitment × (Fin (11 + shape.k) → Fp)) :
    Challenges shape.k Fp :=
  chRecord (fun i => pnu.2 (Fin.castAdd shape.k i))
    (fun j => pnu.2 (Fin.natAdd 11 j))

/-- The underlying proof produced on one oracle table. -/
def runProof (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) :
    AlgebraicWfProof basis (family.vk basis) (family.instanceCommitment basis) :=
  (family.adversary basis).run O

/-- The eleven pre-IPA reads of one run. -/
def runReads (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) :
    Fin 11 → Fp :=
  fun i => O (algebraicFullPrefixesPre family.init (runProof family basis O) i)

/-- The `k` IPA-round reads of one run. -/
def runRounds (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) :
    Fin shape.k → Fp :=
  fun j => O (algebraicFullPrefixes family.init (runProof family basis O) j)

/-- The complete challenge record of one run. -/
def runRecord (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) :
    Challenges shape.k Fp :=
  chRecord (runReads family basis O) (runRounds family basis O)

/-- Wrapping preserves the underlying adversary output. -/
theorem wrappedAdversary_run_fst (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) :
    ((wrappedAdversary family basis).run O).1 = (family.adversary basis).run O := by
  simp only [wrappedAdversary, OracleComp.run_withReads]

/-- Wrapping adds one query per re-read squeeze point: eleven pre-IPA and `shape.k` IPA rounds.
Stated here so callers never unfold the irreducible wrapper. -/
theorem queryBound_wrappedAdversary (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) :
    (wrappedAdversary family basis).QueryBound (family.Q + (11 + shape.k)) := by
  rw [wrappedAdversary]
  exact OracleComp.queryBound_withReads _ (family.queryBound basis)

/-- The wrapped reads reconstruct the run's challenge record. -/
theorem wrappedRecord_run (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) :
    wrappedRecord ((wrappedAdversary family basis).run O) = runRecord family basis O := by
  simp only [wrappedAdversary, OracleComp.run_withReads, wrappedRecord, runRecord]
  exact congrArg₂ chRecord
    (funext fun i => congrArg O (Fin.append_left _ _ i))
    (funext fun j => congrArg O (Fin.append_right _ _ j))

open ComputedAlgebraicFSFamily in
/-- Deployed acceptance at the Fiat-Shamir game is verifier acceptance at the run's record. -/
theorem deployedAccepts_of_fsWinsFull (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (hwin : fsWinsFull (family.adversary basis)
      (fullAlgebraicAcceptDeployed basis (family.vk basis)
        (family.instanceCommitment basis))
      (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) O) :
    DeployedAccepts (ursOfAugmentedBasis shape.k basis) rfl (family.vk basis)
      (family.instanceCommitment basis) (runProof family basis O).proof.1
      (runRecord family basis O) :=
  hwin

open ComputedAlgebraicFSFamily in
/-- The clean recursive-IPA opening, specialized to the proof and reads of this run. -/
theorem cleanOpening_provenance_run (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (coins : family.Coins)
    (h : family.hasCleanOpening basis coins) :
    ∃ (cert : AlgebraicDForkCert (F := Fp)
        (augmentedBasis (ursOfAugmentedBasis shape.k basis).g
          (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w) shape.k)
      (hz : runReads family basis coins.1 10 ≠ 0)
      (hvalid : DeployedForkValid (ursOfAugmentedBasis shape.k basis).g
        (evalVector shape.k (runReads family basis coins.1 7))
        (ursOfAugmentedBasis shape.k basis).u
        (ursOfAugmentedBasis shape.k basis).w (runReads family basis coins.1 10)
        (commit (ursOfAugmentedBasis shape.k basis)
            (adjustedWitness ((runProof family basis coins.1).aMulti
                (runReads family basis coins.1)) (runProof family basis coins.1).s
              (multiopenValue (family.vk basis) (family.instanceCommitment basis)
                (runProof family basis coins.1).proof.1
                (chRecord (runReads family basis coins.1) (fun _ => 0)))
              (runReads family basis coins.1 9)) +
          ((runProof family basis coins.1).multiU (runReads family basis coins.1)
              + runReads family basis coins.1 9 * (runProof family basis coins.1).sU)
            • (ursOfAugmentedBasis shape.k basis).u +
          ((runProof family basis coins.1).multiBlind (runReads family basis coins.1)
              + runReads family basis coins.1 9 * (runProof family basis coins.1).sBlind)
            • (ursOfAugmentedBasis shape.k basis).w)
        cert.toDForkCert),
      (family.instanceAttempt basis coins).output =
          some (deployedAlgebraicInstanceOfCert (runProof family basis coins.1)
            (runReads family basis coins.1) cert hz hvalid) ∧
      ∃ o : (deployedAlgebraicInstanceOfCert (runProof family basis coins.1)
          (runReads family basis coins.1) cert hz hvalid).Opening,
        (deployedAlgebraicInstanceOfCert (runProof family basis coins.1)
          (runReads family basis coins.1) cert hz hvalid).run = PSum.inl o := by
  obtain ⟨x, hout, o, hrun⟩ := h
  have hout0 := hout
  simp only [ComputedAlgebraicFSFamily.instanceAttempt,
    computedDeployedAlgebraicInstanceFromTape, computedDeployedAlgebraicInstance] at hout
  split at hout
  · exact absurd hout (by simp)
  · split at hout
    · obtain rfl := (Option.some.inj hout).symm
      exact ⟨_, _, _, hout0, o, hrun⟩
    · exact absurd hout (by simp)

open ComputedAlgebraicFSFamily in
/-- The deployed-accepting, clean-opening residual. -/
def cleanButNotExtractedDeployed (family : ComputedAlgebraicFSFamily shape)
    (extracted : (AugmentedIndex (2 ^ shape.k) → VestaG) → family.Coins → Prop) :
    Set ((AugmentedIndex (2 ^ shape.k) → VestaG) × family.Coins) :=
  {q | fsWinsFull (family.adversary q.1)
      (fullAlgebraicAcceptDeployed q.1 (family.vk q.1) (family.instanceCommitment q.1))
      (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) q.2.1 ∧
    family.hasCleanOpening q.1 q.2 ∧ ¬ extracted q.1 q.2}

open ComputedAlgebraicFSFamily in
/-- Split deployed extraction failure into recursive-IPA failure and the clean residual. -/
theorem snarkExtractionFailureEventDeployed_subset_union
    (family : ComputedAlgebraicFSFamily shape)
    (extracted : (AugmentedIndex (2 ^ shape.k) → VestaG) → family.Coins → Prop) :
    snarkExtractionFailureEventDeployed family extracted ⊆
      family.snarkFailureEvent ∪ cleanButNotExtractedDeployed family extracted := by
  rintro ⟨basis, coins⟩ ⟨hacc, hnex⟩
  by_cases hclean : family.hasCleanOpening basis coins
  · exact Or.inr ⟨hacc, hclean, hnex⟩
  · exact Or.inl ⟨fullAlgebraicAccept_of_deployed basis (family.vk basis)
      (family.instanceCommitment basis) ((family.adversary basis).run coins.1) _ _ hacc,
      hclean⟩

end Zcash.Snark
