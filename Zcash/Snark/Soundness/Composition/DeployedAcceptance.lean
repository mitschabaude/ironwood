import Zcash.Snark.Soundness.Composition.Decomposition
import Zcash.Snark.Soundness.Multiopen.Deployed

/-!
# Acceptance at the deployed verifier decision

These definitions isolate the deployed-decision event from the historical accepting-multiopen
rewind construction.  They are the acceptance surface used by the rewind-free algebraic bound.
-/

namespace Zcash.Snark

local instance vestaInhabitedDeployedAcceptance : Inhabited VestaG := ⟨0⟩

/-- The Fiat--Shamir acceptance predicate strengthened to the actual deployed verifier decision. -/
def fullAlgebraicAcceptDeployed {shape : Shape}
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (p : AlgebraicWfProof basis vk instanceCommitment)
    (nu : Fin 11 → Fp) (rounds : Fin shape.k → Fp) : Prop :=
  DeployedAccepts (ursOfAugmentedBasis shape.k basis) rfl vk instanceCommitment p.proof.1
    (chRecord nu rounds)

/-- Deployed acceptance implies the verifier-equation predicate used by the recursive extractor. -/
theorem fullAlgebraicAccept_of_deployed {shape : Shape}
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (p : AlgebraicWfProof basis vk instanceCommitment)
    (nu : Fin 11 → Fp) (rounds : Fin shape.k → Fp)
    (h : fullAlgebraicAcceptDeployed basis vk instanceCommitment p nu rounds) :
    fullAlgebraicAccept basis vk instanceCommitment p nu rounds :=
  deployedAccepts_verifierEq (ursOfAugmentedBasis shape.k basis) rfl vk instanceCommitment
    p.proof.1 (chRecord nu rounds) h

/-- Deployed acceptance without the requested extraction endpoint. -/
def snarkExtractionFailureEventDeployed {shape : Shape}
    (family : ComputedAlgebraicFSFamily shape)
    (extracted : (AugmentedIndex (2 ^ shape.k) → VestaG) → family.Coins → Prop) :
    Set ((AugmentedIndex (2 ^ shape.k) → VestaG) × family.Coins) :=
  {q | fsWinsFull (family.adversary q.1)
      (fullAlgebraicAcceptDeployed q.1 (family.vk q.1) (family.instanceCommitment q.1))
      (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) q.2.1 ∧
    ¬ extracted q.1 q.2}

end Zcash.Snark
