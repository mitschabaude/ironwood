import Zcash.Snark.Soundness.Canonical.Vesta
import Zcash.Circuits.Integration.TopLevelAcceptedModel
import Zcash.Snark.Soundness.TopLevelTerminal

/-!
# Circuit-generic Vesta soundness capstone

This module combines the verifier-native Vesta terminal with the generic
`TopLevelCircuit` soundness and public-instance terminals. The circuit determines
its verifying key and instance commitments; successful verification yields its
statement at the public inputs supplied to the verifier.
-/

namespace Zcash.Snark

open Polynomial
open Classical
open scoped ENNReal

open Halo2 Keygen

set_option maxHeartbeats 20000

local instance topLevelVestaInhabited : Inhabited VestaG := ⟨0⟩

attribute [local irreducible] deployedSetQueries deployedSetCommIds
  deployedX4PairCount x4BatchCommitments x4BatchEvals

set_option maxRecDepth 1000000 in
/--
The Vesta soundness capstone for an arbitrary top-level circuit and arbitrary
proof multiplicity.

Acceptance fixes the canonical polynomial assignment.  The caller supplies the
circuit's named component-level correctness package for that assignment, not an
opaque implication to the desired statement.
-/
noncomputable def topLevelStatements_or_relation_of_deployedAccepts
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS VestaG)
    (hk : (pp.mergeDerived top).k = urs.k)
    (inputs :
      Fin (pp.mergeDerived top).numProofs → PublicInput Fp)
    (ps : ProofString (pp.mergeDerived top) Fp VestaG)
    (ch : Challenges (pp.mergeDerived top).k Fp)
    (pU pW : Fp)
    (hpoly : Polynomial Fp)
    {a₀ : Fin (2 ^ urs.k) → Fp}
    (pbatch :
      OpenedBatchOpenings urs (evalVector urs.k ch.x3)
        (x4BatchCommitments
          (instanceCommitment := top.instanceCommitment pp urs inputs)
          urs hk (top.toVerifierKey pp urs) ps ch)
        (x4BatchEvals
          (instanceCommitment := top.instanceCommitment pp urs inputs)
          (top.toVerifierKey pp urs) ps ch)
        a₀ pU pW)
    (hξcur : pbatch.batchChallenge pbatch.current = ch.x4)
    (hlen : ∀ i, i <
        deployedX4PairCount
          (top.toVerifierKey pp urs) (top.instanceCommitment pp urs inputs) ps ch →
      0 < (deployedSetQueries
        (top.toVerifierKey pp urs) (top.instanceCommitment pp urs inputs) ps ch i).length)
    (hprob1 : ∀ i, i <
        deployedX4PairCount
          (top.toVerifierKey pp urs) (top.instanceCommitment pp urs inputs) ps ch →
      (((deployedSetQueries
          (top.toVerifierKey pp urs) (top.instanceCommitment pp urs inputs) ps ch i).length - 1 :
            ℕ) : ℝ≥0∞) /
          Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure
          (Finset.univ.filter
            (OpenedX1Accept urs hk
              (top.toVerifierKey pp urs) (top.instanceCommitment pp urs inputs) ps ch)))
    (haccepts :
      DeployedAccepts urs hk
        (top.toVerifierKey pp urs) (top.instanceCommitment pp urs inputs) ps ch)
    (hblinding :
      (top.toVerifierKey pp urs).blindingFactors <
        (top.toVerifierKey pp urs).n)
    (gateCoherence : TopLevelGateCoherence top pp urs)
    (i m : ℕ)
    (hm : m < (deployedSetQueries
      (top.toVerifierKey pp urs) (top.instanceCommitment pp urs inputs) ps ch i).length)
    (colPoly : Fin (deployedSetQueries
      (top.toVerifierKey pp urs) (top.instanceCommitment pp urs inputs) ps ch i).length →
        Polynomial Fp)
    (hbindAll : ∀ (idx : Fin ((constructIntermediateSets
          (assembleQueries
            (top.toVerifierKey pp urs) (top.instanceCommitment pp urs inputs) ps ch)).points.getD
              i []).length)
        (m₀ : Fin (deployedSetQueries
          (top.toVerifierKey pp urs) (top.instanceCommitment pp urs inputs) ps ch i).length),
      (colPoly m₀).eval
          (((constructIntermediateSets
            (assembleQueries
              (top.toVerifierKey pp urs) (top.instanceCommitment pp urs inputs) ps ch)).points.getD
                i [])[idx]) =
        ((deployedSetQueries
          (top.toVerifierKey pp urs) (top.instanceCommitment pp urs inputs) ps ch i).getD
            (m₀ : ℕ) (.point 0, [])).2.getD (idx : ℕ) 0 ⊕'
        NontrivialRelation (F := Fp) urs.g urs.u urs.w)
    (hquot : hpoly = colPoly ⟨m, hm⟩)
    (hroute : (constructIntermediateSets
      (assembleQueries
        (top.toVerifierKey pp urs) (top.instanceCommitment pp urs inputs) ps ch)).points.getD
          i [] = [ch.x])
    (hevals : ∀ d₀,
      ((deployedSetQueries
        (top.toVerifierKey pp urs) (top.instanceCommitment pp urs inputs) ps ch i).getD m d₀).2 =
        [expectedHEval
          (allExpressions
            (top.toVerifierKey pp urs) ps ch
            (lagrangeBasis
              (top.toVerifierKey pp urs).omega
              (top.toVerifierKey pp urs).n
              (top.toVerifierKey pp urs).blindingFactors
              (ch.x ^ (top.toVerifierKey pp urs).n) ch.x).1
            (lagrangeBasis
              (top.toVerifierKey pp urs).omega
              (top.toVerifierKey pp urs).n
              (top.toVerifierKey pp urs).blindingFactors
              (ch.x ^ (top.toVerifierKey pp urs).n) ch.x).2.1
            (lagrangeBasis
              (top.toVerifierKey pp urs).omega
              (top.toVerifierKey pp urs).n
              (top.toVerifierKey pp urs).blindingFactors
              (ch.x ^ (top.toVerifierKey pp urs).n) ch.x).2.2)
          ch.y (ch.x ^ (top.toVerifierKey pp urs).n)])
    (claimed :
      AcceptedModelClaimedEvaluations
        (memberDecode :=
          vestaExtractedMemberDecode urs hk
            (top.toVerifierKey pp urs) (top.instanceCommitment pp urs inputs) ps ch
            pbatch hlen hprob1 haccepts)
        (hblinding := hblinding) haccepts)
    (hxgood :
      ch.x ∉ szBadSet
        (let model :=
          CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode :=
              vestaExtractedMemberDecode urs hk
                (top.toVerifierKey pp urs) (top.instanceCommitment pp urs inputs) ps ch
                pbatch hlen hprob1 haccepts)
            (hblinding := hblinding) haccepts
        combineConstraints model.fixedCols model.adviceCols model.instanceCols
          model.gates model.sets model.chunks model.lookups
          model.beta model.gamma model.delta model.theta ch.y model.chunkLen
          model.l0 model.lLast model.lBlind -
            hpoly * (X ^ (top.toVerifierKey pp urs).n - 1)))
    (hgoodY : ∀ j,
      ch.y ∉ szBadSet
        (foldSplitWitness
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode :=
              vestaExtractedMemberDecode urs hk
                (top.toVerifierKey pp urs) (top.instanceCommitment pp urs inputs) ps ch
                pbatch hlen hprob1 haccepts)
            (hblinding := hblinding) haccepts).constraints
          (top.toVerifierKey pp urs).n j))
    {cell : Type} [DecidableEq cell] [Fintype cell]
    (correctness : ∀
      (_hsatisfied :
        (CanonicalMemberConstraintRelation.acceptedModel
          (memberDecode :=
            vestaExtractedMemberDecode urs hk
              (top.toVerifierKey pp urs) (top.instanceCommitment pp urs inputs) ps ch
              pbatch hlen hprob1 haccepts)
          (hblinding := hblinding) haccepts).CircuitSat
            ch.y hpoly (top.toVerifierKey pp urs).n a₀),
      TopLevelCircuitCorrectness top pp urs ch
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode :=
            vestaExtractedMemberDecode urs hk
              (top.toVerifierKey pp urs) (top.instanceCommitment pp urs inputs) ps ch
              pbatch hlen hprob1 haccepts)
          haccepts)
        cell
        (NontrivialRelation (F := Fp) urs.g urs.u urs.w)) :
    (∀ proofIndex, top.Statement (inputs proofIndex)) ⊕'
      NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  let vk := top.toVerifierKey pp urs
  let memberDecode :=
    vestaExtractedMemberDecode urs hk vk (top.instanceCommitment pp urs inputs) ps ch
      pbatch hlen hprob1 haccepts
  have hterminal :=
    acceptedModel_circuitSat_or_relation_of_acceptedSelections
      urs hk vk (top.instanceCommitment pp urs inputs) ps ch pU pW hpoly
      pbatch hξcur hlen hprob1 haccepts hblinding
      gateCoherence.adviceQueryCount gateCoherence.instanceQueryCount
      i m hm colPoly hbindAll hquot hroute hevals claimed hxgood
  rcases hterminal with hsatisfied | hrelation
  · exact
      TopLevelAcceptedModel.statements_or_relation_of_circuitSat
        top pp urs hk inputs ps ch pU pW a₀ pbatch memberDecode
        haccepts hblinding hpoly hsatisfied hgoodY
        (correctness hsatisfied)
  · exact PSum.inr hrelation

assert_no_sorry topLevelStatements_or_relation_of_deployedAccepts

end Zcash.Snark
