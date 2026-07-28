import Zcash.Snark.Soundness.Vesta
import Zcash.Snark.Soundness.Forking.Adversary.Algebraic
import Zcash.Snark.Soundness.AGM.Capstone

/-!
# Composing the algebraic forking extraction with the deployed decoded capstone

`Soundness.Forking.Adversary.Algebraic` proves the clean-opening branch of the algebraic forking
family (`runToSnark`, bounded by `snarkFailure_prob_le_of_*`); `Soundness.Vesta` proves the deployed
decoded capstone. The two are architecturally
disjoint — one runs over an adversary-produced `AlgebraicWfProof` at oracle-derived challenges
`chRecord ν`, the other over a deployed `(vk, ps, ch)` run. This module builds the identification
bridge the composition needs on the *computed path*: the algebraic instance's clean `Opening` — an
`IpaRelation` at `commit … aMulti` — is exactly the `IpaRelation` at the deployed opened commitment
`deployedCommitment − pU•u − pW•w` the capstone consumes, once `AlgebraicWfProof.multiopen_repr`
rewrites the commitment. The honest value shift `z⁻¹·vU − ξ·⟨s,b⟩` is *derived*, not assumed: on the
witness-tie branch it is forced to vanish (`shift_eq_zero_of_openings_agree`), and the collision
branch needs only the commitment identification (`opening_commit_deployed_of_instance`), so the
composition chain carries no shift hypothesis.

## The extracted `U`/`W` coordinates (`pU`, `pW`)

`pU`/`pW` are outputs, never hypotheses: the AGM representation (`AlgebraicWfProof.multiopen_repr`)
exposes the adversary's aggregate commitment as `commit(aMulti) + pU•u + pW•w`, so the extracted
opening is the generalized Pedersen triple `(aMulti, pU, pW)` in the augmented basis `(g, u, w)`.
The relation is stated at the de-blinded point `deployedCommitment − pU•u − pW•w` because
`IpaRelation` is the `g`-span opening. `pW` is the `w`-weight of the AGM representation — an
adversary may set it to anything, so the argument never assumes it is nonzero. Its value is
immaterial because the de-blinding subtracts `pW•w` (and `pU•u`) off whatever they are
(`opening_commit_deployed_of_instance`, no value-shift hypothesis). Weight on `u` shifts the opened
value by `z⁻¹·vU`; against the deployed batch opening of the same point that shift either vanishes
or the witnesses collide into a computed `(g,u,w)` relation — a dichotomy the rewind-free AGM
route returns as explicit relation coefficients.
-/

namespace Zcash.Snark

-- The deployed grouping definitions appear inside index types, so a defeq check on an index can
-- pull the whole `constructIntermediateSets (assembleQueries …)` computation through `whnf`.
-- Sealing them keeps those checks syntactic; the proofs below use their equation lemmas.
attribute [local irreducible] deployedSetQueries deployedSetCommIds deployedX4PairCount
  x4BatchCommitments x4BatchEvals

-- Match the instance set `AlgebraicWfProof.multiopen_repr` is stated against
-- (`Forking.Adversary.Algebraic` uses the same concrete `Inhabited VestaG`); a local `[Inhabited]`
-- binder would be a *different* instance term, forcing the `multiopenCommitment` fold through `whnf`.
-- Named (not anonymous) to avoid an auto-generated-name collision with the identical
-- `local instance` in `Forking.Adversary.Provenance` when both are imported into `TrustBoundary`.
local instance vestaInhabitedCompositionBridge : Inhabited VestaG := ⟨0⟩

variable {shape : Shape} {basis : AugmentedIndex (2 ^ shape.k) → VestaG}

/-- `deployedCommitment` at the split URS unfolds to `multiopenCommitment`: definitional (the `hk`
cast is `rfl` on `ursOfAugmentedBasis`, whose `.k` is `shape.k`). Isolated so downstream terms match
`AlgebraicWfProof.multiopen_repr`'s `multiopenCommitment` without forcing the fold through `whnf`. -/
theorem deployedCommitment_eq_multiopen
    (vk : VerifyingKey shape Fp VestaG) (instanceCommitment : Fin shape.numProofs → ℕ → VestaG) (ps : ProofString shape Fp VestaG)
    (ch : Challenges shape.k Fp) :
    deployedCommitment (ursOfAugmentedBasis shape.k basis) rfl vk instanceCommitment ps ch
      = multiopenCommitment (ursOfAugmentedBasis shape.k basis).g
          (ursOfAugmentedBasis shape.k basis).w (ursOfAugmentedBasis shape.k basis).u vk instanceCommitment ps ch :=
  rfl

/-- **The g-span representation of the multiopen commitment (P-identification).** The algebraic
proof's aggregate witness `aMulti ν` commits to `multiopenCommitment − multiU•u − multiBlind•w`:
immediate from `AlgebraicWfProof.multiopen_repr`. -/
theorem commit_aMulti_eq_multiopen
    {vk : VerifyingKey shape Fp VestaG} {instanceCommitment : Fin shape.numProofs → ℕ → VestaG} (p : AlgebraicWfProof basis vk instanceCommitment) (ν : Fin 11 → Fp) :
    commit (ursOfAugmentedBasis shape.k basis) (p.aMulti ν)
      = multiopenCommitment (ursOfAugmentedBasis shape.k basis).g
          (ursOfAugmentedBasis shape.k basis).w (ursOfAugmentedBasis shape.k basis).u
          vk instanceCommitment p.algebraicProof.erase (chRecord ν (fun _ => 0))
        - p.multiU ν • (ursOfAugmentedBasis shape.k basis).u
        - p.multiBlind ν • (ursOfAugmentedBasis shape.k basis).w := by
  have h := p.multiopen_repr ν
  rw [sub_sub, eq_sub_iff_add_eq, ← add_assoc]
  exact h

/-- **The algebraic clean opening is an `IpaRelation` at the identified commitment/value (the
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

/-- **The bridge at the constructed instance.** The clean opening is an `IpaRelation` at the
deployed opened commitment `deployedCommitment − multiU•u − multiBlind•w` with `v = multiopenValue`
(`commit_aMulti_eq_multiopen` identifies the commitment). Only this standalone bridge carries
`hshift`; the composition derives the shift on the witness tie
(`shift_eq_zero_of_openings_agree`). -/
theorem ipaRelation_deployed_of_instance
    {vk : VerifyingKey shape Fp VestaG} {instanceCommitment : Fin shape.numProofs → ℕ → VestaG} (p : AlgebraicWfProof basis vk instanceCommitment) (ν : Fin 11 → Fp)
    (cert : AlgebraicDForkCert (F := Fp)
      (augmentedBasis (ursOfAugmentedBasis shape.k basis).g
        (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w) shape.k)
    (hz : ν 10 ≠ 0)
    (hvalid : DeployedForkValid (ursOfAugmentedBasis shape.k basis).g
      (evalVector shape.k (ν 7)) (ursOfAugmentedBasis shape.k basis).u
      (ursOfAugmentedBasis shape.k basis).w (ν 10)
      (commit (ursOfAugmentedBasis shape.k basis)
          (adjustedWitness (p.aMulti ν) p.s
            (multiopenValue vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0))) (ν 9)) +
        (p.multiU ν + ν 9 * p.sU) • (ursOfAugmentedBasis shape.k basis).u +
        (p.multiBlind ν + ν 9 * p.sBlind) • (ursOfAugmentedBasis shape.k basis).w)
      cert.toDForkCert)
    (hshift : (ν 10)⁻¹ * (p.multiU ν + ν 9 * p.sU)
        - ν 9 * innerProduct p.s (evalVector shape.k (ν 7)) = 0)
    (o : (deployedAlgebraicInstanceOfCert p ν cert hz hvalid).Opening) :
    IpaRelation (ursOfAugmentedBasis shape.k basis)
      (deployedCommitment (ursOfAugmentedBasis shape.k basis) rfl vk instanceCommitment p.proof.1
            (chRecord ν (fun _ => 0))
        - p.multiU ν • (ursOfAugmentedBasis shape.k basis).u
        - p.multiBlind ν • (ursOfAugmentedBasis shape.k basis).w)
      (evalVector shape.k (ν 7)) (multiopenValue vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0))) o.1 :=
  ipaRelation_of_opening (deployedAlgebraicInstanceOfCert p ν cert hz hvalid)
    (by
      simp only [deployedAlgebraicInstanceOfCert]
      rw [deployedCommitment_eq_multiopen,
        show (p.proof.1 : ProofString shape Fp VestaG) = p.algebraicProof.erase from rfl]
      exact commit_aMulti_eq_multiopen p ν)
    rfl hshift o

/-- The extracted opening commits to the de-blinded deployed commitment
`deployedCommitment − multiU•u − multiBlind•w` — the commitment conjunct of
`ipaRelation_deployed_of_instance`, available with no value-shift hypothesis. -/
theorem opening_commit_deployed_of_instance
    {vk : VerifyingKey shape Fp VestaG} {instanceCommitment : Fin shape.numProofs → ℕ → VestaG} (p : AlgebraicWfProof basis vk instanceCommitment) (ν : Fin 11 → Fp)
    (cert : AlgebraicDForkCert (F := Fp)
      (augmentedBasis (ursOfAugmentedBasis shape.k basis).g
        (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w) shape.k)
    (hz : ν 10 ≠ 0)
    (hvalid : DeployedForkValid (ursOfAugmentedBasis shape.k basis).g
      (evalVector shape.k (ν 7)) (ursOfAugmentedBasis shape.k basis).u
      (ursOfAugmentedBasis shape.k basis).w (ν 10)
      (commit (ursOfAugmentedBasis shape.k basis)
          (adjustedWitness (p.aMulti ν) p.s
            (multiopenValue vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0))) (ν 9)) +
        (p.multiU ν + ν 9 * p.sU) • (ursOfAugmentedBasis shape.k basis).u +
        (p.multiBlind ν + ν 9 * p.sBlind) • (ursOfAugmentedBasis shape.k basis).w)
      cert.toDForkCert)
    (o : (deployedAlgebraicInstanceOfCert p ν cert hz hvalid).Opening) :
    commit (ursOfAugmentedBasis shape.k basis) o.1
      = deployedCommitment (ursOfAugmentedBasis shape.k basis) rfl vk instanceCommitment p.proof.1
            (chRecord ν (fun _ => 0))
        - p.multiU ν • (ursOfAugmentedBasis shape.k basis).u
        - p.multiBlind ν • (ursOfAugmentedBasis shape.k basis).w :=
  o.2.1.trans (by
    simp only [deployedAlgebraicInstanceOfCert]
    rw [deployedCommitment_eq_multiopen,
      show (p.proof.1 : ProofString shape Fp VestaG) = p.algebraicProof.erase from rfl]
    exact commit_aMulti_eq_multiopen p ν)

/-- **The honest value shift is forced on the witness tie.** The clean opening opens at
`multiopenValue + (z⁻¹·vU − ξ·⟨s,b⟩)`; a witness `a₀` of the deployed batch opens the same inner
product at `multiopenValue`. If the two witnesses agree, the shift `z⁻¹·vU − ξ·⟨s,b⟩` is `0` —
the condition `ipaRelation_deployed_of_instance` names `hshift`, derived rather than assumed. -/
theorem shift_eq_zero_of_openings_agree
    {vk : VerifyingKey shape Fp VestaG} {instanceCommitment : Fin shape.numProofs → ℕ → VestaG} (p : AlgebraicWfProof basis vk instanceCommitment) (ν : Fin 11 → Fp)
    (cert : AlgebraicDForkCert (F := Fp)
      (augmentedBasis (ursOfAugmentedBasis shape.k basis).g
        (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w) shape.k)
    (hz : ν 10 ≠ 0)
    (hvalid : DeployedForkValid (ursOfAugmentedBasis shape.k basis).g
      (evalVector shape.k (ν 7)) (ursOfAugmentedBasis shape.k basis).u
      (ursOfAugmentedBasis shape.k basis).w (ν 10)
      (commit (ursOfAugmentedBasis shape.k basis)
          (adjustedWitness (p.aMulti ν) p.s
            (multiopenValue vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0))) (ν 9)) +
        (p.multiU ν + ν 9 * p.sU) • (ursOfAugmentedBasis shape.k basis).u +
        (p.multiBlind ν + ν 9 * p.sBlind) • (ursOfAugmentedBasis shape.k basis).w)
      cert.toDForkCert)
    (o : (deployedAlgebraicInstanceOfCert p ν cert hz hvalid).Opening)
    {a₀ : Fin (2 ^ shape.k) → Fp}
    (hval₀ : innerProduct a₀ (evalVector shape.k (ν 7))
      = multiopenValue vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)))
    (hae : o.1 = a₀) :
    (ν 10)⁻¹ * (p.multiU ν + ν 9 * p.sU)
      - ν 9 * innerProduct p.s (evalVector shape.k (ν 7)) = 0 := by
  have h := o.2.2
  rw [hae] at h
  -- Re-ascribe by definitional unfolding: the instance's projections (`x.b`, `x.v`, …) reduce to
  -- the `ν`-expressions, aligning the hidden `2 ^ urs.k` index with `2 ^ shape.k` so `rw` matches.
  have h' : innerProduct a₀ (evalVector shape.k (ν 7))
      = multiopenValue vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0))
        + (ν 10)⁻¹ * (p.multiU ν + ν 9 * p.sU)
        - ν 9 * innerProduct p.s (evalVector shape.k (ν 7)) := h
  rw [hval₀, add_sub_assoc] at h'
  exact left_eq_add.mp h'

/-- `ipaRelation_deployed_of_instance` with `hshift` discharged by
`shift_eq_zero_of_openings_agree`: on the witness tie the clean opening satisfies the deployed
`IpaRelation` at `multiopenValue` with no shift hypothesis. -/
theorem ipaRelation_deployed_of_openings_agree
    {vk : VerifyingKey shape Fp VestaG} {instanceCommitment : Fin shape.numProofs → ℕ → VestaG} (p : AlgebraicWfProof basis vk instanceCommitment) (ν : Fin 11 → Fp)
    (cert : AlgebraicDForkCert (F := Fp)
      (augmentedBasis (ursOfAugmentedBasis shape.k basis).g
        (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w) shape.k)
    (hz : ν 10 ≠ 0)
    (hvalid : DeployedForkValid (ursOfAugmentedBasis shape.k basis).g
      (evalVector shape.k (ν 7)) (ursOfAugmentedBasis shape.k basis).u
      (ursOfAugmentedBasis shape.k basis).w (ν 10)
      (commit (ursOfAugmentedBasis shape.k basis)
          (adjustedWitness (p.aMulti ν) p.s
            (multiopenValue vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0))) (ν 9)) +
        (p.multiU ν + ν 9 * p.sU) • (ursOfAugmentedBasis shape.k basis).u +
        (p.multiBlind ν + ν 9 * p.sBlind) • (ursOfAugmentedBasis shape.k basis).w)
      cert.toDForkCert)
    (o : (deployedAlgebraicInstanceOfCert p ν cert hz hvalid).Opening)
    {a₀ : Fin (2 ^ shape.k) → Fp}
    (hval₀ : innerProduct a₀ (evalVector shape.k (ν 7))
      = multiopenValue vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)))
    (hae : o.1 = a₀) :
    IpaRelation (ursOfAugmentedBasis shape.k basis)
      (deployedCommitment (ursOfAugmentedBasis shape.k basis) rfl vk instanceCommitment p.proof.1
            (chRecord ν (fun _ => 0))
        - p.multiU ν • (ursOfAugmentedBasis shape.k basis).u
        - p.multiBlind ν • (ursOfAugmentedBasis shape.k basis).w)
      (evalVector shape.k (ν 7)) (multiopenValue vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0))) o.1 :=
  ipaRelation_deployed_of_instance p ν cert hz hvalid
    (shift_eq_zero_of_openings_agree p ν cert hz hvalid o hval₀ hae) o



/-! ## G4 — the quantitative knowledge-error bound (conditional)

The clean-opening failure `snarkFailureEvent` is already bounded
(`snarkFailure_prob_le_of_generatorRO_textbookDL`). On every clean-opening run the composition
delivers `SnarkRelation ∨ DL` *given the deployed gate data*
(`pbatch`/`mdec`/`hquot`/`hgood`/layout). So the SNARK-extraction failure is contained in the
clean-opening failure and inherits the same bound — **conditional on the gate data discharging on
clean openings** (`hExtract`).

This generic conditional bridge is retained for callers that already have `hExtract`.  The concrete
deployed path no longer discharges it through multiopen rewinding: `AGM.DeployedRootDecode` decodes
the squeeze-pinned algebraic representations directly, and `Composition.DeployedRootContainment`
prices each resulting bad-root event additively. -/

namespace ComputedAlgebraicFSFamily

variable {shape : Shape}

/-- The SNARK-extraction-failure event: full deployed acceptance with no successful SNARK extraction
`extracted`. `extracted` is the composition's per-run conclusion (`SnarkRelation ∨ DL`), delivered on
the clean-opening branch given the deployed gate data. -/
def snarkExtractionFailureEvent (family : ComputedAlgebraicFSFamily shape)
    (extracted : (AugmentedIndex (2 ^ shape.k) → VestaG) → family.Coins → Prop) :
    Set ((AugmentedIndex (2 ^ shape.k) → VestaG) × family.Coins) :=
  {q | fsWinsFull (family.adversary q.1) (fullAlgebraicAccept q.1 (family.vk q.1) (family.instanceCommitment q.1))
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
/-- **Conditional knowledge-soundness bound.** The measure of "deployed acceptance but no
SNARK extraction" inherits the clean-opening bound
`(Q+k)·3/|Fp| + (Q+1)/|Fp| + ε + 1/|Fp|`, **conditional on `hExtract`** — that every clean-opening run
delivers the extraction, given the deployed gate data. By
set-containment (`snarkExtractionFailureEvent_subset`) + outer-measure monotonicity, so the concrete
AGM bound transfers verbatim. `hExtract` is the honest disjoint-halves gap: discharging it family-wide
needs a failure-probability bound over the deployed accept measures, which does not exist (the
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
        (bound + 1 / Fintype.card Fp) :=
  le_trans
    ((independentProductPMF (orchardGeneratorROSetup query)
        (PMF.uniformOfFintype family.Coins)).toOuterMeasure.mono
      (Set.preimage_mono (family.snarkExtractionFailureEvent_subset extracted hExtract)))
    (snarkFailure_prob_le_of_generatorRO_textbookDL B hB query hquery family hDL)

/-- **Instance provenance.** Whenever the computed family's `instanceAttempt` yields an
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
    ∃ (p : AlgebraicWfProof basis (family.vk basis) (family.instanceCommitment basis)) (ν : Fin 11 → Fp)
      (cert : AlgebraicDForkCert (F := Fp)
        (augmentedBasis (ursOfAugmentedBasis shape.k basis).g
          (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w) shape.k)
      (hz : ν 10 ≠ 0)
      (hvalid : DeployedForkValid (ursOfAugmentedBasis shape.k basis).g
        (evalVector shape.k (ν 7)) (ursOfAugmentedBasis shape.k basis).u
        (ursOfAugmentedBasis shape.k basis).w (ν 10)
        (commit (ursOfAugmentedBasis shape.k basis)
            (adjustedWitness (p.aMulti ν) p.s
              (multiopenValue (family.vk basis) (family.instanceCommitment basis) p.proof.1 (chRecord ν (fun _ => 0))) (ν 9)) +
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

end Zcash.Snark
