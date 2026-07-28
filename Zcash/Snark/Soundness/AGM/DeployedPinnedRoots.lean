import Zcash.Common.RelationWitness
import Zcash.Snark.Soundness.AGM.DeployedRootDecode
import Zcash.Snark.Soundness.AGM.OnlineMembers
import Zcash.Snark.Soundness.Composition.DeployedRuntime
import Zcash.Snark.Soundness.Forking.PinnedRoots

/-!
# The deployed pinned AGM root family

The adapter from rewind-free algebraic batch data to `PinnedRootFamily`. Its bad sets are the two
IPA shift polynomials and the deployed `x4`, `x3`, `x2`, and per-set `x1` polynomials.

A live family carries an oracle computation of each root set that never queries that event's own
priced squeeze point, and the leave-one-squeeze invariance the probability layer needs follows from
that. The computation may query later batching challenges, so strict-prefix determination is a
sufficient condition rather than the interface.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (card_Fp scalarFieldOrder)

open Classical Polynomial
open scoped ENNReal

local instance vestaInhabitedDeployedPinnedRoots : Inhabited VestaG := ⟨0⟩

variable {shape : Shape}

attribute [local irreducible] deployedX4PairCount deployedSetQueries
  x4BatchCommitments deployedSetMemberCommitments


/-- Output type of the challenge-read wrapper used by the composition. -/
abbrev WrappedAlgebraicOutput (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) :=
  AlgebraicWfProof basis (family.vk basis) (family.instanceCommitment basis) ×
    (Fin (11 + shape.k) -> Fp)

/-- The eleven pre-IPA answers recorded by the wrapped adversary. -/
def wrappedPreIpaReads {family : ComputedAlgebraicFSFamily shape}
    {basis : AugmentedIndex (2 ^ shape.k) -> VestaG}
    (pnu : WrappedAlgebraicOutput family basis) : Fin 11 -> Fp :=
  fun i => pnu.2 (Fin.castAdd shape.k i)

/-- The challenge record relevant to multiopen assembly.  IPA-round challenges do not occur in
this layer, so fixing them to zero matches `AlgebraicWfProof.multiopen_repr` exactly. -/
def wrappedPreIpaRecord {family : ComputedAlgebraicFSFamily shape}
    {basis : AugmentedIndex (2 ^ shape.k) -> VestaG}
    (pnu : WrappedAlgebraicOutput family basis) : Challenges shape.k Fp :=
  chRecord (wrappedPreIpaReads pnu) (fun _ => 0)

/-- The wrapped output's pre-IPA answers are the composition's `runReads`. -/
theorem wrappedPreIpaReads_run (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) :
    wrappedPreIpaReads ((wrappedAdversary family basis).run O) = runReads family basis O := by
  funext i
  simp only [wrappedPreIpaReads, wrappedAdversary, OracleComp.run_withReads, runReads, runProof]
  exact congrArg O (Fin.append_left _ _ i)

/-- Rewind-free deployed batches tied to the current wrapped output's canonical aggregate
coordinates. -/
structure DeployedBatchWitness (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (pnu : WrappedAlgebraicOutput family basis) where
  fixedRepresentations : List (AlgebraicPoint (F := Fp) basis)
  canonical : CanonicalOnlineMultiopenCoordinates pnu.1 fixedRepresentations
  membersCovered : DeployedMembersCovered (family.vk basis) (family.instanceCommitment basis)
    pnu.1.algebraicProof fixedRepresentations
  batches : DeployedAlgebraicBatches (ursOfAugmentedBasis shape.k basis) rfl
    (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
    (wrappedPreIpaRecord pnu)
    (pnu.1.aMulti (wrappedPreIpaReads pnu))
    (pnu.1.multiU (wrappedPreIpaReads pnu))
    (pnu.1.multiBlind (wrappedPreIpaReads pnu))
  memberCoeffs : forall i
      (hi : i < deployedX4PairCount (family.vk basis) (family.instanceCommitment basis)
        pnu.1.proof.1 (wrappedPreIpaRecord pnu)),
    (batches.x1 i hi).coeffs =
      (deployedMemberRepresentationsOfCovered pnu.1 fixedRepresentations membersCovered
        (wrappedPreIpaReads pnu) i hi).coeffs
  memberU : forall i
      (hi : i < deployedX4PairCount (family.vk basis) (family.instanceCommitment basis)
        pnu.1.proof.1 (wrappedPreIpaRecord pnu)),
    (batches.x1 i hi).uComp =
      (deployedMemberRepresentationsOfCovered pnu.1 fixedRepresentations membersCovered
        (wrappedPreIpaReads pnu) i hi).uComp
  memberW : forall i
      (hi : i < deployedX4PairCount (family.vk basis) (family.instanceCommitment basis)
        pnu.1.proof.1 (wrappedPreIpaRecord pnu)),
    (batches.x1 i hi).wComp =
      (deployedMemberRepresentationsOfCovered pnu.1 fixedRepresentations membersCovered
        (wrappedPreIpaReads pnu) i hi).wComp

/-- Algebraic unbatching either supplies every deployed batch or returns a concrete augmented-basis
relation. -/
abbrev DeployedRootOutcomeProvider (family : ComputedAlgebraicFSFamily shape) :=
  forall (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp),
    DeployedBatchWitness family basis ((wrappedAdversary family basis).run O) ⊕'
      AugmentedRelationWitness (F := Fp)
        (ursOfAugmentedBasis shape.k basis).g
        (ursOfAugmentedBasis shape.k basis).u
        (ursOfAugmentedBasis shape.k basis).w

/-- Squeeze index used by one root event: `xi`, `z`, `x4`, `x3`, `x2`, and the union of all
`x1` roots. -/
def deployedRootChallengeIndex (i : Fin 6) : Fin 11 :=
  if i.val = 0 then 9 else if i.val = 1 then 10 else if i.val = 2 then 8
  else if i.val = 3 then 7 else if i.val = 4 then 6 else 5

/-- The oracle point of one deployed root event. -/
noncomputable def deployedRootPoint (family : ComputedAlgebraicFSFamily shape)
    {basis : AugmentedIndex (2 ^ shape.k) -> VestaG}
    (pnu : WrappedAlgebraicOutput family basis) (i : Fin 6) :=
  algebraicFullPrefixesPre family.init pnu.1 (deployedRootChallengeIndex i)

/-- Reading a deployed root event's point returns the corresponding recorded challenge. -/
theorem deployedRootPoint_run (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) (i : Fin 6) :
    O (deployedRootPoint family ((wrappedAdversary family basis).run O) i) =
      runReads family basis O (deployedRootChallengeIndex i) := by
  simp only [deployedRootPoint, wrappedAdversary_run_fst, runReads, runProof]

/-- Direct budget of one deployed root event. -/
noncomputable def deployedRootEventBudget (shape : Shape)
    (i : Fin 6) : ENNReal :=
  if i.val = 0 then 1 / Fintype.card Fp
  else if i.val = 1 then 1 / Fintype.card Fp
  else if i.val = 2 then
    ((shape.numPointSets + 1 : Nat) : ENNReal) / Fintype.card Fp
  else if i.val = 3 then
    ((max (2 ^ shape.k) (queryBudget shape) + 2 * queryBudget shape : Nat) : ENNReal) /
      Fintype.card Fp
  else if i.val = 4 then
    ((shape.numPointSets * queryBudget shape : Nat) : ENNReal) / Fintype.card Fp
  else
    ((shape.numPointSets * queryBudget shape * queryBudget shape : Nat) : ENNReal) /
      Fintype.card Fp

/-- The exact bad-root set for one event.  A relation outcome needs no bad-root charge because it
is already a successful algebraic extraction. -/
noncomputable def deployedRootBad (family : ComputedAlgebraicFSFamily shape)
    (outcome : DeployedRootOutcomeProvider family)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (_pnu : WrappedAlgebraicOutput family basis)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)
    (i : Fin 6) : Set Fp :=
  let pnu := (wrappedAdversary family basis).run O
  match outcome basis O with
  | PSum.inr _ => ∅
  | PSum.inl witness =>
      let p := pnu.1
      let nu := wrappedPreIpaReads pnu
      let ch := wrappedPreIpaRecord pnu
      let batches := witness.batches
      if i.val = 0 then
        ↑(szBadSet (ipaShiftXiPolynomial
          (commitGen (evalVector shape.k ch.x3) (p.aMulti nu) -
            multiopenValue (family.vk basis) (family.instanceCommitment basis) p.proof.1 ch)
          (commitGen (evalVector shape.k ch.x3) p.s)))
      else if i.val = 1 then
        ↑(szBadSet (ipaShiftZPolynomial
          (commitGen (evalVector shape.k ch.x3) (p.aMulti nu) -
            multiopenValue (family.vk basis) (family.instanceCommitment basis) p.proof.1 ch)
          (p.multiU nu) p.sU (commitGen (evalVector shape.k ch.x3) p.s) ch.xi))
      else if i.val = 2 then
        deployedX4RootSet (ursOfAugmentedBasis shape.k basis) rfl
          (family.vk basis) (family.instanceCommitment basis) p.proof.1 ch batches
      else if i.val = 3 then
        deployedX3RootSet (ursOfAugmentedBasis shape.k basis) rfl
          (family.vk basis) (family.instanceCommitment basis) p.proof.1 ch batches
      else if i.val = 4 then
        deployedX2RootSet (ursOfAugmentedBasis shape.k basis) rfl
          (family.vk basis) (family.instanceCommitment basis) p.proof.1 ch batches
      else
        deployedX1AllRootSet (ursOfAugmentedBasis shape.k basis) rfl
          (family.vk basis) (family.instanceCommitment basis) p.proof.1 ch batches

/-- Every explicit bad set has its advertised direct Schwartz--Zippel price. -/
theorem deployedRootBad_measure_le (family : ComputedAlgebraicFSFamily shape)
    (outcome : DeployedRootOutcomeProvider family)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (pnu : WrappedAlgebraicOutput family basis)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)
    (i : Fin 6) :
    (PMF.uniformOfFintype Fp).toOuterMeasure
        (deployedRootBad family outcome basis pnu O i) <= deployedRootEventBudget shape i := by
  let actual := (wrappedAdversary family basis).run O
  change (PMF.uniformOfFintype Fp).toOuterMeasure
      (deployedRootBad family outcome basis actual O i) <= deployedRootEventBudget shape i
  cases hout : outcome basis O with
  | inl witness =>
    simp only [deployedRootBad, hout]
    by_cases h0 : i.val = 0
    · simpa [h0, deployedRootEventBudget, uniformChallenge] using
        ipaShiftXi_badSet_measure_le
          (commitGen (evalVector shape.k (wrappedPreIpaRecord actual).x3)
              (actual.1.aMulti (wrappedPreIpaReads actual)) -
            multiopenValue (family.vk basis) (family.instanceCommitment basis)
              actual.1.proof.1 (wrappedPreIpaRecord actual))
          (commitGen (evalVector shape.k (wrappedPreIpaRecord actual).x3) actual.1.s)
    by_cases h1 : i.val = 1
    · simpa [h0, h1, deployedRootEventBudget, uniformChallenge] using
        ipaShiftZ_badSet_measure_le
          (commitGen (evalVector shape.k (wrappedPreIpaRecord actual).x3)
              (actual.1.aMulti (wrappedPreIpaReads actual)) -
            multiopenValue (family.vk basis) (family.instanceCommitment basis)
              actual.1.proof.1 (wrappedPreIpaRecord actual))
          (actual.1.multiU (wrappedPreIpaReads actual)) actual.1.sU
          (commitGen (evalVector shape.k (wrappedPreIpaRecord actual).x3) actual.1.s)
          (wrappedPreIpaRecord actual).xi
    by_cases h2 : i.val = 2
    · simpa [h0, h1, h2, deployedRootEventBudget, uniformChallenge] using
        deployedX4RootSet_measure_le_shape (ursOfAugmentedBasis shape.k basis) rfl
          (family.vk basis) (family.instanceCommitment basis) actual.1.proof.1
          (wrappedPreIpaRecord actual) witness.batches
    by_cases h3 : i.val = 3
    · simpa [h0, h1, h2, h3, deployedRootEventBudget, uniformChallenge] using
        deployedX3RootSet_measure_le_shape (ursOfAugmentedBasis shape.k basis) rfl
          (family.vk basis) (family.instanceCommitment basis) actual.1.proof.1
          (wrappedPreIpaRecord actual) witness.batches
    by_cases h4 : i.val = 4
    · simpa [h0, h1, h2, h3, h4, deployedRootEventBudget, uniformChallenge] using
        deployedX2RootSet_measure_le_shape (ursOfAugmentedBasis shape.k basis) rfl
          (family.vk basis) (family.instanceCommitment basis) actual.1.proof.1
          (wrappedPreIpaRecord actual) witness.batches
    · simpa [h0, h1, h2, h3, h4, deployedRootEventBudget, uniformChallenge] using
        deployedX1AllRootSet_measure_le (ursOfAugmentedBasis shape.k basis) rfl
          (family.vk basis) (family.instanceCommitment basis) actual.1.proof.1
          (wrappedPreIpaRecord actual) witness.batches
  | inr relation => simp [deployedRootBad, hout, deployedRootEventBudget]

/-- The event budgets sum to the conservative shape budget. -/
theorem deployedRootEventBudget_sum_le (shape : Shape) :
    (∑ i : Fin 6, deployedRootEventBudget shape i) <=
      algebraicRootBudget shape shape.k := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
    Fin.sum_univ_succ, Fin.sum_univ_one]
  norm_num [deployedRootEventBudget, algebraicRootBudget]
  simp only [div_eq_mul_inv]
  ring_nf
  exact le_rfl

/-- **Transcript-stage causality for deployed root data.** The bad set for event `i` is determined
by oracle answers at transcripts strictly shorter than its own squeeze prefix. This is the natural
property exported by a sequential Fiat–Shamir implementation: later answers, including the answer
being priced, cannot affect data already emitted before that squeeze. -/
def DeployedRootPrefixDetermined (family : ComputedAlgebraicFSFamily shape)
    (outcome : DeployedRootOutcomeProvider family) : Prop :=
  forall basis (i : Fin 6)
    (O O' : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp),
    (forall t : BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k),
      t.val.length < preIpaLen shape family.init.length (deployedRootChallengeIndex i) ->
        O t = O' t) ->
    deployedRootBad family outcome basis ((wrappedAdversary family basis).run O) O i =
      deployedRootBad family outcome basis ((wrappedAdversary family basis).run O') O' i

/-- The causal consequence needed by `PinnedRootEvent`: reprogramming a root event's own squeeze
answer leaves that event's bad set unchanged.

Bad sets may consume anything fixed before the squeeze: the prefix, the earlier squeeze answers,
and the retained representations. Only the answer being priced is barred. Earlier answers need
naming separately because halo2 never reabsorbs them, so the prefix alone does not determine
them. -/
def DeployedRootSqueezeInvariance (family : ComputedAlgebraicFSFamily shape)
    (outcome : DeployedRootOutcomeProvider family) : Prop :=
  forall basis (i : Fin 6)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) (v : Fp),
    deployedRootBad family outcome basis
        ((wrappedAdversary family basis).run (Function.update O
          (deployedRootPoint family ((wrappedAdversary family basis).run O) i) v))
        (Function.update O
          (deployedRootPoint family ((wrappedAdversary family basis).run O) i) v) i =
      deployedRootBad family outcome basis ((wrappedAdversary family basis).run O) O i

/-- Strict prefix determination implies the exact reprogramming invariance used by the additive
root-event bound. The updated point has the squeeze prefix's own length, so every strictly shorter
oracle answer is unchanged. -/
theorem deployedRootSqueezeInvariance_of_prefixDetermined
    (family : ComputedAlgebraicFSFamily shape) (outcome : DeployedRootOutcomeProvider family)
    (hcausal : DeployedRootPrefixDetermined family outcome) :
    DeployedRootSqueezeInvariance family outcome := by
  intro basis i O v
  apply hcausal basis i _ O
  intro t ht
  rw [Function.update_apply, if_neg]
  intro hEq
  have hlen : (deployedRootPoint family
      ((wrappedAdversary family basis).run O) i).val.length =
      preIpaLen shape family.init.length (deployedRootChallengeIndex i) := by
    unfold deployedRootPoint
    exact preIpaSqueezePoints_length_eq family.init _
      ((wrappedAdversary family basis).run O).1.proof.2 _
  rw [hEq, hlen] at ht
  exact lt_irrefl _ ht

/-- Reprogramming a point that a computation did not query leaves its result unchanged. -/
theorem OracleComp.run_update_of_not_mem_queries {T F α : Type*} [DecidableEq T]
    (A : OracleComp T F α) (O : T → F) (t : T) (v : F)
    (hfresh : t ∉ A.queries O) :
    A.run (Function.update O t v) = A.run O := by
  induction A with
  | pure a => rfl
  | query q k ih =>
      simp only [OracleComp.queries, List.mem_cons, not_or] at hfresh
      have hqt : q ≠ t := Ne.symm hfresh.1
      rw [OracleComp.run_query, OracleComp.run_query, Function.update_apply, if_neg hqt]
      exact ih (O q) hfresh.2

/-- A representation-carrying root-set computation that stops short of each priced squeeze.

`stage` is an actual oracle computation, `fresh` proves that it has not queried the squeeze point
selected by the deployed run, and `agrees` connects its result to the final direct decoder. The
pinning equation is therefore a consequence of query chronology, not a renamed equality field. -/
structure DeployedRootOnlineTrace (family : ComputedAlgebraicFSFamily shape)
    (outcome : DeployedRootOutcomeProvider family) where
  stage :
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) -> Fin 6 ->
      OracleComp
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k)) Fp (Set Fp)
  agrees : forall (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) (i : Fin 6)
      (O : BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp),
    (stage basis i).run O =
      deployedRootBad family outcome basis ((wrappedAdversary family basis).run O) O i
  fresh : forall (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) (i : Fin 6)
      (O : BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp),
    deployedRootPoint family ((wrappedAdversary family basis).run O) i ∉
      (stage basis i).queries O

/-- The online root trace derives the exact squeeze invariance consumed by probability pricing. -/
theorem DeployedRootOnlineTrace.toSqueezeInvariance
    {family : ComputedAlgebraicFSFamily shape}
    {outcome : DeployedRootOutcomeProvider family}
    (trace : DeployedRootOnlineTrace family outcome) :
    DeployedRootSqueezeInvariance family outcome := by
  intro basis i O v
  let point := deployedRootPoint family ((wrappedAdversary family basis).run O) i
  let updated := Function.update O point v
  calc
    deployedRootBad family outcome basis ((wrappedAdversary family basis).run updated)
        updated i = (trace.stage basis i).run updated :=
      (trace.agrees basis i updated).symm
    _ = (trace.stage basis i).run O :=
      OracleComp.run_update_of_not_mem_queries _ _ _ _ (trace.fresh basis i O)
    _ = deployedRootBad family outcome basis ((wrappedAdversary family basis).run O) O i :=
      trace.agrees basis i O

/-- An online AGM family carrying a concrete batch-or-relation outcome and the emission-stage
trace from which root squeeze invariance is derived. Reverse unbatching may use later challenges;
only each event's own answer is excluded from its retained pre-squeeze set. -/
structure ComputedDeployedRootFSFamily (shape : Shape)
    extends ComputedOnlineMemberFSFamily shape where
  outcome : DeployedRootOutcomeProvider toComputedAlgebraicFSFamily
  rootTrace : DeployedRootOnlineTrace toComputedAlgebraicFSFamily outcome

namespace ComputedDeployedRootFSFamily

/-- The reprogramming invariant consumed by the pinned-root probability theorem. -/
theorem pinned (family : ComputedDeployedRootFSFamily shape) :
    DeployedRootSqueezeInvariance family.toComputedAlgebraicFSFamily family.outcome :=
  family.rootTrace.toSqueezeInvariance

/-- Forget the tighter root data. -/
abbrev toFamily (family : ComputedDeployedRootFSFamily shape) :
    ComputedAlgebraicFSFamily shape := family.toComputedAlgebraicFSFamily

/-- The complete relation producer used by the rewind-free deployed layer: the recursive
extractor's `relationFinder` extended by the `outcome` relation.  Both branches stay in one
data-returning finder — an ∃-closed relation would be vacuous in a prime-order group, where such
a relation always exists, and so could not be charged to DLOG.  Computable relative to
`family.outcome`; #96 must supply a
computable direct-coordinate outcome before applying a concrete DLOG assumption. -/
def deployedRelationFinder (family : ComputedDeployedRootFSFamily shape) :
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) -> family.toFamily.Coins ->
      Option (AlgebraicRelationWitness (F := Fp) basis) :=
  fun basis coins =>
    match family.toFamily.relationFinder basis coins with
    | some relation => some relation
    | none =>
        match family.outcome basis coins.1 with
        | PSum.inl _ => none
        | PSum.inr relation =>
            some (augmentedBasis_ursOfAugmentedBasis shape.k basis ▸
              relation.toAlgebraicRelationWitness)

/-- The combined finder returns an explicit relation on this run. -/
def deployedRelationEvent (family : ComputedDeployedRootFSFamily shape) :
    Set ((AugmentedIndex (2 ^ shape.k) -> VestaG) × family.toFamily.Coins) :=
  {p | (family.deployedRelationFinder p.1 p.2).isSome}

/-- Conditional textbook single-instance DLOG pricing for every relation branch of the recursive
and rewind-free extractors.  The only reduction loss is the additive `1/|Fp|`. -/
theorem deployedRelation_prob_le_of_textbookDL
    (B : VestaG) (family : ComputedDeployedRootFSFamily shape) {bound : ENNReal}
    (hDL : TextbookDLWithCoinsAdvantageLE B family.deployedRelationFinder bound) :
    (PMF.uniformOfFintype
        ((AugmentedIndex (2 ^ shape.k) -> Fp) × family.toFamily.Coins)).toOuterMeasure
        (relSetWithCoins B family.deployedRelationFinder)
      <= (bound + 1 / Fintype.card Fp) :=
  relationWithCoins_prob_le_of_textbookDL B family.deployedRelationFinder hDL

/-- Transfer the complete relation event across a uniform-URS basis identification. -/
theorem deployedRelation_prob_eq_of_uniformURS {Omega : Type*} (setup : PMF Omega)
    (B : VestaG) (family : ComputedDeployedRootFSFamily shape)
    (basisOf : Omega -> AugmentedIndex (2 ^ shape.k) -> VestaG)
    (hURS : OrchardUniformURSIdentification setup shape.k B basisOf) :
    (independentProductPMF setup
      (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure
        ((fun p => (basisOf p.1, p.2)) ⁻¹' family.deployedRelationEvent) =
      (PMF.uniformOfFintype
        ((AugmentedIndex (2 ^ shape.k) -> Fp) × family.toFamily.Coins)).toOuterMeasure
        (relSetWithCoins B family.deployedRelationFinder) := by
  let coinPMF := PMF.uniformOfFintype family.toFamily.Coins
  have hprod :
      (independentProductPMF setup coinPMF).map (fun p => (basisOf p.1, p.2)) =
        (independentProductPMF
          (PMF.uniformOfFintype (AugmentedIndex (2 ^ shape.k) -> Fp)) coinPMF).map
            (fun p => (scalarBasis B p.1, p.2)) := by
    calc
      _ = independentProductPMF (setup.map basisOf) coinPMF :=
        independentProductPMF_map_left setup coinPMF basisOf
      _ = independentProductPMF
          ((PMF.uniformOfFintype (AugmentedIndex (2 ^ shape.k) -> Fp)).map (scalarBasis B))
          coinPMF := congrArg (fun p => independentProductPMF p coinPMF) hURS
      _ = _ := (independentProductPMF_map_left
        (PMF.uniformOfFintype (AugmentedIndex (2 ^ shape.k) -> Fp)) coinPMF
        (scalarBasis B)).symm
  have hmeasure := congrArg
    (fun p : PMF ((AugmentedIndex (2 ^ shape.k) -> VestaG) × family.toFamily.Coins) =>
      p.toOuterMeasure family.deployedRelationEvent) hprod
  change ((independentProductPMF setup coinPMF).map
      (fun p => (basisOf p.1, p.2))).toOuterMeasure family.deployedRelationEvent =
    ((independentProductPMF
      (PMF.uniformOfFintype (AugmentedIndex (2 ^ shape.k) -> Fp)) coinPMF).map
        (fun p => (scalarBasis B p.1, p.2))).toOuterMeasure
          family.deployedRelationEvent at hmeasure
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply] at hmeasure
  calc
    _ = (independentProductPMF
          (PMF.uniformOfFintype (AugmentedIndex (2 ^ shape.k) -> Fp)) coinPMF).toOuterMeasure
          ((fun p => (scalarBasis B p.1, p.2)) ⁻¹' family.deployedRelationEvent) := hmeasure
    _ = (PMF.uniformOfFintype
          ((AugmentedIndex (2 ^ shape.k) -> Fp) × family.toFamily.Coins)).toOuterMeasure
          (relSetWithCoins B family.deployedRelationFinder) := by
      rw [independentProductPMF_uniform]
      congr 1
      ext p
      simp only [Set.mem_preimage, deployedRelationEvent, Set.mem_setOf_eq, relSetWithCoins,
        Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Generator-random-oracle form of the complete deployed relation bound. -/
theorem deployedRelation_prob_le_of_generatorRO_textbookDL
    {T : Type*} [DecidableEq T] (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ shape.k) -> T) (hquery : Function.Injective query)
    (family : ComputedDeployedRootFSFamily shape) {bound : ENNReal}
    (hDL : TextbookDLWithCoinsAdvantageLE B family.deployedRelationFinder bound) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          family.deployedRelationEvent)
      <= (bound + 1 / Fintype.card Fp) := by
  rw [family.deployedRelation_prob_eq_of_uniformURS
    (orchardGeneratorROSetup query) B (orchardGeneratorROBasis query)
    (orchard_uniformURSIdentification_of_generatorRO shape.k B hB query hquery)]
  exact family.deployedRelation_prob_le_of_textbookDL B hDL

/-- The concrete deployed root events, ready for the additive coupling theorem. -/
noncomputable def pinnedRoots (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) :
    PinnedRootFamily (wrappedAdversary family.toFamily basis) 6 where
  event i :=
    { point := fun pnu => deployedRootPoint family.toFamily pnu i
      bad := fun pnu O => deployedRootBad family.toFamily family.outcome basis pnu O i
      budget := deployedRootEventBudget shape i
      measure_le := fun pnu O =>
        deployedRootBad_measure_le family.toFamily family.outcome basis pnu O i
      pinned := fun O v => family.pinned basis i O v }

/-- The six good-root facts exposed when the concrete root family does not land. -/
structure DeployedGoodRoots (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)
    (witness : DeployedBatchWitness family.toFamily basis
      ((wrappedAdversary family.toFamily basis).run O)) : Prop where
  xi : wrappedPreIpaReads ((wrappedAdversary family.toFamily basis).run O) 9 ∉
    deployedRootBad family.toFamily family.outcome basis
      ((wrappedAdversary family.toFamily basis).run O) O 0
  z : wrappedPreIpaReads ((wrappedAdversary family.toFamily basis).run O) 10 ∉
    deployedRootBad family.toFamily family.outcome basis
      ((wrappedAdversary family.toFamily basis).run O) O 1
  x4 : wrappedPreIpaReads ((wrappedAdversary family.toFamily basis).run O) 8 ∉
    deployedRootBad family.toFamily family.outcome basis
      ((wrappedAdversary family.toFamily basis).run O) O 2
  x3 : wrappedPreIpaReads ((wrappedAdversary family.toFamily basis).run O) 7 ∉
    deployedRootBad family.toFamily family.outcome basis
      ((wrappedAdversary family.toFamily basis).run O) O 3
  x2 : wrappedPreIpaReads ((wrappedAdversary family.toFamily basis).run O) 6 ∉
    deployedRootBad family.toFamily family.outcome basis
      ((wrappedAdversary family.toFamily basis).run O) O 4
  x1 : wrappedPreIpaReads ((wrappedAdversary family.toFamily basis).run O) 5 ∉
    deployedRootBad family.toFamily family.outcome basis
      ((wrappedAdversary family.toFamily basis).run O) O 5

/-- Non-landing of the concrete family is exactly goodness of all six explicit root sets. -/
theorem goodRoots_of_not_landing (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)
    (witness : DeployedBatchWitness family.toFamily basis
      ((wrappedAdversary family.toFamily basis).run O))
    (_hout : family.outcome basis O =
      PSum.inl witness)
    (hnot : ¬(family.pinnedRoots basis).Landing O) :
    DeployedGoodRoots family basis O witness := by
  have hgood (i : Fin 6) : ¬((family.pinnedRoots basis).event i).Landing O := by
    intro hi
    exact hnot ⟨i, hi⟩
  have hroot (i : Fin 6) :
      wrappedPreIpaReads ((wrappedAdversary family.toFamily basis).run O)
          (deployedRootChallengeIndex i) ∉
        deployedRootBad family.toFamily family.outcome basis
          ((wrappedAdversary family.toFamily basis).run O) O i := by
    have hi := hgood i
    change O (deployedRootPoint family.toFamily
        ((wrappedAdversary family.toFamily basis).run O) i) ∉
      deployedRootBad family.toFamily family.outcome basis
        ((wrappedAdversary family.toFamily basis).run O) O i at hi
    have hpoint := deployedRootPoint_run family.toFamily basis O i
    rw [hpoint] at hi
    simpa [wrappedPreIpaReads_run] using hi
  refine { xi := ?_, z := ?_, x4 := ?_, x3 := ?_, x2 := ?_, x1 := ?_ }
  · simpa [deployedRootChallengeIndex] using hroot (0 : Fin 6)
  · simpa [deployedRootChallengeIndex] using hroot (1 : Fin 6)
  · simpa [deployedRootChallengeIndex] using hroot (2 : Fin 6)
  · simpa [deployedRootChallengeIndex] using hroot (3 : Fin 6)
  · simpa [deployedRootChallengeIndex] using hroot (4 : Fin 6)
  · simpa [deployedRootChallengeIndex] using hroot (5 : Fin 6)

/-- The root family's total direct budget is `algebraicRootBudget`. -/
theorem pinnedRoots_budget_le (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) :
    (∑ i : Fin 6, ((family.pinnedRoots basis).event i).budget) <=
      algebraicRootBudget shape shape.k :=
  deployedRootEventBudget_sum_le shape

end ComputedDeployedRootFSFamily

end Zcash.Snark
