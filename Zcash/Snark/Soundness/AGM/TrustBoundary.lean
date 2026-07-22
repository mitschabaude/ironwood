import Zcash.Snark.Soundness.AGM.BindingSignature
import Zcash.Snark.Soundness.AGM.Capstone
import Zcash.Snark.Soundness.AGM.ProbabilityVesta
import Zcash.Snark.Soundness.Forking.Adversary
import Zcash.Snark.Soundness.Compose67
import Zcash.Snark.Soundness.Multiopen.BudgetedExtraction
import Zcash.Snark.Soundness.VestaBudget
import Mathlib.Util.AssertNoSorry

/-!
# AGM trust-boundary checks

The AGM kernels compute representations, openings, relations, certificates, and deployed instances
as data. `assert_no_sorry` checks the executable producer and consumer path; the guarded reports
record its proof dependencies.
-/

open Zcash.Snark

assert_no_sorry discreteLogOfBasis_of_relation
assert_no_sorry DLChallengeGame.solveFromRelation
assert_no_sorry fixedSlotExtractOrMiss
assert_no_sorry AugmentedRelationWitness.toAlgebraicRelationWitness
assert_no_sorry relationWitnessOfCollision
assert_no_sorry discreteLogOfAugmentedRelationAtChallenge
assert_no_sorry separateOrRelationWitness
assert_no_sorry relationOfFoldGensWitness
assert_no_sorry deployedLeafPeelWitness
assert_no_sorry deployedToAcceptVWitness
assert_no_sorry algebraicRelationOfDeployedAccept
assert_no_sorry AlgebraicProver.toProver
assert_no_sorry AlgebraicDForkCert.toDForkCert
assert_no_sorry algebraicProverAccept_forkValid
assert_no_sorry deployedAlgebraicForkingRelation
assert_no_sorry deployed_forking_relation_shifted
assert_no_sorry deployedAlgebraicForkingRelation_shifted
assert_no_sorry deployedAlgebraicForkingFixedSlot
assert_no_sorry DeployedAlgebraicForkingInstance.run
assert_no_sorry DeployedAlgebraicForkingInstance.ProducesRelation
assert_no_sorry deployedAlgebraicRelationProduced
assert_no_sorry deployedAlgebraicRelationEvent
assert_no_sorry deployedAlgebraicRelationFinder
assert_no_sorry deployedAlgebraicRelationFinder_isSome_iff
assert_no_sorry deployedAlgebraicRelation
assert_no_sorry deployedAlgebraicRelationWitness
assert_no_sorry orchardDeployedAlgebraicForkingFixedSlot
assert_no_sorry orchardDeployedRelationSet
assert_no_sorry OrchardUniformURSIdentification
assert_no_sorry orchardGeneratorROSetup
assert_no_sorry orchardGeneratorROBasis
assert_no_sorry orchard_uniformURSIdentification_of_generatorRO
assert_no_sorry recursiveAlgebraicForkFrom
assert_no_sorry recursiveAlgebraicForkFrom_realizes
assert_no_sorry algebraicForkCertAttempt
assert_no_sorry algebraicForkCertAttempt_valid
assert_no_sorry computedDeployedAlgebraicInstance
assert_no_sorry computedAlgebraicInstanceFailure_measure_le
assert_no_sorry AlgebraicRelationWitness.augment
assert_no_sorry DeployedAlgebraicForkingInstance.runRelation
assert_no_sorry DeployedAlgebraicForkingInstance.runRelation_isSome_of_mismatch
assert_no_sorry DeployedAlgebraicForkingInstance.runToSnark
assert_no_sorry ComputedAlgebraicFSFamily.relationFinder
assert_no_sorry ComputedAlgebraicFSFamily.relationFinder_isSome_of_bindingWin
assert_no_sorry ComputedAlgebraicFSFamily.snarkRelationFinder
assert_no_sorry ComputedAlgebraicFSFamily.snarkRelation_prob_le_of_textbookDL
assert_no_sorry ComputedAlgebraicFSFamily.acceptExtractionFailure_measure_le
assert_no_sorry ComputedAlgebraicFSFamily.snarkNonRelationFailure
assert_no_sorry ComputedAlgebraicFSFamily.snarkNonRelationFailure_measure_le
assert_no_sorry ComputedAlgebraicFSFamily.snarkFailure_prob_le_of_textbookDL
assert_no_sorry ComputedAlgebraicFSFamily.snarkFailure_prob_le_of_textbookDL_full
assert_no_sorry ComputedAlgebraicFSFamily.snarkFailure_prob_le_of_uniformURS_textbookDL
assert_no_sorry ComputedAlgebraicFSFamily.snarkFailure_prob_le_of_generatorRO_textbookDL
assert_no_sorry ComputedAlgebraicFSFamily.binding_prob_le_of_textbookDL
assert_no_sorry ComputedAlgebraicFSFamily.binding_prob_le_of_uniformURS_textbookDL
assert_no_sorry ComputedAlgebraicFSFamily.binding_prob_le_of_generatorRO_textbookDL
assert_no_sorry ComputedAlgebraicFSFamily.ReductionEfficient
assert_no_sorry ComputedAlgebraicFSFamily.reductionEfficient_exists
assert_no_sorry ComputedAlgebraicFSFamily.instanceAttempt_runs_eq
assert_no_sorry ComputedAlgebraicFSFamily.reductionEfficient_exponential
assert_no_sorry ComputedAlgebraicFSFamily.DiscreteLogRelationHardFor
assert_no_sorry ComputedAlgebraicFSFamily.knowledgeSoundness_under_DL
assert_no_sorry ComputedAlgebraicFSFamily.binding_under_DL
assert_no_sorry bindingWin_unbounded_measure_le
assert_no_sorry queryCharge
assert_no_sorry queryCharge_sum_mul_le
assert_no_sorry le_queryCharge_of_mem_queries
assert_no_sorry mem_queries_dedup
assert_no_sorry applyUpdates_apply_mem_nodup
assert_no_sorry queryCharge_sum_mul_le_table_budget
assert_no_sorry steeredCharge_context_sum_mul_le
assert_no_sorry steeredCharge_context_sum_mul_le_table_budget
assert_no_sorry steeredCharge_sum_mul_le
assert_no_sorry scanCandidate_self
assert_no_sorry self_mem_goodChallenges_iff
assert_no_sorry scanRank_insert_erase
assert_no_sorry scanRank_insert_eq_filter
assert_no_sorry goodChallengesAt
assert_no_sorry OracleComp.queries_queryList
assert_no_sorry recursiveAlgebraicForkFrom_node_runs_le_gated
assert_no_sorry OracleComp.queries_bind
assert_no_sorry OracleComp.mem_queries_completing
assert_no_sorry scanCandidateAt
assert_no_sorry scanCandidateAt_fork
assert_no_sorry scanCandidateAt_update
assert_no_sorry goodChallengesAt_fork
assert_no_sorry goodChallengesAt_update
assert_no_sorry sum_card_scanRank_erase_lt_le
assert_no_sorry OracleComp.restrictSum
assert_no_sorry fsWinsFull_restrictSum_le
assert_no_sorry ComputedAlgebraicFSFamilyRand.determinize
assert_no_sorry ComputedAlgebraicFSFamilyRand.binding_prob_le_of_textbookDL_rand
assert_no_sorry ComputedAlgebraicFSFamilyRand.snarkFailure_prob_le_of_textbookDL_rand
assert_no_sorry ComputedAlgebraicFSFamily.snarkFailureEvent
assert_no_sorry ComputedAlgebraicFSFamilyRand.foldedRelationFinder
assert_no_sorry ComputedAlgebraicFSFamilyRand.binding_prob_le_of_foldedTextbookDL_rand
assert_no_sorry ComputedAlgebraicFSFamilyRand.foldedSnarkRelationFinder
assert_no_sorry ComputedAlgebraicFSFamilyRand.snarkFailure_prob_le_of_foldedTextbookDL_rand
assert_no_sorry ComputedAlgebraicFSFamilyUnbounded.globalReachSet
assert_no_sorry ComputedAlgebraicFSFamilyUnbounded.reachSet_subset_globalReachSet
assert_no_sorry ComputedAlgebraicFSFamilyUnbounded.splitFamilyRand
assert_no_sorry ComputedAlgebraicFSFamilyUnbounded.run_splitFamilyRand_adversary
assert_no_sorry ComputedAlgebraicFSFamilyUnbounded.binding_prob_le_of_unbounded_foldedTextbookDL
assert_no_sorry ComputedAlgebraicFSFamilyUnbounded.snarkFailure_prob_le_of_unbounded_foldedTextbookDL
assert_no_sorry uniformURS_basis_transfer
assert_no_sorry ComputedAlgebraicFSFamilyUnbounded.snarkFailureEventUnbounded
assert_no_sorry ComputedAlgebraicFSFamilyUnbounded.snarkFailure_prob_le_of_unbounded_uniformURS_textbookDL
assert_no_sorry ComputedAlgebraicFSFamilyUnbounded.snarkFailure_prob_le_of_unbounded_generatorRO_textbookDL
assert_no_sorry ComputedAlgebraicFSFamilyUnbounded.bindingEventUnbounded
assert_no_sorry ComputedAlgebraicFSFamilyUnbounded.binding_prob_le_of_unbounded_uniformURS_textbookDL
assert_no_sorry ComputedAlgebraicFSFamilyUnbounded.binding_prob_le_of_unbounded_generatorRO_textbookDL
assert_no_sorry ComputedAlgebraicFSFamilyUnboundedRand.determinize
assert_no_sorry ComputedAlgebraicFSFamilyUnboundedRand.globalReachSet
assert_no_sorry ComputedAlgebraicFSFamilyUnboundedRand.reachSet_subset_globalReachSet
assert_no_sorry ComputedAlgebraicFSFamilyUnboundedRand.splitFamilyRand
assert_no_sorry ComputedAlgebraicFSFamilyUnboundedRand.run_splitFamilyRand_adversary
assert_no_sorry ComputedAlgebraicFSFamilyUnboundedRand.binding_prob_le_of_unboundedRand_foldedTextbookDL
assert_no_sorry ComputedAlgebraicFSFamilyUnboundedRand.snarkFailure_prob_le_of_unboundedRand_foldedTextbookDL
assert_no_sorry ComputedAlgebraicFSFamilyUnboundedRand.snarkFailureEventUnboundedRand
assert_no_sorry ComputedAlgebraicFSFamilyUnboundedRand.snarkFailure_prob_le_of_unboundedRand_uniformURS_textbookDL
assert_no_sorry ComputedAlgebraicFSFamilyUnboundedRand.snarkFailure_prob_le_of_unboundedRand_generatorRO_textbookDL
assert_no_sorry ComputedAlgebraicFSFamilyUnboundedRand.bindingEventUnboundedRand
assert_no_sorry ComputedAlgebraicFSFamilyUnboundedRand.binding_prob_le_of_unboundedRand_uniformURS_textbookDL
assert_no_sorry ComputedAlgebraicFSFamilyUnboundedRand.binding_prob_le_of_unboundedRand_generatorRO_textbookDL
assert_no_sorry recursiveAlgebraicForkFrom_node_runs_le
assert_no_sorry recursiveAlgebraicFork_sum_runs_le_unconditional
assert_no_sorry recursiveAlgebraicFork_oracle_tape_sum_runs_le_unconditional
assert_no_sorry recursiveAlgebraicForkFrom_sum_runs_le_of_forkSpread
assert_no_sorry recursiveAlgebraicFork_sum_runs_le_of_forkSpread
assert_no_sorry AlgebraicPoint.point_eq_components
assert_no_sorry Msm.eval_repr
assert_no_sorry RepresentedMultiopen.ofCoveredList
assert_no_sorry AlgebraicWfProof.ofRepresented
assert_no_sorry assembleQueries_points_mem
assert_no_sorry constructIntermediateSets_ref_mem
assert_no_sorry multiopenMsm_points_mem
assert_no_sorry AlgebraicWfProof.ofStandard
assert_no_sorry OracleComp.reachSet
assert_no_sorry OracleComp.run_congr_reachSet
assert_no_sorry OracleComp.restrictTo
assert_no_sorry OracleComp.splitDomain
assert_no_sorry finite_domain_restriction
assert_no_sorry fsWinsFull_mapDomain_measure_eq
assert_no_sorry fsWinsFull_splitDomain
assert_no_sorry fsWinsFull_unbounded_measure_le
assert_no_sorry truncateTranscript
assert_no_sorry Zcash.Security.BindingSignature.NontrivialRelation.toAlgebraicRelationWitness
assert_no_sorry Zcash.Security.BindingSignature.NontrivialRelation.toDiscreteLog
assert_no_sorry Zcash.Security.BindingSignature.orchardImbalanceToDiscreteLog
assert_no_sorry Zcash.Security.BindingSignature.saplingImbalanceToDiscreteLog

/-- info: 'Zcash.Snark.discreteLogOfBasis_of_relation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms discreteLogOfBasis_of_relation

/-- info: 'Zcash.Snark.DLChallengeGame.solveFromRelation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DLChallengeGame.solveFromRelation

/-- info: 'Zcash.Snark.fixedSlotExtractOrMiss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fixedSlotExtractOrMiss

/-- info: 'Zcash.Snark.AugmentedRelationWitness.toAlgebraicRelationWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AugmentedRelationWitness.toAlgebraicRelationWitness

/-- info: 'Zcash.Snark.relationWitnessOfCollision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms relationWitnessOfCollision

/-- info: 'Zcash.Snark.discreteLogOfAugmentedRelationAtChallenge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms discreteLogOfAugmentedRelationAtChallenge

/-- info: 'Zcash.Snark.separateOrRelationWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms separateOrRelationWitness

/-- info: 'Zcash.Snark.relationOfFoldGensWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms relationOfFoldGensWitness

/-- info: 'Zcash.Snark.deployedLeafPeelWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms deployedLeafPeelWitness

/-- info: 'Zcash.Snark.deployedToAcceptVWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms deployedToAcceptVWitness

/-- info: 'Zcash.Snark.algebraicRelationOfDeployedAccept' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms algebraicRelationOfDeployedAccept

/-- info: 'Zcash.Snark.deployedAlgebraicForkingRelation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms deployedAlgebraicForkingRelation

/-- info: 'Zcash.Snark.deployedAlgebraicForkingFixedSlot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms deployedAlgebraicForkingFixedSlot

/-- info: 'Zcash.Snark.deployedAlgebraicRelationFinder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms deployedAlgebraicRelationFinder

/-- info: 'Zcash.Snark.deployedAlgebraicRelation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms deployedAlgebraicRelation

/-- info: 'Zcash.Snark.deployedAlgebraicRelationWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms deployedAlgebraicRelationWitness

/-- info: 'Zcash.Security.BindingSignature.NontrivialRelation.toAlgebraicRelationWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Zcash.Security.BindingSignature.NontrivialRelation.toAlgebraicRelationWitness

/-- info: 'Zcash.Security.BindingSignature.NontrivialRelation.toDiscreteLog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Zcash.Security.BindingSignature.NontrivialRelation.toDiscreteLog

/-! The probability layer contains theorems rather than data-producing definitions. The checks below
pin its proof dependencies. -/

assert_no_sorry hitProb_ge_inv_card
assert_no_sorry relSet_card_le_succSet_card
assert_no_sorry reduction_advantage_ge
assert_no_sorry relation_prob_le_of_DL
assert_no_sorry winSet_card
assert_no_sorry textbook_winProb_eq_succProb
assert_no_sorry relation_prob_le_of_textbookDL
assert_no_sorry orchard_relation_prob_le_of_DL
assert_no_sorry orchard_reduction_advantage_ge
assert_no_sorry orchard_relation_prob_le_of_textbookDL
assert_no_sorry commitment_binding_prob_le_of_textbookDL
assert_no_sorry orchard_deployed_reduction_advantage_ge
assert_no_sorry orchard_deployed_relation_prob_le_of_textbookDL
assert_no_sorry orchard_deployed_relation_set_eq_relSet
assert_no_sorry orchard_deployed_relation_event_prob_le_of_textbookDL
assert_no_sorry orchard_deployed_relation_prob_eq_of_uniformURS
assert_no_sorry orchard_deployed_relation_prob_le_of_uniformURS_textbookDL
assert_no_sorry orchard_deployed_relation_prob_le_of_generatorRO_textbookDL

-- The multiopen value-check chain (issue #18): the deployed value check derived from the nested
-- forking floors, the x₁ member un-batch on top of it, and the terminal with `hadvice`/`hinstance`
-- produced rather than assumed (`Soundness.Multiopen.ValueCheckX3`, `Soundness.Vesta`).
assert_no_sorry deployed_value_check_node_binding
assert_no_sorry deployed_member_node_binding
assert_no_sorry orchard_verifier_vesta_member_constraint_derived

-- The forking-extraction ∘ decoded-capstone composition (`Soundness.Compose67`): the algebraic
-- clean opening identified with the deployed capstone's shape (`ipaRelation_deployed_of_instance`),
-- the witness-tie composition (`member_snark_of_instance`), and the computed-path soundness
-- endpoint (`orchard_verifier_sound_vesta_computed`) that concludes the plain `SnarkRelation` with
-- NO `ExtractableFromAcceptance` hypothesis. On the witness tie the opened-value shift is derived
-- (`shift_eq_zero_of_openings_agree`), so `hshift` survives only on the standalone single-opening
-- bridge. `snarkExtraction_prob_le_of_generatorRO_textbookDL` is the CONDITIONAL knowledge-error
-- bound: the SNARK-extraction failure is contained in the clean-opening failure and inherits its
-- `(Q+k)·3/|Fp| + (Q+1)/|Fp| + |basis|·ε` bound, conditional on `hExtract` (clean opening ⟹
-- extraction). Discharging `hExtract` — coupling the AGM family's coin measure to the multiopen
-- budget below — is the remaining reconciliation.
assert_no_sorry ipaRelation_deployed_of_instance
assert_no_sorry member_snark_of_instance
assert_no_sorry snarkRelation_of_memberColumns
assert_no_sorry orchard_verifier_sound_vesta_computed
assert_no_sorry snarkExtraction_prob_le_of_generatorRO_textbookDL
assert_no_sorry instanceAttempt_provenance
assert_no_sorry ipaRelation_deployed_of_openings_agree
assert_no_sorry shift_eq_zero_of_openings_agree

-- The budgeted multiopen extraction (`Soundness.Multiopen.FloorBudget`,
-- `Soundness.Multiopen.BudgetedExtraction`): the heavy-fiber Markov descent
-- (`uniformOfFintype_heavy_fiber_lt`) replaces the `∀`-over-runs squeeze floors of the value-check
-- and member cores with a single joint accept floor at honest-base thresholds, the runs pinned by
-- the canonical selectors; `deployed_member_budget` is the combined soundness budget — the joint
-- accept measure sits within the four-threshold budget, or every decoded member column takes its
-- claimed evaluation (or a computed relation exists).
assert_no_sorry uniformOfFintype_heavy_fiber_lt
assert_no_sorry deployed_value_check_node_binding_budgeted
assert_no_sorry deployed_member_node_binding_budgeted
assert_no_sorry deployed_member_budget

-- The budgeted capstone and computed path (`Soundness.VestaBudget`): the derived deployed member
-- capstone with the run-quantified floors replaced by the joint accept floor, and the computed-path
-- endpoint with the member decode constructed and `hquot` derived — no extraction-data hypothesis.
assert_no_sorry deployed_member_node_binding_at_point_budgeted
assert_no_sorry orchard_verifier_vesta_member_constraint_budgeted
assert_no_sorry member_relation_or_dlr_of_instance_budgeted
assert_no_sorry member_snark_of_instance_budgeted
assert_no_sorry orchard_verifier_sound_vesta_budgeted

/-- info: 'Zcash.Snark.orchard_verifier_vesta_member_constraint_budgeted' depends on axioms:
[propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms orchard_verifier_vesta_member_constraint_budgeted

/-- info: 'Zcash.Snark.orchard_verifier_sound_vesta_budgeted' depends on axioms: [propext,
Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms orchard_verifier_sound_vesta_budgeted

/-- info: 'Zcash.Snark.uniformOfFintype_heavy_fiber_lt' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uniformOfFintype_heavy_fiber_lt

/-- info: 'Zcash.Snark.deployed_member_node_binding_budgeted' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms deployed_member_node_binding_budgeted

/-- info: 'Zcash.Snark.deployed_member_budget' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms deployed_member_budget

/-- info: 'Zcash.Snark.ipaRelation_deployed_of_openings_agree' depends on axioms: [propext,
Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms ipaRelation_deployed_of_openings_agree

/-- info: 'Zcash.Snark.shift_eq_zero_of_openings_agree' depends on axioms: [propext,
Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms shift_eq_zero_of_openings_agree

/-- info: 'Zcash.Snark.relation_prob_le_of_textbookDL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms relation_prob_le_of_textbookDL

/-! The Vesta endpoints also depend on CompElliptic's `native_decide` point-count axiom through the
`Module Fp VestaG` instance. The checks below record that extra dependency. -/

/-- info: 'Zcash.Snark.orchard_relation_prob_le_of_textbookDL' depends on axioms: [propext,
Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms orchard_relation_prob_le_of_textbookDL

/-- info: 'Zcash.Snark.commitment_binding_prob_le_of_textbookDL' depends on axioms: [propext,
Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms commitment_binding_prob_le_of_textbookDL

/-- info: 'Zcash.Snark.orchard_deployed_relation_prob_le_of_textbookDL' depends on axioms: [propext,
Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms orchard_deployed_relation_prob_le_of_textbookDL

/-- info: 'Zcash.Snark.orchard_deployed_relation_prob_le_of_uniformURS_textbookDL' depends on axioms:
[propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms orchard_deployed_relation_prob_le_of_uniformURS_textbookDL

/-- info: 'Zcash.Snark.orchard_uniformURSIdentification_of_generatorRO' depends on axioms: [propext,
Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms orchard_uniformURSIdentification_of_generatorRO

/-- info: 'Zcash.Snark.orchard_deployed_relation_prob_le_of_generatorRO_textbookDL' depends on axioms:
[propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms orchard_deployed_relation_prob_le_of_generatorRO_textbookDL

/-! The adversary bounds charge query loss, `z = 0`, and fixed-slot DL. Vesta inherits
CompElliptic's point-count axiom. A polynomial AFK call bound is unproved; PPT time is external. -/

/-- info: 'Zcash.Snark.ComputedAlgebraicFSFamily.binding_prob_le_of_textbookDL' depends on axioms:
[propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputedAlgebraicFSFamily.binding_prob_le_of_textbookDL

/-- info: 'Zcash.Snark.ComputedAlgebraicFSFamily.binding_prob_le_of_uniformURS_textbookDL' depends on
axioms: [propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputedAlgebraicFSFamily.binding_prob_le_of_uniformURS_textbookDL

/-- info: 'Zcash.Snark.ComputedAlgebraicFSFamily.binding_prob_le_of_generatorRO_textbookDL' depends on
axioms: [propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputedAlgebraicFSFamily.binding_prob_le_of_generatorRO_textbookDL

/-- info: 'Zcash.Snark.ComputedAlgebraicFSFamilyRand.binding_prob_le_of_textbookDL_rand' depends on
axioms: [propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputedAlgebraicFSFamilyRand.binding_prob_le_of_textbookDL_rand

/-- info: 'Zcash.Snark.ComputedAlgebraicFSFamilyRand.binding_prob_le_of_foldedTextbookDL_rand' depends
on axioms: [propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputedAlgebraicFSFamilyRand.binding_prob_le_of_foldedTextbookDL_rand

/-- info: 'Zcash.Snark.ComputedAlgebraicFSFamilyUnbounded.binding_prob_le_of_unbounded_foldedTextbookDL'
depends on axioms: [propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms
  ComputedAlgebraicFSFamilyUnbounded.binding_prob_le_of_unbounded_foldedTextbookDL

/-- info: 'Zcash.Snark.ComputedAlgebraicFSFamilyRand.snarkFailure_prob_le_of_foldedTextbookDL_rand'
depends on axioms: [propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputedAlgebraicFSFamilyRand.snarkFailure_prob_le_of_foldedTextbookDL_rand

/-- info: 'Zcash.Snark.ComputedAlgebraicFSFamilyUnbounded.snarkFailure_prob_le_of_unbounded_foldedTextbookDL'
depends on axioms: [propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms
  ComputedAlgebraicFSFamilyUnbounded.snarkFailure_prob_le_of_unbounded_foldedTextbookDL

/-- info: 'Zcash.Snark.ComputedAlgebraicFSFamilyUnbounded.snarkFailure_prob_le_of_unbounded_generatorRO_textbookDL'
depends on axioms: [propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms
  ComputedAlgebraicFSFamilyUnbounded.snarkFailure_prob_le_of_unbounded_generatorRO_textbookDL

/-- info: 'Zcash.Snark.ComputedAlgebraicFSFamilyUnbounded.binding_prob_le_of_unbounded_generatorRO_textbookDL'
depends on axioms: [propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms
  ComputedAlgebraicFSFamilyUnbounded.binding_prob_le_of_unbounded_generatorRO_textbookDL

/-- info: 'Zcash.Snark.ComputedAlgebraicFSFamilyUnboundedRand.snarkFailure_prob_le_of_unboundedRand_generatorRO_textbookDL'
depends on axioms: [propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms
  ComputedAlgebraicFSFamilyUnboundedRand.snarkFailure_prob_le_of_unboundedRand_generatorRO_textbookDL

/-- info: 'Zcash.Snark.ComputedAlgebraicFSFamilyUnboundedRand.binding_prob_le_of_unboundedRand_generatorRO_textbookDL'
depends on axioms: [propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms
  ComputedAlgebraicFSFamilyUnboundedRand.binding_prob_le_of_unboundedRand_generatorRO_textbookDL

/-- info: 'Zcash.Snark.ComputedAlgebraicFSFamilyUnboundedRand.snarkFailure_prob_le_of_unboundedRand_uniformURS_textbookDL'
depends on axioms: [propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms
  ComputedAlgebraicFSFamilyUnboundedRand.snarkFailure_prob_le_of_unboundedRand_uniformURS_textbookDL

/-- info: 'Zcash.Snark.ComputedAlgebraicFSFamilyUnboundedRand.binding_prob_le_of_unboundedRand_uniformURS_textbookDL'
depends on axioms: [propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms
  ComputedAlgebraicFSFamilyUnboundedRand.binding_prob_le_of_unboundedRand_uniformURS_textbookDL

/-- info: 'Zcash.Snark.recursiveAlgebraicFork_oracle_tape_sum_runs_le_unconditional' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms recursiveAlgebraicFork_oracle_tape_sum_runs_le_unconditional

/-- info: 'Zcash.Snark.recursiveAlgebraicFork_sum_runs_le_of_forkSpread' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms recursiveAlgebraicFork_sum_runs_le_of_forkSpread

/-- info: 'Zcash.Snark.bindingWin_unbounded_measure_le' depends on axioms: [propext,
Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms bindingWin_unbounded_measure_le

/-! The executable producer returns the deployed `S ⊕' relation` dichotomy. -/

/-- info: 'Zcash.Snark.DeployedAlgebraicForkingInstance.runToSnark' depends on axioms: [propext,
Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms DeployedAlgebraicForkingInstance.runToSnark

/-- info: 'Zcash.Snark.ComputedAlgebraicFSFamily.snarkRelation_prob_le_of_textbookDL' depends on
axioms: [propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputedAlgebraicFSFamily.snarkRelation_prob_le_of_textbookDL

/-- info: 'Zcash.Snark.ComputedAlgebraicFSFamily.snarkFailure_prob_le_of_textbookDL' depends on
axioms: [propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputedAlgebraicFSFamily.snarkFailure_prob_le_of_textbookDL

/-- info: 'Zcash.Snark.ComputedAlgebraicFSFamily.snarkFailure_prob_le_of_textbookDL_full' depends on
axioms: [propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputedAlgebraicFSFamily.snarkFailure_prob_le_of_textbookDL_full

/-- info: 'Zcash.Snark.ComputedAlgebraicFSFamily.snarkFailure_prob_le_of_generatorRO_textbookDL'
depends on axioms: [propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputedAlgebraicFSFamily.snarkFailure_prob_le_of_generatorRO_textbookDL

/-- info: 'Zcash.Snark.ComputedAlgebraicFSFamily.snarkNonRelationFailure_measure_le' depends on
axioms: [propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputedAlgebraicFSFamily.snarkNonRelationFailure_measure_le

/-- info: 'Zcash.Snark.ComputedAlgebraicFSFamily.reductionEfficient_exists' depends on axioms:
[propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputedAlgebraicFSFamily.reductionEfficient_exists

/-- info: 'Zcash.Snark.ComputedAlgebraicFSFamily.reductionEfficient_exponential' depends on axioms:
[propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputedAlgebraicFSFamily.reductionEfficient_exponential

/-- info: 'Zcash.Snark.ComputedAlgebraicFSFamily.knowledgeSoundness_under_DL' depends on axioms:
[propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputedAlgebraicFSFamily.knowledgeSoundness_under_DL

/-- info: 'Zcash.Snark.ComputedAlgebraicFSFamily.binding_under_DL' depends on axioms: [propext,
Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputedAlgebraicFSFamily.binding_under_DL

/-- info: 'Zcash.Snark.ComputedAlgebraicFSFamily.snarkFailure_prob_le_of_uniformURS_textbookDL'
depends on axioms: [propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputedAlgebraicFSFamily.snarkFailure_prob_le_of_uniformURS_textbookDL

/-- info: 'Zcash.Snark.ComputedAlgebraicFSFamilyRand.snarkFailure_prob_le_of_textbookDL_rand'
depends on axioms: [propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputedAlgebraicFSFamilyRand.snarkFailure_prob_le_of_textbookDL_rand

/-- info: 'Zcash.Snark.ComputedAlgebraicFSFamilyUnbounded.snarkFailure_prob_le_of_unbounded_uniformURS_textbookDL'
depends on axioms: [propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms
  ComputedAlgebraicFSFamilyUnbounded.snarkFailure_prob_le_of_unbounded_uniformURS_textbookDL

/-- info: 'Zcash.Snark.ComputedAlgebraicFSFamilyUnbounded.binding_prob_le_of_unbounded_uniformURS_textbookDL'
depends on axioms: [propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms
  ComputedAlgebraicFSFamilyUnbounded.binding_prob_le_of_unbounded_uniformURS_textbookDL

/-- info: 'Zcash.Snark.ComputedAlgebraicFSFamily.instanceAttempt_runs_eq' depends on axioms:
[propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputedAlgebraicFSFamily.instanceAttempt_runs_eq

/-- info: 'Zcash.Snark.uniformURS_basis_transfer' depends on axioms: [propext, Classical.choice,
Quot.sound, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms uniformURS_basis_transfer

/-- info: 'Zcash.Snark.recursiveAlgebraicFork_sum_runs_le_unconditional' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms recursiveAlgebraicFork_sum_runs_le_unconditional

/-- info: 'Zcash.Snark.queryCharge_sum_mul_le_table_budget' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms queryCharge_sum_mul_le_table_budget

/-- info: 'Zcash.Snark.steeredCharge_context_sum_mul_le_table_budget' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms steeredCharge_context_sum_mul_le_table_budget

/-- info: 'Zcash.Snark.sum_card_scanRank_erase_lt_le' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sum_card_scanRank_erase_lt_le

/-- info: 'Zcash.Snark.recursiveAlgebraicForkFrom_node_runs_le_gated' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms recursiveAlgebraicForkFrom_node_runs_le_gated
