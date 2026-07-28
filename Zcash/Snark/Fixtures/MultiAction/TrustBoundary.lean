import Zcash.Snark.Fixtures.MultiAction.Fixture
import Zcash.Snark.Fixtures.MultiAction.Degree
import Zcash.Snark.Fixtures.MultiAction.StaticChecks
import Zcash.Snark.Fixtures.MultiAction.Schedule
import Zcash.Snark.Fixtures.MultiAction.KnowledgeError
import Zcash.Meta.AxiomCheck

/-!
# Checked trust boundary of the concrete multi-action fixture

The multi-action analog of `Fixtures.SingleAction.TrustBoundary`, and checked the same way: CI
bounds the trusted base of the concrete coordinate validation, verifier fingerprint match, executable
Vesta MSM identity, and instance-commitment derivation, and pins the exact axiom set of the
`native_decide` claims among them.

* `assert_axioms` (from `Zcash.Meta.AxiomCheck`) — bounds the trusted base at the standard tier,
  rejecting `sorryAx` and any unexpected axiom, walking the whole elaborated dependency graph
  (`Lean.collectAxioms`) rather than a syntactic scan. `+native` on the captured fixtures that run
  through `native_decide`.
* `#print axioms` pinned by `#guard_msgs` — freezes the exact axiom set, so a newly introduced
  axiom fails the build. As in the single-action sibling, this is the case the pinned form is
  reserved for: for a concrete numeric fixture the exact axiom set *is* the claim, documenting that
  compiler trust enters here and nowhere else.

The instance-commitment derivation (`instance_commitments_derived`,
`capturedPublicInstances_within_lagrange`) is pinned on the same footing, together with the data and
functions it ranges over; see the single-action sibling for why this is the fixture's new trust
surface.
-/

assert_axioms Zcash.Snark.Fixture2.capturedPointCoordinatesValid_eq_true +native(
  Zcash.Snark.Fixture2.capturedPointCoordinatesValid_eq_true)
assert_axioms Zcash.Snark.Fixture2.capturedInit_startsWith_vkTranscriptRepr +native(
  Zcash.Snark.Fixture2.capturedInit_startsWith_vkTranscriptRepr)
assert_axioms Zcash.Snark.Fixture2.fingerprint_matches +native(
  Zcash.Snark.Fixture2.fingerprint_matches)
assert_axioms Zcash.Snark.Fixture2.capturedMsm_eval_eq_zero +native(
  Zcash.Snark.Fixture2.capturedMsm_eval_eq_zero)
assert_axioms Zcash.Snark.Fixture2.assembledMsm_eval_eq_zero +native(
  Zcash.Snark.Fixture2.capturedMsm_eval_eq_zero,
  Zcash.Snark.Fixture2.fingerprint_matches)
assert_axioms Zcash.Arithmetic.Msm.evalNat
assert_axioms Zcash.Snark.assemble
-- The captured key's degree budget: one literal (`20470`) dominates every constraint family,
-- so the `x`-squeeze schedule's `epsilonX` is the concrete `20470 / |𝔽|` at this key.
assert_axioms Zcash.Snark.Fixture2.vk_gates_degree_le +native(
  Zcash.Snark.Fixture2.vk_gates_degree_le)
assert_axioms Zcash.Snark.Fixture2.vk_chunk_width_le +native(
  Zcash.Snark.Fixture2.vk_chunk_width_le)
assert_axioms Zcash.Snark.Fixture2.vk_lookup_input_degree_le +native(
  Zcash.Snark.Fixture2.vk_lookup_input_degree_le)
assert_axioms Zcash.Snark.Fixture2.vk_lookup_table_degree_le +native(
  Zcash.Snark.Fixture2.vk_lookup_table_degree_le)
assert_axioms Zcash.Snark.Fixture2.vk_quotient_tail_le +native(
  Zcash.Snark.Fixture2.vk_quotient_tail_le)
assert_axioms Zcash.Snark.Fixture2.vk_n_pred_le +native(Zcash.Snark.Fixture2.vk_n_pred_le)
assert_axioms Zcash.Snark.Fixture2.shape_k_pred_le +native(Zcash.Snark.Fixture2.shape_k_pred_le)
-- The captured key's static checks: the query layouts cover the shape's counts, `ω` has order
-- dividing `n`, and `n` does not vanish in `𝔽` — packaged for any family carrying the
-- captured non-group profile. Literal equality of fixed Vesta commitments is intentionally absent.
assert_axioms Zcash.Snark.Fixture2.capturedVerifierKeyProfile_vk
assert_axioms Zcash.Snark.Fixture2.vk_advice_layout_length +native(
  Zcash.Snark.Fixture2.vk_advice_layout_length)
assert_axioms Zcash.Snark.Fixture2.vk_instance_layout_length +native(
  Zcash.Snark.Fixture2.vk_instance_layout_length)
assert_axioms Zcash.Snark.Fixture2.vk_fixed_layout_length +native(
  Zcash.Snark.Fixture2.vk_fixed_layout_length)
assert_axioms Zcash.Snark.Fixture2.vk_omega_order +native(Zcash.Snark.Fixture2.vk_omega_order)
assert_axioms Zcash.Snark.Fixture2.vk_n_cast_ne_zero +native(
  Zcash.Snark.Fixture2.vk_n_cast_ne_zero)
assert_axioms Zcash.Snark.Fixture2.deployedConstraintStaticChecks_of_captured +native(
  Zcash.Snark.Fixture2.vk_advice_layout_length,
  Zcash.Snark.Fixture2.vk_fixed_layout_length,
  Zcash.Snark.Fixture2.vk_instance_layout_length,
  Zcash.Snark.Fixture2.vk_n_cast_ne_zero,
  Zcash.Snark.Fixture2.vk_omega_order,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- The `x`-squeeze schedule at the captured key: the degree caps are discharged, so `epsilonX` is
-- the concrete `20470 / |𝔽|`; exact leave-one-`x` invariance follows from the family's
-- fresh-query constraint trace.
assert_axioms Zcash.Snark.Fixture2.deployedConstraintXSqueezeSchedule_captured +native(
  Zcash.Snark.Fixture2.shape_k_pred_le,
  Zcash.Snark.Fixture2.vk_chunk_width_le,
  Zcash.Snark.Fixture2.vk_gates_degree_le,
  Zcash.Snark.Fixture2.vk_lookup_input_degree_le,
  Zcash.Snark.Fixture2.vk_lookup_table_degree_le,
  Zcash.Snark.Fixture2.vk_n_pred_le,
  Zcash.Snark.Fixture2.vk_quotient_tail_le,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- The deployed compressed-identity extraction bound at the captured key: the rewind-free
-- capstone with the static checks and degree caps discharged, so the bad-`x` term is the concrete
-- `(Q + 1) · 20470 / |𝔽|` and the multiopen term is the additive root budget.  Semantic
-- circuit satisfaction additionally uses the four-budget promotion in the core trust census.
assert_axioms Zcash.Snark.Fixture2.orchard_deployed_knowledge_error_captured +native(
  Zcash.Snark.Fixture2.shape_k_pred_le,
  Zcash.Snark.Fixture2.vk_advice_layout_length,
  Zcash.Snark.Fixture2.vk_chunk_width_le,
  Zcash.Snark.Fixture2.vk_fixed_layout_length,
  Zcash.Snark.Fixture2.vk_gates_degree_le,
  Zcash.Snark.Fixture2.vk_instance_layout_length,
  Zcash.Snark.Fixture2.vk_lookup_input_degree_le,
  Zcash.Snark.Fixture2.vk_lookup_table_degree_le,
  Zcash.Snark.Fixture2.vk_n_cast_ne_zero,
  Zcash.Snark.Fixture2.vk_n_pred_le,
  Zcash.Snark.Fixture2.vk_omega_order,
  Zcash.Snark.Fixture2.vk_quotient_tail_le,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
-- The same bound on the interpolation-free route: the deployed constraint family is built by
-- `ofCovered` from the two fresh-query traces, with no field-capacity premise or interpolation.
assert_axioms Zcash.Snark.Fixture2.orchard_deployed_knowledge_error_captured_direct +native(
  Zcash.Snark.Fixture2.shape_k_pred_le,
  Zcash.Snark.Fixture2.vk_advice_layout_length,
  Zcash.Snark.Fixture2.vk_chunk_width_le,
  Zcash.Snark.Fixture2.vk_fixed_layout_length,
  Zcash.Snark.Fixture2.vk_gates_degree_le,
  Zcash.Snark.Fixture2.vk_instance_layout_length,
  Zcash.Snark.Fixture2.vk_lookup_input_degree_le,
  Zcash.Snark.Fixture2.vk_lookup_table_degree_le,
  Zcash.Snark.Fixture2.vk_n_cast_ne_zero,
  Zcash.Snark.Fixture2.vk_n_pred_le,
  Zcash.Snark.Fixture2.vk_omega_order,
  Zcash.Snark.Fixture2.vk_quotient_tail_le,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)

-- The instance-commitment derivation: the two captured claims, plus the data and functions they
-- range over. The latter are flagless — they are ordinary definitions, so compiler trust must not
-- reach them; only the two claims about them may spend it.
assert_axioms Zcash.Snark.Fixture2.instance_commitments_derived +native(
  Zcash.Snark.Fixture2.instance_commitments_derived)
assert_axioms Zcash.Snark.Fixture2.capturedPublicInstances_within_lagrange +native(
  Zcash.Snark.Fixture2.capturedPublicInstances_within_lagrange)
assert_axioms Zcash.Snark.Fixture2.capturedUrsGLagrange
assert_axioms Zcash.Snark.Fixture2.capturedPublicInstances
assert_axioms Zcash.Snark.Fixture2.commitLagrange
assert_axioms Zcash.Snark.Fixture2.derivedInstanceCommitment

-- `whitespace := lax` collapses all whitespace, so the pin is insensitive to how
-- `#print axioms` line-wraps the list (a formatting artifact of the axiom-name lengths).
/-- info: 'Zcash.Snark.Fixture2.fingerprint_matches' depends on axioms: [propext, Classical.choice, Quot.sound, Zcash.Snark.Fixture2.fingerprint_matches._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Zcash.Snark.Fixture2.fingerprint_matches

/-- info: 'Zcash.Snark.Fixture2.capturedMsm_eval_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound, Zcash.Snark.Fixture2.capturedMsm_eval_eq_zero._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Zcash.Snark.Fixture2.capturedMsm_eval_eq_zero

/-- info: 'Zcash.Snark.Fixture2.instance_commitments_derived' depends on axioms: [propext, Classical.choice, Quot.sound, Zcash.Snark.Fixture2.instance_commitments_derived._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Zcash.Snark.Fixture2.instance_commitments_derived

/-- info: 'Zcash.Snark.Fixture2.capturedPublicInstances_within_lagrange' depends on axioms: [propext, Classical.choice, Quot.sound, Zcash.Snark.Fixture2.capturedPublicInstances_within_lagrange._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Zcash.Snark.Fixture2.capturedPublicInstances_within_lagrange
