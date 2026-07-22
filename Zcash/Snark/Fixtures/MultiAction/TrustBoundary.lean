import Zcash.Snark.Fixtures.MultiAction.Fixture
import Mathlib.Util.AssertNoSorry

/-!
# Checked trust boundary of the concrete multi-action fixture

The multi-action analog of `Fixtures.SingleAction.TrustBoundary`: CI checks that no `sorry` reaches
the concrete coordinate validation, verifier fingerprint match, or executable Vesta MSM identity.
-/

open Zcash.Snark Zcash.Snark.Fixture2

assert_no_sorry capturedPointCoordinatesValid_eq_true
assert_no_sorry capturedInit_startsWith_vkTranscriptRepr
assert_no_sorry fingerprint_matches
assert_no_sorry capturedMsm_eval_eq_zero
assert_no_sorry assembledMsm_eval_eq_zero
assert_no_sorry Msm.evalNat
assert_no_sorry assemble

/-- info: 'Zcash.Snark.Fixture2.fingerprint_matches' depends on axioms: [propext, Classical.choice, Quot.sound, fingerprint_matches._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms fingerprint_matches

/-- info: 'Zcash.Snark.Fixture2.capturedMsm_eval_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound, capturedMsm_eval_eq_zero._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms capturedMsm_eval_eq_zero
