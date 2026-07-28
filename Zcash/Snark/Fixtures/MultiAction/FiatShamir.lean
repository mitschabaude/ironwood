import Zcash.Snark.Fixtures.MultiAction.Fixture
import Zcash.Snark.Fixtures.ScheduleMarker

/-!
# Fiat–Shamir schedule check for the multi-action capture

This file checks the deployed absorb/squeeze order against a multi-action Rust capture and then
matches `nonInteractiveFingerprint` to the captured MSM. `capturedFs` returns a captured challenge
only at its captured transcript prefix, converted by `markerSchedule` to the model's marker encoding.

With `numProofs = 2`, the check covers the per-proof absorb order that the single-action fixture cannot
distinguish. The Rust capture is trusted to provide the typed proof data, transcript events, and
challenges, not transcript bytes. General IPA ordering and sub-proof traversal are proved elsewhere;
this remains a concrete full-schedule regression.
-/

namespace Zcash.Snark.Fixture2

open Zcash.Snark

/-- The challenge values as emitted by the Rust transcript-event capture. -/
def capturedChallengeValues : List Fp :=
  capturedScheduleEntries.map Prod.snd

/-- The same challenge values, projected through the generated `ch` record. -/
def expectedChallengeValues : List Fp :=
  [ch.theta, ch.beta, ch.gamma, ch.y, ch.x, ch.x1, ch.x2, ch.x3, ch.x4, ch.xi, ch.z]
    ++ List.ofFn (fun j : Fin shape.k => ch.ipaRound j)

/-- The generated schedule carries the same challenge sequence as the generated `ch` record. -/
theorem capturedChallengeValues_eq_expected : capturedChallengeValues = expectedChallengeValues := by
  native_decide

/-- The fallback value used when `deriveChallenges` presents an unexpected transcript prefix. -/
def missingChallenge : Fp := 0

theorem missingChallenge_not_captured : missingChallenge ∉ capturedChallengeValues := by
  native_decide

/-- The captured challenges are distinct, so record equality also detects swapped output fields. -/
theorem capturedChallengeValues_nodup : capturedChallengeValues.Nodup := by
  native_decide

/-- Every captured squeeze prefix starts with the generated pre-proof verifier transcript prefix. -/
def capturedScheduleIncludesInit : Bool :=
  capturedScheduleEntries.all fun e => decide (e.1.take capturedInit.length = capturedInit)

theorem capturedScheduleIncludesInit_eq_true : capturedScheduleIncludesInit = true := by
  native_decide

/-- The captured schedule converted from challenge re-absorption to challenge-marker encoding. -/
def markerScheduleEntries : List (List (TranscriptElt Fp G) × Fp) :=
  markerSchedule capturedScheduleEntries

/-- Return a captured challenge at its recorded prefix and `missingChallenge` elsewhere. -/
def capturedFs : FiatShamir Fp G := {
  squeeze := fun t =>
    match markerScheduleEntries.find? (fun e => decide (e.1 = t)) with
    | some e => e.2
    | none => missingChallenge
}

/-- The Lean schedule reaches every captured challenge for the multi-action proof. -/
theorem deriveChallenges_matches_captured_schedule :
    deriveChallenges capturedFs capturedInit ps = ch := by native_decide

/-- The Fiat–Shamir-derived fingerprint matches the captured multi-action MSM under the concrete captured
schedule oracle above. -/
theorem nonInteractiveFingerprint_matches :
    MsmMatch (nonInteractiveFingerprint capturedFs capturedInit vk derivedInstanceCommitment ps) capturedMsm := by
  unfold nonInteractiveFingerprint
  rw [deriveChallenges_matches_captured_schedule]
  exact fingerprint_matches

end Zcash.Snark.Fixture2
