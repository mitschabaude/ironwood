import Zcash.Snark.Fixtures.SingleAction.Fixture
import Zcash.Snark.Fixtures.MultiAction.Fixture
import Mathlib.Util.AssertNoSorry

/-!
# Post-NU6.3 fixture provenance

Cross-capture checks for the canonical Post-NU6.3 Orchard/Ironwood verifying key and URS. During
fixture generation, Orchard first compares the exact `PinnedVerificationKey` debug representation
against its checked-in `circuit_description_post_nu6_3`; Halo2 then derives and emits the transcript
representation below from that same verified key object.

Lean does not reimplement Halo2's `Debug` serialization or Blake2b derivation. The hand-pinned scalar
here makes fixture drift visible in this repository, while the Rust regeneration assertion binds it
to the full canonical pinned key.
-/

namespace Zcash.Snark.PostNu63Fixture

/-- Halo2's transcript representation of the canonical Post-NU6.3 pinned verifying key. -/
def canonicalVkTranscriptRepr : Fp :=
  (8223501628842095769 : Fp)
    + (2306373111636605627 : Fp) * (2 : Fp) ^ 64
    + (3243000079158773602 : Fp) * (2 : Fp) ^ 128
    + (370130488735545691 : Fp) * (2 : Fp) ^ 192

theorem singleAction_uses_postNu63 : Fixture.capturedCircuitId = "PostNu6_3" := by
  native_decide

theorem multiAction_uses_postNu63 : Fixture2.capturedCircuitId = "PostNu6_3" := by
  native_decide

theorem singleAction_uses_canonicalVk :
    Fixture.capturedVkTranscriptRepr = canonicalVkTranscriptRepr := by
  native_decide

theorem multiAction_uses_canonicalVk :
    Fixture2.capturedVkTranscriptRepr = canonicalVkTranscriptRepr := by
  native_decide

/-- Both captures use the same deterministic Halo2 URS (`g`, then `w` and `u` occupy the first
`2^11 + 2` entries in each generated concrete-point table).

This detects *skew* between the two captures' generators, not the correctness of the URS itself:
both lists are emitted by the same generator, so an equally wrong URS in both would still pass. The
independent binding is elsewhere — `capturedMsm_eval_eq_zero` computes the MSM against this exact URS
and would fail with overwhelming probability for a URS that was not Halo2's deterministic one. -/
theorem captures_use_same_urs_coordinates :
    Fixture.capturedPointCoordinates.take (2 ^ 11 + 2)
      = Fixture2.capturedPointCoordinates.take (2 ^ 11 + 2) := by
  native_decide

-- Trust-boundary guards: fail the `FixtureCheck` build if any provenance theorem above comes to
-- rest on a `sorry` reached through some dependency (the checks are `native_decide`, so a hole
-- would otherwise only surface as a warning). Mirrors the `SingleAction`/`MultiAction` boundaries.
assert_no_sorry singleAction_uses_postNu63
assert_no_sorry multiAction_uses_postNu63
assert_no_sorry singleAction_uses_canonicalVk
assert_no_sorry multiAction_uses_canonicalVk
assert_no_sorry captures_use_same_urs_coordinates

end Zcash.Snark.PostNu63Fixture
