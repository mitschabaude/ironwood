import Zcash.Snark.Keygen.Pipeline
import Zcash.Circuits.Action.TopLevel

/-!
# The Action verifying key, fully derived

The `Pipeline.lean` generic `keygen_vk` instantiated at the closed Orchard Action
circuit: every definition here is a `TopLevelCircuit` method applied to
`actionCircuit`. The names are the certification surface —
`Certificate.lean` (the expensive module, built only in the `FixtureCheck` lane)
proves them equal to the capture (`commitments_derived`, `vk_eq_derived`,
`shape_eq_mergeDerived`, `vk_eq_toVerifierKey`); clients consume the data without
evaluating the certificate.
-/

namespace Zcash.Snark.Keygen

open Zcash.Snark
open Zcash.Circuits.Action (actionCircuit)

variable {G : Type} [AddCommGroup G] [Inhabited G]

/-- The derived fixed-column commitments of the Action circuit against a URS
(`TopLevelCircuit.fixedCommitments`). All 29 are certified equal to the capture in
`commitments_derived`. -/
def derivedFixedCommitments (urs : URS G) : List G :=
  actionCircuit.fixedCommitments urs

/-- The derived permutation common commitments of the Action circuit against a URS
(`TopLevelCircuit.permutationCommitments`). Certified against the capture in
`commitments_derived`. -/
def derivedPermutationCommonCommitments (urs : URS G) : List G :=
  actionCircuit.permutationCommitments urs

/-- The Action `VerifyingKey` with EVERY field derived from the circuit (+ the URS for
the two commitment families) at an explicitly-given `Shape` —
`TopLevelCircuit.verifierKeyAt` at the Action circuit. The record equality with the
capture is `Certificate.lean`'s `vk_eq_derived`; the derived-`Shape` method form is
`toVerifierKey_action`/`vk_eq_toVerifierKey`. -/
def derivedActionVk (shape : Shape) (urs : URS G) : VerifyingKey shape Fp G :=
  actionCircuit.verifierKeyAt shape urs

/-- Transporting `derivedActionVk` along a shape equality is `derivedActionVk` at the
other shape — the record mentions the shape only in its `Fin`-domain types. -/
theorem derivedActionVk_cast {s₁ s₂ : Shape} (hs : s₁ = s₂) (urs : URS G) :
    hs ▸ derivedActionVk s₁ urs = derivedActionVk s₂ urs := by
  cases hs; rfl

/-- The method form is the shape-explicit core at the derived `Shape` — definitional. -/
theorem toVerifierKey_action (pp : ProofParams) (urs : URS G) :
    actionCircuit.toVerifierKey pp urs
      = derivedActionVk (pp.mergeDerived actionCircuit) urs := rfl

end Zcash.Snark.Keygen
