import Zcash.Snark.Fixtures.MultiAction.Fixture
import Zcash.Snark.Soundness.Composition.DeployedConstraintContainment

/-!
# The captured verifying key's static checks

`DeployedConstraintStaticChecks` collects the verifying-key facts the rewind-free constraint
capstone needs independently of the adversary run: the three query layouts cover the shape's query
counts, `ω` has order dividing `n`, and `n` does not vanish in `𝔽`. This module evaluates all five
at the captured Post-NU6.3 key and packages them for any family with the captured key profile.

Group commitments are deliberately outside that profile. In the AGM game they must be represented
over the sampled basis, so demanding literal equality with the fixture's fixed Vesta points would
leave the premise uninhabited for some bases.
-/

namespace Zcash.Snark.Fixture2

open Zcash.Snark

/-- The part of the captured verifying key used by the static and degree checks. The two
group-valued commitment families are intentionally absent: the AGM setup resamples the basis,
and public verifier points must therefore be supplied with representations over that basis. -/
structure CapturedVerifierKeyProfile
    (candidate : VerifyingKey shape Fp VestaG) : Prop where
  omega : candidate.omega = vk.omega
  n : candidate.n = vk.n
  gates : candidate.gates = vk.gates
  instanceQueryLayout : candidate.instanceQueryLayout = vk.instanceQueryLayout
  adviceQueryLayout : candidate.adviceQueryLayout = vk.adviceQueryLayout
  fixedQueryLayout : candidate.fixedQueryLayout = vk.fixedQueryLayout
  permutationChunks : candidate.permutationChunks = vk.permutationChunks
  lookupInputExprs : candidate.lookupInputExprs = vk.lookupInputExprs
  lookupTableExprs : candidate.lookupTableExprs = vk.lookupTableExprs

/-- The captured key itself has the captured non-group profile. -/
theorem capturedVerifierKeyProfile_vk : CapturedVerifierKeyProfile vk := by
  constructor <;> rfl

/-- The captured advice query layout covers the shape's advice query count (`25`). -/
theorem vk_advice_layout_length : shape.numAdviceQueries ≤ vk.adviceQueryLayout.length := by
  native_decide

/-- The captured instance query layout covers the shape's instance query count (`1`). -/
theorem vk_instance_layout_length : shape.numInstanceQueries ≤ vk.instanceQueryLayout.length := by
  native_decide

/-- The captured fixed query layout covers the shape's fixed query count (`29`). -/
theorem vk_fixed_layout_length : shape.numFixedQueries ≤ vk.fixedQueryLayout.length := by
  native_decide

/-- The captured `ω` has order dividing `n`: `ω ^ 2048 = 1`. -/
theorem vk_omega_order : vk.omega ^ vk.n = 1 := by
  native_decide

/-- The captured domain size does not vanish in the scalar field: `(2048 : 𝔽) ≠ 0`. -/
theorem vk_n_cast_ne_zero : ((vk.n : ℕ) : Fp) ≠ 0 := by
  native_decide

/-- **The static checks at the captured key profile.** Any deployed root family carrying the
captured scalar and query-layout data satisfies `DeployedConstraintStaticChecks`; no equality of
the verifier's group commitments is required. -/
theorem deployedConstraintStaticChecks_of_captured
    (family : ComputedDeployedRootFSFamily shape)
    (hvk : ∀ basis, CapturedVerifierKeyProfile (family.vk basis)) :
    DeployedConstraintStaticChecks family :=
  { adviceLength := fun basis => by
      rw [(hvk basis).adviceQueryLayout]
      exact vk_advice_layout_length
    instanceLength := fun basis => by
      rw [(hvk basis).instanceQueryLayout]
      exact vk_instance_layout_length
    fixedLength := fun basis => by
      rw [(hvk basis).fixedQueryLayout]
      exact vk_fixed_layout_length
    omegaOrder := fun basis => by
      rw [(hvk basis).omega, (hvk basis).n]
      exact vk_omega_order
    characteristic := fun basis => by
      rw [(hvk basis).n]
      exact vk_n_cast_ne_zero }

end Zcash.Snark.Fixture2
