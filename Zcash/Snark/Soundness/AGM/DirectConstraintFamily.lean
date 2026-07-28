import Zcash.Snark.Soundness.AGM.DirectX4Columns
import Zcash.Snark.Soundness.Composition.DeployedConstraintContainment

/-!
# Computable direct deployed-constraint family

Packages the interpolation-free root decoder with its two staged chronology traces. The
construction is executable: the traces are proof-layer inputs, and the outcome is the computable
`deployedRootOutcomeOfCovered`.
-/

namespace Zcash.Snark

variable {shape : Shape}

/-- Build the direct deployed-constraint family from online member coverage and the two staged
traces. No offline interpolation or classical choice enters the executable outcome. -/
def ComputedDeployedConstraintFSFamily.ofCovered
    (online : ComputedOnlineMemberFSFamily shape)
    (rootTrace : DeployedRootOnlineTrace online.toFamily
      (deployedRootOutcomeOfCovered online))
    (xTrace : DeployedConstraintXOnlineTrace
      (ComputedDeployedRootFSFamily.ofCovered online rootTrace)) :
    ComputedDeployedConstraintFSFamily shape :=
  .ofRoot (ComputedDeployedRootFSFamily.ofCovered online rootTrace) xTrace

end Zcash.Snark
