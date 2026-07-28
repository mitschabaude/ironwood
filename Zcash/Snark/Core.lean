/-
Copyright (c) 2026 Ironwood Contributors.
Released under the Apache License, Version 2.0.
-/
import Zcash.Arithmetic.Msm

/-!
# Compatibility shim: `Msm` under `Zcash.Snark`

The generated fixture captures spell the fingerprint MSM bare (`Msm shape.k Fp G`) while
declaring inside `namespace Zcash.Snark.Fixture`, so the enclosing-namespace walk needs the name
to exist at `Zcash.Snark`. It lives in `Zcash.Arithmetic.Msm` and is not common enough to earn
root vocabulary the way `Fp` and `URS` do, so this one alias carries it. Delete this file when
the captures are next regenerated; no editable module depends on it.
-/

namespace Zcash.Snark

export Zcash.Arithmetic (Msm)

end Zcash.Snark
