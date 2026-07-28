/-
Copyright (c) 2026 Ironwood Contributors.
Released under the Apache License, Version 2.0.
-/
import Zcash.Arithmetic.Field
import Zcash.Arithmetic.Group

/-!
# The arithmetic tier, and the two names it lends the whole repository

`Zcash/Arithmetic/` holds the objects every other tier is stated over: the scalar field, the
verifier group's reference string, the fingerprint MSM and the fast kernels behind them. Most
of those names are local vocabulary and stay qualified — a module that wants `bestFftG` or
`omegaOf` opens `Zcash.Arithmetic` for exactly that name.

`Fp` and `URS` are the exceptions. They appear in nearly every statement in the repository, so
they are re-exported at the `Zcash` root: any module declaring inside `Zcash.*` finds them by
the enclosing-namespace walk, with no `open` at all. Nothing else earns root vocabulary.

There is deliberately no `G` here. The verifier group is a type *variable* throughout
(`URS (G : Type*)`, `variable {G : Type*}`); the concrete instantiations bind their own `G`
locally, so there is no declaration to export.
-/

namespace Zcash

export Arithmetic (Fp URS)

end Zcash
