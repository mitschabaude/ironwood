/-
Copyright (c) 2026 Ironwood Contributors.
Released under the Apache License, Version 2.0.
-/
import CompElliptic.Curves.Pasta.Fast.Projective
import Zcash.Arithmetic.Field
import CompElliptic.Curves.PastaOrder

/-!
# The Vesta curve as an `Fp`-module, as a plain `def`

The keygen bilinearity theorem (`commitLagrangeSpec_derivedUrsGLagrange`) needs the verifier
group to be an `Fp`-module: `ZMod.val`-smuls only compose across the DFT because `p • P = 0`.
`Zcash.Snark.Soundness.Vesta` installs exactly that instance (`vestaFpModule`) for the deployed
curve, but its import closure is the whole soundness development, which the concrete keygen
certificate has no reason to load.

This module supplies the same structure for `Fast.Projective.G` from CompElliptic's pinned
point count alone, and deliberately **not** as an `instance`: the theorems it feeds have
`Fp`-module-free statements (`commitLagrangeSpec` smuls are `ℕ`-smuls), so the structure is
only ever needed *inside* proofs, where it is introduced explicitly.  Keeping it out of
instance search is what guarantees no second `Module Fp (SWPoint Vesta.curve)` can collide
with `Soundness.Vesta`'s in a module that reaches both.
-/

namespace Zcash.Arithmetic

open CompElliptic.Curves.Pasta
open CompElliptic.Curves.Pasta.Fast.Projective

/-- Every Vesta point is `p`-torsion, from CompElliptic's pinned `Vesta.card_eq` and the fact
that a finite group is annihilated by its cardinality.  Mirrors `Zcash.Snark.vestaOrder`. -/
theorem vestaGroupOrder (P : G) : (scalarFieldOrder : ℕ) • P = 0 := by
  have hcard : Nat.card G = scalarFieldOrder := Vesta.card_eq
  rw [← hcard]
  exact addOrderOf_dvd_iff_nsmul_eq_zero.mp (addOrderOf_dvd_natCard P)

/-- The deployed verifier group as an `Fp`-module.  NOT an instance — see the module
docstring; introduce it with `haveI` inside a proof that needs it. -/
@[implicit_reducible]
def vestaFpModuleDef : Module Fp G := AddCommGroup.zmodModule vestaGroupOrder

end Zcash.Arithmetic
