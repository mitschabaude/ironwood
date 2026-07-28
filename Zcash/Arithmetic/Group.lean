import Mathlib

/-!
# The verifier group `E_q` and the uniform reference string

The halo2 verifier operates over the Vesta curve `E_q` (`vesta::Affine`): every commitment in the
proof, every reference-string generator, and the final multiscalar-multiplication (MSM) check live
in this group. We deliberately model it abstractly, as an `F`-module `G` (`F = F_p`, the scalar
field): the only structure the verifier's MSM uses is the `F`-linear combination of group elements,
so the argument stays curve-agnostic and never reaches into concrete curve arithmetic.

The concrete instantiation is unconditional: CompElliptic's Vesta curve
(`SWPoint Vesta.curve`) is a proven `AddCommGroup` — not an assumption — and
`Pasta.Vesta.card_eq` pins its order `p` with no assumption, making it a
`Module (ZMod p)` (`vestaFpModule`). The Vesta capstones (`Soundness.Vesta`) instantiate `G`
there with no change to this argument.
-/

namespace Zcash.Arithmetic

/-- The uniform reference string, mirroring halo2 `Params` (`poly/commitment.rs`): `k` is the
`log₂` of the domain size, `g` the `n = 2 ^ k` generators, `w` the blinding generator, and `u`
the inner-product generator. The Lagrange basis is omitted: the verifier's MSM is expressed over
the monomial basis `g`. -/
structure URS (G : Type*) where
  k : ℕ
  g : Fin (2 ^ k) → G
  w : G
  u : G

end Zcash.Arithmetic
