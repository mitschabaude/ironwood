import Mathlib
import Zcash.Arithmetic

/-!
# The Schwartz–Zippel soundness bound for the fingerprint

A fingerprint can be summarised more cheaply by a random evaluation: two fingerprints that differ as
polynomials in the proof scalars and challenges agree at a uniformly random point only with small
probability. This module pins that probability down by specialising Mathlib's Schwartz–Zippel lemma to
the verifier's field `F_p`. (The *realized* fingerprint in this development is the decidable
coefficient comparison, `Zcash.Snark.Fingerprint.Match`; this random-evaluation variant is not yet
instantiated at the concrete coefficients — see below.)

For a nonzero polynomial of total degree `d` in `n` variables over `F_p`, the fraction of `F_pⁿ`
on which it vanishes is at most `d / p` (`p = scalarFieldOrder ≈ 2²⁵⁴`) — so a false match
between distinct degree-`d` fingerprints is negligible. (Applying this to the concrete
fingerprint polynomial remains open; see `Zcash.Snark.Fingerprint.Match`.)
-/

namespace Zcash.Snark

open Zcash.Arithmetic (card_Fp scalarFieldOrder)

open MvPolynomial Finset Fintype

/-- **Schwartz–Zippel for the fingerprint field.** A nonzero polynomial `p` of total degree `d` in `n`
variables over `F_p` vanishes on at most a `d / |F_p|` fraction of `F_pⁿ`: the fraction of evaluation
points at which `p` is zero is `≤ p.totalDegree / scalarFieldOrder`. This is the SZ bound underlying a
random-evaluation fingerprint — the chance a random point fails to witness a nonzero polynomial. -/
theorem fingerprint_schwartz_zippel {n : ℕ} {p : MvPolynomial (Fin n) Fp} (hp : p ≠ 0) :
    (#{f ∈ piFinset fun _ => (univ : Finset Fp) | eval f p = 0} : ℚ≥0)
        / (scalarFieldOrder : ℚ≥0) ^ n ≤ (p.totalDegree : ℚ≥0) / scalarFieldOrder := by
  have h := schwartz_zippel_totalDegree hp (univ : Finset Fp)
  simpa only [Finset.card_univ, card_Fp] using h

end Zcash.Snark
