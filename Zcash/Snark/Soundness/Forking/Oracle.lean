import Mathlib.Probability.Distributions.Uniform
import Zcash.Snark.Verifier.FiatShamir
import Zcash.Snark.Core.Field

/-!
# Random-oracle model for Fiat–Shamir

`Verifier.FiatShamir` derives challenges with an abstract `squeeze`. The deployed verifier uses
Blake2b. The soundness proof models it as a random function with uniform answers that can be changed
at one query.

This module supplies the random-oracle primitives the forking development is framed with:

* `reprogram` changes the answer at one transcript prefix. Rewinding reruns the prover with that
  changed answer.
* `uniformChallenge` and `uniformChallenge_badSet` model a fresh field challenge and its probability
  of landing in a finite bad set.

## Challenge-vector distribution

The forking proof uses the uniform distribution on IPA challenge vectors.
`Soundness.Forking.Rewind.roChallenges_ipaRound_uniform` derives that distribution for a fixed proof
from one assumption:

> **Random oracle.** The Blake2b squeeze is idealized as a *uniform random function* `O` over its query domain.

Each round reads `O` at a distinct transcript prefix, so the answers are independent and uniform.
This also assumes that transcript encoding is injective and that halo2's `Challenge255 → Fp`
conversion is exactly uniform. The real conversion has a negligible, unaccounted reduction bias.

Thus the challenge distribution is proved inside the random-oracle model, while the model itself
remains an assumption about Blake2b.

## Remaining adversary model

A full reduction must model a forger that queries `O`, derive `hprob` from its advantage, and pay the
random-oracle query loss. That adversary experiment is outside this PR. The fixed-proof endpoints
measure one proof over all challenges; they do not yet measure a real Fiat–Shamir attack.

`uniformChallenge_badSet` is used directly for the `1/p` blinding budget.

Two scope notes, both part of that floor, not the derived uniformity:

* Beating `kerr` proves that a witness exists; it does not implement an expected-polynomial-time
  extractor.
* The `Fp`-squeeze exclusions — the Schwartz–Zippel `d / p`, the `z ≠ 0` and `ξ`-recovery `1 / p`
  singletons, and any further point exclusions — are combined into one subadditive bound by
  `Soundness.GoodChallenge.uniformChallenge_szBadSet_union`. The cross-domain forking budgets — the
  `kerr` tree count over the round-*vector* domain and the random-oracle query loss — remain part of
  this floor: they live in the adversary experiment that is outside this PR.
-/

namespace Zcash.Snark

open scoped ENNReal

variable {F G : Type*}

/-! ## Reprogramming — the rewinding primitive -/

open Classical in
/-- Change the oracle's answer at `t` to `c`, leaving all other answers unchanged. -/
noncomputable def reprogram (O : List (TranscriptElt F G) → F) (t : List (TranscriptElt F G)) (c : F) :
    List (TranscriptElt F G) → F :=
  fun t' => if t' = t then c else O t'

@[simp] theorem reprogram_self (O : List (TranscriptElt F G) → F) (t : List (TranscriptElt F G)) (c : F) :
    reprogram O t c t = c := by
  simp [reprogram]

theorem reprogram_ne {O : List (TranscriptElt F G) → F} {t t' : List (TranscriptElt F G)} {c : F}
    (h : t' ≠ t) : reprogram O t c t' = O t' := by
  simp [reprogram, h]

/-! ## The uniform-challenge idealization -/

/-- A fresh random-oracle squeeze, modeled as uniform over `Fp`.

Halo2's real field conversion has negligible reduction bias that is not included in the bounds. -/
noncomputable def uniformChallenge : PMF Fp := PMF.uniformOfFintype Fp

/-- A uniform challenge lands in `bad` with probability `|bad| / |Fp|`. -/
theorem uniformChallenge_badSet (bad : Finset Fp) :
    uniformChallenge.toOuterMeasure bad = (bad.card : ℝ≥0∞) / Fintype.card Fp := by
  rw [uniformChallenge, PMF.toOuterMeasure_apply_finset]
  simp only [PMF.uniformOfFintype_apply, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

end Zcash.Snark
