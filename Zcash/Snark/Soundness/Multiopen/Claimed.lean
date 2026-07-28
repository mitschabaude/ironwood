import Mathlib
import Zcash.Snark.Soundness.Multiopen.RPoly
import Zcash.Snark.Soundness.Multiopen.ValueCheck
import Zcash.Snark.Soundness.GoodChallenge
import Zcash.Snark.Soundness.Forking.Probability

/-!
# Claimed-evaluation binding through the `x₃` rewinds

`RPoly` proved that enough interpolation samples force a decoded column to be the `r`-polynomial.
This module produces those samples from an accept *measure*:

* `claimedEval_of_x3Prob` — an accept measure of the `x₃`-rewound runs beating `(|points| − 1) / p`
  yields the distinct samples, binding each decoded column's value at every rotated query point to
  the proof string's claimed evaluation. The runs are the `reprogramX3` events (`Forking.Rewind`,
  sealed by `Forking.Ordering`), under the usual random-oracle uniformity axiom.
* `gateGood_of_xProb` — with the claimed evaluations pinned, the gate-check difference polynomial
  is fixed before `x` is sampled, so an accept measure over the deployed `x`-squeeze produces a
  good challenge outside its bad set (`GoodChallenge.exists_accepting_good_challenge`).
-/

namespace Zcash.Snark

open Polynomial
open scoped ENNReal

/-- **The `x₃` forking floor for claimed-evaluation binding.** Given the per-accepting-run value
consistency `acc χ → col.eval χ = lagrangeEval χ points evals` (the verifier's multiopen value
check), an honest accepting run `x₀`, and an accept measure beating `(|points| − 1) / p`, every
rotated query point's value of the decoded column is the proof string's claimed evaluation. The
counting floor turns the measure into `|points|` distinct interpolation samples and
`col_eval_node_eq_claimed` (`Soundness.Multiopen.RPoly`) forces the `r`-polynomial identity. -/
theorem claimedEval_of_x3Prob {points evals : List Fp} {col : Polynomial Fp}
    (hlen : 0 < points.length)
    (hnode : Function.Injective (fun i : Fin points.length => points[i]))
    (hdeg : col.natDegree < points.length)
    (acc : Fp → Prop) [DecidablePred acc]
    (hconsistent : ∀ χ, acc χ → col.eval χ = lagrangeEval χ points evals)
    {x₀ : Fp} (hx₀ : acc x₀)
    (hprob : (((points.length - 1 : ℕ)) : ℝ≥0∞) / Fintype.card Fp
      < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter acc))
    (i : Fin points.length) :
    col.eval points[i] = evals.getD (i : ℕ) 0 := by
  have hn : points.length = points.length - 1 + 1 := (Nat.succ_pred_eq_of_pos hlen).symm
  obtain ⟨ξ, hξinj, _hξ0, hξacc⟩ :=
    exists_injective_accepting_of_measure (acc := acc) hx₀ hprob
  exact col_eval_node_eq_claimed hlen hnode hdeg (fun j => ξ (Fin.cast hn j))
    (fun j j' h => Fin.cast_injective hn (hξinj h))
    (fun j => hconsistent _ (hξacc (Fin.cast hn j))) i


/-- **Gate `x`→`x₃` transport, grounded on the deployed `x`-squeeze.** With the decoded columns'
claimed evaluations pinned (`claimedEval_of_x3Prob`), the gate-check difference `C` is a fixed
function of the committed data, so an accept measure over the deployed `x`-squeeze beating
`natDegree C / p` produces a good gate-check challenge outside `szBadSet C` — the `_xgood` rungs'
`accX`, derived from the deployed measure rather than assumed. -/
theorem gateGood_of_xProb {acc : Fp → Prop} [DecidablePred acc] (C : Polynomial Fp)
    (hprob : (C.natDegree : ℝ≥0∞) / (Fintype.card Fp : ℝ≥0∞)
      < uniformChallenge.toOuterMeasure (Finset.univ.filter acc)) :
    ∃ xv, acc xv ∧ xv ∉ szBadSet C :=
  exists_accepting_good_challenge C hprob


end Zcash.Snark
