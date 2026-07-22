import Mathlib
import Zcash.Snark.Soundness.Multiopen.RPoly
import Zcash.Snark.Soundness.Multiopen.ValueCheck
import Zcash.Snark.Soundness.GoodChallenge
import Zcash.Snark.Soundness.Forking.Probability

/-!
# Claimed-evaluation binding through the `x₃` rewinds

`Soundness.Multiopen.RPoly` proved the sample-forces-identity core: a decoded column of degree
`< |points|` that reproduces the deployed `r`-value `lagrangeEval · points evals` at `|points|`
distinct interpolation challenges is the `r`-polynomial, so its value at each rotated node is the
claimed evaluation (`col_eval_node_eq_claimed`). This module produces those samples from an accept
*measure*, closing the last fingerprint-delegated step:

* `claimedEval_of_x3Prob` — **the `x₃` forking floor for claimed-eval binding.** From a per-run
  consistency `acc χ → col.eval χ = lagrangeEval χ points evals` (the verifier's multiopen value
  check at the interpolation challenge, `Verifier.Checks.multiopenEval`) and an accept measure of
  the `x₃`-rewound runs beating `(|points| − 1) / p`, the single-squeeze counting floor
  (`exists_injective_accepting_of_measure`) yields the `|points|` distinct samples, and the decoded
  column's value at every rotated query point `ωⁱ·x` is bound to the proof string's claimed
  evaluation. The measure carries the same random-oracle uniformity axiom as every `hprob`
  (`Soundness.Forking.Oracle`); the runs are the `reprogramX3` reprogramming events
  (`Soundness.Forking.Rewind`, sealed by `Soundness.Forking.Ordering`). This is the value-side twin
  of the `x₄` opened chain (`Soundness.Multiopen.Opened`), consuming the same rewinding floor.

* `gateGood_of_xProb` — **the gate `x`→`x₃` transport, grounded.** Once the decoded
  columns' claimed evaluations are pinned by the binding above, the gate-check difference polynomial
  `C` is a fixed function of the committed data. An accept measure over the deployed `x`-squeeze
  events beating `natDegree C / p` then produces a good gate-check challenge outside `szBadSet C`
  (`Soundness.GoodChallenge.exists_accepting_good_challenge`), so the `_xgood` rungs' `accX` event is
  grounded over the deployed `x`-squeeze rather than assumed. The Schwartz–Zippel difference is
  pinned before `x` is sampled (`adviceCommitments_mem_preXTranscript`/`hPieces_mem_preXTranscript`,
  `Soundness.Forking.Ordering`), the commit-before-challenge ordering the argument needs.
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

/-- **The `x₂` set-separation counting floor (a general algebraic lemma).** Given `acc χ →
multiopenEval χ x₃ sets = 0` and an accept measure of the `x₂`-rewound runs beating `(|sets| − 1) / p`,
the single-squeeze counting floor turns the measure into `|sets|` pairwise-distinct `x₂` samples and
`multiopenEval_perSet_zero_of_samples` forces each set's cleared contribution `(qⱼ − r(x₃))·∏(x₃−node)⁻¹`
to vanish. It is the degree-`|sets|`-in-`x₂` separation of the `Σⱼ x₂ʲ·(…)` fold.

**Caveat on the deployed hook.** The premise `multiopenEval χ x₃ sets = 0` is *not* directly what
deployed acceptance supplies: acceptance forces the IPA to open to `multiopenValue` (which is computed
from the claimed data, hence self-consistent — `deployed_verification_eq`), not to `0`. The operative
binding for the deployed value check is instead the `x₃`-rewind: the quotient column `q′_col` is fixed
across `x₃`-rewinds (`q′` absorbed before `x₃`) and satisfies `q′_col.eval x₃ = multiopenEval x₂ x₃ sets`
(`Opened.openedDecodedCols_top_eval_x3`), so it is *that* rewind that pins the per-set consistency after
denominator clearing. This lemma captures the set-separation *structure*; the end-to-end derivation of
`hconsistent` is the landed fixed-`q′` composition — `deployed_value_check_node_binding` /
`deployed_member_node_binding` (`Soundness.Multiopen.ValueCheckX3`), consumed by
`Soundness.Vesta.orchard_verifier_vesta_member_constraint_derived`. -/
theorem claimedCombined_of_x2Prob {x3 : Fp} {sets : List (List Fp × List Fp × Fp)}
    (hlen : 0 < sets.length)
    (acc : Fp → Prop) [DecidablePred acc]
    (hvanish : ∀ χ, acc χ → multiopenEval χ x3 sets = 0)
    {x₀ : Fp} (hx₀ : acc x₀)
    (hprob : (((sets.length - 1 : ℕ)) : ℝ≥0∞) / Fintype.card Fp
      < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter acc))
    (j : Fin sets.length) :
    ((sets.reverse.getD j ([], [], 0)).2.2
        - lagrangeEval x3 (sets.reverse.getD j ([], [], 0)).1 (sets.reverse.getD j ([], [], 0)).2.1)
      * ∏ m ∈ Finset.range (sets.reverse.getD j ([], [], 0)).1.length,
          (x3 - (sets.reverse.getD j ([], [], 0)).1.getD m 0)⁻¹ = 0 := by
  have hn : sets.length = sets.length - 1 + 1 := (Nat.succ_pred_eq_of_pos hlen).symm
  obtain ⟨ξ, hξinj, _hξ0, hξacc⟩ :=
    exists_injective_accepting_of_measure (acc := acc) hx₀ hprob
  exact multiopenEval_perSet_zero_of_samples (fun r => ξ (Fin.cast hn r))
    (fun r r' h => Fin.cast_injective hn (hξinj h))
    (fun r => hvanish _ (hξacc (Fin.cast hn r))) j

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

/-- **F6: `hgood` is derived from the `x`-accept measure, not assumed.** Composing `gateGood_of_xProb`
with `not_mem_szBadSet`: an accept measure over the deployed `x`-squeeze beating `natDegree C / p`
yields an accepting challenge `xv` at which the gate-check difference `C` satisfies exactly the `hgood`
shape — if the identity fails as polynomials, its evaluation at `xv` is nonzero. So the terminal's
`hgood` premise is dischargeable at the good challenge produced by the floor. -/
theorem hgood_of_xProb {acc : Fp → Prop} [DecidablePred acc] (C : Polynomial Fp)
    (hprob : (C.natDegree : ℝ≥0∞) / (Fintype.card Fp : ℝ≥0∞)
      < uniformChallenge.toOuterMeasure (Finset.univ.filter acc)) :
    ∃ xv, acc xv ∧ (C ≠ 0 → C.eval xv ≠ 0) := by
  obtain ⟨xv, hacc, hxv⟩ := gateGood_of_xProb C hprob
  exact ⟨xv, hacc, not_mem_szBadSet.mp hxv⟩

end Zcash.Snark
