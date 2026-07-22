import Zcash.Snark.Soundness.Multiopen.Claimed
import Zcash.Snark.Soundness.Multiopen.ValueCheckDeployed

/-!
# F3: the deployed `x₃` value bridge

The multiopen value check binds each decoded aggregate column to its claimed interpolation. The
counting-floor core (`Soundness.Multiopen.Claimed.claimedEval_of_x3Prob`) already turns an `x₃`
accept measure plus a per-accepting-run *consistency* — the decoded column reproduces the deployed
`r`-value at the accepting interpolation challenge — into the node binding: at each rotated set
point, the aggregate column's value is the claimed evaluation.

This module instantiates that core at the deployed grouping. `deployed_aggregate_node_binding_of_x3consistency`
fixes the decoded column to the fingerprinted `x₄`-slot aggregate for point set `j`
(`openedDecodedCols pbatch` at batch position `count − 1 − j`) and the accept event to
`OpenedX3Accept` (the `reprogramX3` rewinds, `Soundness.Multiopen.Opened`). The per-run consistency
`hconsistent` is the operative deployed hook — it is what the fixed-`q′` commitment binding across
the `x₃`-rewinds supplies (`openedDecodedCols_top_eval_x3` pins `q′` before `x₃`, so it is shared
across the family); producing it end-to-end from acceptance is the remaining constraint-side work.
-/

namespace Zcash.Snark

open Polynomial
open scoped ENNReal
open Classical

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- **The deployed multiopen value check for one point set's aggregate, from the `x₃` floor.**
`claimedEval_of_x3Prob` instantiated at the deployed grouping: the decoded `x₄`-slot aggregate
column for point set `j` (`openedDecodedCols pbatch` at batch position `count − 1 − j`), given the
per-accepting-run consistency `hconsistent` (the column reproduces the claimed interpolation
`lagrangeEval χ points evals` at every accepting `x₃`-rewind `χ`) and an `OpenedX3Accept` measure
beating `(|points| − 1) / p`, takes its claimed evaluation at each rotated set point. The consistency
premise is the fixed-`q′` commitment-binding hook (`openedDecodedCols_top_eval_x3`): `q′` is absorbed
before `x₃`, so the aggregate is a single fixed polynomial across the rewound family, and the value
check pins it to the `r`-interpolant — the node binding, with no vanishing assumed. -/
theorem deployed_aggregate_node_binding_of_x3consistency [DecidableEq G] [Inhabited G]
    {shape : Shape} (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {b a₀ : Fin (2 ^ urs.k) → Fp} {pU pW : Fp}
    (pbatch : OpenedBatchOpenings urs (evalVector urs.k ch.x3)
      (x4BatchCommitments urs hk vk ps ch) (x4BatchEvals vk ps ch) a₀ pU pW)
    (j : ℕ) (hj : j < deployedX4PairCount vk ps ch)
    {points evals : List Fp}
    (hlen : 0 < points.length)
    (hnode : Function.Injective (fun i : Fin points.length => points[i]))
    (hdeg : (openedDecodedCols pbatch ⟨deployedX4PairCount vk ps ch - 1 - j, by omega⟩).natDegree
      < points.length)
    (hconsistent : ∀ χ, OpenedX3Accept urs hk vk ps ch b χ →
      (openedDecodedCols pbatch ⟨deployedX4PairCount vk ps ch - 1 - j, by omega⟩).eval χ
        = lagrangeEval χ points evals)
    {χ₀ : Fp} (hχ₀ : OpenedX3Accept urs hk vk ps ch b χ₀)
    (hprob : (((points.length - 1 : ℕ)) : ℝ≥0∞) / Fintype.card Fp
      < (PMF.uniformOfFintype Fp).toOuterMeasure
          (Finset.univ.filter (OpenedX3Accept urs hk vk ps ch b)))
    (i : Fin points.length) :
    (openedDecodedCols pbatch ⟨deployedX4PairCount vk ps ch - 1 - j, by omega⟩).eval points[i]
      = evals.getD (i : ℕ) 0 :=
  claimedEval_of_x3Prob hlen hnode hdeg (OpenedX3Accept urs hk vk ps ch b) hconsistent hχ₀ hprob i

/-- **Per-rewind IPA relation from an `x₃` accept (discharge step 1).** Extracting the opening from
`OpenedX3Accept`: an accepting `x₃`-rewound run's forked transcript opens its commitment to the
run's own `multiopenValue`, so `ipaRelation_extract` yields an `IpaRelation` witness. This is the
entry point for discharging the `hconsistent` premise of
`deployed_aggregate_node_binding_of_x3consistency` — but only the entry point: turning this single
combined-value opening into the per-set value identity `col_j.eval χ = uⱼ` requires *decoding the
rewound run's `x₄` batch* (its own `x₄`-rewind family) and the inner `x₂` separation, i.e. nested
`x₄`- and `x₂`-accept measures per `x₃`-sample. Those nested measures are the remaining constraint. -/
theorem openedX3_relation_of_accept [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {b : Fin (2 ^ urs.k) → Fp} {χ : Fp}
    (hacc : OpenedX3Accept urs hk vk ps ch b χ) :
    ∃ (r : X3Run shape G) (z blind : Fp)
      (fs : ForkedTranscript urs hk vk (r.spliced ps) (r.challenges ch χ) b z blind)
      (a : Fin (2 ^ urs.k) → Fp),
      IpaRelation urs fs.openedCommitment b
        (multiopenValue vk (r.spliced ps) (r.challenges ch χ)) a := by
  obtain ⟨r, z, blind, fs, t, ht⟩ := hacc
  obtain ⟨a, ha⟩ := ipaRelation_extract urs b fs.openedCommitment
    (multiopenValue vk (r.spliced ps) (r.challenges ch χ)) t ht
  exact ⟨r, z, blind, fs, a, ha⟩

/-- **Augmented two-openings binding (discharge step 4 lever).** The `U`/`W`-carrying generalization
of `hasNontrivialRelation_of_two_openings`: if two witness vectors open the *same* group element in
augmented form (`commit a + αU·U + αW·W = commit a' + βU·U + βW·W`), then either the witnesses agree
or a nontrivial `(g, U, W)` relation exists. This is what identifies the decoded `x₄`-slot aggregate
of an `x₃`-rewound run with the honest one: their column commitments coincide
(`x3Run_x4Qs`/`x3Run_qPrime` — the aggregates are fixed before `x₃`), so the two augmented openings
of the shared commitment force equal witnesses, else break binding. -/
theorem hasNontrivialRelation_of_two_augmented_openings (urs : URS G)
    {a a' : Fin (2 ^ urs.k) → Fp} {αU αW βU βW : Fp}
    (h : commit urs a + αU • urs.u + αW • urs.w = commit urs a' + βU • urs.u + βW • urs.w) :
    a = a' ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  by_cases hae : a = a'
  · exact Or.inl hae
  · refine Or.inr ⟨a - a', αU - βU, αW - βW, Or.inl (sub_ne_zero.mpr hae), ?_⟩
    have hsub : commitGen (F := Fp) urs.g (a - a') = commit urs a - commit urs a' := by
      simp only [commit, commitGen, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
    rw [hsub, sub_smul, sub_smul]
    have h0 := sub_eq_zero.mpr h
    rw [← h0]
    abel

/-- **The rewound run's decoded aggregate value at χ (discharge steps 2+3).** From an
`OpenedX3Accept` at base `evalVector urs.k χ` — the base the accepting `x₃`-rewound run's IPA opens
over, since its own interpolation challenge is `χ` — plus that run's `x₄`-rewind accept measure,
`openedX4Rewind_of_x4Prob_forked` (fed the run's own accepting tree as its current-slot event and the
per-rewind `IpaRelation` from `openedX3_relation_of_accept`) produces an `OpenedBatchOpenings` for the
rewound run over base `evalVector urs.k χ`; `openedDecodedCols_eval_x3` then fires (the base matches
the run's `x₃ = χ`), pinning the run's decoded `x₄`-slot aggregate at `χ` to its claimed set
evaluation. The base is χ-dependent — resolving the apparent base-vector mismatch entirely at the use
site, no signature change: the honest `pbatch` (base `evalVector ch.x3`) only *defines* the aggregate
polynomial, whose value at `χ` is base-free. The nested `x₄` measure is a genuine floor, quantified
over the run (`∀ r`) since the run is existential in the accept. -/
theorem openedX3_rewound_aggregate_value [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) {χ : Fp} (j : ℕ)
    (hprob4 : ∀ r : X3Run shape G,
      (deployedX4PairCount vk (r.spliced ps) (r.challenges ch χ) : ℝ≥0∞) / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
            (OpenedX4Accept urs hk vk (r.spliced ps) (r.challenges ch χ) (evalVector urs.k χ))))
    (hacc : OpenedX3Accept urs hk vk ps ch (evalVector urs.k χ) χ) :
    ∃ (r : X3Run shape G) (a : Fin (2 ^ urs.k) → Fp) (pU pW : Fp)
      (batch : OpenedBatchOpenings urs (evalVector urs.k χ)
        (x4BatchCommitments urs hk vk (r.spliced ps) (r.challenges ch χ))
        (x4BatchEvals vk (r.spliced ps) (r.challenges ch χ)) a pU pW),
      (openedDecodedCols batch
          ⟨deployedX4PairCount vk (r.spliced ps) (r.challenges ch χ) - 1 - j, by omega⟩).eval χ
        = x4BatchEvals vk (r.spliced ps) (r.challenges ch χ)
          ⟨deployedX4PairCount vk (r.spliced ps) (r.challenges ch χ) - 1 - j, by omega⟩ := by
  obtain ⟨r, z, blind, fs, t, ht⟩ := hacc
  obtain ⟨a, ha⟩ := ipaRelation_extract urs (evalVector urs.k χ) fs.openedCommitment
    (multiopenValue vk (r.spliced ps) (r.challenges ch χ)) t ht
  refine ⟨r, a, fs.pU, fs.pW,
    openedX4Rewind_of_x4Prob_forked urs hk vk (r.spliced ps) (r.challenges ch χ) fs ⟨t, ht⟩
      (hprob4 r) a ha, ?_⟩
  exact openedDecodedCols_eval_x3 urs hk vk (r.spliced ps) (r.challenges ch χ) _ _

set_option maxHeartbeats 1000000 in
/-- **Binding the rewound aggregate to the honest one (discharge step 4).** The honest `pbatch` and a
rewound run's batch decode the *same* `x₄`-slot aggregate commitment — the point-set aggregates are
fixed before `x₃` (`x3Run_x4Qs`/`x3Run_qPrime`), so `x4BatchCommitments` agrees slot-for-slot. Both
decodes therefore give augmented openings of one group element; `hasNontrivialRelation_of_two_augmented_openings`
forces their coefficient vectors equal (hence the decoded aggregate polynomials equal), or exhibits a
nontrivial `(g, U, W)` relation. This is what lets the fixed honest `col_j` inherit the rewound run's
value identity at `χ`. -/
theorem openedX3_agg_binding [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) (r : X3Run shape G) {χ : Fp}
    (j : ℕ) (hj : j < deployedX4PairCount vk ps ch)
    {pU pW : Fp} {aa : Fin (2 ^ urs.k) → Fp}
    (pbatch : OpenedBatchOpenings urs (evalVector urs.k ch.x3)
      (x4BatchCommitments urs hk vk ps ch) (x4BatchEvals vk ps ch) aa pU pW)
    {aχ : Fin (2 ^ urs.k) → Fp} {pUχ pWχ : Fp}
    (batch_χ : OpenedBatchOpenings urs (evalVector urs.k χ)
      (x4BatchCommitments urs hk vk (r.spliced ps) (r.challenges ch χ))
      (x4BatchEvals vk (r.spliced ps) (r.challenges ch χ)) aχ pUχ pWχ) :
    openedDecodedCols pbatch ⟨deployedX4PairCount vk ps ch - 1 - j, by omega⟩
        = openedDecodedCols batch_χ
          ⟨deployedX4PairCount vk (r.spliced ps) (r.challenges ch χ) - 1 - j, by omega⟩
      ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  have hcc : deployedX4PairCount vk (r.spliced ps) (r.challenges ch χ)
      = deployedX4PairCount vk ps ch := x3Run_pairCount vk ps ch r χ
  -- the two batches decode the same x₄-slot commitment
  have hcommeq : x4BatchCommitments urs hk vk ps ch
        ⟨deployedX4PairCount vk ps ch - 1 - j, by omega⟩
      = x4BatchCommitments urs hk vk (r.spliced ps) (r.challenges ch χ)
        ⟨deployedX4PairCount vk (r.spliced ps) (r.challenges ch χ) - 1 - j, by omega⟩ := by
    have hidx : deployedX4PairCount vk ps ch - 1 - (deployedX4PairCount vk ps ch - 1 - j)
        = deployedX4PairCount vk (r.spliced ps) (r.challenges ch χ) - 1
            - (deployedX4PairCount vk (r.spliced ps) (r.challenges ch χ) - 1 - j) := by omega
    rw [x4BatchCommitments_getD urs hk vk ps ch (j := ⟨_, by omega⟩) (by simp only [Fin.val_mk]; omega),
      x4BatchCommitments_getD urs hk vk (r.spliced ps) (r.challenges ch χ) (j := ⟨_, by omega⟩)
        (by simp only [Fin.val_mk]; omega),
      x3Run_x4Qs, hidx]
  have hc1 := (openedColumnDecode pbatch).commitment
    ⟨deployedX4PairCount vk ps ch - 1 - j, by omega⟩
  have hc2 := (openedColumnDecode batch_χ).commitment
    ⟨deployedX4PairCount vk (r.spliced ps) (r.challenges ch χ) - 1 - j, by omega⟩
  rcases hasNontrivialRelation_of_two_augmented_openings urs
      (hc1.trans (hcommeq.trans hc2.symm)) with heq | hdlr
  · exact Or.inl (by simp only [openedDecodedCols, heq])
  · exact Or.inr hdlr

/-- **Per-χ consistency, reduced to the inner `x₂` consistency (discharge steps 2-4 combined).**
Composing the rewound aggregate value (steps 2-3) with the binding (step 4): at an accepting
`x₃`-rewind `χ`, the honest aggregate `col_j` evaluates at `χ` to the rewound run's claimed set
evaluation, which the inner-`x₂` consistency `hx2cons` (the run's claimed set eval equals the
`r`-interpolation `lagrangeEval χ points evals`) identifies with the deployed `r`-value — the
per-χ `hconsistent` for `deployed_aggregate_node_binding_of_x3consistency`, or a `HasNontrivialRelation`.
The `hx2cons` premise is the innermost fork: it is discharged by the `x₂` set-separation
(`claimedCombined_of_x2Prob`) at the rewound run — a nested `x₂` accept measure per `x₃`-sample. -/
theorem openedX3_perχ_consistency [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) {χ : Fp} (j : ℕ)
    (hj : j < deployedX4PairCount vk ps ch)
    {pU pW : Fp} {aa : Fin (2 ^ urs.k) → Fp}
    (pbatch : OpenedBatchOpenings urs (evalVector urs.k ch.x3)
      (x4BatchCommitments urs hk vk ps ch) (x4BatchEvals vk ps ch) aa pU pW)
    {points evals : List Fp}
    (hprob4 : ∀ r : X3Run shape G,
      (deployedX4PairCount vk (r.spliced ps) (r.challenges ch χ) : ℝ≥0∞) / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
            (OpenedX4Accept urs hk vk (r.spliced ps) (r.challenges ch χ) (evalVector urs.k χ))))
    (hx2cons : ∀ r : X3Run shape G,
      x4BatchEvals vk (r.spliced ps) (r.challenges ch χ)
          ⟨deployedX4PairCount vk (r.spliced ps) (r.challenges ch χ) - 1 - j, by omega⟩
        = lagrangeEval χ points evals)
    (hacc : OpenedX3Accept urs hk vk ps ch (evalVector urs.k χ) χ) :
    (openedDecodedCols pbatch ⟨deployedX4PairCount vk ps ch - 1 - j, by omega⟩).eval χ
        = lagrangeEval χ points evals
      ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  obtain ⟨r, a, pUχ, pWχ, batch, hval⟩ :=
    openedX3_rewound_aggregate_value urs hk vk ps ch j hprob4 hacc
  rcases openedX3_agg_binding urs hk vk ps ch r j hj pbatch batch with heq | hdlr
  · exact Or.inl (by rw [heq, hval, hx2cons r])
  · exact Or.inr hdlr

set_option maxHeartbeats 1000000 in
/-- **The deployed `x₃` value check, closed to the inner `x₂` consistency (F3 capstone).** Assembling
the per-χ consistency (`openedX3_perχ_consistency`) over the `x₃`-rewind family: *either* the honest
`x₄`-slot aggregate for point set `j` takes its claimed interpolation at each rotated set point (the
node binding, via `claimedEval_of_x3Prob` at the χ-dependent accept), *or* a nontrivial `(g, U, W)`
relation exists. Classical case split on whether the per-χ consistency holds for every accepting
`x₃`-rewind: if it does, the `x₃` floor pins the aggregate to the `r`-polynomial; if it fails at some
`χ`, the per-χ dichotomy there yields the relation. The remaining premises are all genuine forking
floors — the `x₃` accept measure `hprob`, the nested `x₄` measures `hprob4`, and the inner `x₂`
consistency `hx2cons` (discharged by `claimedCombined_of_x2Prob` at each rewound run, the innermost
fork). No `hconsistent` assumed: it is produced here. -/
theorem deployed_aggregate_node_binding_or_dlr [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {pU pW : Fp} {aa : Fin (2 ^ urs.k) → Fp}
    (pbatch : OpenedBatchOpenings urs (evalVector urs.k ch.x3)
      (x4BatchCommitments urs hk vk ps ch) (x4BatchEvals vk ps ch) aa pU pW)
    (j : ℕ) (hj : j < deployedX4PairCount vk ps ch)
    {points evals : List Fp}
    (hlen : 0 < points.length)
    (hnode : Function.Injective (fun i : Fin points.length => points[i]))
    (hdeg : (openedDecodedCols pbatch ⟨deployedX4PairCount vk ps ch - 1 - j, by omega⟩).natDegree
      < points.length)
    (hprob4 : ∀ χ : Fp, ∀ r : X3Run shape G,
      (deployedX4PairCount vk (r.spliced ps) (r.challenges ch χ) : ℝ≥0∞) / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
            (OpenedX4Accept urs hk vk (r.spliced ps) (r.challenges ch χ) (evalVector urs.k χ))))
    (hx2cons : ∀ χ : Fp, ∀ r : X3Run shape G,
      x4BatchEvals vk (r.spliced ps) (r.challenges ch χ)
          ⟨deployedX4PairCount vk (r.spliced ps) (r.challenges ch χ) - 1 - j, by omega⟩
        = lagrangeEval χ points evals)
    {χ₀ : Fp} (hχ₀ : OpenedX3Accept urs hk vk ps ch (evalVector urs.k χ₀) χ₀)
    (hprob : (((points.length - 1 : ℕ)) : ℝ≥0∞) / Fintype.card Fp
      < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
          (fun χ => OpenedX3Accept urs hk vk ps ch (evalVector urs.k χ) χ)))
    (i : Fin points.length) :
    (openedDecodedCols pbatch ⟨deployedX4PairCount vk ps ch - 1 - j, by omega⟩).eval points[i]
        = evals.getD (i : ℕ) 0
      ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  by_cases hcons : ∀ χ, OpenedX3Accept urs hk vk ps ch (evalVector urs.k χ) χ →
      (openedDecodedCols pbatch ⟨deployedX4PairCount vk ps ch - 1 - j, by omega⟩).eval χ
        = lagrangeEval χ points evals
  · exact Or.inl (claimedEval_of_x3Prob hlen hnode hdeg
      (fun χ => OpenedX3Accept urs hk vk ps ch (evalVector urs.k χ) χ) hcons hχ₀ hprob i)
  · push_neg at hcons
    obtain ⟨χ, hPχ, hne⟩ := hcons
    rcases openedX3_perχ_consistency urs hk vk ps ch j hj pbatch (hprob4 χ) (hx2cons χ) hPχ with
      hc | hdlr
    · exact absurd hc hne
    · exact Or.inr hdlr

/-- **The `hx2cons` slot is the claimed set evaluation `uⱼ` (inner-`x₂` reduction).** Unfolding the
`x₄`-batch eval at point set `j`'s slot `count − 1 − j` through `x4BatchEvals_getD`: it is exactly the
prover's claimed set evaluation `multiopenUⱼ`. So the remaining F3 premise `hx2cons`
(`x4BatchEvals … ⟨count−1−j⟩ = lagrangeEval χ points evals`) is precisely *the claimed set evaluation
equals the `r`-interpolation* — the halo2 multiopen's per-set value soundness. Discharging it is the
inner `x₂` set-separation, which — as `claimedCombined_of_x2Prob`'s caveat notes and the `X2Run`
structure confirms (`q′` is *re-sent* across `x₂`-rewinds, so there is no fixed-`q′` anchor at `x₂`) —
is the genuine remaining constraint-side obligation, not a direct existing-lemma call. -/
theorem hx2cons_slot_eq_multiopenU [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {j : ℕ} (hj : j < deployedX4PairCount vk ps ch) :
    x4BatchEvals vk ps ch ⟨deployedX4PairCount vk ps ch - 1 - j, by omega⟩
      = (List.ofFn ps.multiopenU).getD j 0 := by
  rw [x4BatchEvals_getD vk ps ch
    (j := ⟨deployedX4PairCount vk ps ch - 1 - j, by omega⟩) (by simp only [Fin.val_mk]; omega)]
  congr 1
  simp only [Fin.val_mk]
  omega

/-- `multiopenEval` in forward-order power form: reindexing `multiopenEval_powerForm` by set
reflection, so ascending set index `j` carries `x₂^(len−1−j)` and reads `sets.getD j` directly
(no `reverse`). The bookkeeping step toward matching the deployed value check against the
per-set `hsamp` shape of `deployed_setAggregate_node_binding`. -/
theorem multiopenEval_powerForm_forward (x2 x3 : Fp) (sets : List (List Fp × List Fp × Fp)) :
    multiopenEval x2 x3 sets
      = ∑ j ∈ Finset.range sets.length,
          x2 ^ (sets.length - 1 - j) * (((sets.getD j ([], [], 0)).2.2
              - lagrangeEval x3 (sets.getD j ([], [], 0)).1 (sets.getD j ([], [], 0)).2.1)
            * ∏ m ∈ Finset.range (sets.getD j ([], [], 0)).1.length,
                (x3 - (sets.getD j ([], [], 0)).1.getD m 0)⁻¹) := by
  rw [multiopenEval_powerForm]
  conv_rhs => rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  simp only [Finset.mem_range] at hj
  have hrev : sets.reverse.getD j ([], [], 0) = sets.getD (sets.length - 1 - j) ([], [], 0) := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_reverse (by omega)]
  rw [hrev, show sets.length - 1 - (sets.length - 1 - j) = j from by omega]

/-- The product over a distinct point list's *indices* equals the product over its point *finset* —
the `hsamp` denominator's product-shape conversion (`∏ over range length` ↔ `∏ over deployedSetPts`). -/
theorem prod_range_getD_eq_toFinset {l : List Fp} (hnd : l.Nodup) (χ : Fp) :
    (∏ m ∈ Finset.range l.length, (χ - l.getD m 0)) = ∏ p ∈ l.toFinset, (χ - p) := by
  rw [← Fin.prod_univ_eq_prod_range (fun m => χ - l.getD m 0) l.length]
  refine Finset.prod_bij (fun (i : Fin l.length) _ => l.get i) ?_ ?_ ?_ ?_
  · intro i _; exact List.mem_toFinset.mpr (List.get_mem l i)
  · intro i _ i' _ h
    exact (List.nodup_iff_injective_get.mp hnd) (by simpa using h)
  · intro p hp
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp hp)
    exact ⟨i, Finset.mem_univ _, hi⟩
  · intro i _
    simp [List.getD_eq_getElem, List.get_eq_getElem, i.isLt]

/-- Inverse form of the product-shape conversion. -/
theorem prod_inv_range_getD_eq_toFinset {l : List Fp} (hnd : l.Nodup) (χ : Fp) :
    (∏ m ∈ Finset.range l.length, (χ - l.getD m 0)⁻¹) = (∏ p ∈ l.toFinset, (χ - p))⁻¹ := by
  rw [← prod_range_getD_eq_toFinset hnd χ, ← Finset.prod_inv_distrib]

/-- **`hsamp` from the value-check power form (reversed convention).** The per-`x₂`-value multiopen
value identity in exactly the shape `node_binding_of_samples` consumes, with the set index reversed
(`ζʲ` pairs with `sets.reverse.getD j`, resolving the power/index convention gap between the deployed
`multiopenEval` and the abstract value check). Given the run's opening `qv = multiopenEval ζ χ sets`
and, per reversed index `j`, the field identifications — the decoded aggregate value `(col j).eval χ`
is the claimed set eval `(sets.reverse.getD j).2.2`, `(r j).eval χ` is the interpolation, and the
set's point list is `Nodup` with `toFinset = pts j` — the value expands to
`∑ⱼ ζʲ (colⱼ − rⱼ)(χ)·(∏ p∈pts j, (χ − p))⁻¹`. Pure algebra over `multiopenEval_powerForm` and
`prod_inv_range_getD_eq_toFinset`; this is the `hsamp` premise of `node_binding_of_samples`. -/
theorem hsamp_of_multiopenEval_reversed {numSets : ℕ}
    (sets : List (List Fp × List Fp × Fp)) (hlen : sets.length = numSets)
    (col r : Fin numSets → Polynomial Fp) (pts : Fin numSets → Finset Fp)
    (ζ χ qv : Fp)
    (hqv : qv = multiopenEval ζ χ sets)
    (hnd : ∀ j : Fin numSets, (sets.reverse.getD (j : ℕ) ([], [], 0)).1.Nodup)
    (hpts : ∀ j : Fin numSets, (sets.reverse.getD (j : ℕ) ([], [], 0)).1.toFinset = pts j)
    (hu : ∀ j : Fin numSets, (col j).eval χ = (sets.reverse.getD (j : ℕ) ([], [], 0)).2.2)
    (hr : ∀ j : Fin numSets, (r j).eval χ
        = lagrangeEval χ (sets.reverse.getD (j : ℕ) ([], [], 0)).1
            (sets.reverse.getD (j : ℕ) ([], [], 0)).2.1) :
    qv = ∑ j : Fin numSets, ζ ^ (j : ℕ) * (col j - r j).eval χ * (∏ p ∈ pts j, (χ - p))⁻¹ := by
  rw [hqv, multiopenEval_powerForm, hlen, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [eval_sub, hu j, hr j, ← hpts j, ← prod_inv_range_getD_eq_toFinset (hnd j) χ]
  ring

/-- **Node binding from a grid of run openings (F3 step-4 assembly).** Composing
`hsamp_of_multiopenEval_reversed` with `node_binding_of_samples`: at each grid point `(s, t)` an
`x₂`-value `ζ s` and interpolation challenge `χ s t`, the run's opening exposes the quotient column's
value as `multiopenEval (ζ s) (χ s t) (sets s t)` (`hopen`), and the reversed field identifications
(`hnd`/`hpts`/`hu`/`hr`) turn that into the per-`x₂` `hsamp` shape. Given enough distinct `ζ`
(injective) and `χ s` samples, the cleared-denominator Schwartz–Zippel core forces, at each set
point, the aggregate column to take its interpolated value: `(col j₀).eval p = (r j₀).eval p`. This
is the deployed value check reduced to its openings + field identifications — no vanishing assumed;
the remaining obligation is to supply `hopen`/`hu` from acceptance (the nested `x₂`×`x₃` grid) and the
deployed field identifications. -/
theorem node_binding_of_grid_openings {numSets : ℕ}
    (allPts : Finset Fp) (pts : Fin numSets → Finset Fp) (hsub : ∀ j, pts j ⊆ allPts)
    (col r qCol : Fin numSets → Polynomial Fp)
    (ζ : Fin numSets → Fp) (hζ : Function.Injective ζ) (d : ℕ)
    (hdeg : ∀ s, (qCol s * vanishingProd allPts
        - ∑ j : Fin numSets, C (ζ s ^ (j : ℕ)) *
            ((col j - r j) * coProd allPts (pts j))).natDegree ≤ d)
    (χ : Fin numSets → Fin (d + 1) → Fp) (hχinj : ∀ s, Function.Injective (χ s))
    (hnode : ∀ s t j, (vanishingProd (pts j)).eval (χ s t) ≠ 0)
    (sets : Fin numSets → Fin (d + 1) → List (List Fp × List Fp × Fp))
    (hlen : ∀ s t, (sets s t).length = numSets)
    (hopen : ∀ s t, (qCol s).eval (χ s t) = multiopenEval (ζ s) (χ s t) (sets s t))
    (hnd : ∀ s t (j : Fin numSets), ((sets s t).reverse.getD (j : ℕ) ([], [], 0)).1.Nodup)
    (hpts : ∀ s t (j : Fin numSets), ((sets s t).reverse.getD (j : ℕ) ([], [], 0)).1.toFinset = pts j)
    (hu : ∀ s t (j : Fin numSets),
      (col j).eval (χ s t) = ((sets s t).reverse.getD (j : ℕ) ([], [], 0)).2.2)
    (hr : ∀ s t (j : Fin numSets), (r j).eval (χ s t)
        = lagrangeEval (χ s t) ((sets s t).reverse.getD (j : ℕ) ([], [], 0)).1
            ((sets s t).reverse.getD (j : ℕ) ([], [], 0)).2.1)
    (j₀ : Fin numSets) {p : Fp} (hp : p ∈ pts j₀) (hpall : p ∈ allPts) :
    (col j₀).eval p = (r j₀).eval p :=
  node_binding_of_samples allPts pts hsub col r qCol ζ hζ d hdeg χ hχinj hnode
    (fun s t => hsamp_of_multiopenEval_reversed (sets s t) (hlen s t) col r pts (ζ s) (χ s t)
      ((qCol s).eval (χ s t)) (hopen s t) (hnd s t) (hpts s t) (hu s t) (hr s t))
    j₀ hp hpall

/-- The deployed multiopen value-check `sets` (halo2 `setsForEval`): per point set, its points, the
`x₁`-compressed evaluation vector, and the prover's claimed set evaluation `multiopenUⱼ`. This is the
list `deployedBaseEval` feeds `multiopenEval`; naming it lets the value check's field identifications
be stated. -/
noncomputable def deployedSetsForEval [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) :
    List (List Fp × List Fp × Fp) :=
  let grouped := constructIntermediateSets (assembleQueries vk ps ch)
  let compressed := (grouped.sets.zip grouped.points).map (fun sp => compressSet ch.x1 sp.1 sp.2.length)
  ((grouped.points.zip (compressed.map Prod.snd)).zip (List.ofFn ps.multiopenU)).map
    (fun p => (p.1.1, p.1.2, p.2))

/-- `deployedBaseEval` is `multiopenEval` over `deployedSetsForEval` — definitional. -/
theorem deployedBaseEval_eq_multiopenEval [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) :
    deployedBaseEval vk ps ch = multiopenEval ch.x2 ch.x3 (deployedSetsForEval vk ps ch) := rfl

/-- **Shape alignment: the value-check `sets` has exactly `deployedX4PairCount` entries.** Both reduce
to `min(min(gsets.length, gpoints.length), numPointSets)` — the grouping's set count clipped to the
prover's claimed-eval count — so no `= shape.numPointSets` fact is needed. This lets the deployed
value check be instantiated at `numSets := deployedX4PairCount`. -/
theorem deployedSetsForEval_length [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) :
    (deployedSetsForEval vk ps ch).length = deployedX4PairCount vk ps ch := by
  have hsp := constructIntermediateSets_points_length (assembleQueries vk ps ch)
  simp only [deployedSetsForEval, deployedX4PairCount, deployedX4Pairs, deployedX4Qs,
    List.length_map, List.length_zip, List.length_ofFn]
  omega

/-- The `j`-th value-check set's point list is grouping point set `j`'s points — so its finset is
`deployedSetPts j`. The points-field identification for `node_binding_of_grid_openings`. -/
theorem deployedSetsForEval_getD_points [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {k : ℕ} (hk : k < deployedX4PairCount vk ps ch) :
    ((deployedSetsForEval vk ps ch).getD k ([], [], 0)).1
      = (constructIntermediateSets (assembleQueries vk ps ch)).points.getD k [] := by
  have hlen := deployedSetsForEval_length vk ps ch
  have hsp := constructIntermediateSets_points_length (assembleQueries vk ps ch)
  have hcount : deployedX4PairCount vk ps ch
      ≤ (constructIntermediateSets (assembleQueries vk ps ch)).points.length := by
    simp only [deployedX4PairCount, deployedX4Pairs, deployedX4Qs, List.length_map,
      List.length_zip, List.length_ofFn]
    omega
  rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact hk),
    List.getD_eq_getElem _ _ (by omega)]
  simp only [deployedSetsForEval, List.getElem_map, List.getElem_zip]

/-- The `j`-th value-check set's point finset is exactly `deployedSetPts j` — the `hpts`
field-identification for `node_binding_of_grid_openings`. -/
theorem deployedSetsForEval_getD_toFinset [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {k : ℕ} (hk : k < deployedX4PairCount vk ps ch) :
    ((deployedSetsForEval vk ps ch).getD k ([], [], 0)).1.toFinset = deployedSetPts vk ps ch k := by
  rw [deployedSetsForEval_getD_points vk ps ch hk, deployedSetPts]

/-- The `j`-th value-check set's point list is duplicate-free — the `hnd` field-identification for
`node_binding_of_grid_openings`, via `constructIntermediateSets_points_nodup`. -/
theorem deployedSetsForEval_getD_nodup [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {k : ℕ} (hk : k < deployedX4PairCount vk ps ch) :
    ((deployedSetsForEval vk ps ch).getD k ([], [], 0)).1.Nodup := by
  rw [deployedSetsForEval_getD_points vk ps ch hk]
  exact constructIntermediateSets_points_nodup _ _

/-- The `reverse`d value-check `sets`, at index `k`, reads grouping set `numSets − 1 − k`'s point
list — the reversed index the `multiopenEval` power convention pairs `x₂^k` with. -/
theorem deployedSetsForEval_reverse_getD_points [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {k : ℕ} (hk : k < deployedX4PairCount vk ps ch) :
    ((deployedSetsForEval vk ps ch).reverse.getD k ([], [], 0)).1
      = (constructIntermediateSets (assembleQueries vk ps ch)).points.getD
          (deployedX4PairCount vk ps ch - 1 - k) [] := by
  have hlen := deployedSetsForEval_length vk ps ch
  have htup : (deployedSetsForEval vk ps ch).reverse.getD k ([], [], 0)
      = (deployedSetsForEval vk ps ch).getD (deployedX4PairCount vk ps ch - 1 - k) ([], [], 0) := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_reverse (by rw [hlen]; exact hk), hlen]
  rw [htup]
  exact deployedSetsForEval_getD_points vk ps ch (by omega)

/-- The reversed value-check set's point finset is `deployedSetPts (numSets − 1 − k)` — the `hpts`
field-ID at the reversed indexing. -/
theorem deployedSetsForEval_reverse_getD_toFinset [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {k : ℕ} (hk : k < deployedX4PairCount vk ps ch) :
    ((deployedSetsForEval vk ps ch).reverse.getD k ([], [], 0)).1.toFinset
      = deployedSetPts vk ps ch (deployedX4PairCount vk ps ch - 1 - k) := by
  rw [deployedSetsForEval_reverse_getD_points vk ps ch hk, deployedSetPts]

/-- The reversed value-check set's point list is `Nodup` — the `hnd` field-ID at the reversed
indexing. -/
theorem deployedSetsForEval_reverse_getD_nodup [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {k : ℕ} (hk : k < deployedX4PairCount vk ps ch) :
    ((deployedSetsForEval vk ps ch).reverse.getD k ([], [], 0)).1.Nodup := by
  rw [deployedSetsForEval_reverse_getD_points vk ps ch hk]
  exact constructIntermediateSets_points_nodup _ _

/-- The reversed value-check set's claimed-eval (`u`) field at index `k` is the batch eval slot `k`
(`x4BatchEvals`) — the `u`-field counterpart of `deployedSetsForEval_reverse_getD_points`. Both reduce
to the prover's claimed set eval `multiopenU` at position `count − 1 − k`: `deployedSetsForEval`'s
`.2.2` and `deployedX4Pairs`'s `.2` are the same `List.ofFn ps.multiopenU` component. This is the
identity `deployed_node_binding_of_grid`'s `hu` needs to match `openedX3_rewound_batch_eval`'s
`x4BatchEvals` values to `(sets s t).reverse.getD j |>.2.2`. -/
theorem deployedSetsForEval_reverse_getD_u [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {k : ℕ} (hk : k < deployedX4PairCount vk ps ch) :
    ((deployedSetsForEval vk ps ch).reverse.getD k ([], [], 0)).2.2
      = x4BatchEvals vk ps ch ⟨k, Nat.lt_succ_of_lt hk⟩ := by
  have hlenS := deployedSetsForEval_length vk ps ch
  have hlenP : (deployedX4Pairs vk ps ch).length = deployedX4PairCount vk ps ch := rfl
  have hik : deployedX4PairCount vk ps ch - 1 - k < deployedX4PairCount vk ps ch := by omega
  -- per-index: both the value-check set's u-field and the batch pair's eval are `multiopenU[i]`
  have key : ((deployedSetsForEval vk ps ch).getD
        (deployedX4PairCount vk ps ch - 1 - k) ([], [], 0)).2.2
      = ((deployedX4Pairs vk ps ch).getD
        (deployedX4PairCount vk ps ch - 1 - k) (Msm.zero shape.k Fp G, 0)).2 := by
    rw [List.getD_eq_getElem _ _ (by rw [hlenS]; exact hik),
        List.getD_eq_getElem _ _ (by rw [hlenP]; exact hik)]
    simp only [deployedSetsForEval, deployedX4Pairs, List.getElem_map, List.getElem_zip]
  -- reduce `x4BatchEvals ⟨k⟩` (k < count) and both reverses to forward `getD (count−1−k)`
  rw [x4BatchEvals]
  simp only [hk, if_true]
  rw [List.getD_eq_getElem?_getD (l := (deployedSetsForEval vk ps ch).reverse),
      List.getElem?_reverse (by rw [hlenS]; exact hk), hlenS,
      ← List.getD_eq_getElem?_getD,
      List.getD_eq_getElem?_getD (l := (deployedX4Pairs vk ps ch).reverse),
      List.getElem?_reverse (by rw [hlenP]; exact hk), hlenP,
      ← List.getD_eq_getElem?_getD]
  exact key

set_option maxHeartbeats 1000000 in
/-- **The deployed value-check node binding, reduced to the grid openings (F3 instantiation).**
`node_binding_of_grid_openings` instantiated at the deployed grouping with the reversed indexing
`multiopenEval`'s `x₂`-power convention needs: `pts j := deployedSetPts (numSets − 1 − j)`,
`col j := openedDecodedCols pbatch ⟨j⟩`, `r j` the interpolant of set `numSets − 1 − j`'s points and
evals. The structural field identifications (`hnd`/`hpts`/`hr`) are discharged from the reversed
value-check-set lemmas + `lagrangePoly_eval`; what remains as premises is exactly the measure-based
grid — the run openings `hopen`, the per-grid `col = u` bindings `hu`, the sample injectivity and
distinctness — together with the grouping-fixity field agreements `hsetpts`/`hsetevals` (the grid
runs' value-check sets share the honest grouping's points/evals). This is the deployed value check
with everything except the nested `x₂`×`x₃` accept-measure extraction discharged. -/
theorem deployed_node_binding_of_grid [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {a₀ : Fin (2 ^ urs.k) → Fp} {pU pW : Fp}
    (pbatch : OpenedBatchOpenings urs (evalVector urs.k ch.x3)
      (x4BatchCommitments urs hk vk ps ch) (x4BatchEvals vk ps ch) a₀ pU pW)
    (d : ℕ)
    (ζ : Fin (deployedX4PairCount vk ps ch) → Fp) (hζ : Function.Injective ζ)
    (χ : Fin (deployedX4PairCount vk ps ch) → Fin (d + 1) → Fp)
    (hχinj : ∀ s, Function.Injective (χ s))
    (qCol : Fin (deployedX4PairCount vk ps ch) → Polynomial Fp)
    (sets : Fin (deployedX4PairCount vk ps ch) → Fin (d + 1) → List (List Fp × List Fp × Fp))
    (hlen : ∀ s t, (sets s t).length = deployedX4PairCount vk ps ch)
    (hsetpts : ∀ s t (j : Fin (deployedX4PairCount vk ps ch)),
      ((sets s t).reverse.getD (j : ℕ) ([], [], 0)).1
        = ((deployedSetsForEval vk ps ch).reverse.getD (j : ℕ) ([], [], 0)).1)
    (hsetevals : ∀ s t (j : Fin (deployedX4PairCount vk ps ch)),
      ((sets s t).reverse.getD (j : ℕ) ([], [], 0)).2.1
        = ((deployedSetsForEval vk ps ch).reverse.getD (j : ℕ) ([], [], 0)).2.1)
    (hdeg : ∀ s, ((qCol s) * vanishingProd (deployedAllPts vk ps ch)
        - ∑ j : Fin (deployedX4PairCount vk ps ch), C (ζ s ^ (j : ℕ)) *
            ((openedDecodedCols pbatch ⟨(j : ℕ), Nat.lt_succ_of_lt j.isLt⟩
              - lagrangePoly ((deployedSetsForEval vk ps ch).reverse.getD (j : ℕ) ([], [], 0)).1
                  ((deployedSetsForEval vk ps ch).reverse.getD (j : ℕ) ([], [], 0)).2.1)
              * coProd (deployedAllPts vk ps ch)
                  (deployedSetPts vk ps ch (deployedX4PairCount vk ps ch - 1 - (j : ℕ))))).natDegree
          ≤ d)
    (hnode : ∀ s t (j : Fin (deployedX4PairCount vk ps ch)),
      (vanishingProd (deployedSetPts vk ps ch
        (deployedX4PairCount vk ps ch - 1 - (j : ℕ)))).eval (χ s t) ≠ 0)
    (hopen : ∀ s t, (qCol s).eval (χ s t) = multiopenEval (ζ s) (χ s t) (sets s t))
    (hu : ∀ s t (j : Fin (deployedX4PairCount vk ps ch)),
      (openedDecodedCols pbatch ⟨(j : ℕ), Nat.lt_succ_of_lt j.isLt⟩).eval (χ s t)
        = ((sets s t).reverse.getD (j : ℕ) ([], [], 0)).2.2)
    (j₀ : Fin (deployedX4PairCount vk ps ch)) {p : Fp}
    (hp : p ∈ deployedSetPts vk ps ch (deployedX4PairCount vk ps ch - 1 - (j₀ : ℕ))) :
    (openedDecodedCols pbatch ⟨(j₀ : ℕ), Nat.lt_succ_of_lt j₀.isLt⟩).eval p
      = (lagrangePoly ((deployedSetsForEval vk ps ch).reverse.getD (j₀ : ℕ) ([], [], 0)).1
          ((deployedSetsForEval vk ps ch).reverse.getD (j₀ : ℕ) ([], [], 0)).2.1).eval p := by
  refine node_binding_of_grid_openings (deployedAllPts vk ps ch)
    (fun j => deployedSetPts vk ps ch (deployedX4PairCount vk ps ch - 1 - (j : ℕ)))
    (fun j => deployedSetPts_subset vk ps ch _)
    (fun j => openedDecodedCols pbatch ⟨(j : ℕ), Nat.lt_succ_of_lt j.isLt⟩)
    (fun j => lagrangePoly ((deployedSetsForEval vk ps ch).reverse.getD (j : ℕ) ([], [], 0)).1
        ((deployedSetsForEval vk ps ch).reverse.getD (j : ℕ) ([], [], 0)).2.1)
    qCol ζ hζ d hdeg χ hχinj hnode sets hlen hopen ?_ ?_ hu ?_ j₀ hp
    (deployedSetPts_subset vk ps ch _ hp)
  · -- hnd
    intro s t j
    rw [hsetpts s t j]; exact deployedSetsForEval_reverse_getD_nodup vk ps ch j.isLt
  · -- hpts
    intro s t j
    rw [hsetpts s t j]; exact deployedSetsForEval_reverse_getD_toFinset vk ps ch j.isLt
  · -- hr
    intro s t j
    rw [hsetpts s t j, hsetevals s t j]
    exact lagrangePoly_eval
      (List.nodup_iff_injective_getElem.mp (deployedSetsForEval_reverse_getD_nodup vk ps ch j.isLt))
      (χ s t)

/-- **Per-rewind IPA relation from an `x₂` accept (grid extraction, x₂ entry point).** The `x₂`
analogue of `openedX3_relation_of_accept`: an accepting `x₂`-rewound run's forked transcript opens
its commitment to the run's own `multiopenValue`, so `ipaRelation_extract` yields an `IpaRelation`
witness. `OpenedX2Accept` is structurally identical to `OpenedX3Accept` (both range over their run's
re-sent opening), so the extraction is the same. This is the outer entry point for the nested
`x₂`×`x₃` grid the deployed value check runs over. -/
theorem openedX2_relation_of_accept [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {b : Fin (2 ^ urs.k) → Fp} {χ : Fp}
    (hacc : OpenedX2Accept urs hk vk ps ch b χ) :
    ∃ (r : X2Run shape G) (z blind : Fp)
      (fs : ForkedTranscript urs hk vk (r.spliced ps) (r.challenges ch χ) b z blind)
      (a : Fin (2 ^ urs.k) → Fp),
      IpaRelation urs fs.openedCommitment b
        (multiopenValue vk (r.spliced ps) (r.challenges ch χ)) a := by
  obtain ⟨r, z, blind, fs, t, ht⟩ := hacc
  obtain ⟨a, ha⟩ := ipaRelation_extract urs b fs.openedCommitment
    (multiopenValue vk (r.spliced ps) (r.challenges ch χ)) t ht
  exact ⟨r, z, blind, fs, a, ha⟩

/-- **The rewound run's `q′` value at χ (grid `hopen` building block).** The top-slot companion of
`openedX3_rewound_aggregate_value`: from an `OpenedX3Accept` at base `evalVector urs.k χ` plus the
run's `x₄`-rewind measure, the extracted batch's decoded `q′` column (top slot, index `count`)
evaluates at `χ` to `deployedBaseEval` — which is `multiopenEval x₂ x₃ (deployedSetsForEval)`
(`deployedBaseEval_eq_multiopenEval`). Applied at an `x₂`-rewound base string this supplies the grid
opening `(qCol s).eval (χ s t) = multiopenEval (ζ s) (χ s t) sets` that `deployed_node_binding_of_grid`
consumes as `hopen`. -/
theorem openedX3_rewound_qprime_value [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) {χ : Fp}
    (hprob4 : ∀ r : X3Run shape G,
      (deployedX4PairCount vk (r.spliced ps) (r.challenges ch χ) : ℝ≥0∞) / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
            (OpenedX4Accept urs hk vk (r.spliced ps) (r.challenges ch χ) (evalVector urs.k χ))))
    (hacc : OpenedX3Accept urs hk vk ps ch (evalVector urs.k χ) χ) :
    ∃ (r : X3Run shape G) (a : Fin (2 ^ urs.k) → Fp) (pU pW : Fp)
      (batch : OpenedBatchOpenings urs (evalVector urs.k χ)
        (x4BatchCommitments urs hk vk (r.spliced ps) (r.challenges ch χ))
        (x4BatchEvals vk (r.spliced ps) (r.challenges ch χ)) a pU pW),
      (openedDecodedCols batch
          ⟨deployedX4PairCount vk (r.spliced ps) (r.challenges ch χ), Nat.lt_succ_self _⟩).eval χ
        = deployedBaseEval vk (r.spliced ps) (r.challenges ch χ) := by
  obtain ⟨r, z, blind, fs, t, ht⟩ := hacc
  obtain ⟨a, ha⟩ := ipaRelation_extract urs (evalVector urs.k χ) fs.openedCommitment
    (multiopenValue vk (r.spliced ps) (r.challenges ch χ)) t ht
  refine ⟨r, a, fs.pU, fs.pW,
    openedX4Rewind_of_x4Prob_forked urs hk vk (r.spliced ps) (r.challenges ch χ) fs ⟨t, ht⟩
      (hprob4 r) a ha, ?_⟩
  exact openedDecodedCols_top_eval_x3 urs hk vk (r.spliced ps) (r.challenges ch χ) _

set_option maxHeartbeats 1000000 in
/-- **Binding a rewound `x₂` run's aggregate to the honest one (grid `hu` building block).** The `x₂`
analogue of `openedX3_agg_binding`: the honest `pbatch` and a batch for an `x₂`-rewound run decode the
*same* `x₄`-slot commitment — the point-set aggregates are fixed before `x₂` (`x2Run_x4Qs`), so
`x4BatchCommitments` agrees slot-for-slot — hence their decoded aggregate polynomials are equal, or a
nontrivial `(g, U, W)` relation exists. Composed with `openedX3_agg_binding` at the `x₂`-rewound base
this discharges the grid `hu` for the doubly-rewound runs. -/
theorem openedX2_agg_binding [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) (r : X2Run shape G) {χ : Fp}
    (j : ℕ) (hj : j < deployedX4PairCount vk ps ch)
    {pU pW : Fp} {aa : Fin (2 ^ urs.k) → Fp}
    (pbatch : OpenedBatchOpenings urs (evalVector urs.k ch.x3)
      (x4BatchCommitments urs hk vk ps ch) (x4BatchEvals vk ps ch) aa pU pW)
    {aχ : Fin (2 ^ urs.k) → Fp} {pUχ pWχ : Fp}
    (batch_χ : OpenedBatchOpenings urs (evalVector urs.k χ)
      (x4BatchCommitments urs hk vk (r.spliced ps) (r.challenges ch χ))
      (x4BatchEvals vk (r.spliced ps) (r.challenges ch χ)) aχ pUχ pWχ) :
    openedDecodedCols pbatch ⟨deployedX4PairCount vk ps ch - 1 - j, by omega⟩
        = openedDecodedCols batch_χ
          ⟨deployedX4PairCount vk (r.spliced ps) (r.challenges ch χ) - 1 - j, by omega⟩
      ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  have hcc : deployedX4PairCount vk (r.spliced ps) (r.challenges ch χ)
      = deployedX4PairCount vk ps ch := x2Run_pairCount vk ps ch r χ
  have hcommeq : x4BatchCommitments urs hk vk ps ch
        ⟨deployedX4PairCount vk ps ch - 1 - j, by omega⟩
      = x4BatchCommitments urs hk vk (r.spliced ps) (r.challenges ch χ)
        ⟨deployedX4PairCount vk (r.spliced ps) (r.challenges ch χ) - 1 - j, by omega⟩ := by
    have hidx : deployedX4PairCount vk ps ch - 1 - (deployedX4PairCount vk ps ch - 1 - j)
        = deployedX4PairCount vk (r.spliced ps) (r.challenges ch χ) - 1
            - (deployedX4PairCount vk (r.spliced ps) (r.challenges ch χ) - 1 - j) := by omega
    rw [x4BatchCommitments_getD urs hk vk ps ch (j := ⟨_, by omega⟩) (by simp only [Fin.val_mk]; omega),
      x4BatchCommitments_getD urs hk vk (r.spliced ps) (r.challenges ch χ) (j := ⟨_, by omega⟩)
        (by simp only [Fin.val_mk]; omega),
      x2Run_x4Qs, hidx]
  have hc1 := (openedColumnDecode pbatch).commitment
    ⟨deployedX4PairCount vk ps ch - 1 - j, by omega⟩
  have hc2 := (openedColumnDecode batch_χ).commitment
    ⟨deployedX4PairCount vk (r.spliced ps) (r.challenges ch χ) - 1 - j, by omega⟩
  rcases hasNontrivialRelation_of_two_augmented_openings urs
      (hc1.trans (hcommeq.trans hc2.symm)) with heq | hdlr
  · exact Or.inl (by simp only [openedDecodedCols, heq])
  · exact Or.inr hdlr

set_option maxHeartbeats 1000000 in
/-- **Binding the doubly-rewound aggregate directly to the honest one (grid `hu` building block).**
The composed `x₂`-then-`x₃` analogue: the honest `pbatch` and a batch for a doubly-rewound run
(`x₂`-rewind `r₂` then `x₃`-rewind `r₃`) decode the *same* `x₄`-slot aggregate commitment — the
point-set aggregates are fixed before `x₂` (`x2Run_x4Qs`) and before `x₃` (`x3Run_x4Qs`), so
`deployedX4Qs` agrees at the doubly-rewound base — hence their decoded aggregate polynomials are
equal, or a nontrivial `(g, U, W)` relation exists. This is the direct `honest ↔ doubly-rewound`
binding the grid `hu` needs (no intermediate batch, avoiding the `x₂` base/challenge coupling). -/
theorem openedX2X3_agg_binding [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (r₂ : X2Run shape G) {ζ : Fp} (r₃ : X3Run shape G) {χ : Fp}
    (j : ℕ) (hj : j < deployedX4PairCount vk ps ch)
    {pU pW : Fp} {aa : Fin (2 ^ urs.k) → Fp}
    (pbatch : OpenedBatchOpenings urs (evalVector urs.k ch.x3)
      (x4BatchCommitments urs hk vk ps ch) (x4BatchEvals vk ps ch) aa pU pW)
    {aχ : Fin (2 ^ urs.k) → Fp} {pUχ pWχ : Fp}
    (batch_χ : OpenedBatchOpenings urs (evalVector urs.k χ)
      (x4BatchCommitments urs hk vk (r₃.spliced (r₂.spliced ps))
        (r₃.challenges (r₂.challenges ch ζ) χ))
      (x4BatchEvals vk (r₃.spliced (r₂.spliced ps)) (r₃.challenges (r₂.challenges ch ζ) χ))
      aχ pUχ pWχ) :
    openedDecodedCols pbatch ⟨deployedX4PairCount vk ps ch - 1 - j, by omega⟩
        = openedDecodedCols batch_χ
          ⟨deployedX4PairCount vk (r₃.spliced (r₂.spliced ps))
            (r₃.challenges (r₂.challenges ch ζ) χ) - 1 - j, by omega⟩
      ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  have hcc : deployedX4PairCount vk (r₃.spliced (r₂.spliced ps))
        (r₃.challenges (r₂.challenges ch ζ) χ) = deployedX4PairCount vk ps ch :=
    (x3Run_pairCount vk (r₂.spliced ps) (r₂.challenges ch ζ) r₃ χ).trans
      (x2Run_pairCount vk ps ch r₂ ζ)
  have hcommeq : x4BatchCommitments urs hk vk ps ch
        ⟨deployedX4PairCount vk ps ch - 1 - j, by omega⟩
      = x4BatchCommitments urs hk vk (r₃.spliced (r₂.spliced ps))
          (r₃.challenges (r₂.challenges ch ζ) χ)
        ⟨deployedX4PairCount vk (r₃.spliced (r₂.spliced ps))
          (r₃.challenges (r₂.challenges ch ζ) χ) - 1 - j, by omega⟩ := by
    have hidx : deployedX4PairCount vk ps ch - 1 - (deployedX4PairCount vk ps ch - 1 - j)
        = deployedX4PairCount vk (r₃.spliced (r₂.spliced ps))
            (r₃.challenges (r₂.challenges ch ζ) χ) - 1
            - (deployedX4PairCount vk (r₃.spliced (r₂.spliced ps))
                (r₃.challenges (r₂.challenges ch ζ) χ) - 1 - j) := by omega
    rw [x4BatchCommitments_getD urs hk vk ps ch (j := ⟨_, by omega⟩) (by simp only [Fin.val_mk]; omega),
      x4BatchCommitments_getD urs hk vk (r₃.spliced (r₂.spliced ps))
        (r₃.challenges (r₂.challenges ch ζ) χ) (j := ⟨_, by omega⟩)
        (by simp only [Fin.val_mk]; omega),
      x3Run_x4Qs, x2Run_x4Qs, hidx]
  have hc1 := (openedColumnDecode pbatch).commitment
    ⟨deployedX4PairCount vk ps ch - 1 - j, by omega⟩
  have hc2 := (openedColumnDecode batch_χ).commitment
    ⟨deployedX4PairCount vk (r₃.spliced (r₂.spliced ps))
      (r₃.challenges (r₂.challenges ch ζ) χ) - 1 - j, by omega⟩
  rcases hasNontrivialRelation_of_two_augmented_openings urs
      (hc1.trans (hcommeq.trans hc2.symm)) with heq | hdlr
  · exact Or.inl (by simp only [openedDecodedCols, heq])
  · exact Or.inr hdlr

set_option maxHeartbeats 1000000 in
/-- **The `q′` (top-slot) column is fixed across `x₃`-rewinds (grid `qCol` `t`-independence lever).**
The top slot (index `count`) of `x4BatchCommitments` is the quotient commitment `q′`, which is
*absorbed before `x₃`* (`x3Run_qPrime`), so it agrees between the honest batch and any `x₃`-rewound
run's batch. Both decodes are augmented openings of that shared `q′`, so
`hasNontrivialRelation_of_two_augmented_openings` forces the decoded `q′` columns equal — or exhibits
a nontrivial relation. This is what makes the grid's `qCol s` well-defined independent of the
`x₃`-sample `t`: across the x₃-family (at a fixed `x₂`-rewind) the decoded `q′` column is one fixed
polynomial. (Unlike the aggregate slots, `q′` is *not* fixed across `x₂`-rewinds — it is re-sent —
so this fixity is x₃-only, which is exactly the `t`-direction.) -/
theorem openedX3_qprime_binding [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) (r : X3Run shape G) {χ : Fp}
    {pU pW : Fp} {aa : Fin (2 ^ urs.k) → Fp}
    (pbatch : OpenedBatchOpenings urs (evalVector urs.k ch.x3)
      (x4BatchCommitments urs hk vk ps ch) (x4BatchEvals vk ps ch) aa pU pW)
    {aχ : Fin (2 ^ urs.k) → Fp} {pUχ pWχ : Fp}
    (batch_χ : OpenedBatchOpenings urs (evalVector urs.k χ)
      (x4BatchCommitments urs hk vk (r.spliced ps) (r.challenges ch χ))
      (x4BatchEvals vk (r.spliced ps) (r.challenges ch χ)) aχ pUχ pWχ) :
    openedDecodedCols pbatch ⟨deployedX4PairCount vk ps ch, Nat.lt_succ_self _⟩
        = openedDecodedCols batch_χ
          ⟨deployedX4PairCount vk (r.spliced ps) (r.challenges ch χ), Nat.lt_succ_self _⟩
      ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  have hcommeq : x4BatchCommitments urs hk vk ps ch
        ⟨deployedX4PairCount vk ps ch, Nat.lt_succ_self _⟩
      = x4BatchCommitments urs hk vk (r.spliced ps) (r.challenges ch χ)
        ⟨deployedX4PairCount vk (r.spliced ps) (r.challenges ch χ), Nat.lt_succ_self _⟩ := by
    simp only [x4BatchCommitments, lt_self_iff_false]
    exact (x3Run_qPrime ps r).symm
  have hc1 := (openedColumnDecode pbatch).commitment
    ⟨deployedX4PairCount vk ps ch, Nat.lt_succ_self _⟩
  have hc2 := (openedColumnDecode batch_χ).commitment
    ⟨deployedX4PairCount vk (r.spliced ps) (r.challenges ch χ), Nat.lt_succ_self _⟩
  rcases hasNontrivialRelation_of_two_augmented_openings urs
      (hc1.trans (hcommeq.trans hc2.symm)) with heq | hdlr
  · exact Or.inl (by simp only [openedDecodedCols, heq])
  · exact Or.inr hdlr

set_option maxHeartbeats 1000000 in
/-- **The `q′` (top-slot) column agrees across two `x₃`-rewinds of the same base (pair form).** Both
`x₃`-rewound runs `r`, `r'` (of the same string `ps`) decode the *same* `q′` commitment at their top
slots — `q′` is absorbed before `x₃` (`x3Run_qPrime`), so `x4BatchCommitments … ⟨count⟩` of either
rewind is `ps.multiopenQPrime`. Hence the two batches' decoded `q′` columns are equal, or a nontrivial
`(g, U, W)` relation exists. Unlike `openedX3_qprime_binding` (which anchors to the honest batch),
this binds two *rewound* batches directly — the form the grid's `t`-independence of `qCol s` needs at
an `x₂`-rewound base (where `q′` is re-sent, so the honest anchor is unavailable). -/
theorem openedX3_qprime_binding_pair [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (r r' : X3Run shape G) {χ χ' : Fp}
    {aa aa' : Fin (2 ^ urs.k) → Fp} {pU pW pU' pW' : Fp}
    (batch : OpenedBatchOpenings urs (evalVector urs.k χ)
      (x4BatchCommitments urs hk vk (r.spliced ps) (r.challenges ch χ))
      (x4BatchEvals vk (r.spliced ps) (r.challenges ch χ)) aa pU pW)
    (batch' : OpenedBatchOpenings urs (evalVector urs.k χ')
      (x4BatchCommitments urs hk vk (r'.spliced ps) (r'.challenges ch χ'))
      (x4BatchEvals vk (r'.spliced ps) (r'.challenges ch χ')) aa' pU' pW') :
    openedDecodedCols batch
        ⟨deployedX4PairCount vk (r.spliced ps) (r.challenges ch χ), Nat.lt_succ_self _⟩
        = openedDecodedCols batch'
          ⟨deployedX4PairCount vk (r'.spliced ps) (r'.challenges ch χ'), Nat.lt_succ_self _⟩
      ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  have hcommeq : x4BatchCommitments urs hk vk (r.spliced ps) (r.challenges ch χ)
        ⟨deployedX4PairCount vk (r.spliced ps) (r.challenges ch χ), Nat.lt_succ_self _⟩
      = x4BatchCommitments urs hk vk (r'.spliced ps) (r'.challenges ch χ')
        ⟨deployedX4PairCount vk (r'.spliced ps) (r'.challenges ch χ'), Nat.lt_succ_self _⟩ := by
    simp only [x4BatchCommitments, lt_self_iff_false]
    exact (x3Run_qPrime ps r).trans (x3Run_qPrime ps r').symm
  have hc1 := (openedColumnDecode batch).commitment
    ⟨deployedX4PairCount vk (r.spliced ps) (r.challenges ch χ), Nat.lt_succ_self _⟩
  have hc2 := (openedColumnDecode batch').commitment
    ⟨deployedX4PairCount vk (r'.spliced ps) (r'.challenges ch χ'), Nat.lt_succ_self _⟩
  rcases hasNontrivialRelation_of_two_augmented_openings urs
      (hc1.trans (hcommeq.trans hc2.symm)) with heq | hdlr
  · exact Or.inl (by simp only [openedDecodedCols, heq])
  · exact Or.inr hdlr

/-- **A single rewound batch giving all slot values (grid extraction, combined form).** The `∀`-slot
generalization of `openedX3_rewound_aggregate_value`: from one `OpenedX3Accept` at base
`evalVector urs.k χ` plus the run's `x₄`-rewind measure, one extraction produces one
`OpenedBatchOpenings` whose decoded column at *every* slot `j` evaluates at `χ` to the slot's claimed
evaluation (`openedDecodedCols_eval_x3`). Using a single batch — rather than separately extracting for
the `q′` slot and the aggregate slots — is what lets the grid's `hopen` (top slot) and `hu` (aggregate
slots) reference the *same* `sets s t` (that run's `deployedSetsForEval`). -/
theorem openedX3_rewound_batch_eval [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) {χ : Fp}
    (hprob4 : ∀ r : X3Run shape G,
      (deployedX4PairCount vk (r.spliced ps) (r.challenges ch χ) : ℝ≥0∞) / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
            (OpenedX4Accept urs hk vk (r.spliced ps) (r.challenges ch χ) (evalVector urs.k χ))))
    (hacc : OpenedX3Accept urs hk vk ps ch (evalVector urs.k χ) χ) :
    ∃ (r : X3Run shape G) (a : Fin (2 ^ urs.k) → Fp) (pU pW : Fp)
      (batch : OpenedBatchOpenings urs (evalVector urs.k χ)
        (x4BatchCommitments urs hk vk (r.spliced ps) (r.challenges ch χ))
        (x4BatchEvals vk (r.spliced ps) (r.challenges ch χ)) a pU pW),
      ∀ j, (openedDecodedCols batch j).eval χ
        = x4BatchEvals vk (r.spliced ps) (r.challenges ch χ) j := by
  obtain ⟨r, z, blind, fs, t, ht⟩ := hacc
  obtain ⟨a, ha⟩ := ipaRelation_extract urs (evalVector urs.k χ) fs.openedCommitment
    (multiopenValue vk (r.spliced ps) (r.challenges ch χ)) t ht
  refine ⟨r, a, fs.pU, fs.pW,
    openedX4Rewind_of_x4Prob_forked urs hk vk (r.spliced ps) (r.challenges ch χ) fs ⟨t, ht⟩
      (hprob4 r) a ha, ?_⟩
  intro j
  exact openedDecodedCols_eval_x3 urs hk vk (r.spliced ps) (r.challenges ch χ) _ j

/-- The `x₄` batch's top slot is the recomputed base evaluation (the `else` branch of
`x4BatchEvals`) — the value the quotient commitment `q′` is claimed to open to. Composed with
`deployedBaseEval_eq_multiopenEval` this is the grid `hopen`'s right-hand side. -/
theorem x4BatchEvals_top [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) :
    x4BatchEvals vk ps ch ⟨deployedX4PairCount vk ps ch, Nat.lt_succ_self _⟩
      = deployedBaseEval vk ps ch := by
  show (if deployedX4PairCount vk ps ch < deployedX4PairCount vk ps ch then _
    else deployedBaseEval vk ps ch) = deployedBaseEval vk ps ch
  rw [if_neg (lt_irrefl _)]

/-- **The value-check sets' points and compressed-evals fields are fixed under a double
(`x₂`-then-`x₃`) rewind.** The grouping and the `x₁` compression read only pre-`x₂` data
(`x2Run_assembleQueries`/`x3Run_assembleQueries`, and both challenge records keep `x₁`), so entry
`k` of the doubly-rewound `deployedSetsForEval` agrees with the honest one in its point list (`.1`)
and its compressed eval vector (`.2.1`); only the claimed set evaluation (`.2.2`, the re-sent
`multiopenU`) moves per run. -/
theorem deployedSetsForEval_x2x3_getD_fields [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (r₂ : X2Run shape G) (ζv : Fp) (r₃ : X3Run shape G) (χv : Fp) {k : ℕ}
    (hk : k < deployedX4PairCount vk ps ch) :
    ((deployedSetsForEval vk (r₃.spliced (r₂.spliced ps))
        (r₃.challenges (r₂.challenges ch ζv) χv)).getD k ([], [], 0)).1
        = ((deployedSetsForEval vk ps ch).getD k ([], [], 0)).1
      ∧ ((deployedSetsForEval vk (r₃.spliced (r₂.spliced ps))
        (r₃.challenges (r₂.challenges ch ζv) χv)).getD k ([], [], 0)).2.1
        = ((deployedSetsForEval vk ps ch).getD k ([], [], 0)).2.1 := by
  have hcc : deployedX4PairCount vk (r₃.spliced (r₂.spliced ps))
      (r₃.challenges (r₂.challenges ch ζv) χv) = deployedX4PairCount vk ps ch :=
    (x3Run_pairCount vk (r₂.spliced ps) (r₂.challenges ch ζv) r₃ χv).trans
      (x2Run_pairCount vk ps ch r₂ ζv)
  have hk1 : k < (deployedSetsForEval vk (r₃.spliced (r₂.spliced ps))
      (r₃.challenges (r₂.challenges ch ζv) χv)).length := by
    rw [deployedSetsForEval_length, hcc]; exact hk
  have hk2 : k < (deployedSetsForEval vk ps ch).length := by
    rw [deployedSetsForEval_length]; exact hk
  rw [List.getD_eq_getElem _ _ hk1, List.getD_eq_getElem _ _ hk2]
  refine ⟨?_, ?_⟩ <;>
    · simp only [deployedSetsForEval, List.getElem_map, List.getElem_zip]
      rfl

/-- Reversed-index form of `deployedSetsForEval_x2x3_getD_fields` — the `hsetpts`/`hsetevals`
field agreements `deployed_node_binding_of_grid` consumes for the doubly-rewound grid runs. -/
theorem deployedSetsForEval_x2x3_reverse_getD_fields [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (r₂ : X2Run shape G) (ζv : Fp) (r₃ : X3Run shape G) (χv : Fp) {k : ℕ}
    (hk : k < deployedX4PairCount vk ps ch) :
    ((deployedSetsForEval vk (r₃.spliced (r₂.spliced ps))
        (r₃.challenges (r₂.challenges ch ζv) χv)).reverse.getD k ([], [], 0)).1
        = ((deployedSetsForEval vk ps ch).reverse.getD k ([], [], 0)).1
      ∧ ((deployedSetsForEval vk (r₃.spliced (r₂.spliced ps))
        (r₃.challenges (r₂.challenges ch ζv) χv)).reverse.getD k ([], [], 0)).2.1
        = ((deployedSetsForEval vk ps ch).reverse.getD k ([], [], 0)).2.1 := by
  have hcc : deployedX4PairCount vk (r₃.spliced (r₂.spliced ps))
      (r₃.challenges (r₂.challenges ch ζv) χv) = deployedX4PairCount vk ps ch :=
    (x3Run_pairCount vk (r₂.spliced ps) (r₂.challenges ch ζv) r₃ χv).trans
      (x2Run_pairCount vk ps ch r₂ ζv)
  have hlen1 : (deployedSetsForEval vk (r₃.spliced (r₂.spliced ps))
      (r₃.challenges (r₂.challenges ch ζv) χv)).length = deployedX4PairCount vk ps ch := by
    rw [deployedSetsForEval_length, hcc]
  have hlen2 : (deployedSetsForEval vk ps ch).length = deployedX4PairCount vk ps ch :=
    deployedSetsForEval_length vk ps ch
  have h1 : (deployedSetsForEval vk (r₃.spliced (r₂.spliced ps))
        (r₃.challenges (r₂.challenges ch ζv) χv)).reverse.getD k ([], [], 0)
      = (deployedSetsForEval vk (r₃.spliced (r₂.spliced ps))
          (r₃.challenges (r₂.challenges ch ζv) χv)).getD
            (deployedX4PairCount vk ps ch - 1 - k) ([], [], 0) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_reverse (by rw [hlen1]; exact hk), hlen1,
      ← List.getD_eq_getElem?_getD]
  have h2 : (deployedSetsForEval vk ps ch).reverse.getD k ([], [], 0)
      = (deployedSetsForEval vk ps ch).getD (deployedX4PairCount vk ps ch - 1 - k) ([], [], 0) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_reverse (by rw [hlen2]; exact hk), hlen2,
      ← List.getD_eq_getElem?_getD]
  rw [h1, h2]
  exact deployedSetsForEval_x2x3_getD_fields vk ps ch r₂ ζv r₃ χv (by omega)

/-- A coefficient-vector polynomial has degree below its length: each summand `C aᵢ · Xⁱ` has
`natDegree ≤ i < n`. The decoded batch columns (`openedDecodedCols`) are `coeffsToPoly` of
`Fin (2 ^ k)` vectors, so their degree is below `2 ^ k`. -/
theorem coeffsToPoly_natDegree_lt {n : ℕ} (hn : 0 < n) (a : Fin n → Fp) :
    (coeffsToPoly a).natDegree < n := by
  have hle : (coeffsToPoly a).natDegree ≤ n - 1 := by
    rw [coeffsToPoly]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun i _ => ?_)
    calc (Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)).natDegree
        ≤ (Polynomial.X ^ (i : ℕ) : Polynomial Fp).natDegree :=
          Polynomial.natDegree_C_mul_le _ _
      _ = (i : ℕ) := Polynomial.natDegree_X_pow _
      _ ≤ n - 1 := by have := i.isLt; omega
  omega

/-- The `r`-interpolant's degree is at most the node count — the `≤` form of
`lagrangePoly_natDegree_lt`, covering the empty point list (where the interpolant is `0`). -/
theorem lagrangePoly_natDegree_le {points evals : List Fp}
    (hnode : Function.Injective (fun i : Fin points.length => points[i])) :
    (lagrangePoly points evals).natDegree ≤ points.length := by
  rcases Nat.eq_zero_or_pos points.length with h0 | hpos
  · haveI : IsEmpty (Fin points.length) := by rw [h0]; exact Fin.isEmpty
    rw [lagrangePoly, Finset.univ_eq_empty, Lagrange.interpolate_empty,
      Polynomial.natDegree_zero]
    exact Nat.zero_le _
  · exact le_of_lt (lagrangePoly_natDegree_lt hpos hnode)

/-- The vanishing polynomial's degree is at most its point count. -/
theorem vanishingProd_natDegree_le (pts : Finset Fp) :
    (vanishingProd pts).natDegree ≤ pts.card := by
  rw [vanishingProd]
  calc (∏ p ∈ pts, (X - C p)).natDegree
      ≤ ∑ p ∈ pts, (X - C p).natDegree := Polynomial.natDegree_prod_le _ _
    _ = pts.card := by simp [Polynomial.natDegree_X_sub_C]

/-- The complementary product's degree is at most the full point count. -/
theorem coProd_natDegree_le (all pts : Finset Fp) :
    (coProd all pts).natDegree ≤ all.card :=
  le_trans (vanishingProd_natDegree_le _) (Finset.card_le_card Finset.sdiff_subset)

/-- **The grid's uniform degree bound (stage B).** The cleared-denominator combination that
`node_binding_of_grid_openings`'s `hdeg` measures — `qCol·D − ∑ⱼ ζʲ·((colⱼ − rⱼ)·Wⱼ)` — has
`natDegree ≤ N + |allPts|` whenever the quotient column and the per-set differences are bounded by
`N`: the products add at most `|allPts|` (the vanishing/complementary factors), and the sum and
difference take maxima. Instantiated with `N := max (2 ^ k) |allPts|`, this is the explicit `d` the
deployed capstone feeds the grid. -/
theorem grid_hdeg_bound {numSets : ℕ} (allPts : Finset Fp) (pts : Fin numSets → Finset Fp)
    (col r qCol : Fin numSets → Polynomial Fp) (ζ : Fin numSets → Fp) {N : ℕ}
    (hq : ∀ s, (qCol s).natDegree ≤ N)
    (hcr : ∀ j, (col j - r j).natDegree ≤ N) (s : Fin numSets) :
    (qCol s * vanishingProd allPts
      - ∑ j : Fin numSets, C (ζ s ^ (j : ℕ)) *
          ((col j - r j) * coProd allPts (pts j))).natDegree ≤ N + allPts.card := by
  refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
  · exact le_trans Polynomial.natDegree_mul_le
      (add_le_add (hq s) (vanishingProd_natDegree_le _))
  · refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun j _ => ?_)
    calc (C (ζ s ^ (j : ℕ)) * ((col j - r j) * coProd allPts (pts j))).natDegree
        ≤ ((col j - r j) * coProd allPts (pts j)).natDegree :=
          Polynomial.natDegree_C_mul_le _ _
      _ ≤ (col j - r j).natDegree + (coProd allPts (pts j)).natDegree :=
          Polynomial.natDegree_mul_le
      _ ≤ N + allPts.card := add_le_add (hcr j) (coProd_natDegree_le _ _)

set_option maxHeartbeats 2000000 in
/-- **The deployed multiopen value check from the nested `x₂`×`x₃`×`x₄` floors (F3 capstone).**
*Either* the honest `x₄`-slot aggregate column for point set `count − 1 − j₀` takes its claimed
interpolation at each of that set's points, *or* a nontrivial `(g, U, W)` relation exists. Everything
is produced from the accept floors — no per-run consistency, no vanishing, and no grid openings are
assumed:

* the `x₂` floor (`hζ₀`/`hprob2`) yields `count` distinct set-separation samples `ζ` with accepting
  `x₂`-rewound runs (`OpenedX2Accept`, the `reprogramX2` events);
* at each `x₂`-rewound base, the `x₃` floor (`hx3anchor`/`hprob3`) yields `d + 1` distinct
  interpolation samples, and per grid point the nested `x₄` floor (`hprob4`) decodes that run's
  batch (`openedX3_rewound_batch_eval`);
* the fixed-`q′` binding across the inner `x₃`-family (`openedX3_qprime_binding_pair`) makes the
  quotient column per `x₂`-sample well-defined, and the doubly-rewound aggregate binding
  (`openedX2X3_agg_binding`) ties every grid decode to the honest aggregate — each on pain of a
  computed `HasNontrivialRelation`;
* the cleared-denominator core (`deployed_node_binding_of_grid` ← `node_binding_of_samples`)
  separates the per-set contributions and pins the aggregate at every set point.

The measure hypotheses carry the random-oracle uniformity axiom (`Soundness.Forking.Oracle`), and
`havoid` is the standard sample-avoidance floor (the finitely many nodes are hit with negligible
probability). This discharges the `hconsistent`/`hx2cons` chain end-to-end: the deployed value
check, from acceptance. -/
theorem deployed_value_check_node_binding [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {a₀ : Fin (2 ^ urs.k) → Fp} {pU pW : Fp}
    (pbatch : OpenedBatchOpenings urs (evalVector urs.k ch.x3)
      (x4BatchCommitments urs hk vk ps ch) (x4BatchEvals vk ps ch) a₀ pU pW)
    {b₂ : Fin (2 ^ urs.k) → Fp} {ζ₀ : Fp}
    (hζ₀ : OpenedX2Accept urs hk vk ps ch b₂ ζ₀)
    (hprob2 : ((deployedX4PairCount vk ps ch - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
      < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
          (OpenedX2Accept urs hk vk ps ch b₂)))
    (hx3anchor : ∀ (r₂ : X2Run shape G) (ζv : Fp), ∃ χ₀ : Fp,
      OpenedX3Accept urs hk vk (r₂.spliced ps) (r₂.challenges ch ζv) (evalVector urs.k χ₀) χ₀)
    (hprob3 : ∀ (r₂ : X2Run shape G) (ζv : Fp),
      ((max (2 ^ urs.k) (deployedAllPts vk ps ch).card
          + (deployedAllPts vk ps ch).card : ℕ) : ℝ≥0∞) / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
            (fun χv => OpenedX3Accept urs hk vk (r₂.spliced ps) (r₂.challenges ch ζv)
              (evalVector urs.k χv) χv)))
    (hprob4 : ∀ (r₂ : X2Run shape G) (ζv χv : Fp) (r₃ : X3Run shape G),
      (deployedX4PairCount vk (r₃.spliced (r₂.spliced ps))
          (r₃.challenges (r₂.challenges ch ζv) χv) : ℝ≥0∞) / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
            (OpenedX4Accept urs hk vk (r₃.spliced (r₂.spliced ps))
              (r₃.challenges (r₂.challenges ch ζv) χv) (evalVector urs.k χv))))
    (havoid : ∀ (r₂ : X2Run shape G) (ζv χv : Fp),
      OpenedX3Accept urs hk vk (r₂.spliced ps) (r₂.challenges ch ζv) (evalVector urs.k χv) χv →
      ∀ k, χv ∉ deployedSetPts vk ps ch k)
    (j₀ : Fin (deployedX4PairCount vk ps ch)) {p : Fp}
    (hp : p ∈ deployedSetPts vk ps ch (deployedX4PairCount vk ps ch - 1 - (j₀ : ℕ))) :
    (openedDecodedCols pbatch ⟨(j₀ : ℕ), Nat.lt_succ_of_lt j₀.isLt⟩).eval p
        = (lagrangePoly ((deployedSetsForEval vk ps ch).reverse.getD (j₀ : ℕ) ([], [], 0)).1
            ((deployedSetsForEval vk ps ch).reverse.getD (j₀ : ℕ) ([], [], 0)).2.1).eval p
      ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  classical
  by_cases hrel : HasNontrivialRelation (F := Fp) urs.g urs.u urs.w
  · exact Or.inr hrel
  refine Or.inl ?_
  have hcpos : 0 < deployedX4PairCount vk ps ch := lt_of_le_of_lt (Nat.zero_le _) j₀.isLt
  have hn : deployedX4PairCount vk ps ch - 1 + 1 = deployedX4PairCount vk ps ch :=
    Nat.succ_pred_eq_of_pos hcpos
  -- the x₂ sample family, reindexed to `Fin count`
  have hζfam : ∃ ζ : Fin (deployedX4PairCount vk ps ch) → Fp,
      Function.Injective ζ ∧ ∀ s, OpenedX2Accept urs hk vk ps ch b₂ (ζ s) := by
    obtain ⟨ζ', hinj, _, hacc⟩ := exists_injective_accepting_of_measure
      (acc := OpenedX2Accept urs hk vk ps ch b₂) hζ₀ hprob2
    exact ⟨fun s => ζ' (Fin.cast hn.symm s),
      fun a b h => Fin.cast_injective hn.symm (hinj h), fun s => hacc _⟩
  obtain ⟨ζ, hζinj, hζacc⟩ := hζfam
  -- per-sample x₂ run (the accepting continuation)
  have hruns : ∀ s : Fin (deployedX4PairCount vk ps ch), ∃ r : X2Run shape G, True :=
    fun s => (hζacc s).elim fun r _ => ⟨r, trivial⟩
  choose r₂ hr₂ using hruns
  -- per-x₂ x₃ sample families at the rewound bases
  have hχfam : ∀ s : Fin (deployedX4PairCount vk ps ch),
      ∃ ξ : Fin (max (2 ^ urs.k) (deployedAllPts vk ps ch).card
          + (deployedAllPts vk ps ch).card + 1) → Fp,
        Function.Injective ξ ∧ ∀ t, OpenedX3Accept urs hk vk ((r₂ s).spliced ps)
          ((r₂ s).challenges ch (ζ s)) (evalVector urs.k (ξ t)) (ξ t) := by
    intro s
    obtain ⟨χ₀, hχ₀⟩ := hx3anchor (r₂ s) (ζ s)
    obtain ⟨ξ, hinj, _, hacc⟩ := exists_injective_accepting_of_measure
      (acc := fun χv => OpenedX3Accept urs hk vk ((r₂ s).spliced ps)
        ((r₂ s).challenges ch (ζ s)) (evalVector urs.k χv) χv) hχ₀ (hprob3 (r₂ s) (ζ s))
    exact ⟨ξ, hinj, hacc⟩
  choose χ hχinj hχacc using hχfam
  -- per-grid-point extracted batch with all-slot values
  have hbat : ∀ (s : Fin (deployedX4PairCount vk ps ch))
      (t : Fin (max (2 ^ urs.k) (deployedAllPts vk ps ch).card
        + (deployedAllPts vk ps ch).card + 1)),
      ∃ (r₃ : X3Run shape G) (a : Fin (2 ^ urs.k) → Fp) (pUχ pWχ : Fp)
        (B : OpenedBatchOpenings urs (evalVector urs.k (χ s t))
          (x4BatchCommitments urs hk vk (r₃.spliced ((r₂ s).spliced ps))
            (r₃.challenges ((r₂ s).challenges ch (ζ s)) (χ s t)))
          (x4BatchEvals vk (r₃.spliced ((r₂ s).spliced ps))
            (r₃.challenges ((r₂ s).challenges ch (ζ s)) (χ s t))) a pUχ pWχ),
        ∀ j, (openedDecodedCols B j).eval (χ s t)
          = x4BatchEvals vk (r₃.spliced ((r₂ s).spliced ps))
              (r₃.challenges ((r₂ s).challenges ch (ζ s)) (χ s t)) j :=
    fun s t => openedX3_rewound_batch_eval urs hk vk ((r₂ s).spliced ps)
      ((r₂ s).challenges ch (ζ s)) (fun r₃ => hprob4 (r₂ s) (ζ s) (χ s t) r₃) (hχacc s t)
  choose r₃f aF pUF pWF Bf hBspec using hbat
  -- pair counts of the doubly-rewound runs
  have hccst : ∀ s t, deployedX4PairCount vk ((r₃f s t).spliced ((r₂ s).spliced ps))
      ((r₃f s t).challenges ((r₂ s).challenges ch (ζ s)) (χ s t))
        = deployedX4PairCount vk ps ch := fun s t =>
    (x3Run_pairCount vk ((r₂ s).spliced ps) ((r₂ s).challenges ch (ζ s)) (r₃f s t)
      (χ s t)).trans (x2Run_pairCount vk ps ch (r₂ s) (ζ s))
  -- premise: value-check set lengths
  have hlen' : ∀ s t, (deployedSetsForEval vk ((r₃f s t).spliced ((r₂ s).spliced ps))
      ((r₃f s t).challenges ((r₂ s).challenges ch (ζ s)) (χ s t))).length
        = deployedX4PairCount vk ps ch :=
    fun s t => (deployedSetsForEval_length vk _ _).trans (hccst s t)
  -- premise: the grid runs' sets share the honest points and compressed evals
  have hsetpts' : ∀ s t (j : Fin (deployedX4PairCount vk ps ch)),
      ((deployedSetsForEval vk ((r₃f s t).spliced ((r₂ s).spliced ps))
        ((r₃f s t).challenges ((r₂ s).challenges ch (ζ s)) (χ s t))).reverse.getD (j : ℕ)
          ([], [], 0)).1
        = ((deployedSetsForEval vk ps ch).reverse.getD (j : ℕ) ([], [], 0)).1 :=
    fun s t j => (deployedSetsForEval_x2x3_reverse_getD_fields vk ps ch (r₂ s) (ζ s)
      (r₃f s t) (χ s t) j.isLt).1
  have hsetevals' : ∀ s t (j : Fin (deployedX4PairCount vk ps ch)),
      ((deployedSetsForEval vk ((r₃f s t).spliced ((r₂ s).spliced ps))
        ((r₃f s t).challenges ((r₂ s).challenges ch (ζ s)) (χ s t))).reverse.getD (j : ℕ)
          ([], [], 0)).2.1
        = ((deployedSetsForEval vk ps ch).reverse.getD (j : ℕ) ([], [], 0)).2.1 :=
    fun s t j => (deployedSetsForEval_x2x3_reverse_getD_fields vk ps ch (r₂ s) (ζ s)
      (r₃f s t) (χ s t) j.isLt).2
  -- premise: the uniform degree bound
  have hdeg' : ∀ s, ((openedDecodedCols (Bf s 0)
      ⟨deployedX4PairCount vk ((r₃f s 0).spliced ((r₂ s).spliced ps))
        ((r₃f s 0).challenges ((r₂ s).challenges ch (ζ s)) (χ s 0)), Nat.lt_succ_self _⟩)
        * vanishingProd (deployedAllPts vk ps ch)
      - ∑ j : Fin (deployedX4PairCount vk ps ch), C (ζ s ^ (j : ℕ)) *
          ((openedDecodedCols pbatch ⟨(j : ℕ), Nat.lt_succ_of_lt j.isLt⟩
            - lagrangePoly ((deployedSetsForEval vk ps ch).reverse.getD (j : ℕ) ([], [], 0)).1
                ((deployedSetsForEval vk ps ch).reverse.getD (j : ℕ) ([], [], 0)).2.1)
            * coProd (deployedAllPts vk ps ch)
                (deployedSetPts vk ps ch
                  (deployedX4PairCount vk ps ch - 1 - (j : ℕ))))).natDegree
      ≤ max (2 ^ urs.k) (deployedAllPts vk ps ch).card + (deployedAllPts vk ps ch).card := by
    intro s
    refine grid_hdeg_bound (deployedAllPts vk ps ch)
      (fun j => deployedSetPts vk ps ch (deployedX4PairCount vk ps ch - 1 - (j : ℕ)))
      (fun j => openedDecodedCols pbatch ⟨(j : ℕ), Nat.lt_succ_of_lt j.isLt⟩)
      (fun j => lagrangePoly
        ((deployedSetsForEval vk ps ch).reverse.getD (j : ℕ) ([], [], 0)).1
        ((deployedSetsForEval vk ps ch).reverse.getD (j : ℕ) ([], [], 0)).2.1)
      (fun s' => openedDecodedCols (Bf s' 0)
        ⟨deployedX4PairCount vk ((r₃f s' 0).spliced ((r₂ s').spliced ps))
          ((r₃f s' 0).challenges ((r₂ s').challenges ch (ζ s')) (χ s' 0)),
          Nat.lt_succ_self _⟩)
      ζ ?_ ?_ s
    · intro s'
      exact le_trans (le_of_lt (coeffsToPoly_natDegree_lt (by positivity) _))
        (le_max_left _ _)
    · intro j
      refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
      · exact le_trans (le_of_lt (coeffsToPoly_natDegree_lt (by positivity) _))
          (le_max_left _ _)
      · have hnd := deployedSetsForEval_reverse_getD_nodup vk ps ch j.isLt
        have hle := lagrangePoly_natDegree_le
          (points := ((deployedSetsForEval vk ps ch).reverse.getD (j : ℕ) ([], [], 0)).1)
          (evals := ((deployedSetsForEval vk ps ch).reverse.getD (j : ℕ) ([], [], 0)).2.1)
          (List.nodup_iff_injective_getElem.mp hnd)
        have hcard : ((deployedSetsForEval vk ps ch).reverse.getD (j : ℕ) ([], [], 0)).1.length
            ≤ (deployedAllPts vk ps ch).card := by
          rw [← List.toFinset_card_of_nodup hnd,
            deployedSetsForEval_reverse_getD_toFinset vk ps ch j.isLt]
          exact Finset.card_le_card (deployedSetPts_subset vk ps ch _)
        exact le_trans (le_trans hle hcard) (le_max_right _ _)
  -- premise: the samples avoid the nodes
  have hnode' : ∀ s t (j : Fin (deployedX4PairCount vk ps ch)),
      (vanishingProd (deployedSetPts vk ps ch
        (deployedX4PairCount vk ps ch - 1 - (j : ℕ)))).eval (χ s t) ≠ 0 :=
    fun s t j => vanishingProd_eval_ne (havoid (r₂ s) (ζ s) (χ s t) (hχacc s t) _)
  -- premise: the run openings (top slot, t-independent via the fixed-q′ pair binding)
  have hopen' : ∀ s t, (openedDecodedCols (Bf s 0)
      ⟨deployedX4PairCount vk ((r₃f s 0).spliced ((r₂ s).spliced ps))
        ((r₃f s 0).challenges ((r₂ s).challenges ch (ζ s)) (χ s 0)),
        Nat.lt_succ_self _⟩).eval (χ s t)
      = multiopenEval (ζ s) (χ s t) (deployedSetsForEval vk
          ((r₃f s t).spliced ((r₂ s).spliced ps))
          ((r₃f s t).challenges ((r₂ s).challenges ch (ζ s)) (χ s t))) := by
    intro s t
    rcases openedX3_qprime_binding_pair urs hk vk ((r₂ s).spliced ps)
        ((r₂ s).challenges ch (ζ s)) (r₃f s 0) (r₃f s t) (Bf s 0) (Bf s t) with heq | hdlr
    · rw [heq, hBspec s t, x4BatchEvals_top]
      exact deployedBaseEval_eq_multiopenEval vk _ _
    · exact absurd hdlr hrel
  -- premise: the honest aggregate takes the grid runs' claimed set evals
  have hu' : ∀ s t (j : Fin (deployedX4PairCount vk ps ch)),
      (openedDecodedCols pbatch ⟨(j : ℕ), Nat.lt_succ_of_lt j.isLt⟩).eval (χ s t)
        = ((deployedSetsForEval vk ((r₃f s t).spliced ((r₂ s).spliced ps))
            ((r₃f s t).challenges ((r₂ s).challenges ch (ζ s)) (χ s t))).reverse.getD (j : ℕ)
              ([], [], 0)).2.2 := by
    intro s t j
    have hjlt : deployedX4PairCount vk ps ch - 1 - (j : ℕ) < deployedX4PairCount vk ps ch := by
      have := j.isLt; omega
    rcases openedX2X3_agg_binding urs hk vk ps ch (r₂ s) (r₃f s t)
        (deployedX4PairCount vk ps ch - 1 - (j : ℕ)) hjlt pbatch (Bf s t) with heq | hdlr
    swap
    · exact absurd hdlr hrel
    have hval1 : deployedX4PairCount vk ps ch - 1
        - (deployedX4PairCount vk ps ch - 1 - (j : ℕ)) = (j : ℕ) := by
      have := j.isLt; omega
    simp only [hval1] at heq
    rw [heq, hBspec s t]
    have hval2 : deployedX4PairCount vk ((r₃f s t).spliced ((r₂ s).spliced ps))
        ((r₃f s t).challenges ((r₂ s).challenges ch (ζ s)) (χ s t)) - 1
        - (deployedX4PairCount vk ps ch - 1 - (j : ℕ)) = (j : ℕ) := by
      have h1 := hccst s t
      have h2 := j.isLt
      omega
    simp only [hval2]
    exact (deployedSetsForEval_reverse_getD_u vk _ _
      (by rw [hccst s t]; exact j.isLt)).symm
  -- assemble
  exact deployed_node_binding_of_grid urs hk vk ps ch pbatch
    (max (2 ^ urs.k) (deployedAllPts vk ps ch).card + (deployedAllPts vk ps ch).card)
    ζ hζinj χ hχinj
    (fun s => openedDecodedCols (Bf s 0)
      ⟨deployedX4PairCount vk ((r₃f s 0).spliced ((r₂ s).spliced ps))
        ((r₃f s 0).challenges ((r₂ s).challenges ch (ζ s)) (χ s 0)), Nat.lt_succ_self _⟩)
    (fun s t => deployedSetsForEval vk ((r₃f s t).spliced ((r₂ s).spliced ps))
      ((r₃f s t).challenges ((r₂ s).challenges ch (ζ s)) (χ s t)))
    hlen' hsetpts' hsetevals' hdeg' hnode' hopen' hu' j₀ hp

/-! ## F2: the `x₁` member un-batch -/

/-- **The compression fold's evaluation accumulator, generically (F2 stage A).** Over the raw fold
state (accumulator `ev`, running power `pw`): each member `m` contributes its claimed-eval list
scaled by the running `x₁`-power, so the folded entry at any in-range point index is the starting
entry plus `pw` times the `x₁`-power fold of the members' claimed evaluations at that index. The
member eval lists must carry one entry per set point (`hlens`) for the `zip` not to truncate. -/
theorem compressSet_evals_foldl {k' : ℕ} {F G' : Type*} [Field F]
    (x1 : F) (sq : List (CommitmentRef k' F G' × List F))
    (d₀ : CommitmentRef k' F G' × List F) {np idx : ℕ} (hidx : idx < np)
    (hlens : ∀ qc ∈ sq, qc.2.length = np) :
    ∀ (msm : Msm k' F G') (ev : List F) (pw : F), ev.length = np →
      (sq.foldl (fun (st : Msm k' F G' × List F × F) qc =>
          (accumulateCommitment st.2.2 qc.1 st.1,
           (st.2.1.zip qc.2).map (fun e => e.1 + e.2 * st.2.2),
           st.2.2 * x1)) (msm, ev, pw)).2.1.getD idx 0
        = ev.getD idx 0
          + pw * (∑ m ∈ Finset.range sq.length,
              x1 ^ m * ((sq.getD m d₀).2.getD idx 0)) := by
  induction sq with
  | nil => intro msm ev pw hev; simp
  | cons qc sq ih =>
      intro msm ev pw hev
      rw [List.foldl_cons]
      dsimp only
      have hqclen : qc.2.length = np := hlens qc (List.mem_cons_self ..)
      have hevlen' : ((ev.zip qc.2).map (fun e => e.1 + e.2 * pw)).length = np := by
        rw [List.length_map, List.length_zip, hev, hqclen, min_self]
      rw [ih (fun qc' hqc' => hlens qc' (List.mem_cons_of_mem _ hqc')) _ _ _ hevlen']
      have hentry : ((ev.zip qc.2).map (fun e => e.1 + e.2 * pw)).getD idx 0
          = ev.getD idx 0 + qc.2.getD idx 0 * pw := by
        rw [List.getD_eq_getElem _ _ (by rw [hevlen']; exact hidx),
          List.getD_eq_getElem _ _ (by rw [hev]; exact hidx),
          List.getD_eq_getElem _ _ (by rw [hqclen]; exact hidx)]
        simp [List.getElem_zip]
      rw [hentry, List.length_cons, Finset.sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, one_mul, mul_add,
        Finset.mul_sum]
      rw [show (∑ m ∈ Finset.range sq.length,
            pw * x1 * (x1 ^ m * ((sq.getD m d₀).2.getD idx 0)))
          = ∑ m ∈ Finset.range sq.length,
            pw * (x1 ^ (m + 1) * ((sq.getD m d₀).2.getD idx 0)) from
        Finset.sum_congr rfl (fun m _ => by ring)]
      ring

/-- **The compressed set evaluations are the `x₁`-power folds of the member evaluations (F2 stage
A).** At any in-range point index, `compressSet`'s evaluation vector entry is
`∑ₘ x₁^m · (member m's claimed eval at that point)`. -/
theorem compressSet_snd_getD {k' : ℕ} {F G' : Type*} [Field F]
    (x1 : F) (sq : List (CommitmentRef k' F G' × List F))
    (d₀ : CommitmentRef k' F G' × List F) {np idx : ℕ} (hidx : idx < np)
    (hlens : ∀ qc ∈ sq, qc.2.length = np) :
    (compressSet x1 sq np).2.getD idx 0
      = ∑ m ∈ Finset.range sq.length, x1 ^ m * ((sq.getD m d₀).2.getD idx 0) := by
  have h := compressSet_evals_foldl x1 sq d₀ hidx hlens (Msm.zero k' F G')
    (List.replicate np (0 : F)) 1 (by simp)
  simp only [compressSet]
  rw [h, List.getD_eq_getElem _ _ (by rw [List.length_replicate]; exact hidx),
    List.getElem_replicate, one_mul, zero_add]

/-- The `k`-th value-check set's compressed evaluation vector is `compressSet`'s — the evals-field
identification for the deployed sets (the `.2.1` companion of `deployedSetsForEval_getD_points`). -/
theorem deployedSetsForEval_getD_evals [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {k : ℕ} (hk : k < deployedX4PairCount vk ps ch) :
    ((deployedSetsForEval vk ps ch).getD k ([], [], 0)).2.1
      = (compressSet ch.x1 (deployedSetQueries vk ps ch k)
          ((constructIntermediateSets (assembleQueries vk ps ch)).points.getD k []).length).2 := by
  have hsp := constructIntermediateSets_points_length (assembleQueries vk ps ch)
  have hcnt : deployedX4PairCount vk ps ch
      ≤ (constructIntermediateSets (assembleQueries vk ps ch)).points.length := by
    simp only [deployedX4PairCount, deployedX4Pairs, deployedX4Qs, List.length_map,
      List.length_zip, List.length_ofFn]
    omega
  have hzip : k < ((constructIntermediateSets (assembleQueries vk ps ch)).sets.zip
      (constructIntermediateSets (assembleQueries vk ps ch)).points).length := by
    rw [List.length_zip]
    omega
  have hpts : k < (constructIntermediateSets (assembleQueries vk ps ch)).points.length := by
    omega
  rw [List.getD_eq_getElem _ _ (by rw [deployedSetsForEval_length]; exact hk)]
  simp only [deployedSetsForEval, List.getElem_map, List.getElem_zip]
  simp only [deployedSetQueries]
  rw [List.getD_eq_getElem _ _ hzip, List.getD_eq_getElem _ _ hpts]
  simp only [List.getElem_zip]

/-- The grouping's point lists are shared across `x₁` rewinds. -/
theorem x1Run_groupPoints [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (r : X1Run shape G) (ξ : Fp) :
    (constructIntermediateSets (assembleQueries vk (r.spliced ps) (r.challenges ch ξ))).points
      = (constructIntermediateSets (assembleQueries vk ps ch)).points := by
  rw [x1Run_assembleQueries]

/-- The deployed point sets are shared across `x₁` rewinds. -/
theorem x1Run_setPts [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (r : X1Run shape G) (ξ : Fp) (k : ℕ) :
    deployedSetPts vk (r.spliced ps) (r.challenges ch ξ) k = deployedSetPts vk ps ch k := by
  simp only [deployedSetPts, x1Run_assembleQueries]

/-! ### `deployedAllPts` splice-invariance (option-(b) stage 4a)

The union of all deployed point sets — whose cardinality is the `x₃` (`hprob3`) threshold in the
derived terminal — is built entirely from `constructIntermediateSets (assembleQueries vk ps ch)`
(`deployedAllPts`/`deployedSetPts`, `ValueCheckDeployed`), so it inherits the `assembleQueries`
seal (`x{1,2,3,4}Run_assembleQueries`, `Deployed`) verbatim: the rewound base's point union — hence
its cardinality — is the honest one. Together with `x{1,2,3,4}Run_pairCount`/`_setQueries` (already
in `Deployed`), this shows *every* deployed threshold is a splice-invariant structural constant, the
enabling fact for reading the run-indexed floors off the base-independent budget. -/

/-- The deployed point-set union is shared across `x₁` rewinds. -/
theorem x1Run_allPts [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (r : X1Run shape G) (ξ : Fp) :
    deployedAllPts vk (r.spliced ps) (r.challenges ch ξ) = deployedAllPts vk ps ch := by
  simp only [deployedAllPts, deployedSetPts, x1Run_assembleQueries]

/-- The deployed point-set union is shared across `x₂` rewinds. -/
theorem x2Run_allPts [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (r : X2Run shape G) (ζ : Fp) :
    deployedAllPts vk (r.spliced ps) (r.challenges ch ζ) = deployedAllPts vk ps ch := by
  simp only [deployedAllPts, deployedSetPts, x2Run_assembleQueries]

/-- The deployed point-set union is shared across `x₃` rewinds. -/
theorem x3Run_allPts [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (r : X3Run shape G) (χ : Fp) :
    deployedAllPts vk (r.spliced ps) (r.challenges ch χ) = deployedAllPts vk ps ch := by
  simp only [deployedAllPts, deployedSetPts, x3Run_assembleQueries]

/-- The deployed point-set union is shared across `x₄` rewinds. -/
theorem x4Run_allPts [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (r : X4Run shape G) (ω : Fp) :
    deployedAllPts vk (r.spliced ps) (r.challenges ch ω) = deployedAllPts vk ps ch := by
  simp only [deployedAllPts, deployedSetPts, x4Run_assembleQueries]

/-- The deployed point-union cardinality (the `hprob3` threshold ingredient) is `x₁`-invariant. -/
theorem x1Run_allPts_card [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (r : X1Run shape G) (ξ : Fp) :
    (deployedAllPts vk (r.spliced ps) (r.challenges ch ξ)).card = (deployedAllPts vk ps ch).card :=
  congrArg Finset.card (x1Run_allPts vk ps ch r ξ)

/-- The deployed point-union cardinality is `x₂`-invariant. -/
theorem x2Run_allPts_card [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (r : X2Run shape G) (ζ : Fp) :
    (deployedAllPts vk (r.spliced ps) (r.challenges ch ζ)).card = (deployedAllPts vk ps ch).card :=
  congrArg Finset.card (x2Run_allPts vk ps ch r ζ)

/-- **The `x₁`-rewound value-check set at `k`: honest points, `ξ`-compressed member evals (F2 stage
A).** At an `x₁`-rewound base the grouping is the honest one (`x1Run_assembleQueries`) and only the
compression challenge moves (`(r.challenges ch ξ).x1 = ξ`), so set `k`'s point list is the honest
grouping's and its compressed evaluation vector is `compressSet ξ` over the honest routed queries. -/
theorem deployedSetsForEval_x1_getD_fields [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (r : X1Run shape G) (ξ : Fp) {k : ℕ} (hk : k < deployedX4PairCount vk ps ch) :
    ((deployedSetsForEval vk (r.spliced ps) (r.challenges ch ξ)).getD k ([], [], 0)).1
        = (constructIntermediateSets (assembleQueries vk ps ch)).points.getD k []
      ∧ ((deployedSetsForEval vk (r.spliced ps) (r.challenges ch ξ)).getD k ([], [], 0)).2.1
        = (compressSet ξ (deployedSetQueries vk ps ch k)
            ((constructIntermediateSets (assembleQueries vk ps ch)).points.getD k []).length).2 := by
  have hcc : deployedX4PairCount vk (r.spliced ps) (r.challenges ch ξ)
      = deployedX4PairCount vk ps ch := x1Run_pairCount vk ps ch r ξ
  constructor
  · rw [deployedSetsForEval_getD_points vk _ _ (by rw [hcc]; exact hk), x1Run_groupPoints]
  · rw [deployedSetsForEval_getD_evals vk _ _ (by rw [hcc]; exact hk), x1Run_groupPoints,
      x1Run_setQueries]
    rfl

set_option maxHeartbeats 4000000 in
/-- **The `x₁`-rewound aggregate opens the `ξ`-fold of the decoded member columns (F2 stage B).**
An `x₁`-rewound run's decoded `x₄`-slot aggregate for point set `i` and the `ξ`-power combination
of a member decode's columns are two augmented openings of the *same* group element: the run's
`x₄`-slot commitment is the `ξ`-power fold of the routed member commitments (`deployedX4Qs_getD_eval`
at the rewound base, the queries fixed by `x1Run_setQueries`), and the member decode's columns open
exactly those member commitments (`OpenedMemberDecode.commitment`, linearly combined). So the two
coefficient vectors are equal, or a nontrivial `(g, U, W)` relation exists. -/
theorem openedX1_agg_member_binding [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (i : ℕ) (hi : i < deployedX4PairCount vk ps ch)
    {a₀ : Fin (2 ^ urs.k) → Fp} {pU pW : Fp}
    {pbatch : OpenedBatchOpenings urs (evalVector urs.k ch.x3)
      (x4BatchCommitments urs hk vk ps ch) (x4BatchEvals vk ps ch) a₀ pU pW}
    (md : OpenedMemberDecode urs hk vk ps ch pbatch i hi)
    (r : X1Run shape G) (ξ : Fp)
    {bR aR : Fin (2 ^ urs.k) → Fp} {pUR pWR : Fp}
    (B : OpenedBatchOpenings urs bR
      (x4BatchCommitments urs hk vk (r.spliced ps) (r.challenges ch ξ))
      (x4BatchEvals vk (r.spliced ps) (r.challenges ch ξ)) aR pUR pWR) :
    (openedColumnDecode B).coeffs
        ⟨deployedX4PairCount vk (r.spliced ps) (r.challenges ch ξ) - 1 - i, by omega⟩
      = ∑ m : Fin (deployedSetQueries vk ps ch i).length, ξ ^ (m : ℕ) • md.cols m
    ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  have hcc : deployedX4PairCount vk (r.spliced ps) (r.challenges ch ξ)
      = deployedX4PairCount vk ps ch := x1Run_pairCount vk ps ch r ξ
  -- the ξ-run's decoded aggregate opens the ξ-power fold of the member commitments
  have hc2 := (openedColumnDecode B).commitment
    ⟨deployedX4PairCount vk (r.spliced ps) (r.challenges ch ξ) - 1 - i, by omega⟩
  rw [x4BatchCommitments_getD urs hk vk (r.spliced ps) (r.challenges ch ξ)
    (j := ⟨_, by omega⟩) (by simp only [Fin.val_mk]; omega)] at hc2
  simp only [Fin.val_mk,
    show deployedX4PairCount vk (r.spliced ps) (r.challenges ch ξ) - 1
      - (deployedX4PairCount vk (r.spliced ps) (r.challenges ch ξ) - 1 - i) = i from by omega]
    at hc2
  have hqs : i < (deployedX4Qs vk (r.spliced ps) (r.challenges ch ξ)).length := by
    rw [x1Run_x4Qs_length]
    have hle : deployedX4PairCount vk ps ch ≤ (deployedX4Qs vk ps ch).length := by
      simp only [deployedX4PairCount, deployedX4Pairs, List.length_zip, List.length_ofFn]
      omega
    omega
  rw [deployedX4Qs_getD_eval (hk ▸ urs.g) urs.w urs.u vk (r.spliced ps) (r.challenges ch ξ) hqs,
    x1Run_setQueries, show (r.challenges ch ξ).x1 = ξ from rfl] at hc2
  -- the member decode's columns open the same fold, linearly combined
  have hcomb : commit urs
        (∑ m : Fin (deployedSetQueries vk ps ch i).length, ξ ^ (m : ℕ) • md.cols m)
      + (∑ m : Fin (deployedSetQueries vk ps ch i).length, ξ ^ (m : ℕ) * md.uComp m) • urs.u
      + (∑ m : Fin (deployedSetQueries vk ps ch i).length, ξ ^ (m : ℕ) * md.wComp m) • urs.w
      = ∑ m ∈ Finset.range (deployedSetQueries vk ps ch i).length,
          ξ ^ m • ((deployedSetQueries vk ps ch i).getD m (.point 0, [])).1.eval
            ⟨shape.k, hk ▸ urs.g, urs.w, urs.u⟩ := by
    rw [← Fin.sum_univ_eq_sum_range (fun m =>
      ξ ^ m • ((deployedSetQueries vk ps ch i).getD m (.point 0, [])).1.eval
        ⟨shape.k, hk ▸ urs.g, urs.w, urs.u⟩)]
    have hsum : ∑ m : Fin (deployedSetQueries vk ps ch i).length,
        ξ ^ (m : ℕ) • ((deployedSetQueries vk ps ch i).getD (m : ℕ) (.point 0, [])).1.eval
          ⟨shape.k, hk ▸ urs.g, urs.w, urs.u⟩
        = ∑ m : Fin (deployedSetQueries vk ps ch i).length,
            ξ ^ (m : ℕ) • (commit urs (md.cols m) + md.uComp m • urs.u + md.wComp m • urs.w) :=
      Finset.sum_congr rfl (fun m _ => by rw [md.commitment m])
    rw [hsum]
    simp only [smul_add, Finset.sum_add_distrib, smul_smul]
    congr 1
    · congr 1
      · simp only [commit_eq_commitGen]
        rw [commitGen_sum]
        exact Finset.sum_congr rfl (fun m _ => commitGen_smul_left _ _ _)
      · rw [Finset.sum_smul]
    · rw [Finset.sum_smul]
  rcases hasNontrivialRelation_of_two_augmented_openings urs (hc2.trans hcomb.symm) with
    heq | hdlr
  · exact Or.inl heq
  · exact Or.inr hdlr

set_option maxHeartbeats 4000000 in
/-- **Eval form of the `x₁` aggregate↔member binding (F2 stage B).** The `x₁`-rewound run's decoded
aggregate polynomial for set `i` evaluates anywhere to the `ξ`-power fold of the member column
polynomials' values — or a nontrivial relation exists. The `x₁` un-batch equates this against the
compressed claimed evaluations at each set point. -/
theorem openedX1_agg_member_eval [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (i : ℕ) (hi : i < deployedX4PairCount vk ps ch)
    {a₀ : Fin (2 ^ urs.k) → Fp} {pU pW : Fp}
    {pbatch : OpenedBatchOpenings urs (evalVector urs.k ch.x3)
      (x4BatchCommitments urs hk vk ps ch) (x4BatchEvals vk ps ch) a₀ pU pW}
    (md : OpenedMemberDecode urs hk vk ps ch pbatch i hi)
    (r : X1Run shape G) (ξ : Fp)
    {bR aR : Fin (2 ^ urs.k) → Fp} {pUR pWR : Fp}
    (B : OpenedBatchOpenings urs bR
      (x4BatchCommitments urs hk vk (r.spliced ps) (r.challenges ch ξ))
      (x4BatchEvals vk (r.spliced ps) (r.challenges ch ξ)) aR pUR pWR) (p : Fp) :
    (openedDecodedCols B
        ⟨deployedX4PairCount vk (r.spliced ps) (r.challenges ch ξ) - 1 - i, by omega⟩).eval p
      = ∑ m : Fin (deployedSetQueries vk ps ch i).length,
          ξ ^ (m : ℕ) * (coeffsToPoly (md.cols m)).eval p
    ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  rcases openedX1_agg_member_binding urs hk vk ps ch i hi md r ξ B with heq | hdlr
  · refine Or.inl ?_
    rw [openedDecodedCols, heq, coeffsToPoly_eval, commitGen_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [commitGen_smul_left, ← coeffsToPoly_eval, smul_eq_mul]
  · exact Or.inr hdlr

/-- **`hql` discharged: each routed member of a deployed point set claims one evaluation per set
point** (`constructIntermediateSets_eval_length` at the deployed queries). This closes the
one structural bookkeeping premise of `deployed_member_node_binding`. -/
theorem deployedSetQueries_eval_length [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (i : ℕ) :
    ∀ qc ∈ deployedSetQueries vk ps ch i,
      qc.2.length
        = ((constructIntermediateSets (assembleQueries vk ps ch)).points.getD i []).length := by
  intro qc hqc
  refine constructIntermediateSets_eval_length (assembleQueries vk ps ch) i qc ?_
  simpa only [deployedSetQueries, constructIntermediateSets_zip_sets_getD] using hqc

/-- The opened `x₁` accept event with the batch base pinned to the run's own interpolation point:
some `x₁`-rewound run accepts and carries an opened `x₄` batch over base
`evalVector urs.k (run's x₃)` — the base the deployed value check
(`deployed_value_check_node_binding`) types its batch at. This strengthens `OpenedX1Accept` only in
pinning the (there existential) base vector; the honest run witnesses it at `ch.x1` through the
honest batch (base `evalVector ch.x3`, the honest challenges by structure eta). -/
def OpenedX1PinnedAccept [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (χv : Fp) : Prop :=
  ∃ (run : X1Run shape G) (aR : Fin (2 ^ urs.k) → Fp) (pUR pWR : Fp),
    DeployedAccepts urs hk vk (run.spliced ps) (run.challenges ch χv) ∧
    Nonempty (OpenedBatchOpenings urs (evalVector urs.k ((run.challenges ch χv).x3))
      (x4BatchCommitments urs hk vk (run.spliced ps) (run.challenges ch χv))
      (x4BatchEvals vk (run.spliced ps) (run.challenges ch χv)) aR pUR pWR)

set_option maxHeartbeats 4000000 in
/-- **The deployed member-column node binding, from the nested `x₁`×`x₂`×`x₃`×`x₄` floors (F2
capstone).** *Either* each decoded member column of point set `i` takes its claimed evaluation at
each of the set's points, *or* a nontrivial `(g, U, W)` relation exists. The `x₁` un-batch of the
deployed value check, produced from the accept floors:

* the `x₁` floor (`hξ₀`/`hprob1`) yields `|members|` distinct compression samples with accepting
  runs carrying opened `x₄` batches at their own interpolation bases (`OpenedX1PinnedAccept`, the
  `reprogramX1` events);
* at each `x₁`-rewound base, the deployed value check (`deployed_value_check_node_binding` — the
  nested `x₂`/`x₃`/`x₄` floors `hx2`/`hx3anchor`/`hprob3`/`hprob4`/`havoid`, instantiated at that
  base) pins the run's aggregate to the interpolant of the `ξ`-compressed claimed evaluations
  (`deployedSetsForEval_x1_getD_fields`/`compressSet_snd_getD`);
* the run's aggregate is simultaneously the `ξ`-power fold of the decoded member columns
  (`openedX1_agg_member_eval`), each on pain of a computed relation;
* equating the two folds at the distinct samples separates the members
  (`member_binding_of_x1_samples`).

The `hql` premise is the structural one-eval-per-set-point bookkeeping of the grouping. This is the
witness → real-columns binding of zcash/ironwood#18, member by member, point by point. -/
theorem deployed_member_node_binding [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {a₀ : Fin (2 ^ urs.k) → Fp} {pU pW : Fp}
    {pbatch : OpenedBatchOpenings urs (evalVector urs.k ch.x3)
      (x4BatchCommitments urs hk vk ps ch) (x4BatchEvals vk ps ch) a₀ pU pW}
    (i : ℕ) (hi : i < deployedX4PairCount vk ps ch)
    (md : OpenedMemberDecode urs hk vk ps ch pbatch i hi)
    {ξ₀ : Fp} (hξ₀ : OpenedX1PinnedAccept urs hk vk ps ch ξ₀)
    (hprob1 : (((deployedSetQueries vk ps ch i).length - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
      < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
          (OpenedX1PinnedAccept urs hk vk ps ch)))
    (hx2 : ∀ (r₁ : X1Run shape G) (ξv : Fp), ∃ (b₂ : Fin (2 ^ urs.k) → Fp) (ζ₀ : Fp),
      OpenedX2Accept urs hk vk (r₁.spliced ps) (r₁.challenges ch ξv) b₂ ζ₀ ∧
      ((deployedX4PairCount vk (r₁.spliced ps) (r₁.challenges ch ξv) - 1 : ℕ) : ℝ≥0∞)
          / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
            (OpenedX2Accept urs hk vk (r₁.spliced ps) (r₁.challenges ch ξv) b₂)))
    (hx3anchor : ∀ (r₁ : X1Run shape G) (ξv : Fp) (r₂ : X2Run shape G) (ζv : Fp), ∃ χ₀ : Fp,
      OpenedX3Accept urs hk vk (r₂.spliced (r₁.spliced ps))
        (r₂.challenges (r₁.challenges ch ξv) ζv) (evalVector urs.k χ₀) χ₀)
    (hprob3 : ∀ (r₁ : X1Run shape G) (ξv : Fp) (r₂ : X2Run shape G) (ζv : Fp),
      ((max (2 ^ urs.k) (deployedAllPts vk (r₁.spliced ps) (r₁.challenges ch ξv)).card
          + (deployedAllPts vk (r₁.spliced ps) (r₁.challenges ch ξv)).card : ℕ) : ℝ≥0∞)
          / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
            (fun χv => OpenedX3Accept urs hk vk (r₂.spliced (r₁.spliced ps))
              (r₂.challenges (r₁.challenges ch ξv) ζv) (evalVector urs.k χv) χv)))
    (hprob4 : ∀ (r₁ : X1Run shape G) (ξv : Fp) (r₂ : X2Run shape G) (ζv χv : Fp)
        (r₃ : X3Run shape G),
      (deployedX4PairCount vk (r₃.spliced (r₂.spliced (r₁.spliced ps)))
          (r₃.challenges (r₂.challenges (r₁.challenges ch ξv) ζv) χv) : ℝ≥0∞)
          / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
            (OpenedX4Accept urs hk vk (r₃.spliced (r₂.spliced (r₁.spliced ps)))
              (r₃.challenges (r₂.challenges (r₁.challenges ch ξv) ζv) χv)
              (evalVector urs.k χv))))
    (havoid : ∀ (r₁ : X1Run shape G) (ξv : Fp) (r₂ : X2Run shape G) (ζv χv : Fp),
      OpenedX3Accept urs hk vk (r₂.spliced (r₁.spliced ps))
        (r₂.challenges (r₁.challenges ch ξv) ζv) (evalVector urs.k χv) χv →
      ∀ k', χv ∉ deployedSetPts vk (r₁.spliced ps) (r₁.challenges ch ξv) k')
    (hql : ∀ qc ∈ deployedSetQueries vk ps ch i,
      qc.2.length
        = ((constructIntermediateSets (assembleQueries vk ps ch)).points.getD i []).length)
    (idx : Fin ((constructIntermediateSets (assembleQueries vk ps ch)).points.getD i []).length)
    (m₀ : Fin (deployedSetQueries vk ps ch i).length) :
    (coeffsToPoly (md.cols m₀)).eval
        (((constructIntermediateSets (assembleQueries vk ps ch)).points.getD i [])[idx])
      = ((deployedSetQueries vk ps ch i).getD (m₀ : ℕ) (.point 0, [])).2.getD (idx : ℕ) 0
    ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  classical
  by_cases hrel : HasNontrivialRelation (F := Fp) urs.g urs.u urs.w
  · exact Or.inr hrel
  refine Or.inl ?_
  have hnpos : 0 < (deployedSetQueries vk ps ch i).length :=
    lt_of_le_of_lt (Nat.zero_le _) m₀.isLt
  have hnn : (deployedSetQueries vk ps ch i).length - 1 + 1
      = (deployedSetQueries vk ps ch i).length := Nat.succ_pred_eq_of_pos hnpos
  -- the x₁ sample family
  have hξfam : ∃ ξ : Fin (deployedSetQueries vk ps ch i).length → Fp,
      Function.Injective ξ ∧ ∀ s, OpenedX1PinnedAccept urs hk vk ps ch (ξ s) := by
    obtain ⟨ξ', hinj, _, hacc⟩ := exists_injective_accepting_of_measure
      (acc := OpenedX1PinnedAccept urs hk vk ps ch) hξ₀ hprob1
    exact ⟨fun s => ξ' (Fin.cast hnn.symm s),
      fun a b h => Fin.cast_injective hnn.symm (hinj h), fun s => hacc _⟩
  obtain ⟨ξ, hξinj, hξacc⟩ := hξfam
  -- per-sample accepting run and pinned-base batch
  have hruns : ∀ s : Fin (deployedSetQueries vk ps ch i).length,
      ∃ (r₁ : X1Run shape G) (aR : Fin (2 ^ urs.k) → Fp) (pUR pWR : Fp),
        Nonempty (OpenedBatchOpenings urs (evalVector urs.k (((r₁.challenges ch (ξ s))).x3))
          (x4BatchCommitments urs hk vk (r₁.spliced ps) (r₁.challenges ch (ξ s)))
          (x4BatchEvals vk (r₁.spliced ps) (r₁.challenges ch (ξ s))) aR pUR pWR) := by
    intro s
    obtain ⟨r₁, aR, pUR, pWR, _, hne⟩ := hξacc s
    exact ⟨r₁, aR, pUR, pWR, hne⟩
  choose r₁f aF pUF pWF hBne using hruns
  -- the node: the idx-th point of set i
  have hndp := constructIntermediateSets_points_nodup (assembleQueries vk ps ch) i
  have hnodeinj := List.nodup_iff_injective_getElem.mp hndp
  -- per-sample aggregate identity: the ξ-fold of the member values equals the ξ-fold of the
  -- claimed evaluations
  have hagg : ∀ s : Fin (deployedSetQueries vk ps ch i).length,
      ∑ m : Fin (deployedSetQueries vk ps ch i).length,
          ξ s ^ (m : ℕ) * (coeffsToPoly (md.cols m)).eval
            (((constructIntermediateSets (assembleQueries vk ps ch)).points.getD i [])[idx])
        = ∑ m : Fin (deployedSetQueries vk ps ch i).length,
            ξ s ^ (m : ℕ)
              * ((deployedSetQueries vk ps ch i).getD (m : ℕ) (.point 0, [])).2.getD (idx : ℕ) 0 := by
    intro s
    have hcc : deployedX4PairCount vk ((r₁f s).spliced ps) ((r₁f s).challenges ch (ξ s))
        = deployedX4PairCount vk ps ch := x1Run_pairCount vk ps ch (r₁f s) (ξ s)
    -- the value check's floor block at the ξ-base
    obtain ⟨b₂, ζ₀', hζacc', hprob2'⟩ := hx2 (r₁f s) (ξ s)
    -- the F3 capstone at the ξ-rewound base
    have hp_i : (((constructIntermediateSets (assembleQueries vk ps ch)).points.getD i [])[idx])
        ∈ deployedSetPts vk ((r₁f s).spliced ps) ((r₁f s).challenges ch (ξ s)) i := by
      rw [x1Run_setPts, deployedSetPts]
      exact List.mem_toFinset.mpr (List.getElem_mem idx.isLt)
    have hA := deployed_value_check_node_binding urs hk vk ((r₁f s).spliced ps)
      ((r₁f s).challenges ch (ξ s)) (hBne s).some hζacc' hprob2'
      (fun r₂ ζv => hx3anchor (r₁f s) (ξ s) r₂ ζv)
      (fun r₂ ζv => hprob3 (r₁f s) (ξ s) r₂ ζv)
      (fun r₂ ζv χv r₃ => hprob4 (r₁f s) (ξ s) r₂ ζv χv r₃)
      (fun r₂ ζv χv h => havoid (r₁f s) (ξ s) r₂ ζv χv h)
      ⟨deployedX4PairCount vk ((r₁f s).spliced ps) ((r₁f s).challenges ch (ξ s)) - 1 - i,
        by omega⟩
      (by
        rw [show deployedX4PairCount vk ((r₁f s).spliced ps) ((r₁f s).challenges ch (ξ s)) - 1
            - (deployedX4PairCount vk ((r₁f s).spliced ps)
                ((r₁f s).challenges ch (ξ s)) - 1 - i) = i from by omega]
        exact hp_i)
    rcases hA with hA | hdlr
    swap
    · exact absurd hdlr hrel
    -- reverse → forward set fields at the ξ-base
    have hrev : (deployedSetsForEval vk ((r₁f s).spliced ps)
          ((r₁f s).challenges ch (ξ s))).reverse.getD
            (deployedX4PairCount vk ((r₁f s).spliced ps)
              ((r₁f s).challenges ch (ξ s)) - 1 - i) ([], [], 0)
        = (deployedSetsForEval vk ((r₁f s).spliced ps)
            ((r₁f s).challenges ch (ξ s))).getD i ([], [], 0) := by
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_reverse (by rw [deployedSetsForEval_length, hcc]; omega),
        deployedSetsForEval_length,
        show deployedX4PairCount vk ((r₁f s).spliced ps) ((r₁f s).challenges ch (ξ s)) - 1
          - (deployedX4PairCount vk ((r₁f s).spliced ps)
              ((r₁f s).challenges ch (ξ s)) - 1 - i) = i from by omega,
        ← List.getD_eq_getElem?_getD]
    obtain ⟨hfpts, hfevals⟩ :=
      deployedSetsForEval_x1_getD_fields vk ps ch (r₁f s) (ξ s) hi
    rw [hrev, hfpts, hfevals] at hA
    -- the interpolant takes the compressed claimed evaluation at the node
    rw [lagrangePoly_eval_node hnodeinj idx] at hA
    rw [compressSet_snd_getD (ξ s) (deployedSetQueries vk ps ch i) (.point 0, [])
      idx.isLt hql] at hA
    -- the aggregate is the ξ-fold of the member values
    have hB := openedX1_agg_member_eval urs hk vk ps ch i hi md (r₁f s) (ξ s) (hBne s).some
      (((constructIntermediateSets (assembleQueries vk ps ch)).points.getD i [])[idx])
    rcases hB with hB | hdlr
    swap
    · exact absurd hdlr hrel
    rw [← hB, hA, ← Fin.sum_univ_eq_sum_range (fun m => ξ s ^ m
      * ((deployedSetQueries vk ps ch i).getD m (.point 0, [])).2.getD (idx : ℕ) 0)]
  -- separate the members at the distinct samples
  exact member_binding_of_x1_samples (fun m => coeffsToPoly (md.cols m))
    (fun m => ((deployedSetQueries vk ps ch i).getD (m : ℕ) (.point 0, [])).2.getD (idx : ℕ) 0)
    (((constructIntermediateSets (assembleQueries vk ps ch)).points.getD i [])[idx])
    ξ hξinj hagg m₀

/-! ## F5: the rotated-point member binding and the derived gate feed -/

/-- The rotated gate feed's value at the gate point is the member column's value at the rotated
query point: `rotatedFeed` composes the column with `ω^rot·X`, so evaluation at `x` lands at
`ω^rot·x = rotateOmega ω x rot`. -/
theorem rotatedFeed_eval {n : ℕ} (omega : Fp) (layout : List (ℕ × ℤ))
    (col : Fin n → Polynomial Fp) {j : ℕ} (hj : j < n) (x : Fp) :
    (rotatedFeed omega layout col j).eval x
      = (col ⟨j, hj⟩).eval (rotateOmega omega x (layout.getD j (0, 0)).2) := by
  simp only [rotatedFeed, finFn, dif_pos hj, Polynomial.eval_comp, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, rotateOmega]
  exact congrArg (fun t => Polynomial.eval t (col ⟨j, hj⟩))
    (mul_comm (omega ^ (layout.getD j (0, 0)).2) x)

/-- Out of the layout's range the rotated feed is the zero polynomial. -/
theorem rotatedFeed_eval_of_ge {n : ℕ} (omega : Fp) (layout : List (ℕ × ℤ))
    (col : Fin n → Polynomial Fp) {j : ℕ} (hj : n ≤ j) (x : Fp) :
    (rotatedFeed omega layout col j).eval x = 0 := by
  simp only [rotatedFeed, finFn, dif_neg (Nat.not_lt.mpr hj), Polynomial.eval_zero]

/-- Each in-range layout entry contributes a column query with its slot identity and rotated
opening point. -/
theorem columnQueries_layout_mem {k' : ℕ} {F G' : Type*} [Field F] (omega x : F)
    (commitment : ℕ → G') (mkId : ℕ → CommitmentId) (layout : List (ℕ × ℤ)) (evals : List F)
    {j : ℕ} (hjl : j < layout.length) (hje : j < evals.length) :
    ∃ q ∈ columnQueries (k := k') omega x commitment mkId layout evals,
      q.commId = mkId (layout.getD j (0, 0)).1 ∧
      q.point = rotateOmega omega x (layout.getD j (0, 0)).2 := by
  have hzip : j < (layout.zip evals).length := by
    rw [List.length_zip]; omega
  refine ⟨_, List.mem_map.mpr ⟨(layout.zip evals)[j], List.getElem_mem hzip, rfl⟩, ?_, ?_⟩
  · show mkId ((layout.zip evals)[j]).1.1 = _
    rw [List.getElem_zip, List.getD_eq_getElem _ _ hjl]
  · show rotateOmega omega x ((layout.zip evals)[j]).1.2 = _
    rw [List.getElem_zip, List.getD_eq_getElem _ _ hjl]

/-- Each in-range advice layout entry contributes a deployed opening query: slot identity
`adviceCol`, opening point `rotateOmega ω x rot` — the query `deployed_query_point_mem` routes. -/
theorem advice_query_mem_assembleQueries [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (pi : Fin shape.numProofs) {j : ℕ} (hjl : j < vk.adviceQueryLayout.length)
    (hje : j < (List.ofFn (ps.adviceEvals pi)).length) :
    ∃ q ∈ assembleQueries vk ps ch,
      q.commId = CommitmentId.adviceCol pi (vk.adviceQueryLayout.getD j (0, 0)).1 ∧
      q.point = rotateOmega vk.omega ch.x (vk.adviceQueryLayout.getD j (0, 0)).2 := by
  obtain ⟨q, hqmem, hqid, hqpt⟩ := columnQueries_layout_mem (k' := shape.k) vk.omega ch.x
    (finFnG (ps.adviceCommitments pi)) (CommitmentId.adviceCol pi) vk.adviceQueryLayout
    (List.ofFn (ps.adviceEvals pi)) hjl hje
  refine ⟨q, ?_, hqid, hqpt⟩
  simp only [assembleQueries]
  refine List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl (List.mem_append.mpr
    (Or.inl ?_)))))
  refine List.mem_flatten.mpr ⟨_, List.mem_ofFn.mpr ⟨pi, rfl⟩, ?_⟩
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl (List.mem_append.mpr
    (Or.inr hqmem)))))

/-- Each in-range instance layout entry contributes a deployed opening query, as
`advice_query_mem_assembleQueries`. -/
theorem instance_query_mem_assembleQueries [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (pi : Fin shape.numProofs) {j : ℕ} (hjl : j < vk.instanceQueryLayout.length)
    (hje : j < (List.ofFn (ps.instanceEvals pi)).length) :
    ∃ q ∈ assembleQueries vk ps ch,
      q.commId = CommitmentId.instanceCol pi (vk.instanceQueryLayout.getD j (0, 0)).1 ∧
      q.point = rotateOmega vk.omega ch.x (vk.instanceQueryLayout.getD j (0, 0)).2 := by
  obtain ⟨q, hqmem, hqid, hqpt⟩ := columnQueries_layout_mem (k' := shape.k) vk.omega ch.x
    (vk.instanceCommitment pi) (CommitmentId.instanceCol pi) vk.instanceQueryLayout
    (List.ofFn (ps.instanceEvals pi)) hjl hje
  refine ⟨q, ?_, hqid, hqpt⟩
  simp only [assembleQueries]
  refine List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl (List.mem_append.mpr
    (Or.inl ?_)))))
  refine List.mem_flatten.mpr ⟨_, List.mem_ofFn.mpr ⟨pi, rfl⟩, ?_⟩
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl (List.mem_append.mpr
    (Or.inl hqmem)))))

/-- The deployed claimed evaluation feed: entry `n` is member `memIdx n` of point set `setIdx n`'s
claimed evaluation at its layout's rotated opening point (located in the set's point list by
`idxOf`), `0` out of range. This is the concrete `adviceClaimed`/`instanceClaimed` the derived
terminal states its gate fold (`hfold`, the zcash/ironwood#11/#13 fingerprint surface) at. -/
noncomputable def deployedClaimedFeed [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {num : ℕ} (setIdx : Fin num → ℕ)
    (memIdx : ∀ j : Fin num, Fin (deployedSetQueries vk ps ch (setIdx j)).length)
    (layout : List (ℕ × ℤ)) : ℕ → Fp :=
  fun n =>
    if h : n < num then
      ((deployedSetQueries vk ps ch (setIdx ⟨n, h⟩)).getD ((memIdx ⟨n, h⟩ : ℕ))
          (.point 0, [])).2.getD
        (((constructIntermediateSets (assembleQueries vk ps ch)).points.getD
            (setIdx ⟨n, h⟩) []).idxOf
          (rotateOmega vk.omega ch.x (layout.getD n (0, 0)).2)) 0
    else 0

set_option maxHeartbeats 4000000 in
/-- **The member node binding at a located set point (F5 stage B).** `deployed_member_node_binding`
with the point membership supplied instead of a positional index and the `hql` bookkeeping
discharged (`deployedSetQueries_eval_length`): each decoded member column takes its claimed
evaluation at any point of its set — located by `idxOf` — or a nontrivial `(g, U, W)` relation
exists. Feeding it the rotated query point (`deployed_query_point_mem`) yields the gate feed's
value binding. -/
theorem deployed_member_node_binding_at_point [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {a₀ : Fin (2 ^ urs.k) → Fp} {pU pW : Fp}
    {pbatch : OpenedBatchOpenings urs (evalVector urs.k ch.x3)
      (x4BatchCommitments urs hk vk ps ch) (x4BatchEvals vk ps ch) a₀ pU pW}
    (i : ℕ) (hi : i < deployedX4PairCount vk ps ch)
    (md : OpenedMemberDecode urs hk vk ps ch pbatch i hi)
    {ξ₀ : Fp} (hξ₀ : OpenedX1PinnedAccept urs hk vk ps ch ξ₀)
    (hprob1 : (((deployedSetQueries vk ps ch i).length - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
      < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
          (OpenedX1PinnedAccept urs hk vk ps ch)))
    (hx2 : ∀ (r₁ : X1Run shape G) (ξv : Fp), ∃ (b₂ : Fin (2 ^ urs.k) → Fp) (ζ₀ : Fp),
      OpenedX2Accept urs hk vk (r₁.spliced ps) (r₁.challenges ch ξv) b₂ ζ₀ ∧
      ((deployedX4PairCount vk (r₁.spliced ps) (r₁.challenges ch ξv) - 1 : ℕ) : ℝ≥0∞)
          / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
            (OpenedX2Accept urs hk vk (r₁.spliced ps) (r₁.challenges ch ξv) b₂)))
    (hx3anchor : ∀ (r₁ : X1Run shape G) (ξv : Fp) (r₂ : X2Run shape G) (ζv : Fp), ∃ χ₀ : Fp,
      OpenedX3Accept urs hk vk (r₂.spliced (r₁.spliced ps))
        (r₂.challenges (r₁.challenges ch ξv) ζv) (evalVector urs.k χ₀) χ₀)
    (hprob3 : ∀ (r₁ : X1Run shape G) (ξv : Fp) (r₂ : X2Run shape G) (ζv : Fp),
      ((max (2 ^ urs.k) (deployedAllPts vk (r₁.spliced ps) (r₁.challenges ch ξv)).card
          + (deployedAllPts vk (r₁.spliced ps) (r₁.challenges ch ξv)).card : ℕ) : ℝ≥0∞)
          / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
            (fun χv => OpenedX3Accept urs hk vk (r₂.spliced (r₁.spliced ps))
              (r₂.challenges (r₁.challenges ch ξv) ζv) (evalVector urs.k χv) χv)))
    (hprob4 : ∀ (r₁ : X1Run shape G) (ξv : Fp) (r₂ : X2Run shape G) (ζv χv : Fp)
        (r₃ : X3Run shape G),
      (deployedX4PairCount vk (r₃.spliced (r₂.spliced (r₁.spliced ps)))
          (r₃.challenges (r₂.challenges (r₁.challenges ch ξv) ζv) χv) : ℝ≥0∞)
          / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
            (OpenedX4Accept urs hk vk (r₃.spliced (r₂.spliced (r₁.spliced ps)))
              (r₃.challenges (r₂.challenges (r₁.challenges ch ξv) ζv) χv)
              (evalVector urs.k χv))))
    (havoid : ∀ (r₁ : X1Run shape G) (ξv : Fp) (r₂ : X2Run shape G) (ζv χv : Fp),
      OpenedX3Accept urs hk vk (r₂.spliced (r₁.spliced ps))
        (r₂.challenges (r₁.challenges ch ξv) ζv) (evalVector urs.k χv) χv →
      ∀ k', χv ∉ deployedSetPts vk (r₁.spliced ps) (r₁.challenges ch ξv) k')
    {p : Fp} (hpt : p ∈ deployedSetPts vk ps ch i)
    (m₀ : Fin (deployedSetQueries vk ps ch i).length) :
    (coeffsToPoly (md.cols m₀)).eval p
      = ((deployedSetQueries vk ps ch i).getD (m₀ : ℕ) (.point 0, [])).2.getD
          ((((constructIntermediateSets (assembleQueries vk ps ch)).points.getD i []).idxOf p)) 0
    ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  have hmem : p ∈ (constructIntermediateSets (assembleQueries vk ps ch)).points.getD i [] := by
    rw [deployedSetPts] at hpt
    exact List.mem_toFinset.mp hpt
  have hlt : ((constructIntermediateSets (assembleQueries vk ps ch)).points.getD i []).idxOf p
      < ((constructIntermediateSets (assembleQueries vk ps ch)).points.getD i []).length :=
    List.idxOf_lt_length_iff.mpr hmem
  have hb := deployed_member_node_binding urs hk vk ps ch i hi md hξ₀ hprob1 hx2 hx3anchor
    hprob3 hprob4 havoid (deployedSetQueries_eval_length vk ps ch i) ⟨_, hlt⟩ m₀
  rcases hb with hb | hdlr
  · refine Or.inl ?_
    rwa [show (((constructIntermediateSets (assembleQueries vk ps ch)).points.getD i []))[
        (⟨_, hlt⟩ : Fin _)] = p from List.getElem_idxOf hlt] at hb
  · exact Or.inr hdlr

end Zcash.Snark
