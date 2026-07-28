import Mathlib
import Zcash.Snark.Soundness.Main
import Zcash.Snark.Soundness.Forking.Probability
import Zcash.Snark.Soundness.Multiopen.Decode
import Zcash.Snark.Soundness.Multiopen.Compat

/-!
# The deployed multiopen statement is a flat power batch in the `x₄` collapse

The decoded-column layer (`Soundness.Multiopen.Decode`) consumes batched openings in flat power form —
`P = Σⱼ ξʲ • Cⱼ` and `v = Σⱼ ξʲ • eⱼ` at distinct batching challenges `ξ` — and until now that form was a
*model boundary*: the flat-batch family carried the power shape of the deployed statement as
the assumptions `hP`/`hv`. This module discharges them against the deployed verifier. As a function of the
`x₄` squeeze — over the runs `{ch with x4 := ξ}`, which `Soundness.Forking.reprogramX4` identifies with
oracle reprogramming — the pinned `deployedCommitment`/`multiopenValue` *are* flat power batches
(`deployedCommitment_x4_batch`/`multiopenValue_x4_batch`), and the coefficient families are read off the
fingerprinted `constructIntermediateSets` grouping (`x4BatchCommitments`/`x4BatchEvals`):

* power `ξ^j` for `j <` the pair count carries an `x₁`-compressed point-set aggregate `qᵢ` and its claimed
  set evaluation `uᵢ` — in *reverse* processing order, because the deployed collapse folds
  `acc ↦ ξ·acc + next` so the last set processed carries `ξ⁰`;
* the top power carries the prover's quotient commitment `q′` and the recomputed base evaluation
  `msm_eval` (`deployedBaseEval`).

So the batch the decode consumes is the deployed grouping itself — per the fingerprint-equivalence principle the decode
*consumes* the fingerprint-validated `constructIntermediateSets` output rather than re-modeling the
batching as an independent flat power series; no separate "flat model = deployed" obligation is left at
the `x₄` level. The batch "columns" at this level are the multiopen aggregates (`qᵢ`, `q′`), not the
circuit columns: unbatching *within* a point set is the `x₁` layer, one level down.

The rewound-family instantiation that used to sit downstream of this — deriving an injective family
of accepting runs over `{ch with x4 := ξᵣ}` from an accept-*measure* hypothesis, via the
single-squeeze counting floor (`exists_injective_accepting_of_measure`,
`Soundness.Forking.Probability`) — has been removed with the rest of the rewind-based route. The
flat-batch facts below stand on their own.

The `x₁` layer then closes the chain down to the *member* commitments — the actual queried column
commitments (advice, instance, fixed, permutation/lookup products, vanishing). The rewound `x₁` runs
share the pre-`x₁` prefix and re-send the post-`x₁` continuation (`spliceMultiopen`/`x1RunChallenges`;
`reprogramX1` at the sealed `preX1Transcript`, `Soundness.Forking.Rewind`/`Forking.Ordering`); the query
list and grouping are *definitionally* shared across runs (`x1Run_assembleQueries`); each run's
aggregate is the run-`x₁`-power batch of the shared members (`x1Run_x4Qs_getD_eval`); and
the extracted witness is the explicit two-level
(`x₄`-then-`x₁`) power combination of member-column witnesses opening the member commitments, via the
canonical decodes at both levels. Per-member claimed evaluations at the original rotated points and
the gate/`x`→`x₃` transport remain the fingerprint-delegated half (`Soundness.Multiopen.Decode`, the
deployed-status section).
-/

namespace Zcash.Snark

open Zcash.Arithmetic (Msm Msm.eval_appendTerm Msm.zero)

/-! ## The scale-and-add fold in closed power form -/

section PowerFold

variable {F : Type*} [Field F] {M : Type*} [AddCommMonoid M] [Module F M]

/-- Closed form of the collapse fold `acc ↦ ξ • acc + g p`: the initial value climbs to the top power
and the folded entries carry ascending powers in *reverse* order (the last entry folded is multiplied by
`ξ⁰`). Stated over an arbitrary entry projection `g` and an arbitrary `getD` default `d` (never evaluated
in range), so the multiopen collapse's commitment and value components both instantiate it directly. -/
theorem foldl_smul_add_powerForm {α : Type*} (ξ : F) (g : α → M) (d : α) (l : List α) (a₀ : M) :
    l.foldl (fun acc p => ξ • acc + g p) a₀
      = ξ ^ l.length • a₀
        + ∑ j ∈ Finset.range l.length, ξ ^ j • g (l.reverse.getD j d) := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l m ih =>
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ih, List.length_append,
        List.reverse_append]
      simp only [List.length_cons, List.length_nil, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.cons_append]
      rw [Finset.sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, one_smul]
      rw [smul_add, smul_smul, ← pow_succ', Finset.smul_sum]
      have hpow : ∀ j, ξ • ξ ^ j • g (l.reverse.getD j d) = ξ ^ (j + 1) • g (l.reverse.getD j d) := by
        intro j
        rw [smul_smul, ← pow_succ']
      rw [Finset.sum_congr rfl fun j _ => hpow j]
      abel

/-- Reassemble a top power plus a range power sum as one `Fin`-indexed power sum, the last index carrying
the top term — the summation shape `BatchOpeningsForWitness` consumes. -/
theorem powerSum_ite_last (ξ : F) (n : ℕ) (c : ℕ → M) (a₀ : M) :
    ξ ^ n • a₀ + ∑ j ∈ Finset.range n, ξ ^ j • c j
      = ∑ j : Fin (n + 1), ξ ^ (j : ℕ) • (if (j : ℕ) < n then c j else a₀) := by
  rw [Fin.sum_univ_castSucc]
  have hcast : ∀ j : Fin n,
      ξ ^ ((j.castSucc : Fin (n + 1)) : ℕ)
          • (if ((j.castSucc : Fin (n + 1)) : ℕ) < n then c ((j.castSucc : Fin (n + 1)) : ℕ) else a₀)
        = ξ ^ (j : ℕ) • c (j : ℕ) := by
    intro j
    rw [Fin.val_castSucc, if_pos j.is_lt]
  rw [Finset.sum_congr rfl fun j _ => hcast j,
    Fin.sum_univ_eq_sum_range (fun j => ξ ^ j • c j) n, Fin.val_last, if_neg (lt_irrefl n)]
  exact add_comm _ _

end PowerFold

/-- A pair-valued fold whose components do not interact is the pair of the component folds. The multiopen
`x₄` collapse (`multiopenCombine`) has exactly this shape: the MSM component folds the compressed set
commitments, the value component the claimed set evaluations. -/
theorem foldl_prod_componentwise {α β γ δ : Type*} (l : List (α × β))
    (f : γ → α → γ) (g : δ → β → δ) (c₀ : γ) (d₀ : δ) :
    l.foldl (fun st p => (f st.1 p.1, g st.2 p.2)) (c₀, d₀)
      = (l.foldl (fun c p => f c p.1) c₀, l.foldl (fun d p => g d p.2) d₀) := by
  induction l generalizing c₀ d₀ with
  | nil => rfl
  | cons p l ih => exact ih (f c₀ p.1) (g d₀ p.2)

/-- The multiopen `x₄` collapse as the pair of its component folds: the MSM side scale-and-adds the
compressed set commitments into the appended `q′`, the value side the claimed set evaluations into the
base evaluation. -/
theorem multiopenCombine_eq_pair {k : ℕ} {F G : Type*} [Field F] (x4 : F) (qPrime : G)
    (qs : List (Msm k F G)) (u : List F) (e₀ : F) (incoming : Msm k F G) :
    multiopenCombine x4 qPrime qs u e₀ incoming
      = ((qs.zip u).foldl (fun c p => (c.scale x4).add p.1) (incoming.appendTerm 1 qPrime),
         (qs.zip u).foldl (fun d p => d * x4 + p.2) e₀) := by
  rw [multiopenCombine]
  exact foldl_prod_componentwise (qs.zip u) (fun c a => (c.scale x4).add a)
    (fun d b => d * x4 + b) (incoming.appendTerm 1 qPrime) e₀

/-- Evaluating the MSM component's scale-and-add fold is the scale-and-add fold of the evaluations
(`Msm.eval_scale`/`eval_add` pushed through the fold). -/
theorem Msm.eval_foldl_scale_add {F G : Type*} [Field F] [AddCommGroup G] [Module F G] {β : Type*}
    (urs : URS G) (ξ : F) (l : List (Msm urs.k F G × β)) (m₀ : Msm urs.k F G) :
    (l.foldl (fun acc p => (acc.scale ξ).add p.1) m₀).eval urs
      = l.foldl (fun acc p => ξ • acc + p.1.eval urs) (m₀.eval urs) := by
  induction l generalizing m₀ with
  | nil => rfl
  | cons p l ih =>
      rw [List.foldl_cons, ih, List.foldl_cons, Msm.eval_add, Msm.eval_scale]

/-! ## The `x₄` collapse in power form (generic multiopen level) -/

section CombinePowerForm

variable {k : ℕ} {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- The MSM component of the multiopen `x₄` collapse over the zero incoming accumulator, evaluated, in
power form: the quotient commitment `q′` at the top power, the zipped `(qᵢ, uᵢ)` pairs' commitment
evaluations at ascending powers in reverse fold order. -/
theorem multiopenCombine_fst_eval_powerForm (urs : URS G) (ξ : F) (qPrime : G)
    (qs : List (Msm urs.k F G)) (u : List F) (e₀ : F) :
    (multiopenCombine ξ qPrime qs u e₀ (Msm.zero urs.k F G)).1.eval urs
      = ξ ^ (qs.zip u).length • qPrime
        + ∑ j ∈ Finset.range (qs.zip u).length,
            ξ ^ j • ((qs.zip u).reverse.getD j (Msm.zero urs.k F G, 0)).1.eval urs := by
  rw [multiopenCombine_eq_pair]
  show ((qs.zip u).foldl (fun c p => (c.scale ξ).add p.1)
      ((Msm.zero urs.k F G).appendTerm 1 qPrime)).eval urs = _
  rw [Msm.eval_foldl_scale_add,
    foldl_smul_add_powerForm ξ (fun p => p.1.eval urs) (Msm.zero urs.k F G, 0) (qs.zip u)
      (((Msm.zero urs.k F G).appendTerm 1 qPrime).eval urs),
    Msm.eval_appendTerm, Msm.eval_zero, one_smul, zero_add]

omit [AddCommGroup G] [Module F G] in
/-- The value component of the multiopen `x₄` collapse, in power form: the base evaluation `msm_eval` at
the top power, the zipped pairs' claimed set evaluations at ascending powers in reverse fold order. -/
theorem multiopenCombine_snd_powerForm (ξ : F) (qPrime : G)
    (qs : List (Msm k F G)) (u : List F) (e₀ : F) (incoming : Msm k F G) :
    (multiopenCombine ξ qPrime qs u e₀ incoming).2
      = ξ ^ (qs.zip u).length • e₀
        + ∑ j ∈ Finset.range (qs.zip u).length,
            ξ ^ j • ((qs.zip u).reverse.getD j (Msm.zero k F G, 0)).2 := by
  rw [multiopenCombine_eq_pair]
  show (qs.zip u).foldl (fun d p => d * ξ + p.2) e₀ = _
  have hfun : (fun (d : F) (p : Msm k F G × F) => d * ξ + p.2)
      = fun d p => ξ • d + p.2 := by
    funext d p
    rw [smul_eq_mul, mul_comm]
  rw [hfun,
    foldl_smul_add_powerForm ξ (fun p : Msm k F G × F => p.2) (Msm.zero k F G, 0) (qs.zip u) e₀]

end CombinePowerForm

/-! ## The `x₁` within-set layer: each aggregate is a power batch of its member commitments -/

section X1PowerForm

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- Accumulating one query commitment into a point set's compressed MSM adds its power-weighted group
value — uniformly over the plain-point and MSM commitment-reference cases. -/
theorem accumulateCommitment_eval (urs : URS G) (pow : F) (c : CommitmentRef urs.k F G)
    (acc : Msm urs.k F G) :
    (accumulateCommitment pow c acc).eval urs = acc.eval urs + pow • c.eval urs := by
  cases c with
  | point p => rw [accumulateCommitment, CommitmentRef.eval, Msm.eval_appendTerm]
  | msm m => rw [accumulateCommitment, CommitmentRef.eval, Msm.eval_add, Msm.eval_scale]

/-- The `x₁` compression fold, evaluated, over a general accumulator: each remaining query contributes
its commitment's group value at the running power. -/
theorem compressSet_fold_eval (urs : URS G) (x1 : F)
    (sq : List (CommitmentRef urs.k F G × List F)) (m₀ : Msm urs.k F G) (ev₀ : List F) (p₀ : F) :
    ((sq.foldl (fun (st : Msm urs.k F G × List F × F) qc =>
        (accumulateCommitment st.2.2 qc.1 st.1,
         (st.2.1.zip qc.2).map (fun e => e.1 + e.2 * st.2.2),
         st.2.2 * x1)) (m₀, ev₀, p₀)).1).eval urs
      = m₀.eval urs
        + ∑ j ∈ Finset.range sq.length,
            (p₀ * x1 ^ j) • (sq.getD j (.point 0, [])).1.eval urs := by
  induction sq generalizing m₀ ev₀ p₀ with
  | nil => simp
  | cons qc sq ih =>
      rw [List.foldl_cons]
      dsimp only
      rw [ih, accumulateCommitment_eval, List.length_cons, Finset.sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one]
      have hpow : ∀ j ∈ Finset.range sq.length,
          (p₀ * x1 * x1 ^ j) • (sq.getD j (.point 0, [])).1.eval urs
            = (p₀ * x1 ^ (j + 1)) • (sq.getD j (.point 0, [])).1.eval urs := by
        intro j _
        rw [mul_assoc, ← pow_succ']
      rw [Finset.sum_congr rfl hpow]
      abel

/-- **The within-set aggregate is a flat power batch in `x₁`.** The compressed point-set commitment
evaluates to the `x₁`-power combination of its member commitments' group values, in processing order —
the `x₁` half of the two-level un-batching. At the `x₄` level the decoded columns are these aggregates
(`x4BatchCommitments`), and rewinding the `x₁` squeeze un-batches them into the member commitments
(the values are heterogeneous across `x₁` runs because `x₃` re-randomizes). -/
theorem compressSet_fst_eval (urs : URS G) (x1 : F)
    (sq : List (CommitmentRef urs.k F G × List F)) (np : ℕ) :
    (compressSet x1 sq np).1.eval urs
      = ∑ j ∈ Finset.range sq.length, x1 ^ j • (sq.getD j (.point 0, [])).1.eval urs := by
  simp only [compressSet]
  rw [compressSet_fold_eval, Msm.eval_zero, zero_add]
  exact Finset.sum_congr rfl fun j _ => by rw [one_mul]

end X1PowerForm

/-! ## The deployed `x₄` batch families, read off the fingerprinted grouping -/

section Deployed

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- The deployed `x₁`-compressed point-set aggregates, exactly as `assembleOpening` builds them from the
fingerprinted `constructIntermediateSets` grouping: per point set (in processing order), the `x₁`-power
fold of the commitments routed to it. -/
def deployedX4Qs [DecidableEq G] [Inhabited G] {shape : Shape} (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) : List (Msm shape.k Fp G) :=
  let grouped := constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)
  ((grouped.sets.zip grouped.points).map (fun sp => compressSet ch.x1 sp.1 sp.2.length)).map Prod.fst

/-- The deployed `x₄`-collapse pair list: the point-set aggregates zipped with the prover's claimed set
evaluations `u`, in the order the collapse folds them. -/
def deployedX4Pairs [DecidableEq G] [Inhabited G] {shape : Shape} (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) : List (Msm shape.k Fp G × Fp) :=
  (deployedX4Qs vk instanceCommitment ps ch).zip (List.ofFn ps.multiopenU)

/-- The number of `x₄`-collapsed `(qᵢ, uᵢ)` pairs. The `x₄` batch has this many aggregate columns plus
the `q′` slot. -/
def deployedX4PairCount [DecidableEq G] [Inhabited G] {shape : Shape} (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) : ℕ :=
  (deployedX4Pairs vk instanceCommitment ps ch).length

/-- The deployed base evaluation `msm_eval` the `x₄` collapse starts from: the `x₂`-combined,
vanishing-divided Lagrange step (`multiopenEval`) over the fingerprinted grouping — the value the
quotient commitment `q′` is claimed to open to. -/
def deployedBaseEval [DecidableEq G] [Inhabited G] {shape : Shape} (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) : Fp :=
  let grouped := constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)
  let compressed := (grouped.sets.zip grouped.points).map (fun sp => compressSet ch.x1 sp.1 sp.2.length)
  multiopenEval ch.x2 ch.x3
    (((grouped.points.zip (compressed.map Prod.snd)).zip (List.ofFn ps.multiopenU)).map
      (fun p => (p.1.1, p.1.2, p.2)))

/-- The deployed `x₄` batch column commitments: ascending `ξ`-powers carry the point-set aggregates in
reverse fold order, the top power the quotient commitment `q′`. These are the "columns" the `x₄`-level
decode recovers — the fingerprinted grouping's own aggregates, not a modeled flat batch. -/
def x4BatchCommitments [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) : Fin (deployedX4PairCount vk instanceCommitment ps ch + 1) → G :=
  fun j =>
    if (j : ℕ) < deployedX4PairCount vk instanceCommitment ps ch then
      ((deployedX4Pairs vk instanceCommitment ps ch).reverse.getD (j : ℕ) (Msm.zero shape.k Fp G, 0)).1.eval
        ⟨shape.k, hk ▸ urs.g, urs.w, urs.u⟩
    else ps.multiopenQPrime

/-- The deployed `x₄` batch column evaluations: ascending `ξ`-powers carry the claimed set evaluations
`uᵢ` in reverse fold order, the top power the recomputed base evaluation `msm_eval`. -/
def x4BatchEvals [DecidableEq G] [Inhabited G] {shape : Shape} (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) :
    Fin (deployedX4PairCount vk instanceCommitment ps ch + 1) → Fp :=
  fun j =>
    if (j : ℕ) < deployedX4PairCount vk instanceCommitment ps ch then
      ((deployedX4Pairs vk instanceCommitment ps ch).reverse.getD (j : ℕ) (Msm.zero shape.k Fp G, 0)).2
    else deployedBaseEval vk instanceCommitment ps ch

/-- **The deployed commitment is a flat power batch in the `x₄` squeeze.** Over the rewound runs
`{ch with x4 := ξ}` — everything upstream of the collapse (`assembleQueries`, the grouping, the `x₁`
compression, the base evaluation) is untouched by the redraw — the pinned `deployedCommitment` is the
`ξ`-power combination of the deployed aggregates. This discharges the flat-batch model boundary's
`hP` for the deployed verifier, closing the flat-batch model boundary at the `x₄` level. -/
theorem deployedCommitment_x4_batch [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (ξ : Fp) :
    deployedCommitment urs hk vk instanceCommitment ps {ch with x4 := ξ}
      = ∑ j : Fin (deployedX4PairCount vk instanceCommitment ps ch + 1),
          ξ ^ (j : ℕ) • x4BatchCommitments urs hk vk instanceCommitment ps ch j := by
  show (assembleOpening ch.x1 ch.x2 ch.x3 ξ ps.multiopenQPrime (List.ofFn ps.multiopenU)
      (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)) (Msm.zero shape.k Fp G)).1.eval
        ⟨shape.k, hk ▸ urs.g, urs.w, urs.u⟩ = _
  rw [assembleOpening, multiopenCombine_fst_eval_powerForm, powerSum_ite_last]
  rfl

omit [AddCommGroup G] [Module Fp G] in
/-- **The deployed value is a flat power batch in the `x₄` squeeze.** The value companion of
`deployedCommitment_x4_batch`: over `{ch with x4 := ξ}`, the pinned `multiopenValue` is the `ξ`-power
combination of the claimed set evaluations with the base evaluation on top — the discharge of
the flat-batch model boundary's `hv`. -/
theorem multiopenValue_x4_batch [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (ξ : Fp) :
    multiopenValue vk instanceCommitment ps {ch with x4 := ξ}
      = ∑ j : Fin (deployedX4PairCount vk instanceCommitment ps ch + 1), ξ ^ (j : ℕ) • x4BatchEvals vk instanceCommitment ps ch j := by
  show (assembleOpening ch.x1 ch.x2 ch.x3 ξ ps.multiopenQPrime (List.ofFn ps.multiopenU)
      (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)) (Msm.zero shape.k Fp G)).2 = _
  rw [assembleOpening, multiopenCombine_snd_powerForm, powerSum_ite_last]
  rfl

/-- The queries the fingerprinted grouping routes to point set `i`, in the accumulate order the `x₁`
compression folds them (`MultiopenGrouped.sets`, zipped with the set's points). -/
def deployedSetQueries [DecidableEq G] [Inhabited G] {shape : Shape} (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) (i : ℕ) :
    List (CommitmentRef shape.k Fp G × List Fp) :=
  (let grouped := constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)
   (grouped.sets.zip grouped.points).getD i ([], [])).1

/-- The slot identities of point set `i`'s routed members, positionally aligned with
`deployedSetQueries` (halo2 `CommitmentData` retains its commitment identity through the grouping;
`constructIntermediateSets_sets_ids_aligned`). `deployedSetCommIds vk instanceCommitment ps ch i |>.getD m` names
*which* commitment — advice/instance/fixed column, permutation/lookup product, vanishing — member
`(i, m)` is, tying the decoded member polynomials back to the verifying key's query layout. -/
def deployedSetCommIds [DecidableEq G] [Inhabited G] {shape : Shape} (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) (i : ℕ) : List CommitmentId :=
  (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).ids.getD i []

omit [AddCommGroup G] [Module Fp G] in
/-- The commitment-identifier list of a deployed point set has one entry per member query.
Restored after the upstream multiopen prune: the canonical resolver bounds member indices with
it, and no replacement was carried over. -/
theorem deployedSetCommIds_length [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (i : ℕ) :
    (deployedSetCommIds vk instanceCommitment ps ch i).length
      = (deployedSetQueries vk instanceCommitment ps ch i).length := by
  simp only [deployedSetCommIds, deployedSetQueries]
  rw [constructIntermediateSets_zip_sets_getD]
  exact constructIntermediateSets_sets_ids_aligned (assembleQueries vk instanceCommitment ps ch) i


/-- **The two-level batch structure, made explicit.** The `x₄`-level batch column `i` (a point-set
aggregate of `deployedX4Qs`) is itself a flat power batch in the `x₁` squeeze of the member commitments
the fingerprinted grouping routes to that set. Composing with `deployedCommitment_x4_batch`: the deployed
commitment is the `x₄`-power batch of `x₁`-power batches of the actual query commitments — the deployed
two-level collapse in closed form. -/
theorem deployedX4Qs_getD_eval [DecidableEq G] [Inhabited G] {shape : Shape}
    (g : Fin (2 ^ shape.k) → G) (w u : G) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) {i : ℕ}
    (hi : i < (deployedX4Qs vk instanceCommitment ps ch).length) :
    ((deployedX4Qs vk instanceCommitment ps ch).getD i (Msm.zero shape.k Fp G)).eval ⟨shape.k, g, w, u⟩
      = ∑ j ∈ Finset.range (deployedSetQueries vk instanceCommitment ps ch i).length,
          ch.x1 ^ j • ((deployedSetQueries vk instanceCommitment ps ch i).getD j (.point 0, [])).1.eval
            ⟨shape.k, g, w, u⟩ := by
  have hzip : i < ((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).sets.zip
      (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points).length := by
    simpa [deployedX4Qs] using hi
  have hq : (deployedX4Qs vk instanceCommitment ps ch).getD i (Msm.zero shape.k Fp G)
      = (compressSet ch.x1 (deployedSetQueries vk instanceCommitment ps ch i)
          (((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).sets.zip
            (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points).getD i
              ([], [])).2.length).1 := by
    rw [deployedX4Qs, List.getD_eq_getElem _ _ (by simpa [deployedX4Qs] using hi),
      List.getElem_map, List.getElem_map, deployedSetQueries,
      List.getD_eq_getElem _ _ hzip]
  rw [hq, compressSet_fst_eval]

/-- The canonical within-set decode across `x₁` rewinds: the Vandermonde-inverse combination of the
per-run aggregate witnesses — the same explicit combination `decodedColumnFamily_of_batch_openings`
uses at the `x₄` level. -/
noncomputable def x1DecodeCols {m n : ℕ} (z : Fin n → Fp) (a : Fin n → (Fin m → Fp)) :
    Fin n → (Fin m → Fp) :=
  fun j => ∑ r, (Matrix.vandermonde z)⁻¹ j r • a r


/-- The canonical `x₁` decode reconstructs every run's aggregate witness as its `x₁`-power
combination. -/
theorem x1DecodeCols_reconstruct {m n : ℕ} (z : Fin n → Fp) (hz : Function.Injective z)
    (a : Fin n → (Fin m → Fp)) (r : Fin n) :
    a r = ∑ j : Fin n, z r ^ (j : ℕ) • x1DecodeCols z a j :=
  (batch_open_reconstruct_with_coeffs z a _
    (fun i j => by simpa using vandermonde_inv_right z hz i j) r).symm

/-- The canonical `x₁` decode transports every run's value equation: the run's claimed set evaluation
is the `x₁`-power combination of the decoded columns' values at that run's own evaluation vector
(heterogeneous per run — `x₃` re-randomizes under `x₁` rewinds through the re-sent `q′`). -/
theorem x1DecodeCols_value {m n : ℕ} (z : Fin n → Fp) (hz : Function.Injective z)
    (a : Fin n → (Fin m → Fp)) (b : Fin n → (Fin m → Fp)) (u : Fin n → Fp)
    (hau : ∀ r, commitGen (b r) (a r) = u r) (r : Fin n) :
    ∑ j : Fin n, z r ^ (j : ℕ) • commitGen (b r) (x1DecodeCols z a j) = u r := by
  have hlin : ∑ j : Fin n, z r ^ (j : ℕ) • commitGen (b r) (x1DecodeCols z a j)
      = commitGen (b r) (∑ j : Fin n, z r ^ (j : ℕ) • x1DecodeCols z a j) := by
    rw [commitGen_sum]
    exact Finset.sum_congr rfl fun j _ => (commitGen_smul_left (b r) _ _).symm
  rw [hlin, ← x1DecodeCols_reconstruct z hz a r]
  exact hau r





/-! ## The `x₁` rewound runs: shared pre-`x₁` prefix, re-sent continuation

Rewinding the compression squeeze is one step deeper than the `x₄` collapse: the rewound prover
re-sends everything absorbed *after* `x₁` — the quotient commitment `q′`, the claimed set evaluations
`u`, and the IPA opening — so `x₃`…`z` and the round challenges re-randomize per run (their squeeze
inputs absorb the fresh continuation), while `x₂` stays the honest one (nothing is absorbed between
the compression squeezes, `preX2Transcript_length_eq`) and everything absorbed before `x₁` is shared:
the column commitments, every claimed evaluation (`adviceEvals_mem_preX1Transcript` and companions,
`Soundness.Forking.Ordering`), hence the whole query list and the fingerprinted grouping. The runs
are `reprogramX1` reprogramming events (`Soundness.Forking.Rewind`) on the spliced strings. What varies per
run is exactly the `x₁`-power weighting of the *same* member commitments — the shape
`x1DecodeCols` un-batches. -/

/-- The rewound prover's post-`x₁` continuation: the proof fields absorbed after `x₁` is squeezed,
re-sent per `x₁` rewind. The `x₁` analogue of the IPA-level `spliceIpa` path data. -/
structure MultiopenContinuation (shape : Shape) (G : Type*) where
  multiopenQPrime : G
  multiopenU : Fin shape.numPointSets → Fp
  ipaS : G
  ipaRounds : Fin shape.k → G × G
  ipaC : Fp
  ipaF : Fp

/-- Splice a post-`x₁` continuation onto the shared pre-`x₁` proof prefix: every field absorbed before
`x₁` is the base `ps`'s, the post-`x₁` fields are the continuation's. -/
def spliceMultiopen {shape : Shape} (ps : ProofString shape Fp G)
    (c : MultiopenContinuation shape G) : ProofString shape Fp G :=
  { ps with
    multiopenQPrime := c.multiopenQPrime
    multiopenU := c.multiopenU
    ipaS := c.ipaS
    ipaRounds := c.ipaRounds
    ipaC := c.ipaC
    ipaF := c.ipaF }

/-- The rewound run's challenge record: pre-`x₁` challenges the honest `ch`'s, the compression
challenge replaced by `χ`, every post-`x₁` challenge the run's own. -/
def x1RunChallenges {k : ℕ} (ch : Challenges k Fp) (χ x2 x3 x4 xi z : Fp)
    (ipaRound : Fin k → Fp) : Challenges k Fp :=
  { theta := ch.theta
    beta := ch.beta
    gamma := ch.gamma
    y := ch.y
    x := ch.x
    x1 := χ
    x2 := x2
    x3 := x3
    x4 := x4
    xi := xi
    z := z
    ipaRound := ipaRound }

/-- One `x₁`-rewound run: the re-sent continuation and the run's post-`x₁` challenges, all carried
free (under reprogramming `x₂` is in fact the honest one — its squeeze input absorbs nothing new —
so the freedom only widens the hypotheses). -/
structure X1Run (shape : Shape) (G : Type*) where
  cont : MultiopenContinuation shape G
  x2 : Fp
  x3 : Fp
  x4 : Fp
  xi : Fp
  z : Fp
  ipaRound : Fin shape.k → Fp

/-- The run's proof string: the shared pre-`x₁` prefix with the run's continuation spliced on. -/
def X1Run.spliced {shape : Shape} (r : X1Run shape G) (ps : ProofString shape Fp G) :
    ProofString shape Fp G :=
  spliceMultiopen ps r.cont

/-- The run's challenge record at compression challenge `χ`. -/
def X1Run.challenges {shape : Shape} (r : X1Run shape G) (ch : Challenges shape.k Fp) (χ : Fp) :
    Challenges shape.k Fp :=
  x1RunChallenges ch χ r.x2 r.x3 r.x4 r.xi r.z r.ipaRound

/-- The honest run as an `X1Run`: its own continuation and challenges. Splicing it back is the
identity (by structure eta), so the honest run sits inside every
`x₁`-rewind family — the eta identities are what instantiations discharge `hcur`/`hwC` at the honest
slot with. -/
def honestX1Run {shape : Shape} (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) :
    X1Run shape G :=
  ⟨⟨ps.multiopenQPrime, ps.multiopenU, ps.ipaS, ps.ipaRounds, ps.ipaC, ps.ipaF⟩,
    ch.x2, ch.x3, ch.x4, ch.xi, ch.z, ch.ipaRound⟩



/-! The pre-`x₁` projections of a rewound run are the honest ones — the per-field `rfl` facts the
root query-list invariance is assembled from (keeping every definitional-equality check small). -/

omit [AddCommGroup G] [Module Fp G] in
/-- Pre-`x₁` challenge projection shared across runs. -/
theorem x1Run_challenges_x {shape : Shape} (r : X1Run shape G) (ch : Challenges shape.k Fp)
    (χ : Fp) : (r.challenges ch χ).x = ch.x := rfl

omit [AddCommGroup G] [Module Fp G] in
/-- Pre-`x₁` challenge projection shared across runs. -/
theorem x1Run_challenges_y {shape : Shape} (r : X1Run shape G) (ch : Challenges shape.k Fp)
    (χ : Fp) : (r.challenges ch χ).y = ch.y := rfl

omit [AddCommGroup G] [Module Fp G] in
/-- Pre-`x₁` proof projection shared across runs. -/
theorem x1Run_spliced_adviceCommitments {shape : Shape} (r : X1Run shape G)
    (ps : ProofString shape Fp G) : (r.spliced ps).adviceCommitments = ps.adviceCommitments := rfl

omit [AddCommGroup G] [Module Fp G] in
/-- Pre-`x₁` proof projection shared across runs. -/
theorem x1Run_spliced_lookupPermutedInput {shape : Shape} (r : X1Run shape G)
    (ps : ProofString shape Fp G) :
    (r.spliced ps).lookupPermutedInput = ps.lookupPermutedInput := rfl

omit [AddCommGroup G] [Module Fp G] in
/-- Pre-`x₁` proof projection shared across runs. -/
theorem x1Run_spliced_lookupPermutedTable {shape : Shape} (r : X1Run shape G)
    (ps : ProofString shape Fp G) :
    (r.spliced ps).lookupPermutedTable = ps.lookupPermutedTable := rfl

omit [AddCommGroup G] [Module Fp G] in
/-- Pre-`x₁` proof projection shared across runs. -/
theorem x1Run_spliced_permutationProduct {shape : Shape} (r : X1Run shape G)
    (ps : ProofString shape Fp G) :
    (r.spliced ps).permutationProduct = ps.permutationProduct := rfl

omit [AddCommGroup G] [Module Fp G] in
/-- Pre-`x₁` proof projection shared across runs. -/
theorem x1Run_spliced_lookupProduct {shape : Shape} (r : X1Run shape G)
    (ps : ProofString shape Fp G) : (r.spliced ps).lookupProduct = ps.lookupProduct := rfl

omit [AddCommGroup G] [Module Fp G] in
/-- Pre-`x₁` proof projection shared across runs. -/
theorem x1Run_spliced_vanishingRandom {shape : Shape} (r : X1Run shape G)
    (ps : ProofString shape Fp G) : (r.spliced ps).vanishingRandom = ps.vanishingRandom := rfl

omit [AddCommGroup G] [Module Fp G] in
/-- Pre-`x₁` proof projection shared across runs. -/
theorem x1Run_spliced_hPieces {shape : Shape} (r : X1Run shape G)
    (ps : ProofString shape Fp G) : (r.spliced ps).hPieces = ps.hPieces := rfl

omit [AddCommGroup G] [Module Fp G] in
/-- Pre-`x₁` proof projection shared across runs. -/
theorem x1Run_spliced_instanceEvals {shape : Shape} (r : X1Run shape G)
    (ps : ProofString shape Fp G) : (r.spliced ps).instanceEvals = ps.instanceEvals := rfl

omit [AddCommGroup G] [Module Fp G] in
/-- Pre-`x₁` proof projection shared across runs. -/
theorem x1Run_spliced_adviceEvals {shape : Shape} (r : X1Run shape G)
    (ps : ProofString shape Fp G) : (r.spliced ps).adviceEvals = ps.adviceEvals := rfl

omit [AddCommGroup G] [Module Fp G] in
/-- Pre-`x₁` proof projection shared across runs. -/
theorem x1Run_spliced_fixedEvals {shape : Shape} (r : X1Run shape G)
    (ps : ProofString shape Fp G) : (r.spliced ps).fixedEvals = ps.fixedEvals := rfl

omit [AddCommGroup G] [Module Fp G] in
/-- Pre-`x₁` proof projection shared across runs. -/
theorem x1Run_spliced_vanishingRandomEval {shape : Shape} (r : X1Run shape G)
    (ps : ProofString shape Fp G) :
    (r.spliced ps).vanishingRandomEval = ps.vanishingRandomEval := rfl

omit [AddCommGroup G] [Module Fp G] in
/-- Pre-`x₁` proof projection shared across runs. -/
theorem x1Run_spliced_permutationCommonEvals {shape : Shape} (r : X1Run shape G)
    (ps : ProofString shape Fp G) :
    (r.spliced ps).permutationCommonEvals = ps.permutationCommonEvals := rfl

omit [AddCommGroup G] [Module Fp G] in
/-- Pre-`x₁` proof projection shared across runs. -/
theorem x1Run_spliced_permutationSetEvals {shape : Shape} (r : X1Run shape G)
    (ps : ProofString shape Fp G) :
    (r.spliced ps).permutationSetEvals = ps.permutationSetEvals := rfl

omit [AddCommGroup G] [Module Fp G] in
/-- Pre-`x₁` proof projection shared across runs. -/
theorem x1Run_spliced_lookupEvals {shape : Shape} (r : X1Run shape G)
    (ps : ProofString shape Fp G) : (r.spliced ps).lookupEvals = ps.lookupEvals := rfl

omit [AddCommGroup G] [Module Fp G] in
/-- The per-sub-proof constraint values are shared across `x₁` rewinds: they read only pre-`x₁`
evaluations and challenges. -/
theorem x1Run_subProofExpressions {shape : Shape} (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) (r : X1Run shape G) (χ : Fp)
    (l0 lLast lBlind : Fp) (p : Fin shape.numProofs) :
    subProofExpressions vk (r.spliced ps) (r.challenges ch χ) l0 lLast lBlind p
      = subProofExpressions vk ps ch l0 lLast lBlind p := rfl

omit [AddCommGroup G] [Module Fp G] in
/-- The full constraint-value list is shared across `x₁` rewinds. -/
theorem x1Run_allExpressions {shape : Shape} (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) (r : X1Run shape G) (χ : Fp)
    (l0 lLast lBlind : Fp) :
    allExpressions vk (r.spliced ps) (r.challenges ch χ) l0 lLast lBlind
      = allExpressions vk ps ch l0 lLast lBlind := by
  simp only [allExpressions, x1Run_subProofExpressions]

omit [AddCommGroup G] [Module Fp G] in
/-- **The query list is shared across `x₁` rewinds** — the root invariance. The assembly reads only
pre-`x₁` data: the commitments and claimed evaluations absorbed before the compression squeeze (none
of the spliced continuation's fields) and the pre-`x₁` challenges (none of the run record's redrawn
fields). Assembled from the per-field projection facts so every definitional-equality check stays
small. Everything grouping-derived is rewritten through this one equality. A refactor of the
assembly's read set — a new challenge read or a post-`x₁` proof-field read — breaks this seal loudly,
by design; extend the per-field projection facts alongside. -/
theorem x1Run_assembleQueries [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (r : X1Run shape G) (χ : Fp) :
    assembleQueries vk instanceCommitment (r.spliced ps) (r.challenges ch χ) = assembleQueries vk instanceCommitment ps ch := by
  simp only [assembleQueries, x1Run_allExpressions, x1Run_challenges_x, x1Run_challenges_y,
    x1Run_spliced_hPieces, x1Run_spliced_instanceEvals, x1Run_spliced_adviceCommitments,
    x1Run_spliced_adviceEvals, x1Run_spliced_permutationProduct,
    x1Run_spliced_permutationSetEvals, x1Run_spliced_lookupProduct,
    x1Run_spliced_lookupPermutedInput, x1Run_spliced_lookupPermutedTable,
    x1Run_spliced_lookupEvals, x1Run_spliced_fixedEvals, x1Run_spliced_permutationCommonEvals,
    x1Run_spliced_vanishingRandom, x1Run_spliced_vanishingRandomEval]

omit [AddCommGroup G] [Module Fp G] in
/-- The grouping's routed queries are shared across `x₁` rewinds. -/
theorem x1Run_setQueries [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (r : X1Run shape G) (χ : Fp) (i : ℕ) :
    deployedSetQueries vk instanceCommitment (r.spliced ps) (r.challenges ch χ) i
      = deployedSetQueries vk instanceCommitment ps ch i := by
  simp only [deployedSetQueries, x1Run_assembleQueries]

omit [AddCommGroup G] [Module Fp G] in
/-- The number of point-set aggregates is shared across `x₁` rewinds. -/
theorem x1Run_x4Qs_length [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (r : X1Run shape G) (χ : Fp) :
    (deployedX4Qs vk instanceCommitment (r.spliced ps) (r.challenges ch χ)).length
      = (deployedX4Qs vk instanceCommitment ps ch).length := by
  simp only [deployedX4Qs, x1Run_assembleQueries, List.length_map]

omit [AddCommGroup G] [Module Fp G] in
/-- The `x₄` pair count is shared across `x₁` rewinds: the grouping is the honest one and the `u`
vector's length is shape-fixed. Interface fact for callers re-indexing a run's `x₄` batch against
the honest one (`x4BatchCommitments_getD` at the run); no in-tree consumer yet. -/
theorem x1Run_pairCount [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (r : X1Run shape G) (χ : Fp) :
    deployedX4PairCount vk instanceCommitment (r.spliced ps) (r.challenges ch χ) = deployedX4PairCount vk instanceCommitment ps ch := by
  simp only [deployedX4PairCount, deployedX4Pairs, List.length_zip, List.length_ofFn,
    x1Run_x4Qs_length]

/-- **The run aggregate is the run-`x₁`-power batch of the honest members.** At a rewound run, point
set `i`'s aggregate evaluates to the `χ`-power combination of the *shared* member commitments the
honest grouping routes to that set — the `x₁` collapse re-weighted, nothing else moved. -/
theorem x1Run_x4Qs_getD_eval [DecidableEq G] [Inhabited G] {shape : Shape}
    (g : Fin (2 ^ shape.k) → G) (w u : G) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) (r : X1Run shape G) (χ : Fp)
    {i : ℕ} (hi : i < (deployedX4Qs vk instanceCommitment ps ch).length) :
    ((deployedX4Qs vk instanceCommitment (r.spliced ps) (r.challenges ch χ)).getD i (Msm.zero shape.k Fp G)).eval
        ⟨shape.k, g, w, u⟩
      = ∑ j ∈ Finset.range (deployedSetQueries vk instanceCommitment ps ch i).length,
          χ ^ j • ((deployedSetQueries vk instanceCommitment ps ch i).getD j (.point 0, [])).1.eval
            ⟨shape.k, g, w, u⟩ := by
  have hi' : i < (deployedX4Qs vk instanceCommitment (r.spliced ps) (r.challenges ch χ)).length := by
    rw [x1Run_x4Qs_length]
    exact hi
  rw [deployedX4Qs_getD_eval g w u vk instanceCommitment (r.spliced ps) (r.challenges ch χ) hi',
    x1Run_setQueries]
  rfl

/-! ## The `x₃` and `x₂` rewound runs: shared prefixes, re-sent continuations

Rewinding the interpolation challenge `x₃` re-sends the fields absorbed after it — the claimed set
evaluations `u` and the IPA opening — while the quotient commitment `q′` is absorbed *before* `x₃`
(`qPrime_mem_preX3Transcript`) and stays shared, as do `x₁`/`x₂`, the query list, the grouping, and
hence the point-set aggregates themselves: across `x₃` runs only the evaluation point and the
claimed set evaluations move. Rewinding `x₂` additionally re-sends `q′`. The runs are the
`reprogramX3`/`reprogramX2` reprogramming events (`Soundness.Forking.Rewind`). -/

/-- The rewound prover's post-`x₃` continuation: the claimed set evaluations and the IPA opening
(`q′` is pre-`x₃` and shared). -/
structure X3Continuation (shape : Shape) (G : Type*) where
  multiopenU : Fin shape.numPointSets → Fp
  ipaS : G
  ipaRounds : Fin shape.k → G × G
  ipaC : Fp
  ipaF : Fp

/-- Splice a post-`x₃` continuation onto the shared pre-`x₃` proof prefix. -/
def spliceX3 {shape : Shape} (ps : ProofString shape Fp G) (c : X3Continuation shape G) :
    ProofString shape Fp G :=
  { ps with
    multiopenU := c.multiopenU
    ipaS := c.ipaS
    ipaRounds := c.ipaRounds
    ipaC := c.ipaC
    ipaF := c.ipaF }

/-- One `x₃`-rewound run: the re-sent continuation and the run's post-`x₃` challenges. -/
structure X3Run (shape : Shape) (G : Type*) where
  cont : X3Continuation shape G
  x4 : Fp
  xi : Fp
  z : Fp
  ipaRound : Fin shape.k → Fp

/-- The run's proof string: the shared pre-`x₃` prefix with the run's continuation spliced on. -/
def X3Run.spliced {shape : Shape} (r : X3Run shape G) (ps : ProofString shape Fp G) :
    ProofString shape Fp G :=
  spliceX3 ps r.cont

/-- The run's challenge record at interpolation challenge `χ`: pre-`x₃` challenges the honest
ones, `x₃ := χ`, post-`x₃` challenges the run's own. -/
def X3Run.challenges {shape : Shape} (r : X3Run shape G) (ch : Challenges shape.k Fp) (χ : Fp) :
    Challenges shape.k Fp :=
  { theta := ch.theta, beta := ch.beta, gamma := ch.gamma, y := ch.y, x := ch.x
    x1 := ch.x1, x2 := ch.x2, x3 := χ, x4 := r.x4, xi := r.xi, z := r.z
    ipaRound := r.ipaRound }









/-- The rewound prover's post-`x₂` continuation: additionally re-sends `q′`. -/
structure X2Continuation (shape : Shape) (G : Type*) where
  multiopenQPrime : G
  multiopenU : Fin shape.numPointSets → Fp
  ipaS : G
  ipaRounds : Fin shape.k → G × G
  ipaC : Fp
  ipaF : Fp

/-- Splice a post-`x₂` continuation onto the shared pre-`x₂` proof prefix. -/
def spliceX2 {shape : Shape} (ps : ProofString shape Fp G) (c : X2Continuation shape G) :
    ProofString shape Fp G :=
  { ps with
    multiopenQPrime := c.multiopenQPrime
    multiopenU := c.multiopenU
    ipaS := c.ipaS
    ipaRounds := c.ipaRounds
    ipaC := c.ipaC
    ipaF := c.ipaF }

/-- One `x₂`-rewound run: the re-sent continuation and the run's post-`x₂` challenges. -/
structure X2Run (shape : Shape) (G : Type*) where
  cont : X2Continuation shape G
  x3 : Fp
  x4 : Fp
  xi : Fp
  z : Fp
  ipaRound : Fin shape.k → Fp

/-- The run's proof string: the shared pre-`x₂` prefix with the run's continuation spliced on. -/
def X2Run.spliced {shape : Shape} (r : X2Run shape G) (ps : ProofString shape Fp G) :
    ProofString shape Fp G :=
  spliceX2 ps r.cont

/-- The run's challenge record at set-separation challenge `χ`. -/
def X2Run.challenges {shape : Shape} (r : X2Run shape G) (ch : Challenges shape.k Fp) (χ : Fp) :
    Challenges shape.k Fp :=
  { theta := ch.theta, beta := ch.beta, gamma := ch.gamma, y := ch.y, x := ch.x
    x1 := ch.x1, x2 := χ, x3 := r.x3, x4 := r.x4, xi := r.xi, z := r.z
    ipaRound := r.ipaRound }







/-! ## The `x₄` rewound runs with a re-sent opening: the adaptive collapse

Rewinding the batching challenge `x₄` re-sends the fields absorbed *after* it — the IPA opening
(`ipaS`, `ipaRounds`, `ipaC`, `ipaF`) — while everything absorbed before `x₄` stays shared: the
claimed set evaluations `u` (`multiopenU_mem_preX4Transcript`), the quotient `q′`, `x₁`/`x₂`/`x₃`,
the query list, the grouping, and hence the point-set aggregates and the recomputed base evaluation.
So the `x₄` batch columns (`x4BatchCommitments`/`x4BatchEvals`) — the aggregates the decode consumes —
are *definitionally* the honest ones across `x₄` runs; only the IPA opening the fork's clean tree
witnesses moves per run. The runs are the `reprogramX4` reprogramming events
(`Soundness.Forking.Rewind`). This is the adaptive analogue of the `x₁` layer's `spliceMultiopen`:
it lets each rewound `x₄` run present its own opening rather than reusing the honest `ps`, so the
accept measure fed to the collapse no longer inherits a constant strategy. -/

/-- The rewound prover's post-`x₄` continuation: the IPA opening absorbed after `x₄` is squeezed
(`u` is pre-`x₄` and shared). -/
structure X4Continuation (shape : Shape) (G : Type*) where
  ipaS : G
  ipaRounds : Fin shape.k → G × G
  ipaC : Fp
  ipaF : Fp

/-- Splice a post-`x₄` continuation onto the shared pre-`x₄` proof prefix. -/
def spliceX4 {shape : Shape} (ps : ProofString shape Fp G) (c : X4Continuation shape G) :
    ProofString shape Fp G :=
  { ps with
    ipaS := c.ipaS
    ipaRounds := c.ipaRounds
    ipaC := c.ipaC
    ipaF := c.ipaF }

/-- One `x₄`-rewound run: the re-sent opening and the run's post-`x₄` challenges. -/
structure X4Run (shape : Shape) (G : Type*) where
  cont : X4Continuation shape G
  xi : Fp
  z : Fp
  ipaRound : Fin shape.k → Fp

/-- The run's proof string: the shared pre-`x₄` prefix with the run's continuation spliced on. -/
def X4Run.spliced {shape : Shape} (r : X4Run shape G) (ps : ProofString shape Fp G) :
    ProofString shape Fp G :=
  spliceX4 ps r.cont

/-- The run's challenge record at batching challenge `χ`: pre-`x₄` challenges the honest ones,
`x₄ := χ`, post-`x₄` challenges the run's own. -/
def X4Run.challenges {shape : Shape} (r : X4Run shape G) (ch : Challenges shape.k Fp) (χ : Fp) :
    Challenges shape.k Fp :=
  { theta := ch.theta, beta := ch.beta, gamma := ch.gamma, y := ch.y, x := ch.x
    x1 := ch.x1, x2 := ch.x2, x3 := ch.x3, x4 := χ, xi := r.xi, z := r.z
    ipaRound := r.ipaRound }

/-- The honest run as an `X4Run`; splicing it back is the identity by structure eta. -/
def honestX4Run {shape : Shape} (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) :
    X4Run shape G :=
  ⟨⟨ps.ipaS, ps.ipaRounds, ps.ipaC, ps.ipaF⟩, ch.xi, ch.z, ch.ipaRound⟩












/-! ## From the `x₄` batch positions back to the sets, and the member binding -/

/-- The in-range `x₄` batch columns, set-indexed: batch column `j` is the aggregate of point set
`count − 1 − j` (the collapse folds the sets so the last one processed carries `ξ⁰`). -/
theorem x4BatchCommitments_getD [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) {j : Fin (deployedX4PairCount vk instanceCommitment ps ch + 1)}
    (hj : (j : ℕ) < deployedX4PairCount vk instanceCommitment ps ch) :
    x4BatchCommitments urs hk vk instanceCommitment ps ch j
      = ((deployedX4Qs vk instanceCommitment ps ch).getD (deployedX4PairCount vk instanceCommitment ps ch - 1 - (j : ℕ))
            (Msm.zero shape.k Fp G)).eval ⟨shape.k, hk ▸ urs.g, urs.w, urs.u⟩ := by
  rw [x4BatchCommitments, if_pos hj]
  have hj₁ : (j : ℕ) < (deployedX4Pairs vk instanceCommitment ps ch).reverse.length := by
    rw [List.length_reverse]
    exact hj
  have hj₂ : deployedX4PairCount vk instanceCommitment ps ch - 1 - (j : ℕ) < (deployedX4Pairs vk instanceCommitment ps ch).length := by
    have hj' : (j : ℕ) < (deployedX4Pairs vk instanceCommitment ps ch).length := hj
    simp only [deployedX4PairCount]
    omega
  have hj₃ : deployedX4PairCount vk instanceCommitment ps ch - 1 - (j : ℕ) < (deployedX4Qs vk instanceCommitment ps ch).length := by
    have hle : (deployedX4Pairs vk instanceCommitment ps ch).length ≤ (deployedX4Qs vk instanceCommitment ps ch).length := by
      simp only [deployedX4Pairs, List.length_zip]
      exact min_le_left _ _
    simp only [deployedX4PairCount]
    omega
  rw [List.getD_eq_getElem _ _ hj₁, List.getElem_reverse, List.getD_eq_getElem _ _ hj₃]
  congr 1
  exact congrArg Prod.fst List.getElem_zip

omit [AddCommGroup G] [Module Fp G] in
/-- The `x₄` pair count is the length of the pair list — the definitional unfolding, as a lemma so
downstream files can use it without delta-reducing the sealed definition. -/
theorem deployedX4PairCount_eq [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) :
    deployedX4PairCount vk instanceCommitment ps ch = (deployedX4Pairs vk instanceCommitment ps ch).length := rfl

omit [AddCommGroup G] [Module Fp G] in
/-- The top slot of the `x₄` batch evaluations is the recomputed base evaluation: the slot index
equals the pair count, so the branch that reads a point set is not taken. -/
theorem x4BatchEvals_top [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) :
    x4BatchEvals vk instanceCommitment ps ch ⟨deployedX4PairCount vk instanceCommitment ps ch, Nat.lt_succ_self _⟩
      = deployedBaseEval vk instanceCommitment ps ch := by
  show (if deployedX4PairCount vk instanceCommitment ps ch < deployedX4PairCount vk instanceCommitment ps ch then _
    else deployedBaseEval vk instanceCommitment ps ch) = deployedBaseEval vk instanceCommitment ps ch
  rw [if_neg (lt_irrefl _)]




end Deployed

end Zcash.Snark
