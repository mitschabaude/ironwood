import Mathlib
import Zcash.Snark.Core.ProofString
import Zcash.Snark.Core.Challenges
import Zcash.Snark.Verifier.Checks
import Zcash.Snark.Verifier.Queries
import Zcash.Snark.Verifier.Expressions
import Zcash.Snark.Verifier.Ipa

/-!
# Assembling the fingerprint MSM

This module composes the verified building blocks into the verifier's MSM assembly, in the exact order
of halo2 `plonk/verifier.rs`. It is the Lean image of the interactive verifier: a pure function of the
proof string, the challenges, and the verifying-key–level circuit structure.

The assembly factors into three stages:

* `assembleQueries` (the upstream) — recompute the vanishing `h` commitment and `expected_h_eval`, then
  build the full ordered list of opening queries (per sub-proof: instance, advice, permutation, lookups;
  then shared: fixed, permutation-common, vanishing).
* `constructIntermediateSets` — group the flat query list into per-point-set commitment and
  evaluation data: VK-fixed bookkeeping, re-derived in Lean rather than supplied, and exercised
  by the `native_decide` fingerprint match.
* `assembleFinalMsm` (the downstream) — takes the `MultiopenGrouped`, then the multiopen `x₁` compression
  and `x₄` collapse, then the IPA fold, producing the final MSM.

The verifying-key data (`VerifyingKey`) — gate polynomials, query layouts, fixed/permutation
commitments, the permutation column/eval chunking, lookup expressions — is circuit-fixed and supplied as
input; the instance commitments are statement-derived (the verifier computes them from the public
instances) and bundled here for the assembly.
-/

namespace Zcash.Snark

/-- A permutation column's evaluation reference (halo2 `get_any_query_index` + `column_type`): the
column's value is the advice / fixed / instance evaluation at the given query index. -/
inductive ColumnRef where
  | advice : ℕ → ColumnRef
  | fixed : ℕ → ColumnRef
  | instance : ℕ → ColumnRef

/-- Resolve a permutation column reference to its claimed evaluation. -/
def ColumnRef.resolve {F : Type*} (cr : ColumnRef) (instanceEvals adviceEvals fixedEvals : ℕ → F) : F :=
  match cr with
  | .advice i => adviceEvals i
  | .fixed i => fixedEvals i
  | .instance i => instanceEvals i

-- TODO(VK-correctness): a `VerifyingKey` value is populated from the halo2 `dump_lean_fixture`
-- capture (`Fixtures/SingleAction/Fixture.lean`) and trusted verbatim — Lean never re-derives it from the
-- Orchard circuit. So "the dumped VK is the real circuit's" is an assumption, not a theorem: the
-- input-faithfulness boundary. Discharging it means re-running keygen and comparing. Distinct
-- from the output-side semantic-adequacy gap (see `Soundness/Main.lean`).
/-- The verifying-key–level circuit structure the assembly needs (halo2 `VerifyingKey` / `ConstraintSystem`).
`omega` is the domain generator and `n = 2 ^ k` the domain size; `blindingFactors`, `delta`, `chunkLen`
are the permutation-argument constants. `gates` are the custom-gate polynomials; `instance/advice/fixed
QueryLayout` are the `(column, rotation)` query lists; `fixedCommitment`, `permutationCommonCommitment`
and `instanceCommitment` (statement-derived) resolve column indices to commitments;
`permutationChunks` groups the permutation columns (with their common-eval indices) per set; and
`lookupInput/TableExprs` are the per-lookup input/table expressions. -/
structure VerifyingKey (shape : Shape) (F G : Type*) where
  omega : F
  n : ℕ
  blindingFactors : ℕ
  delta : F
  chunkLen : ℕ
  gates : List (Expr F)
  instanceQueryLayout : List (ℕ × ℤ)
  adviceQueryLayout : List (ℕ × ℤ)
  fixedQueryLayout : List (ℕ × ℤ)
  fixedCommitment : ℕ → G
  instanceCommitment : Fin shape.numProofs → ℕ → G
  permutationCommonCommitment : Fin shape.numPermutationColumns → G
  permutationChunks : List (List (ColumnRef × ℕ))
  lookupInputExprs : Fin shape.numLookups → List (Expr F)
  lookupTableExprs : Fin shape.numLookups → List (Expr F)

/-- View a `Fin n`-indexed family as a total `ℕ`-indexed function, `0` outside range (the query indices
the verifier uses are always in range). -/
def finFn {F : Type*} [Zero F] {n : ℕ} (f : Fin n → F) : ℕ → F :=
  fun i => if h : i < n then f ⟨i, h⟩ else 0

/-- View a `Fin n`-indexed family of group elements as a total `ℕ`-indexed function (`default`
out of range), like `finFn`. Caveat: an out-of-range index aliases `default` rather than erroring
— the Vesta identity in the concrete fixtures, and `0` in abstract shape fixtures — so faithfulness
rests on the VK's query indices being in range. -/
def finFnG {G : Type*} [Inhabited G] {n : ℕ} (f : Fin n → G) : ℕ → G :=
  fun i => if h : i < n then f ⟨i, h⟩ else default

/-- The `i`-th Lagrange basis polynomial of the size-`n` multiplicative domain, evaluated at `x` (halo2
`EvaluationDomain::l_i_range`): `(xⁿ − 1) · ωⁱ / (n · (x − ωⁱ))`. -/
def lagrangeBasisValue {F : Type*} [Field F] (omega : F) (n : ℕ) (xn x : F) (i : ℤ) : F :=
  (xn - 1) * omega ^ i / ((n : F) * (x - omega ^ i))

/-- The three Lagrange basis values the vanishing check needs (halo2 `plonk/verifier.rs`): `l₀`
(rotation `0`), `l_last` (rotation `−(blinding+1)`), and `l_blind` (sum over rotations `−blinding..−1`). -/
def lagrangeBasis {F : Type*} [Field F] (omega : F) (n blinding : ℕ) (xn x : F) : F × F × F :=
  let l0 := lagrangeBasisValue omega n xn x 0
  let lLast := lagrangeBasisValue omega n xn x (-((blinding : ℤ) + 1))
  let lBlind := ((List.range blinding).map
    (fun j => lagrangeBasisValue omega n xn x (-((j : ℤ) + 1)))).foldl (· + ·) (0 : F)
  (l0, lLast, lBlind)

/-- The constraint values for one sub-proof (halo2 `plonk/verifier.rs`, the per-proof `flat_map`):
the gate-polynomial values, then the permutation-argument values, then the lookup-argument values. -/
def subProofExpressions {shape : Shape} {F G : Type*} [Field F] (vk : VerifyingKey shape F G)
    (ps : ProofString shape F G) (ch : Challenges shape.k F) (l0 lLast lBlind : F)
    (p : Fin shape.numProofs) : List F :=
  let fE := finFn ps.fixedEvals
  let aE := finFn (ps.adviceEvals p)
  let iE := finFn (ps.instanceEvals p)
  let gateE := vk.gates.map (fun g => g.eval fE aE iE)
  let sets := List.ofFn (fun s => ps.permutationSetEvals p s)
  let chunks := (sets.zip vk.permutationChunks).map (fun sc =>
    (sc.1, sc.2.map (fun cr => (cr.1.resolve iE aE fE, finFn ps.permutationCommonEvals cr.2))))
  let permE := permutationExpressions sets chunks ch.beta ch.gamma ch.x vk.delta vk.chunkLen l0 lLast lBlind
  let lookupE := (List.ofFn (fun l => lookupExpressions (ps.lookupEvals p l)
    (vk.lookupInputExprs l) (vk.lookupTableExprs l) fE aE iE ch.theta ch.beta ch.gamma l0 lLast lBlind)).flatten
  gateE ++ permE ++ lookupE

/-- All constraint values across the sub-proofs, in the verifier's order. -/
def allExpressions {shape : Shape} {F G : Type*} [Field F] (vk : VerifyingKey shape F G)
    (ps : ProofString shape F G) (ch : Challenges shape.k F) (l0 lLast lBlind : F) : List F :=
  (List.ofFn (fun p => subProofExpressions vk ps ch l0 lLast lBlind p)).flatten

/-- The verifier's full ordered list of opening queries (halo2 `plonk/verifier.rs`): recompute the
vanishing `h` commitment and `expected_h_eval`, then chain, per sub-proof, the instance / advice /
permutation / lookup queries, followed by the shared fixed / permutation-common / vanishing queries. -/
def assembleQueries {shape : Shape} {F G : Type*} [Field F] [Inhabited G] (vk : VerifyingKey shape F G)
    (ps : ProofString shape F G) (ch : Challenges shape.k F) : List (VerifierQuery shape.k F G) :=
  let x := ch.x
  let xn := x ^ vk.n
  let xNext := rotateOmega vk.omega x 1
  let xInv := rotateOmega vk.omega x (-1)
  let xLast := rotateOmega vk.omega x (-((vk.blindingFactors : ℤ) + 1))
  let lb := lagrangeBasis vk.omega vk.n vk.blindingFactors xn x
  let exprs := allExpressions vk ps ch lb.1 lb.2.1 lb.2.2
  let eHEval := expectedHEval exprs ch.y xn
  let hComm := vanishingHCommitment shape.k xn (List.ofFn ps.hPieces)
  let perProof := (List.ofFn (fun p =>
    columnQueries vk.omega x (vk.instanceCommitment p) (CommitmentId.instanceCol p)
        vk.instanceQueryLayout (List.ofFn (ps.instanceEvals p))
    ++ columnQueries vk.omega x (finFnG (ps.adviceCommitments p)) (CommitmentId.adviceCol p)
        vk.adviceQueryLayout (List.ofFn (ps.adviceEvals p))
    ++ permutationQueries x xNext xLast (CommitmentId.permProduct p)
        (List.ofFn (fun s => (ps.permutationProduct p s, ps.permutationSetEvals p s)))
    ++ lookupQueries x xInv xNext (CommitmentId.lookupProduct p) (CommitmentId.lookupPermInput p)
        (CommitmentId.lookupPermTable p) (List.ofFn (fun l =>
        ({ product := ps.lookupProduct p l, permutedInput := ps.lookupPermutedInput p l,
           permutedTable := ps.lookupPermutedTable p l }, ps.lookupEvals p l))))).flatten
  let fixedQ := columnQueries vk.omega x vk.fixedCommitment CommitmentId.fixedCol vk.fixedQueryLayout
    (List.ofFn ps.fixedEvals)
  let permCommonQ := permutationCommonQueries x CommitmentId.permCommon
    (List.ofFn (fun c => (vk.permutationCommonCommitment c, ps.permutationCommonEvals c)))
  let vanishingQ := vanishingQueries x hComm eHEval ps.vanishingRandom ps.vanishingRandomEval
  perProof ++ fixedQ ++ permCommonQ ++ vanishingQ

/-- The multiopen point-set grouping (halo2 `construct_intermediate_sets` output): per point set,
the queries grouped into it as `(commitment, evaluations at this set's points)`, plus the set's
points, plus — mirroring halo2's `CommitmentData` retaining its commitment identity
(`poly/multiopen.rs`: `CommitmentData { commitment: T, .. }`, identity by pointer equality, here
the `CommitmentId` slot) — the routed members' slot identities, positionally aligned with `sets`
(`ids[i][m]` is the identity of the member `sets[i][m]`; both are projections of one routed list,
`constructIntermediateSets_sets_ids_aligned`). The identity is what ties a decoded member back to
the verifying key's query layout (which column, which rotation). Derived by
`constructIntermediateSets`. -/
structure MultiopenGrouped (k : ℕ) (F G : Type*) where
  sets : List (List (CommitmentRef k F G × List F))
  ids : List (List CommitmentId)
  points : List (List F)

/-- Compress one point set by the `x₁` powers (halo2 `multiopen/verifier.rs` `accumulate`): fold the
set's query contributions, accumulating both the commitment MSM (`Σⱼ x₁ʲ cⱼ`) and the per-point
evaluation vector (`Σⱼ x₁ʲ evalsⱼ`). -/
def compressSet {k : ℕ} {F G : Type*} [Field F] (x1 : F)
    (setQueries : List (CommitmentRef k F G × List F)) (numPoints : ℕ) : Msm k F G × List F :=
  let res := setQueries.foldl (fun (st : Msm k F G × List F × F) qc =>
      (accumulateCommitment st.2.2 qc.1 st.1,
       (st.2.1.zip qc.2).map (fun e => e.1 + e.2 * st.2.2),
       st.2.2 * x1))
    (Msm.zero k F G, List.replicate numPoints (0 : F), (1 : F))
  (res.1, res.2.1)

/-- The multiopen opening MSM and combined value (halo2 `multiopen/verifier.rs`): compress each point
set by `x₁`, compute the combined evaluation by Lagrange interpolation at `x₃` (`multiopenEval`), then
collapse by `x₄` against `q'` (`multiopenCombine`). `u` are the prover's claimed per-set quotient
evaluations. -/
def assembleOpening {k : ℕ} {F G : Type*} [Field F] (x1 x2 x3 x4 : F) (qPrime : G) (u : List F)
    (grouped : MultiopenGrouped k F G) (incoming : Msm k F G) : Msm k F G × F :=
  let compressed := (grouped.sets.zip grouped.points).map (fun sp => compressSet x1 sp.1 sp.2.length)
  let qCommitments := compressed.map Prod.fst
  let setsForEval := ((grouped.points.zip (compressed.map Prod.snd)).zip u).map
    (fun p => (p.1.1, p.1.2, p.2))
  let msmEval := multiopenEval x2 x3 setsForEval
  multiopenCombine x4 qPrime qCommitments u msmEval incoming

/-- The final fingerprint MSM (halo2 `plonk/verifier.rs` → `multiopen/verifier.rs` →
`commitment/verifier.rs`): the multiopen opening, then the IPA fold opening it at `x₃` to the combined
value. `grouped` is the `construct_intermediate_sets` output for `assembleQueries vk ps ch`. -/
def assembleFinalMsm {shape : Shape} {F G : Type*} [Field F] (ps : ProofString shape F G)
    (ch : Challenges shape.k F) (grouped : MultiopenGrouped shape.k F G) : Msm shape.k F G :=
  let opened := assembleOpening ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime (List.ofFn ps.multiopenU)
    grouped (Msm.zero shape.k F G)
  ipaFold ch.x3 opened.2 ps.ipaC ps.ipaF ch.xi ch.z (List.ofFn ch.ipaRound) ps.ipaS
    (List.ofFn ps.ipaRounds) opened.1

/-- **The assembled fingerprint MSM evaluates to the verifier's IPA verification equation.**
Composing `eval_ipaFold` over `assembleFinalMsm = ipaFold … (assembleOpening …).1`: the deployed
MSM's evaluation is the multiopen commitment opened by the IPA, term for term (the closed form is
the statement) — so the deployed accept (`… = 0`) is this verification equation. The URS is built
from `g, w, u`, so its `k` is `shape.k` definitionally — no transport needed. This puts
`eval_ipaFold` on the soundness path. -/
theorem eval_assembleFinalMsm {shape : Shape} {F G : Type*} [Field F] [AddCommGroup G] [Module F G]
    (g : Fin (2 ^ shape.k) → G) (w u : G) (ps : ProofString shape F G) (ch : Challenges shape.k F)
    (grouped : MultiopenGrouped shape.k F G) :
    (assembleFinalMsm ps ch grouped).eval ⟨shape.k, g, w, u⟩
      = (assembleOpening ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime (List.ofFn ps.multiopenU) grouped
            (Msm.zero shape.k F G)).1.eval ⟨shape.k, g, w, u⟩
        + (∑ i, ([-(assembleOpening ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime (List.ofFn ps.multiopenU)
            grouped (Msm.zero shape.k F G)).2].getD i.val 0) • g i)
        + ch.xi • ps.ipaS
        + (((List.ofFn ps.ipaRounds).zip (List.ofFn ch.ipaRound)).map
            (fun p => p.2⁻¹ • p.1.1 + p.2 • p.1.2)).sum
        + (-ps.ipaC * computeB ch.x3 (List.ofFn ch.ipaRound) * ch.z) • u
        + (-ps.ipaF) • w
        + (∑ i, ((computeS (List.ofFn ch.ipaRound) (-ps.ipaC)).getD i.val 0) • g i) := by
  simp only [assembleFinalMsm]
  rw [eval_ipaFold]

/-- Re-derivation of halo2 `construct_intermediate_sets` (`poly/multiopen.rs`): group the flat
opening queries into point sets, producing the `MultiopenGrouped` that `assembleOpening` consumes
— derived in Lean rather than supplied. Queries are grouped by slot identity (`commId`, halo2's
pointer identity — see `CommitmentId`); the orderings mirror the Rust and are noted step by step
in the body. `constructIntermediateSets?` is the rejecting form. -/
def constructIntermediateSets {k : ℕ} {F G : Type*} [DecidableEq F] [DecidableEq G]
    (queries : List (VerifierQuery k F G)) : MultiopenGrouped k F G :=
  -- distinct points, in first-appearance order; `pointIdx p` is `p`'s index in that order
  let points : List F :=
    queries.foldl (fun acc q => if q.point ∈ acc then acc else acc ++ [q.point]) []
  let pointIdx : F → ℕ := fun p => points.findIdx (fun x => decide (x = p))
  -- distinct commitments by slot identity (`commId`), in first-appearance order (halo2 `IndexMap` by
  -- pointer identity); the paired `CommitmentRef` is the curve value the group contributes to the MSM
  let comms : List (CommitmentId × CommitmentRef k F G) :=
    queries.foldl (fun acc q => if acc.any (fun c => decide (c.1 = q.commId)) then acc
      else acc ++ [(q.commId, q.commitment)]) []
  -- per commitment (halo2 `CommitmentData`, identity retained): its slot identity, curve value,
  -- ascending point-index set, and eval vector over that set
  let commData : List (CommitmentId × CommitmentRef k F G × List ℕ × List F) :=
    comms.map fun c =>
      let qs := queries.filter fun q => decide (q.commId = c.1)
      let idxs := qs.map fun q => pointIdx q.point
      let idxSet := (List.range points.length).filter fun i => idxs.contains i
      let evals := idxSet.filterMap fun i =>
        (qs.find? fun q => decide (pointIdx q.point = i)).map (·.eval)
      (c.1, c.2, idxSet, evals)
  -- distinct point-index sets, first-appearance order (over commitments) → set index
  let setList : List (List ℕ) :=
    commData.foldl (fun acc cd => if cd.2.2.1 ∈ acc then acc else acc ++ [cd.2.2.1]) []
  let setIdx : List ℕ → ℕ := fun s => setList.findIdx fun x => decide (x = s)
  -- accumulate order is reversed commitment order; per set, the members routed to it — `sets`
  -- (curve value, evals) and `ids` (slot identity) are projections of the same routed list, so
  -- they are positionally aligned by construction
  let revData := commData.reverse
  let routed : ℕ → List (CommitmentId × CommitmentRef k F G × List ℕ × List F) :=
    fun si => revData.filter fun cd => decide (setIdx cd.2.2.1 = si)
  let sets : List (List (CommitmentRef k F G × List F)) :=
    (List.range setList.length).map fun si => (routed si).map fun cd => (cd.2.1, cd.2.2.2)
  let ids : List (List CommitmentId) :=
    (List.range setList.length).map fun si => (routed si).map (·.1)
  -- per set, its points in ascending point-index order
  let setPoints : List (List F) := setList.map fun s => s.filterMap fun i => points[i]?
  { sets := sets, ids := ids, points := setPoints }

/-- The grouping's `ids` and `sets` views are positionally aligned: per point set they are two
projections of the same routed member list (halo2's `CommitmentData` entries routed to that set),
so their lengths agree — `ids[i][m]` names the slot identity of the member `sets[i][m]`. -/
theorem constructIntermediateSets_sets_ids_aligned {k : ℕ} {F G : Type*} [DecidableEq F]
    [DecidableEq G] (queries : List (VerifierQuery k F G)) (i : ℕ) :
    ((constructIntermediateSets queries).ids.getD i []).length
      = ((constructIntermediateSets queries).sets.getD i []).length := by
  simp only [constructIntermediateSets, List.getD_eq_getElem?_getD, List.getElem?_map]
  rcases h : (List.range _)[i]? with _ | si
  · simp
  · simp [List.length_map]

/-- The `ids` view has one entry per point set, aligned with `sets`. -/
theorem constructIntermediateSets_ids_length {k : ℕ} {F G : Type*} [DecidableEq F]
    [DecidableEq G] (queries : List (VerifierQuery k F G)) :
    (constructIntermediateSets queries).ids.length
      = (constructIntermediateSets queries).sets.length := by
  simp [constructIntermediateSets]

/-- `sets` and `points` have one entry per point set. -/
theorem constructIntermediateSets_points_length {k : ℕ} {F G : Type*} [DecidableEq F]
    [DecidableEq G] (queries : List (VerifierQuery k F G)) :
    (constructIntermediateSets queries).sets.length
      = (constructIntermediateSets queries).points.length := by
  simp [constructIntermediateSets]

/-- Projecting the first component of the `sets.zip points` view (`deployedSetQueries`'s shape) is
the plain `sets` entry — the zip never truncates, since `sets` and `points` are equal-length. -/
theorem constructIntermediateSets_zip_sets_getD {k : ℕ} {F G : Type*} [DecidableEq F]
    [DecidableEq G] (queries : List (VerifierQuery k F G)) (i : ℕ) :
    (((constructIntermediateSets queries).sets.zip
        (constructIntermediateSets queries).points).getD i ([], [])).1
      = (constructIntermediateSets queries).sets.getD i [] := by
  have hlen := constructIntermediateSets_points_length queries
  rcases lt_or_ge i (constructIntermediateSets queries).sets.length with hi | hi
  · rw [List.getD_eq_getElem _ _ (by rw [List.length_zip, ← hlen, min_self]; exact hi),
      List.getElem_zip, List.getD_eq_getElem _ _ hi]
  · rw [List.getD_eq_default _ _ (by rw [List.length_zip, ← hlen, min_self]; exact hi),
      List.getD_eq_default _ _ hi]

/-- Anything already in the accumulator survives the first-appearance dedup fold. -/
private theorem mem_dedup_foldl_mono {α β : Type*} [DecidableEq β] (l : List α) (f : α → β) :
    ∀ (init : List β) (x : β), x ∈ init →
      x ∈ l.foldl (fun acc a => if f a ∈ acc then acc else acc ++ [f a]) init := by
  induction l with
  | nil => intro init x hx; simpa using hx
  | cons a l ih =>
      intro init x hx
      rw [List.foldl_cons]
      apply ih
      by_cases h : f a ∈ init
      · rwa [if_pos h]
      · rw [if_neg h]; exact List.mem_append.mpr (Or.inl hx)

/-- Every element's image under `f` lands in the first-appearance dedup fold over `l`. -/
private theorem mem_dedup_foldl {α β : Type*} [DecidableEq β] (l : List α) (f : α → β) :
    ∀ (init : List β) {a : α}, a ∈ l →
      f a ∈ l.foldl (fun acc b => if f b ∈ acc then acc else acc ++ [f b]) init := by
  induction l with
  | nil => intro init a ha; exact absurd ha (List.not_mem_nil)
  | cons c l ih =>
      intro init a ha
      rw [List.foldl_cons]
      rcases List.mem_cons.mp ha with rfl | ha'
      · apply mem_dedup_foldl_mono
        by_cases h : f a ∈ init
        · rwa [if_pos h]
        · rw [if_neg h]; exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
      · exact ih _ ha'

/-- `findIdx` of a present element retrieves it: the option-get at that index is the element. -/
private theorem getElem?_findIdx_self {α : Type*} [DecidableEq α] {l : List α} {x : α}
    (h : x ∈ l) : l[l.findIdx (fun y => decide (y = x))]? = some x := by
  have hex : ∃ z ∈ l, (fun y => decide (y = x)) z = true := ⟨x, h, by simp⟩
  have hlt : l.findIdx (fun y => decide (y = x)) < l.length :=
    List.findIdx_lt_length_of_exists hex
  rw [List.getElem?_eq_getElem hlt]
  have hval := List.findIdx_getElem (p := fun y => decide (y = x)) (xs := l) (w := hlt)
  simp only [decide_eq_true_eq] at hval
  rw [hval]

/-- **Point routing (F4 core).** Every query's point lands in the point list of the set its
commitment slot is routed to: if `q ∈ queries` and `q.commId` names member `m` of point set `si`
(`ids[si][m] = q.commId`), then `q.point` appears in set `si`'s points. The point companion of
`constructIntermediateSets_ref_mem` — a query routed into a set by its slot identity has its opening
point among that set's points, since the set's points are exactly the point-indices of the members
routed there. -/
theorem constructIntermediateSets_point_mem {k : ℕ} {F G : Type*} [DecidableEq F] [DecidableEq G]
    (queries : List (VerifierQuery k F G))
    {q : VerifierQuery k F G} (hq : q ∈ queries) {si m : ℕ} {d₀ : CommitmentId}
    (hlt : m < ((constructIntermediateSets queries).ids.getD si []).length)
    (hid : ((constructIntermediateSets queries).ids.getD si []).getD m d₀ = q.commId) :
    q.point ∈ (constructIntermediateSets queries).points.getD si [] := by
  classical
  -- positional `getD` → membership: `q.commId` is a member of set `si`'s id list
  have hmem : q.commId ∈ (constructIntermediateSets queries).ids.getD si [] := by
    have h1 : ((constructIntermediateSets queries).ids.getD si [])[m] = q.commId := by
      rw [← hid, List.getD_eq_getElem _ _ hlt]
    exact h1 ▸ List.getElem_mem hlt
  simp only [constructIntermediateSets] at hmem ⊢
  -- reduce `ids.getD si` (a `(range _).map _` list) to its `si`-th entry
  rw [List.getD_eq_getElem?_getD, List.getElem?_map] at hmem
  rcases hrange : (List.range _)[si]? with _ | j
  · rw [hrange] at hmem
    simp only [Option.map_none, Option.getD_none, List.not_mem_nil] at hmem
  · rw [hrange] at hmem
    obtain ⟨hsiN, hjval⟩ := List.getElem?_eq_some_iff.mp hrange
    rw [List.getElem_range] at hjval
    subst j
    simp only [Option.map_some, Option.getD_some] at hmem
    obtain ⟨cd, hcd, hcd1⟩ := List.mem_map.mp hmem
    -- `cd` is routed to `si` and its commId is `q.commId`
    rw [List.mem_filter] at hcd
    obtain ⟨hcdrev, hcddec⟩ := hcd
    rw [decide_eq_true_eq] at hcddec
    rw [List.mem_reverse] at hcdrev
    -- `cd`'s point-index set is set `si`'s distinct index list, so `points.getD si` filters it
    have hcdset := mem_dedup_foldl _ (fun x => x.2.2.1) ([] : List (List ℕ)) hcdrev
    have hsi := getElem?_findIdx_self hcdset
    simp only [hcddec] at hsi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, hsi, Option.map_some,
      Option.getD_some, List.mem_filterMap]
    -- the point-index of `q.point` witnesses membership: it is a valid index retrieving `q.point`,
    -- and it lies in `cd`'s (hence set `si`'s) index set because `q` is one of `cd`'s queries
    refine ⟨(List.foldl (fun acc q => if q.point ∈ acc then acc else acc ++ [q.point]) []
      queries).findIdx (fun y => decide (y = q.point)), ?_, ?_⟩
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hcdrev
      refine List.mem_filter.mpr ⟨?_, ?_⟩
      · rw [List.mem_range]
        exact List.findIdx_lt_length_of_exists
          ⟨q.point, mem_dedup_foldl _ (fun x => x.point) [] hq, by simp⟩
      · exact (List.contains_iff_mem).mpr (List.mem_map.mpr
          ⟨q, List.mem_filter.mpr ⟨hq, by rw [decide_eq_true_eq]; exact hcd1.symm⟩, rfl⟩)
    · exact getElem?_findIdx_self (mem_dedup_foldl _ (fun x => x.point) [] hq)

/-- The first-appearance dedup fold produces a `Nodup` list (it appends only elements not already
present). -/
private theorem nodup_dedup_foldl {α β : Type*} [DecidableEq β] (l : List α) (f : α → β) :
    ∀ (init : List β), init.Nodup →
      (l.foldl (fun acc a => if f a ∈ acc then acc else acc ++ [f a]) init).Nodup := by
  induction l with
  | nil => intro init h; simpa using h
  | cons a l ih =>
      intro init h
      rw [List.foldl_cons]
      apply ih
      by_cases hmem : f a ∈ init
      · rwa [if_pos hmem]
      · rw [if_neg hmem]
        exact List.Nodup.append h (List.nodup_singleton _) (List.disjoint_singleton.mpr hmem)

/-- **Each deployed point set's point list has no duplicates.** The grouping's `points` field lists
each point set's points; every such list is a `filterMap` of a duplicate-free index set over the
internal distinct-points list (itself `Nodup` by the first-appearance fold), extracting distinct
entries, so it is `Nodup`. -/
theorem constructIntermediateSets_points_nodup {k : ℕ} {F G : Type*} [DecidableEq F] [DecidableEq G]
    (queries : List (VerifierQuery k F G)) (idx : ℕ) :
    ((constructIntermediateSets queries).points.getD idx []).Nodup := by
  classical
  have key : ∀ ps ∈ (constructIntermediateSets queries).points, ps.Nodup := by
    intro ps hps
    simp only [constructIntermediateSets] at hps
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hps
    -- `s` is one of the distinct point-index sets, hence a filtered `range`, hence `Nodup`
    -- (via a fold invariant on the actual `setList` fold, to match its membership instance)
    have hsnodup : s.Nodup := by
      refine List.foldlRecOn (motive := fun acc : List (List ℕ) => ∀ x ∈ acc, x.Nodup)
        _ _ ?_ ?_ s hs
      · intro x hx; exact absurd hx (List.not_mem_nil)
      · intro acc hacc cd hcd
        split
        · exact hacc
        · intro x hx
          rcases List.mem_append.mp hx with h | h
          · exact hacc x h
          · rw [List.mem_singleton] at h
            subst h
            obtain ⟨c, -, rfl⟩ := List.mem_map.mp hcd
            exact List.Nodup.filter _ List.nodup_range
    -- the internal points list is `Nodup`
    have hpnodup : (queries.foldl (fun acc q => if q.point ∈ acc then acc else acc ++ [q.point])
        ([] : List F)).Nodup := nodup_dedup_foldl queries (·.point) [] List.nodup_nil
    -- `filterMap (points[·]?)` preserves `Nodup`: distinct valid indices give distinct entries
    refine List.Nodup.filterMap ?_ hsnodup
    intro i i' b hb hb'
    rw [Option.mem_def, List.getElem?_eq_some_iff] at hb hb'
    obtain ⟨hi, hbi⟩ := hb
    obtain ⟨hi', hbi'⟩ := hb'
    have h2 : (⟨i, hi⟩ : Fin _) = ⟨i', hi'⟩ :=
      List.nodup_iff_injective_getElem.mp hpnodup (hbi.trans hbi'.symm)
    exact congrArg Fin.val h2
  rcases lt_or_ge idx (constructIntermediateSets queries).points.length with hlt | hge
  · rw [List.getD_eq_getElem _ _ hlt]; exact key _ (List.getElem_mem hlt)
  · rw [List.getD_eq_default _ _ hge]; exact List.nodup_nil

/-- Two `filterMap`s over the same list have equal length when both functions are everywhere
defined on it. -/
private theorem length_filterMap_eq_of_forall_isSome {α β γ : Type*}
    {f : α → Option β} {g : α → Option γ} :
    ∀ (l : List α), (∀ x ∈ l, (f x).isSome) → (∀ x ∈ l, (g x).isSome) →
      (l.filterMap f).length = (l.filterMap g).length := by
  intro l
  induction l with
  | nil => intro _ _; rfl
  | cons a l ih =>
      intro hf hg
      have hfa := hf a (List.mem_cons_self ..)
      have hga := hg a (List.mem_cons_self ..)
      rw [List.filterMap_cons, List.filterMap_cons]
      rcases ha : f a with _ | b
      · rw [ha] at hfa; exact absurd hfa (by simp)
      rcases hb : g a with _ | c
      · rw [hb] at hga; exact absurd hga (by simp)
      simp only [List.length_cons]
      exact congrArg Nat.succ (ih (fun x hx => hf x (List.mem_cons_of_mem _ hx))
        (fun x hx => hg x (List.mem_cons_of_mem _ hx)))

/-- **Each routed member claims one evaluation per set point.** A grouped member's evaluation list
and its set's point list are `filterMap`s over the same duplicate-free point-index set, and both
extractions are everywhere defined — every index in the set is in range of the internal points
list, and every index got there from some query of the member's slot, so the `find?` succeeds. So
the lengths agree: the member claims exactly one evaluation at each of its set's points. -/
theorem constructIntermediateSets_eval_length {k : ℕ} {F G : Type*} [DecidableEq F] [DecidableEq G]
    (queries : List (VerifierQuery k F G)) (i : ℕ) :
    ∀ qc ∈ (constructIntermediateSets queries).sets.getD i [],
      qc.2.length = ((constructIntermediateSets queries).points.getD i []).length := by
  classical
  intro qc hqc
  simp only [constructIntermediateSets] at hqc ⊢
  rw [List.getD_eq_getElem?_getD, List.getElem?_map] at hqc
  rcases hrange : (List.range _)[i]? with _ | j
  · rw [hrange] at hqc
    simp only [Option.map_none, Option.getD_none, List.not_mem_nil] at hqc
  · rw [hrange] at hqc
    obtain ⟨hsiN, hjval⟩ := List.getElem?_eq_some_iff.mp hrange
    rw [List.getElem_range] at hjval
    subst j
    simp only [Option.map_some, Option.getD_some] at hqc
    obtain ⟨cd, hcd, rfl⟩ := List.mem_map.mp hqc
    -- `cd` is routed to set `i`: its point-index set is `setList[i]`
    rw [List.mem_filter] at hcd
    obtain ⟨hcdrev, hcddec⟩ := hcd
    rw [decide_eq_true_eq] at hcddec
    rw [List.mem_reverse] at hcdrev
    have hcdset := mem_dedup_foldl _ (fun x => x.2.2.1) ([] : List (List ℕ)) hcdrev
    have hsi := getElem?_findIdx_self hcdset
    simp only [hcddec] at hsi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, hsi, Option.map_some,
      Option.getD_some]
    -- `cd` comes from `commData`: its evals are a `filterMap` over its own index set
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hcdrev
    -- both `filterMap`s are everywhere defined on the index set
    refine length_filterMap_eq_of_forall_isSome _ ?_ ?_
    · intro x hx
      rw [List.mem_filter] at hx
      have hxq := (List.contains_iff_mem).mp hx.2
      obtain ⟨q, hq, hqi⟩ := List.mem_map.mp hxq
      have hfind : (List.find? (fun q' => decide ((List.foldl
          (fun acc q'' => if q''.point ∈ acc then acc else acc ++ [q''.point]) [] queries).findIdx
            (fun y => decide (y = q'.point)) = x))
          (queries.filter (fun q' => decide (q'.commId = c.1)))).isSome := by
        rw [List.find?_isSome]
        exact ⟨q, hq, by simp [hqi]⟩
      simpa using hfind
    · intro x hx
      rw [List.mem_filter, List.mem_range] at hx
      rw [List.getElem?_eq_getElem hx.1]
      exact Option.isSome_some

/-- Whether the flat query list contains two queries for the same commitment slot at the same
point. Halo2 rejects this (`None`, mapped to `OpeningError`), even when the two evaluations
agree. -/
def hasDuplicateCommitmentPoint {k : ℕ} {F G : Type*} [DecidableEq F] :
    List (VerifierQuery k F G) → Bool
  | [] => false
  | q :: qs =>
      qs.any (fun r => decide (r.commId = q.commId ∧ r.point = q.point))
        || hasDuplicateCommitmentPoint qs

/-- Rejecting version of `constructIntermediateSets`, matching halo2's `Option` guard for duplicate
queries with the same commitment slot and point. -/
def constructIntermediateSets? {k : ℕ} {F G : Type*} [DecidableEq F] [DecidableEq G]
    (queries : List (VerifierQuery k F G)) : Option (MultiopenGrouped k F G) :=
  if hasDuplicateCommitmentPoint queries then none else some (constructIntermediateSets queries)

/-- Rejecting version of `assembleOpening`. Halo2 derives the number of `u` evaluations from the grouped
point sets and reads exactly that many scalars; a mismatch means the typed proof string is not the deployed
verifier's read stream. -/
def assembleOpening? {k : ℕ} {F G : Type*} [Field F] (x1 x2 x3 x4 : F) (qPrime : G) (u : List F)
    (grouped : MultiopenGrouped k F G) (incoming : Msm k F G) : Option (Msm k F G × F) :=
  if u.length = grouped.sets.length ∧ grouped.points.length = grouped.sets.length then
    some (assembleOpening x1 x2 x3 x4 qPrime u grouped incoming)
  else
    none

/-- Rejecting version of `assembleFinalMsm`, using the deployed verifier's dynamic `u` count check. -/
def assembleFinalMsm? {shape : Shape} {F G : Type*} [Field F] (ps : ProofString shape F G)
    (ch : Challenges shape.k F) (grouped : MultiopenGrouped shape.k F G) : Option (Msm shape.k F G) :=
  match assembleOpening? ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime (List.ofFn ps.multiopenU)
      grouped (Msm.zero shape.k F G) with
  | some opened =>
      some <| ipaFold ch.x3 opened.2 ps.ipaC ps.ipaF ch.xi ch.z (List.ofFn ch.ipaRound) ps.ipaS
        (List.ofFn ps.ipaRounds) opened.1
  | none => none

/-- The multiopen inverse factors are defined only when the IPA challenge `x₃` is not one of the opened
points in any derived point set. In the deployed verifier this case is a panic, not an error return
(`(x₃ - point).invert().unwrap()` in `multiopen/verifier.rs`); the Lean rejection abstracts that crash —
both are non-accepting, which is what soundness consumes. `card_multiopenPanic_le` bounds the offending
`x₃`: at most one per opened point, a negligible proportion of challenges. -/
def multiopenPointsAvoidX3 {k : ℕ} {F G : Type*} [DecidableEq F] (x3 : F)
    (grouped : MultiopenGrouped k F G) : Bool :=
  grouped.points.all fun pts => pts.all fun point => decide (x3 ≠ point)

/-- **Multiopen panic hits a negligible proportion of challenges.** The IPA challenges `x₃` that trigger
the deployed `(x₃ - point).invert().unwrap()` crash (the `multiopenPointsAvoidX3 = false` case) are
exactly the opened points, so at most the opened-point count across the derived point sets. Over `F_p`
that is a `≤ #points / p` fraction (`|F_p| = p ≈ 2²⁵⁴`, `card_Fp`), negligible since the point count is
polynomial in the circuit size. -/
theorem card_multiopenPanic_le {k : ℕ} {F G : Type*} [DecidableEq F] [Fintype F]
    (grouped : MultiopenGrouped k F G) :
    (Finset.univ.filter (fun x3 : F => multiopenPointsAvoidX3 x3 grouped = false)).card
      ≤ grouped.points.flatten.length := by
  -- the panicking `x₃` embed in the flattened list of opened points
  refine le_trans (Finset.card_le_card ?_) (List.toFinset_card_le _)
  intro x3 hx3
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx3
  rw [List.mem_toFinset]
  -- an `x₃` that avoided every opened point would not panic, contradicting `avoid = false`
  by_contra hnot
  have hAvoid : multiopenPointsAvoidX3 x3 grouped = true := by
    simp only [multiopenPointsAvoidX3, List.all_eq_true, decide_eq_true_eq]
    intro pts hpts point hpoint hx
    exact hnot (List.mem_flatten.mpr ⟨pts, hpts, by rw [hx]; exact hpoint⟩)
  rw [hAvoid] at hx3
  exact Bool.noConfusion hx3

/-- **Vanishing panic hits a negligible proportion of challenges.** The evaluation challenges `x` with
`xⁿ = 1` trigger the deployed `(xⁿ - 1).invert().unwrap()` crash (guarded as `none` in `assemble?`); they
are the `n`-th roots of unity, at most `n` of them (`n = vk.n`, the domain size). Over `F_p` that is a
`≤ n / p` fraction, negligible for `p ≈ 2²⁵⁴`. -/
theorem card_vanishingPanic_le {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}
    (hn : 0 < n) :
    (Finset.univ.filter (fun x : F => x ^ n = 1)).card ≤ n := by
  -- the bad `x` are the roots of `Xⁿ - 1`, at most `n` of them
  refine le_trans (Finset.card_le_card ?_)
    (le_trans (Multiset.toFinset_card_le _) (Polynomial.card_nthRoots n 1))
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
  rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots hn]
  exact hx

/-- `permutation_product_last_eval` is read by halo2 for every non-last permutation set and is absent for
the last set. This checks the typed proof string follows that read schedule. -/
def permutationLastEvalsWellFormed {shape : Shape} {F G : Type*} (ps : ProofString shape F G) : Bool :=
  (List.ofFn (fun p : Fin shape.numProofs =>
    (List.ofFn (fun s : Fin shape.numPermutationSets =>
      if s.val + 1 = shape.numPermutationSets then
        match (ps.permutationSetEvals p s).lastEval with
        | none => true
        | some _ => false
      else
        match (ps.permutationSetEvals p s).lastEval with
        | some _ => true
        | none => false)).all id)).all id

/-- Typed proof-string well-formedness that affects deployed verifier control flow. Byte-level
decoding is outside this layer; `ProofString` starts after it. -/
def proofStringWellFormed {shape : Shape} {F G : Type*} (ps : ProofString shape F G) : Bool :=
  permutationLastEvalsWellFormed ps

/-- The deployed verifier MSM assembly with the rejection paths modeled:
`construct_intermediate_sets` can fail on duplicate commitment/point queries, the number of prover
`u` evaluations must equal the derived number of point sets, inverse denominators must be nonzero, and
typed proof fields must follow Halo2's read schedule.

Two of these rejections abstract deployed *panics*, not error returns: at `xⁿ = 1` halo2 crashes on
`(xn - 1).invert().unwrap()` (`vanishing/verifier.rs`), and at `x₃` hitting an opened point on
`(x₃ - point).invert().unwrap()` (`multiopen/verifier.rs`). Both strike a negligible proportion of
challenges (`card_vanishingPanic_le`, `card_multiopenPanic_le`) and are non-accepting either way, which is
the property the soundness layer consumes; the model just renders "crash" as `none`. -/
def assemble? {shape : Shape} {F G : Type*} [Field F] [DecidableEq F] [DecidableEq G] [Inhabited G]
    (vk : VerifyingKey shape F G) (ps : ProofString shape F G) (ch : Challenges shape.k F) :
    Option (Msm shape.k F G) :=
  if proofStringWellFormed ps then
    if ch.x ^ vk.n = (1 : F) then
      none
    else
      match constructIntermediateSets? (assembleQueries vk ps ch) with
      | some grouped =>
          if multiopenPointsAvoidX3 ch.x3 grouped then
            assembleFinalMsm? ps ch grouped
          else
            none
      | none => none
  else
    none

/-- The full verifier MSM, total form: build the opening queries, derive the multiopen grouping
(`constructIntermediateSets`), then assemble (`assembleFinalMsm`) — the deployed fingerprint as a
pure function of `(vk, ps, ch)`. Wraps `assemble?`, returning the zero MSM on the proof data it
rejects; kept for the algebraic fingerprint lemmas.

**Warning:** the zero-MSM fallback *evaluates to `0`* — the accept value. Never define acceptance as
`(assemble …).eval urs = 0`: on every rejection path that predicate holds vacuously, i.e. the total
wrapper accepts malformed input. Acceptance must go through `assemble?` (as `DeployedAccepts` does),
where rejection is `none`. -/
def assemble {shape : Shape} {F G : Type*} [Field F] [DecidableEq F] [DecidableEq G] [Inhabited G]
    (vk : VerifyingKey shape F G) (ps : ProofString shape F G) (ch : Challenges shape.k F) :
    Msm shape.k F G :=
  (assemble? vk ps ch).getD (Msm.zero shape.k F G)

end Zcash.Snark
