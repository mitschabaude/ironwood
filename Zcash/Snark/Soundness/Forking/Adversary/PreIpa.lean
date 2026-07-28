import Zcash.Snark.Soundness.Forking.Adversary.Adaptive
import Zcash.Snark.Soundness.Forking.Ordering

/-!
# Pre-IPA squeeze points

`preIpaSqueezePoints` names the eleven deployed pre-IPA queries. They are shape-determined,
unchanged by IPA splicing, and read exactly by the deployed challenge derivation. -/

namespace Zcash.Snark

variable {G : Type*}

/-! Each squeeze has a small definition so prefix and length proofs need not unfold the absorb
blocks in `deriveChallenges`. -/

private def sqPt0 {shape : Shape} (init : List (TranscriptElt Fp G))
    (ps : ProofString shape Fp G) : List (TranscriptElt Fp G) :=
  init ++ absorbPoints2 ps.adviceCommitments ++ [.challenge]

private def sqPt1 {shape : Shape} (init : List (TranscriptElt Fp G))
    (ps : ProofString shape Fp G) : List (TranscriptElt Fp G) :=
  sqPt0 init ps ++ absorbLookupPermuted ps.lookupPermutedInput ps.lookupPermutedTable
    ++ [.challenge]

private def sqPt2 {shape : Shape} (init : List (TranscriptElt Fp G))
    (ps : ProofString shape Fp G) : List (TranscriptElt Fp G) :=
  sqPt1 init ps ++ [.challenge]

private def sqPt3 {shape : Shape} (init : List (TranscriptElt Fp G))
    (ps : ProofString shape Fp G) : List (TranscriptElt Fp G) :=
  sqPt2 init ps ++ absorbPoints2 ps.permutationProduct ++ absorbPoints2 ps.lookupProduct
    ++ [TranscriptElt.point ps.vanishingRandom] ++ [.challenge]

private def sqPt4 {shape : Shape} (init : List (TranscriptElt Fp G))
    (ps : ProofString shape Fp G) : List (TranscriptElt Fp G) :=
  sqPt3 init ps ++ absorbPoints ps.hPieces ++ [.challenge]

private def sqEvalElts {shape : Shape} (ps : ProofString shape Fp G) :
    List (TranscriptElt Fp G) :=
  absorbScalars2 ps.instanceEvals ++ absorbScalars2 ps.adviceEvals
    ++ absorbScalars ps.fixedEvals ++ [TranscriptElt.scalar ps.vanishingRandomEval]
    ++ absorbScalars ps.permutationCommonEvals
    ++ (List.ofFn (fun p =>
        (List.ofFn (fun s => absorbPermSet (ps.permutationSetEvals p s))).flatten)).flatten
    ++ (List.ofFn (fun p =>
        (List.ofFn (fun l => absorbLookup (ps.lookupEvals p l))).flatten)).flatten

private def sqPt5 {shape : Shape} (init : List (TranscriptElt Fp G))
    (ps : ProofString shape Fp G) : List (TranscriptElt Fp G) :=
  sqPt4 init ps ++ sqEvalElts ps ++ [.challenge]

private def sqPt6 {shape : Shape} (init : List (TranscriptElt Fp G))
    (ps : ProofString shape Fp G) : List (TranscriptElt Fp G) :=
  sqPt5 init ps ++ [.challenge]

private def sqPt7 {shape : Shape} (init : List (TranscriptElt Fp G))
    (ps : ProofString shape Fp G) : List (TranscriptElt Fp G) :=
  sqPt6 init ps ++ [TranscriptElt.point ps.multiopenQPrime] ++ [.challenge]

private def sqPt8 {shape : Shape} (init : List (TranscriptElt Fp G))
    (ps : ProofString shape Fp G) : List (TranscriptElt Fp G) :=
  sqPt7 init ps ++ absorbScalars ps.multiopenU ++ [.challenge]

private def sqPt9 {shape : Shape} (init : List (TranscriptElt Fp G))
    (ps : ProofString shape Fp G) : List (TranscriptElt Fp G) :=
  sqPt8 init ps ++ [TranscriptElt.point ps.ipaS] ++ [.challenge]

private def sqPt10 {shape : Shape} (init : List (TranscriptElt Fp G))
    (ps : ProofString shape Fp G) : List (TranscriptElt Fp G) :=
  sqPt9 init ps ++ [.challenge]

/-- The eleven deployed pre-IPA squeeze prefixes, in order
`θ β γ y x x₁ x₂ x₃ x₄ ξ z`. Index 10 is `preIpaTranscript`. -/
def preIpaSqueezePoints {shape : Shape} (init : List (TranscriptElt Fp G))
    (ps : ProofString shape Fp G) : Fin 11 → List (TranscriptElt Fp G) :=
  ![sqPt0 init ps, sqPt1 init ps, sqPt2 init ps, sqPt3 init ps, sqPt4 init ps, sqPt5 init ps,
    sqPt6 init ps, sqPt7 init ps, sqPt8 init ps, sqPt9 init ps, sqPt10 init ps]

/-- The last squeeze point (`z`) is the whole pre-IPA transcript. -/
theorem preIpaSqueezePoints_last {shape : Shape} (init : List (TranscriptElt Fp G))
    (ps : ProofString shape Fp G) :
    preIpaSqueezePoints init ps 10 = preIpaTranscript init ps := rfl

/-- The challenge record assembled from a pre-IPA answer vector and a round vector, in squeeze
order. -/
def chRecord {k : ℕ} (ν : Fin 11 → Fp) (χ : Fin k → Fp) : Challenges k Fp :=
  { theta := ν 0, beta := ν 1, gamma := ν 2, y := ν 3, x := ν 4, x1 := ν 5, x2 := ν 6,
    x3 := ν 7, x4 := ν 8, xi := ν 9, z := ν 10, ipaRound := χ }

private theorem chExt {k : ℕ} {F : Type*} {c₁ c₂ : Challenges k F}
    (h1 : c₁.theta = c₂.theta) (h2 : c₁.beta = c₂.beta) (h3 : c₁.gamma = c₂.gamma)
    (h4 : c₁.y = c₂.y) (h5 : c₁.x = c₂.x) (h6 : c₁.x1 = c₂.x1) (h7 : c₁.x2 = c₂.x2)
    (h8 : c₁.x3 = c₂.x3) (h9 : c₁.x4 = c₂.x4) (h10 : c₁.xi = c₂.xi) (h11 : c₁.z = c₂.z)
    (h12 : c₁.ipaRound = c₂.ipaRound) : c₁ = c₂ := by
  cases c₁; cases c₂; simp_all

/-- Replacing the round slot of the zero-round record recovers the full challenge record. -/
theorem chRecord_update {k : ℕ} (ν : Fin 11 → Fp) (χ : Fin k → Fp) :
    ({chRecord (k := k) ν (fun _ => (0 : Fp)) with ipaRound := χ} : Challenges k Fp)
      = chRecord ν χ :=
  chExt rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-- `roChallenges` reads the table at the eleven pre-IPA points and the IPA-round transcripts. -/
theorem roChallenges_eq_chRecord {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) :
    roChallenges O init ps
      = chRecord (fun i => O (preIpaSqueezePoints init ps i))
          (fun j => O (roundTranscriptFin (preIpaTranscript init ps) ps.ipaRounds j)) := by
  refine chExt ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · funext j
    exact deriveChallenges_ipaRound_eq (ofOracle O) init ps j

/-- IPA splicing preserves all eleven pre-IPA squeeze points. -/
theorem preIpaSqueezePoints_spliceIpa {shape : Shape} (init : List (TranscriptElt Fp G))
    (ps : ProofString shape Fp G) (R : Fin shape.k → G × G) (c f : Fp) :
    preIpaSqueezePoints init (spliceIpa ps R c f) = preIpaSqueezePoints init ps := rfl

/-- Splicing leaves the pre-IPA transcript unchanged. -/
theorem preIpaTranscript_spliceIpa {shape : Shape} (init : List (TranscriptElt Fp G))
    (ps : ProofString shape Fp G) (R : Fin shape.k → G × G) (c f : Fp) :
    preIpaTranscript init (spliceIpa ps R c f) = preIpaTranscript init ps := rfl

private theorem sqPt_step01 {shape : Shape} (init : List (TranscriptElt Fp G))
    (ps : ProofString shape Fp G) : sqPt0 init ps <+: sqPt1 init ps :=
  (List.prefix_append _ _).trans (List.prefix_append _ _)

private theorem sqPt_step12 {shape : Shape} (init : List (TranscriptElt Fp G))
    (ps : ProofString shape Fp G) : sqPt1 init ps <+: sqPt2 init ps :=
  List.prefix_append _ _

private theorem sqPt_step23 {shape : Shape} (init : List (TranscriptElt Fp G))
    (ps : ProofString shape Fp G) : sqPt2 init ps <+: sqPt3 init ps :=
  ((List.prefix_append _ _).trans (List.prefix_append _ _)).trans
    ((List.prefix_append _ _).trans (List.prefix_append _ _))

private theorem sqPt_step34 {shape : Shape} (init : List (TranscriptElt Fp G))
    (ps : ProofString shape Fp G) : sqPt3 init ps <+: sqPt4 init ps :=
  (List.prefix_append _ _).trans (List.prefix_append _ _)

private theorem sqPt_step45 {shape : Shape} (init : List (TranscriptElt Fp G))
    (ps : ProofString shape Fp G) : sqPt4 init ps <+: sqPt5 init ps :=
  (List.prefix_append _ _).trans (List.prefix_append _ _)

private theorem sqPt_step56 {shape : Shape} (init : List (TranscriptElt Fp G))
    (ps : ProofString shape Fp G) : sqPt5 init ps <+: sqPt6 init ps :=
  List.prefix_append _ _

private theorem sqPt_step67 {shape : Shape} (init : List (TranscriptElt Fp G))
    (ps : ProofString shape Fp G) : sqPt6 init ps <+: sqPt7 init ps :=
  (List.prefix_append _ _).trans (List.prefix_append _ _)

private theorem sqPt_step78 {shape : Shape} (init : List (TranscriptElt Fp G))
    (ps : ProofString shape Fp G) : sqPt7 init ps <+: sqPt8 init ps :=
  (List.prefix_append _ _).trans (List.prefix_append _ _)

private theorem sqPt_step89 {shape : Shape} (init : List (TranscriptElt Fp G))
    (ps : ProofString shape Fp G) : sqPt8 init ps <+: sqPt9 init ps :=
  (List.prefix_append _ _).trans (List.prefix_append _ _)

private theorem sqPt_step910 {shape : Shape} (init : List (TranscriptElt Fp G))
    (ps : ProofString shape Fp G) : sqPt9 init ps <+: sqPt10 init ps :=
  List.prefix_append _ _

/-- Each pre-IPA squeeze point is a prefix of the pre-IPA transcript (the `z` point is the whole
of it): the eleven points are nested truncations of the same absorb chain. -/
theorem preIpaSqueezePoints_prefix {shape : Shape} (init : List (TranscriptElt Fp G))
    (ps : ProofString shape Fp G) (i : Fin 11) :
    preIpaSqueezePoints init ps i <+: preIpaTranscript init ps := by
  rw [← preIpaSqueezePoints_last init ps]
  have h9 : sqPt9 init ps <+: sqPt10 init ps := sqPt_step910 init ps
  have h8 : sqPt8 init ps <+: sqPt10 init ps := (sqPt_step89 init ps).trans h9
  have h7 : sqPt7 init ps <+: sqPt10 init ps := (sqPt_step78 init ps).trans h8
  have h6 : sqPt6 init ps <+: sqPt10 init ps := (sqPt_step67 init ps).trans h7
  have h5 : sqPt5 init ps <+: sqPt10 init ps := (sqPt_step56 init ps).trans h6
  have h4 : sqPt4 init ps <+: sqPt10 init ps := (sqPt_step45 init ps).trans h5
  have h3 : sqPt3 init ps <+: sqPt10 init ps := (sqPt_step34 init ps).trans h4
  have h2 : sqPt2 init ps <+: sqPt10 init ps := (sqPt_step23 init ps).trans h3
  have h1 : sqPt1 init ps <+: sqPt10 init ps := (sqPt_step12 init ps).trans h2
  have h0 : sqPt0 init ps <+: sqPt10 init ps := (sqPt_step01 init ps).trans h1
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9
  · exact List.prefix_rfl

/-- Each pre-IPA squeeze point is no longer than the pre-IPA transcript — the length half of the
disjointness from the (strictly longer) IPA round transcripts. -/
theorem preIpaSqueezePoints_length_le {shape : Shape} (init : List (TranscriptElt Fp G))
    (ps : ProofString shape Fp G) (i : Fin 11) :
    (preIpaSqueezePoints init ps i).length ≤ (preIpaTranscript init ps).length :=
  (preIpaSqueezePoints_prefix init ps i).length_le

/-! ## Shape-determined squeeze lengths

`PsWellFormed` makes all eleven pre-IPA squeeze lengths depend only on `Shape`. -/

/-- Reader shape: `lastEval` is present for every nonfinal permutation set. -/
def PsWellFormed {shape : Shape} (ps : ProofString shape Fp G) : Prop :=
  ∀ (p : Fin shape.numProofs) (s : Fin shape.numPermutationSets),
    (ps.permutationSetEvals p s).lastEval.isSome = ((s : ℕ) + 1 < shape.numPermutationSets)

private theorem length_absorbPoints {a : ℕ} (f : Fin a → G) :
    (absorbPoints (F := Fp) f).length = a := by
  simp [absorbPoints]

private theorem length_absorbScalars {a : ℕ} (f : Fin a → Fp) :
    (absorbScalars (G := G) f).length = a := by
  simp [absorbScalars]

private theorem length_flatten_ofFn_const {β : Type*} {a c : ℕ} (g : Fin a → List β)
    (hg : ∀ i, (g i).length = c) : ((List.ofFn g).flatten).length = a * c := by
  rw [List.length_flatten, List.map_ofFn]
  rw [show (List.ofFn (List.length ∘ g)) = List.ofFn (fun _ => c) from by
    congr 1
    funext i
    exact hg i]
  rw [List.sum_ofFn]
  simp

private theorem length_absorbPoints2 {a b : ℕ} (f : Fin a → Fin b → G) :
    (absorbPoints2 (F := Fp) f).length = a * b := by
  rw [absorbPoints2]
  exact length_flatten_ofFn_const _ fun i => by simp [absorbPoints]

private theorem length_absorbScalars2 {a b : ℕ} (f : Fin a → Fin b → Fp) :
    (absorbScalars2 (G := G) f).length = a * b := by
  rw [absorbScalars2]
  exact length_flatten_ofFn_const _ fun i => by simp [absorbScalars]

private theorem length_absorbLookupPermuted {a b : ℕ} (input table : Fin a → Fin b → G) :
    (absorbLookupPermuted (F := Fp) input table).length = a * (2 * b) := by
  rw [absorbLookupPermuted]
  refine length_flatten_ofFn_const (c := 2 * b) _ fun p => ?_
  exact (length_flatten_ofFn_const (c := 2) _ fun l => rfl).trans (Nat.mul_comm b 2)

private theorem length_absorbPermSet (e : PermSetEval Fp) :
    (absorbPermSet (G := G) e).length = 2 + (if e.lastEval.isSome then 1 else 0) := by
  rcases he : e.lastEval with _ | v <;> simp [absorbPermSet, he]

/-- The per-set permutation block, under well-formedness: `2` scalars per set plus one `lastEval`
for all but the last set. -/
private theorem length_permSetBlock {n : ℕ} (g : Fin n → PermSetEval Fp)
    (hg : ∀ s : Fin n, (g s).lastEval.isSome = ((s : ℕ) + 1 < n)) :
    ((List.ofFn (fun s => absorbPermSet (G := G) (g s))).flatten).length
      = 2 * n + (n - 1) := by
  have hterm : ∀ s : Fin n, ((List.length ∘ fun s => absorbPermSet (G := G) (g s)) s)
      = 2 + (if (s : ℕ) + 1 < n then 1 else 0) := by
    intro s
    show (absorbPermSet (g s)).length = _
    simp only [length_absorbPermSet, hg s]
  have hcount : (Finset.univ.filter (fun s : Fin n => (s : ℕ) + 1 < n)).card = n - 1 := by
    rcases n with _ | m
    · simp
    · rw [show (Finset.univ.filter (fun s : Fin (m + 1) => (s : ℕ) + 1 < m + 1))
          = Finset.univ.filter (fun s : Fin (m + 1) => s ≠ Fin.last m) from
        Finset.filter_congr fun s _ => by
          simp only [Ne, Fin.ext_iff, Fin.val_last]
          omega]
      rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        Fintype.card_fin]
  calc ((List.ofFn (fun s => absorbPermSet (G := G) (g s))).flatten).length
      = ∑ s : Fin n, (2 + if (s : ℕ) + 1 < n then 1 else 0) := by
        rw [List.length_flatten, List.map_ofFn, List.sum_ofFn]
        exact Finset.sum_congr rfl fun s _ => hterm s
    _ = (∑ _s : Fin n, 2) + ∑ s : Fin n, (if (s : ℕ) + 1 < n then 1 else 0) :=
        Finset.sum_add_distrib
    _ = 2 * n + (n - 1) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
          ← Finset.card_filter, hcount, mul_comm]

private theorem length_lookupEvalBlock {a b : ℕ} (g : Fin a → Fin b → LookupEval Fp) :
    ((List.ofFn (fun p => (List.ofFn (fun l => absorbLookup (G := G) (g p l))).flatten)).flatten
      ).length = a * (5 * b) := by
  refine length_flatten_ofFn_const (c := 5 * b) _ fun p => ?_
  exact (length_flatten_ofFn_const (c := 5) _ fun l => rfl).trans (Nat.mul_comm b 5)

/-- The eleven squeeze positions, as explicit functions of the shape and base length: the deployed
pre-IPA lengths under the reader's parse shape. -/
def preIpaLen (shape : Shape) (n₀ : ℕ) : Fin 11 → ℕ :=
  let l0 := n₀ + shape.numProofs * shape.numAdviceColumns + 1
  let l1 := l0 + shape.numProofs * (2 * shape.numLookups) + 1
  let l2 := l1 + 1
  let l3 := l2 + shape.numProofs * shape.numPermutationSets
    + shape.numProofs * shape.numLookups + 1 + 1
  let l4 := l3 + shape.numQuotientPieces + 1
  let l5 := l4 + (shape.numProofs * shape.numInstanceQueries
    + shape.numProofs * shape.numAdviceQueries + shape.numFixedQueries + 1
    + shape.numPermutationColumns
    + shape.numProofs * (2 * shape.numPermutationSets + (shape.numPermutationSets - 1))
    + shape.numProofs * (5 * shape.numLookups)) + 1
  let l6 := l5 + 1
  let l7 := l6 + 1 + 1
  let l8 := l7 + shape.numPointSets + 1
  let l9 := l8 + 1 + 1
  let l10 := l9 + 1
  ![l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10]

private theorem len_sqPt0 {shape : Shape} (init : List (TranscriptElt Fp G))
    (ps : ProofString shape Fp G) :
    (sqPt0 init ps).length
      = init.length + shape.numProofs * shape.numAdviceColumns + 1 := by
  simp [sqPt0, List.length_append, length_absorbPoints2] ; omega

private theorem len_sqPt1 {shape : Shape} (init : List (TranscriptElt Fp G))
    (ps : ProofString shape Fp G) :
    (sqPt1 init ps).length
      = (sqPt0 init ps).length + shape.numProofs * (2 * shape.numLookups) + 1 := by
  simp [sqPt1, List.length_append, length_absorbLookupPermuted] ; omega

private theorem len_sqPt2 {shape : Shape} (init : List (TranscriptElt Fp G))
    (ps : ProofString shape Fp G) :
    (sqPt2 init ps).length = (sqPt1 init ps).length + 1 := by
  simp [sqPt2]

private theorem len_sqPt3 {shape : Shape} (init : List (TranscriptElt Fp G))
    (ps : ProofString shape Fp G) :
    (sqPt3 init ps).length
      = (sqPt2 init ps).length + shape.numProofs * shape.numPermutationSets
        + shape.numProofs * shape.numLookups + 1 + 1 := by
  simp [sqPt3, List.length_append, length_absorbPoints2] ; omega

private theorem len_sqPt4 {shape : Shape} (init : List (TranscriptElt Fp G))
    (ps : ProofString shape Fp G) :
    (sqPt4 init ps).length = (sqPt3 init ps).length + shape.numQuotientPieces + 1 := by
  simp [sqPt4, List.length_append, length_absorbPoints] ; omega

private theorem len_sqEvalElts {shape : Shape} (ps : ProofString shape Fp G)
    (hwf : PsWellFormed ps) :
    (sqEvalElts ps).length
      = shape.numProofs * shape.numInstanceQueries + shape.numProofs * shape.numAdviceQueries
        + shape.numFixedQueries + 1 + shape.numPermutationColumns
        + shape.numProofs * (2 * shape.numPermutationSets + (shape.numPermutationSets - 1))
        + shape.numProofs * (5 * shape.numLookups) := by
  have hperm : ((List.ofFn (fun p =>
      (List.ofFn (fun s => absorbPermSet (G := G) (ps.permutationSetEvals p s))).flatten)
      ).flatten).length
      = shape.numProofs
        * (2 * shape.numPermutationSets + (shape.numPermutationSets - 1)) :=
    length_flatten_ofFn_const _ fun p => length_permSetBlock _ (hwf p)
  have hlook : ((List.ofFn (fun p =>
      (List.ofFn (fun l => absorbLookup (G := G) (ps.lookupEvals p l))).flatten)
      ).flatten).length
      = shape.numProofs * (5 * shape.numLookups) := length_lookupEvalBlock _
  simp only [sqEvalElts, List.length_append, length_absorbScalars, length_absorbScalars2,
    hperm, hlook, List.length_cons, List.length_nil]

private theorem len_sqPt5 {shape : Shape} (init : List (TranscriptElt Fp G))
    (ps : ProofString shape Fp G) (hwf : PsWellFormed ps) :
    (sqPt5 init ps).length
      = (sqPt4 init ps).length
        + (shape.numProofs * shape.numInstanceQueries
          + shape.numProofs * shape.numAdviceQueries + shape.numFixedQueries + 1
          + shape.numPermutationColumns
          + shape.numProofs * (2 * shape.numPermutationSets + (shape.numPermutationSets - 1))
          + shape.numProofs * (5 * shape.numLookups)) + 1 := by
  simp [sqPt5, List.length_append, len_sqEvalElts ps hwf, Nat.add_assoc]

private theorem len_sqPt6 {shape : Shape} (init : List (TranscriptElt Fp G))
    (ps : ProofString shape Fp G) :
    (sqPt6 init ps).length = (sqPt5 init ps).length + 1 := by
  simp [sqPt6]

private theorem len_sqPt7 {shape : Shape} (init : List (TranscriptElt Fp G))
    (ps : ProofString shape Fp G) :
    (sqPt7 init ps).length = (sqPt6 init ps).length + 1 + 1 := by
  simp [sqPt7, List.length_append]

private theorem len_sqPt8 {shape : Shape} (init : List (TranscriptElt Fp G))
    (ps : ProofString shape Fp G) :
    (sqPt8 init ps).length = (sqPt7 init ps).length + shape.numPointSets + 1 := by
  simp [sqPt8, List.length_append, length_absorbScalars] ; omega

private theorem len_sqPt9 {shape : Shape} (init : List (TranscriptElt Fp G))
    (ps : ProofString shape Fp G) :
    (sqPt9 init ps).length = (sqPt8 init ps).length + 1 + 1 := by
  simp [sqPt9, List.length_append]

private theorem len_sqPt10 {shape : Shape} (init : List (TranscriptElt Fp G))
    (ps : ProofString shape Fp G) :
    (sqPt10 init ps).length = (sqPt9 init ps).length + 1 := by
  simp [sqPt10]

/-- Each well-formed pre-IPA squeeze prefix has its shape-determined length. -/
theorem preIpaSqueezePoints_length_eq {shape : Shape} (init : List (TranscriptElt Fp G))
    (ps : ProofString shape Fp G) (hwf : PsWellFormed ps) (i : Fin 11) :
    (preIpaSqueezePoints init ps i).length = preIpaLen shape init.length i := by
  have h0 := len_sqPt0 (shape := shape) init ps
  have h1 := (len_sqPt1 (shape := shape) init ps).trans (by rw [h0])
  have h2 := (len_sqPt2 (shape := shape) init ps).trans (by rw [h1])
  have h3 := (len_sqPt3 (shape := shape) init ps).trans (by rw [h2])
  have h4 := (len_sqPt4 (shape := shape) init ps).trans (by rw [h3])
  have h5 := (len_sqPt5 (shape := shape) init ps hwf).trans (by rw [h4])
  have h6 := (len_sqPt6 (shape := shape) init ps).trans (by rw [h5])
  have h7 := (len_sqPt7 (shape := shape) init ps).trans (by rw [h6])
  have h8 := (len_sqPt8 (shape := shape) init ps).trans (by rw [h7])
  have h9 := (len_sqPt9 (shape := shape) init ps).trans (by rw [h8])
  have h10 := (len_sqPt10 (shape := shape) init ps).trans (by rw [h9])
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9
  · exact h10

/-- The pre-IPA transcript's length is shape-determined (the `z`-point position). -/
theorem preIpaTranscript_length_eq {shape : Shape} (init : List (TranscriptElt Fp G))
    (ps : ProofString shape Fp G) (hwf : PsWellFormed ps) :
    (preIpaTranscript init ps).length = preIpaLen shape init.length 10 := by
  rw [← preIpaSqueezePoints_last init ps]
  exact preIpaSqueezePoints_length_eq init ps hwf 10

/-! ## Injective absorb encoding

Equal pre-IPA transcripts of well-formed proofs have equal pre-IPA fields. -/

private theorem flatten_ofFn_inj {β : Type*} : ∀ {a : ℕ} (g h : Fin a → List β),
    (List.ofFn g).flatten = (List.ofFn h).flatten →
    (∀ i, (g i).length = (h i).length) → ∀ i, g i = h i
  | 0, _, _, _, _ => fun i => i.elim0
  | a + 1, g, h, heq, hlen => by
      rw [List.ofFn_succ, List.ofFn_succ, List.flatten_cons, List.flatten_cons] at heq
      obtain ⟨h0, htail⟩ := List.append_inj heq (hlen 0)
      intro i
      refine Fin.cases ?_ ?_ i
      · exact h0
      · exact flatten_ofFn_inj (fun j => g j.succ) (fun j => h j.succ)
          htail (fun j => hlen j.succ)

private theorem absorbPoints_inj {a : ℕ} {f g : Fin a → G}
    (h : absorbPoints (F := Fp) f = absorbPoints g) : f = g := by
  funext i
  have h2 := congrFun (List.ofFn_inj.mp h) i
  simpa using h2

private theorem absorbScalars_inj {a : ℕ} {f g : Fin a → Fp}
    (h : absorbScalars (G := G) f = absorbScalars g) : f = g := by
  funext i
  have h2 := congrFun (List.ofFn_inj.mp h) i
  simpa using h2

private theorem absorbPoints2_inj {a b : ℕ} {f g : Fin a → Fin b → G}
    (h : absorbPoints2 (F := Fp) f = absorbPoints2 g) : f = g := by
  funext p
  refine absorbPoints_inj (flatten_ofFn_inj _ _ h (fun i => ?_) p)
  simp [absorbPoints]

private theorem absorbScalars2_inj {a b : ℕ} {f g : Fin a → Fin b → Fp}
    (h : absorbScalars2 (G := G) f = absorbScalars2 g) : f = g := by
  funext p
  refine absorbScalars_inj (flatten_ofFn_inj _ _ h (fun i => ?_) p)
  simp [absorbScalars]

private theorem absorbLookupPermuted_inj {a b : ℕ}
    {i₁ t₁ i₂ t₂ : Fin a → Fin b → G}
    (h : absorbLookupPermuted (F := Fp) i₁ t₁ = absorbLookupPermuted i₂ t₂) :
    i₁ = i₂ ∧ t₁ = t₂ := by
  have hrows := flatten_ofFn_inj _ _ h
    (fun p => by
      rw [length_flatten_ofFn_const (c := 2) _ fun l => rfl,
        length_flatten_ofFn_const (c := 2) _ fun l => rfl])
  have hcell : ∀ (p : Fin a) (l : Fin b), i₁ p l = i₂ p l ∧ t₁ p l = t₂ p l := by
    intro p l
    have hin := flatten_ofFn_inj _ _ (hrows p) (fun l => rfl) l
    injection hin with hh htl
    injection htl with hh2 _
    injection hh with e1
    injection hh2 with e2
    exact ⟨e1, e2⟩
  exact ⟨funext fun p => funext fun l => (hcell p l).1,
    funext fun p => funext fun l => (hcell p l).2⟩

private theorem absorbPermSet_inj {e e' : PermSetEval Fp}
    (hs : e.lastEval.isSome = e'.lastEval.isSome)
    (h : absorbPermSet (G := G) e = absorbPermSet e') : e = e' := by
  rw [absorbPermSet, absorbPermSet] at h
  rcases he : e.lastEval with _ | v <;> rcases he' : e'.lastEval with _ | v' <;>
    rw [he, he'] at h hs <;> simp only [Option.map_none, Option.map_some, Option.toList_none,
      Option.toList_some, Option.isSome_none, Option.isSome_some] at h hs
  · cases e; cases e'
    simp_all
  · simp at hs
  · simp at hs
  · cases e; cases e'
    simp_all

private theorem absorbLookup_inj {e e' : LookupEval Fp}
    (h : absorbLookup (G := G) e = absorbLookup e') : e = e' := by
  rw [absorbLookup, absorbLookup] at h
  cases e; cases e'
  simp_all

private theorem singleton_point_inj {v v' : G}
    (h : [TranscriptElt.point (F := Fp) v] = [TranscriptElt.point v']) : v = v' := by
  simpa using h

private theorem psExt {shape : Shape} {p q : ProofString shape Fp G}
    (h1 : p.adviceCommitments = q.adviceCommitments)
    (h2 : p.lookupPermutedInput = q.lookupPermutedInput)
    (h3 : p.lookupPermutedTable = q.lookupPermutedTable)
    (h4 : p.permutationProduct = q.permutationProduct)
    (h5 : p.lookupProduct = q.lookupProduct)
    (h6 : p.vanishingRandom = q.vanishingRandom)
    (h7 : p.hPieces = q.hPieces)
    (h8 : p.instanceEvals = q.instanceEvals)
    (h9 : p.adviceEvals = q.adviceEvals)
    (h10 : p.fixedEvals = q.fixedEvals)
    (h11 : p.vanishingRandomEval = q.vanishingRandomEval)
    (h12 : p.permutationCommonEvals = q.permutationCommonEvals)
    (h13 : p.permutationSetEvals = q.permutationSetEvals)
    (h14 : p.lookupEvals = q.lookupEvals)
    (h15 : p.multiopenQPrime = q.multiopenQPrime)
    (h16 : p.multiopenU = q.multiopenU)
    (h17 : p.ipaS = q.ipaS)
    (h18 : p.ipaRounds = q.ipaRounds)
    (h19 : p.ipaC = q.ipaC)
    (h20 : p.ipaF = q.ipaF) : p = q := by
  cases p; cases q; simp_all

/-- Two well-formed proofs with the same pre-IPA transcript differ only in their IPA fields. -/
theorem preIpaTranscript_inj {shape : Shape} (init : List (TranscriptElt Fp G))
    {ps ps' : ProofString shape Fp G} (hwf : PsWellFormed ps) (hwf' : PsWellFormed ps')
    (h : preIpaTranscript init ps = preIpaTranscript init ps') :
    ps = spliceIpa ps' ps.ipaRounds ps.ipaC ps.ipaF := by
  have h10 : sqPt10 init ps = sqPt10 init ps' := h
  have h9 : sqPt9 init ps = sqPt9 init ps' := (List.append_inj' h10 rfl).1
  have h9' := List.append_inj' h9 rfl
  have h8pt := List.append_inj' h9'.1 rfl
  have h8 : sqPt8 init ps = sqPt8 init ps' := h8pt.1
  have hIpaS : ps.ipaS = ps'.ipaS := singleton_point_inj h8pt.2
  have h8' := List.append_inj' h8 rfl
  have h7u := List.append_inj' h8'.1
    (by rw [length_absorbScalars, length_absorbScalars])
  have h7 : sqPt7 init ps = sqPt7 init ps' := h7u.1
  have hMU : ps.multiopenU = ps'.multiopenU := absorbScalars_inj h7u.2
  have h7' := List.append_inj' h7 rfl
  have h6q := List.append_inj' h7'.1 rfl
  have h6 : sqPt6 init ps = sqPt6 init ps' := h6q.1
  have hQP : ps.multiopenQPrime = ps'.multiopenQPrime := singleton_point_inj h6q.2
  have h5 : sqPt5 init ps = sqPt5 init ps' := (List.append_inj' h6 rfl).1
  have h5' := List.append_inj' h5 rfl
  have h4e := List.append_inj' h5'.1
    (by rw [len_sqEvalElts ps hwf, len_sqEvalElts ps' hwf'])
  have h4 : sqPt4 init ps = sqPt4 init ps' := h4e.1
  have hEval : sqEvalElts ps = sqEvalElts ps' := h4e.2
  have h4' := List.append_inj' h4 rfl
  have h3h := List.append_inj' h4'.1
    (by rw [length_absorbPoints, length_absorbPoints])
  have h3 : sqPt3 init ps = sqPt3 init ps' := h3h.1
  have hHP : ps.hPieces = ps'.hPieces := absorbPoints_inj h3h.2
  have h3' := List.append_inj' h3 rfl
  have h2v := List.append_inj' h3'.1 rfl
  have hVR : ps.vanishingRandom = ps'.vanishingRandom := singleton_point_inj h2v.2
  have h2l := List.append_inj' h2v.1
    (by rw [length_absorbPoints2, length_absorbPoints2])
  have hLP : ps.lookupProduct = ps'.lookupProduct := absorbPoints2_inj h2l.2
  have h2p := List.append_inj' h2l.1
    (by rw [length_absorbPoints2, length_absorbPoints2])
  have h2 : sqPt2 init ps = sqPt2 init ps' := h2p.1
  have hPP : ps.permutationProduct = ps'.permutationProduct := absorbPoints2_inj h2p.2
  have h1 : sqPt1 init ps = sqPt1 init ps' := (List.append_inj' h2 rfl).1
  have h1' := List.append_inj' h1 rfl
  have h0l := List.append_inj' h1'.1
    (by rw [length_absorbLookupPermuted, length_absorbLookupPermuted])
  have h0 : sqPt0 init ps = sqPt0 init ps' := h0l.1
  obtain ⟨hLPI, hLPT⟩ := absorbLookupPermuted_inj h0l.2
  have h0' := List.append_inj' h0 rfl
  have hAdva := List.append_inj' h0'.1
    (by rw [length_absorbPoints2, length_absorbPoints2])
  have hAdv : ps.adviceCommitments = ps'.adviceCommitments := absorbPoints2_inj hAdva.2
  -- peel the evaluation block
  have he1 := List.append_inj' hEval
    (by rw [length_lookupEvalBlock, length_lookupEvalBlock])
  have hLE : ps.lookupEvals = ps'.lookupEvals := by
    have hrow : ∀ p, (List.ofFn (fun l =>
          absorbLookup (G := G) (ps.lookupEvals p l))).flatten
        = (List.ofFn (fun l => absorbLookup (G := G) (ps'.lookupEvals p l))).flatten :=
      flatten_ofFn_inj _ _ he1.2 (fun p => by
        rw [length_flatten_ofFn_const (c := 5) _ fun _ => rfl,
          length_flatten_ofFn_const (c := 5) _ fun _ => rfl])
    have hcell : ∀ p l, absorbLookup (G := G) (ps.lookupEvals p l)
        = absorbLookup (G := G) (ps'.lookupEvals p l) := fun p =>
      flatten_ofFn_inj _ _ (hrow p) (fun l => rfl)
    funext p l
    exact absorbLookup_inj (hcell p l)
  have he2 := List.append_inj' he1.1
    (by rw [length_flatten_ofFn_const _ fun p => length_permSetBlock _ (hwf p),
      length_flatten_ofFn_const _ fun p => length_permSetBlock _ (hwf' p)])
  have hPSE : ps.permutationSetEvals = ps'.permutationSetEvals := by
    have hrow : ∀ p, (List.ofFn (fun s =>
          absorbPermSet (G := G) (ps.permutationSetEvals p s))).flatten
        = (List.ofFn (fun s => absorbPermSet (G := G) (ps'.permutationSetEvals p s))).flatten :=
      flatten_ofFn_inj _ _ he2.2 (fun p => by
        rw [length_permSetBlock _ (hwf p), length_permSetBlock _ (hwf' p)])
    have hcell : ∀ p s, absorbPermSet (G := G) (ps.permutationSetEvals p s)
        = absorbPermSet (G := G) (ps'.permutationSetEvals p s) := fun p =>
      flatten_ofFn_inj _ _ (hrow p) (fun s => by
        rw [length_absorbPermSet, length_absorbPermSet,
          show (ps.permutationSetEvals p s).lastEval.isSome
              = (ps'.permutationSetEvals p s).lastEval.isSome from
            Bool.eq_iff_iff.mpr (by rw [hwf p s, hwf' p s])])
    funext p s
    exact absorbPermSet_inj (G := G)
      (Bool.eq_iff_iff.mpr (by rw [hwf p s, hwf' p s])) (hcell p s)
  have he3 := List.append_inj' he2.1
    (by rw [length_absorbScalars, length_absorbScalars])
  have hPCE : ps.permutationCommonEvals = ps'.permutationCommonEvals :=
    absorbScalars_inj he3.2
  have he4 := List.append_inj' he3.1 rfl
  have hVRE : ps.vanishingRandomEval = ps'.vanishingRandomEval := by
    have := he4.2
    simpa using this
  have he5 := List.append_inj' he4.1
    (by rw [length_absorbScalars, length_absorbScalars])
  have hFE : ps.fixedEvals = ps'.fixedEvals := absorbScalars_inj he5.2
  have he6 := List.append_inj' he5.1
    (by rw [length_absorbScalars2, length_absorbScalars2])
  have hAE : ps.adviceEvals = ps'.adviceEvals := absorbScalars2_inj he6.2
  have hIE : ps.instanceEvals = ps'.instanceEvals := absorbScalars2_inj he6.1
  -- assemble
  exact psExt hAdv hLPI hLPT hPP hLP hVR hHP hIE hAE hFE hVRE hPCE hPSE hLE hQP hMU hIpaS
    rfl rfl rfl

/-! ## Prefix injectivity at the multiopen squeeze points

Equal `x₁`/`x₂`/`x₃`/`x₄` squeeze points pin every field absorbed before them, leaving exactly
the fields a rewound run re-sends free — the invariance the resampled diagonal's transport
consumes. Same peeling as `preIpaTranscript_inj`, stopped at the earlier prefix. -/

private theorem preX1_fields_inj {shape : Shape} (init : List (TranscriptElt Fp G))
    {ps ps' : ProofString shape Fp G} (hwf : PsWellFormed ps) (hwf' : PsWellFormed ps')
    (h5 : sqPt5 init ps = sqPt5 init ps') :
    ps.adviceCommitments = ps'.adviceCommitments ∧
    ps.lookupPermutedInput = ps'.lookupPermutedInput ∧
    ps.lookupPermutedTable = ps'.lookupPermutedTable ∧
    ps.permutationProduct = ps'.permutationProduct ∧
    ps.lookupProduct = ps'.lookupProduct ∧
    ps.vanishingRandom = ps'.vanishingRandom ∧
    ps.hPieces = ps'.hPieces ∧
    ps.instanceEvals = ps'.instanceEvals ∧
    ps.adviceEvals = ps'.adviceEvals ∧
    ps.fixedEvals = ps'.fixedEvals ∧
    ps.vanishingRandomEval = ps'.vanishingRandomEval ∧
    ps.permutationCommonEvals = ps'.permutationCommonEvals ∧
    ps.permutationSetEvals = ps'.permutationSetEvals ∧
    ps.lookupEvals = ps'.lookupEvals := by
  have h5' := List.append_inj' h5 rfl
  have h4e := List.append_inj' h5'.1
    (by rw [len_sqEvalElts ps hwf, len_sqEvalElts ps' hwf'])
  have h4 : sqPt4 init ps = sqPt4 init ps' := h4e.1
  have hEval : sqEvalElts ps = sqEvalElts ps' := h4e.2
  have h4' := List.append_inj' h4 rfl
  have h3h := List.append_inj' h4'.1
    (by rw [length_absorbPoints, length_absorbPoints])
  have h3 : sqPt3 init ps = sqPt3 init ps' := h3h.1
  have hHP : ps.hPieces = ps'.hPieces := absorbPoints_inj h3h.2
  have h3' := List.append_inj' h3 rfl
  have h2v := List.append_inj' h3'.1 rfl
  have hVR : ps.vanishingRandom = ps'.vanishingRandom := singleton_point_inj h2v.2
  have h2l := List.append_inj' h2v.1
    (by rw [length_absorbPoints2, length_absorbPoints2])
  have hLP : ps.lookupProduct = ps'.lookupProduct := absorbPoints2_inj h2l.2
  have h2p := List.append_inj' h2l.1
    (by rw [length_absorbPoints2, length_absorbPoints2])
  have h2 : sqPt2 init ps = sqPt2 init ps' := h2p.1
  have hPP : ps.permutationProduct = ps'.permutationProduct := absorbPoints2_inj h2p.2
  have h1 : sqPt1 init ps = sqPt1 init ps' := (List.append_inj' h2 rfl).1
  have h1' := List.append_inj' h1 rfl
  have h0l := List.append_inj' h1'.1
    (by rw [length_absorbLookupPermuted, length_absorbLookupPermuted])
  have h0 : sqPt0 init ps = sqPt0 init ps' := h0l.1
  obtain ⟨hLPI, hLPT⟩ := absorbLookupPermuted_inj h0l.2
  have h0' := List.append_inj' h0 rfl
  have hAdva := List.append_inj' h0'.1
    (by rw [length_absorbPoints2, length_absorbPoints2])
  have hAdv : ps.adviceCommitments = ps'.adviceCommitments := absorbPoints2_inj hAdva.2
  have he1 := List.append_inj' hEval
    (by rw [length_lookupEvalBlock, length_lookupEvalBlock])
  have hLE : ps.lookupEvals = ps'.lookupEvals := by
    have hrow : ∀ p, (List.ofFn (fun l =>
          absorbLookup (G := G) (ps.lookupEvals p l))).flatten
        = (List.ofFn (fun l => absorbLookup (G := G) (ps'.lookupEvals p l))).flatten :=
      flatten_ofFn_inj _ _ he1.2 (fun p => by
        rw [length_flatten_ofFn_const (c := 5) _ fun _ => rfl,
          length_flatten_ofFn_const (c := 5) _ fun _ => rfl])
    have hcell : ∀ p l, absorbLookup (G := G) (ps.lookupEvals p l)
        = absorbLookup (G := G) (ps'.lookupEvals p l) := fun p =>
      flatten_ofFn_inj _ _ (hrow p) (fun l => rfl)
    funext p l
    exact absorbLookup_inj (hcell p l)
  have he2 := List.append_inj' he1.1
    (by rw [length_flatten_ofFn_const _ fun p => length_permSetBlock _ (hwf p),
      length_flatten_ofFn_const _ fun p => length_permSetBlock _ (hwf' p)])
  have hPSE : ps.permutationSetEvals = ps'.permutationSetEvals := by
    have hrow : ∀ p, (List.ofFn (fun s =>
          absorbPermSet (G := G) (ps.permutationSetEvals p s))).flatten
        = (List.ofFn (fun s => absorbPermSet (G := G) (ps'.permutationSetEvals p s))).flatten :=
      flatten_ofFn_inj _ _ he2.2 (fun p => by
        rw [length_permSetBlock _ (hwf p), length_permSetBlock _ (hwf' p)])
    have hcell : ∀ p s, absorbPermSet (G := G) (ps.permutationSetEvals p s)
        = absorbPermSet (G := G) (ps'.permutationSetEvals p s) := fun p =>
      flatten_ofFn_inj _ _ (hrow p) (fun s => by
        rw [length_absorbPermSet, length_absorbPermSet,
          show (ps.permutationSetEvals p s).lastEval.isSome
              = (ps'.permutationSetEvals p s).lastEval.isSome from
            Bool.eq_iff_iff.mpr (by rw [hwf p s, hwf' p s])])
    funext p s
    exact absorbPermSet_inj (G := G)
      (Bool.eq_iff_iff.mpr (by rw [hwf p s, hwf' p s])) (hcell p s)
  have he3 := List.append_inj' he2.1
    (by rw [length_absorbScalars, length_absorbScalars])
  have hPCE : ps.permutationCommonEvals = ps'.permutationCommonEvals :=
    absorbScalars_inj he3.2
  have he4 := List.append_inj' he3.1 rfl
  have hVRE : ps.vanishingRandomEval = ps'.vanishingRandomEval := by
    have := he4.2
    simpa using this
  have he5 := List.append_inj' he4.1
    (by rw [length_absorbScalars, length_absorbScalars])
  have hFE : ps.fixedEvals = ps'.fixedEvals := absorbScalars_inj he5.2
  have he6 := List.append_inj' he5.1
    (by rw [length_absorbScalars2, length_absorbScalars2])
  have hAE : ps.adviceEvals = ps'.adviceEvals := absorbScalars2_inj he6.2
  have hIE : ps.instanceEvals = ps'.instanceEvals := absorbScalars2_inj he6.1
  exact ⟨hAdv, hLPI, hLPT, hPP, hLP, hVR, hHP, hIE, hAE, hFE, hVRE, hPCE, hPSE, hLE⟩

/-- **`x`-prefix injectivity.** Two proofs with the same `x` squeeze point agree on every
commitment absorbed before `x` — the advice, lookup-permuted, permutation-product,
lookup-product, vanishing-random, and quotient-piece commitments. No well-formedness is needed:
the pre-`x` segments have count-determined lengths. -/
theorem preXSqueezePoint_inj {shape : Shape} (init : List (TranscriptElt Fp G))
    {ps ps' : ProofString shape Fp G}
    (h : preIpaSqueezePoints init ps 4 = preIpaSqueezePoints init ps' 4) :
    ps.adviceCommitments = ps'.adviceCommitments ∧
    ps.lookupPermutedInput = ps'.lookupPermutedInput ∧
    ps.lookupPermutedTable = ps'.lookupPermutedTable ∧
    ps.permutationProduct = ps'.permutationProduct ∧
    ps.lookupProduct = ps'.lookupProduct ∧
    ps.vanishingRandom = ps'.vanishingRandom ∧
    ps.hPieces = ps'.hPieces := by
  have h4 : sqPt4 init ps = sqPt4 init ps' := h
  have h4' := List.append_inj' h4 rfl
  have h3h := List.append_inj' h4'.1
    (by rw [length_absorbPoints, length_absorbPoints])
  have h3 : sqPt3 init ps = sqPt3 init ps' := h3h.1
  have hHP : ps.hPieces = ps'.hPieces := absorbPoints_inj h3h.2
  have h3' := List.append_inj' h3 rfl
  have h2v := List.append_inj' h3'.1 rfl
  have hVR : ps.vanishingRandom = ps'.vanishingRandom := singleton_point_inj h2v.2
  have h2l := List.append_inj' h2v.1
    (by rw [length_absorbPoints2, length_absorbPoints2])
  have hLP : ps.lookupProduct = ps'.lookupProduct := absorbPoints2_inj h2l.2
  have h2p := List.append_inj' h2l.1
    (by rw [length_absorbPoints2, length_absorbPoints2])
  have h2 : sqPt2 init ps = sqPt2 init ps' := h2p.1
  have hPP : ps.permutationProduct = ps'.permutationProduct := absorbPoints2_inj h2p.2
  have h1 : sqPt1 init ps = sqPt1 init ps' := (List.append_inj' h2 rfl).1
  have h1' := List.append_inj' h1 rfl
  have h0l := List.append_inj' h1'.1
    (by rw [length_absorbLookupPermuted, length_absorbLookupPermuted])
  have h0 : sqPt0 init ps = sqPt0 init ps' := h0l.1
  obtain ⟨hLPI, hLPT⟩ := absorbLookupPermuted_inj h0l.2
  have h0' := List.append_inj' h0 rfl
  have hAdva := List.append_inj' h0'.1
    (by rw [length_absorbPoints2, length_absorbPoints2])
  have hAdv : ps.adviceCommitments = ps'.adviceCommitments := absorbPoints2_inj hAdva.2
  exact ⟨hAdv, hLPI, hLPT, hPP, hLP, hVR, hHP⟩

/-- **`x₁`-prefix injectivity.** Two well-formed proofs with the same `x₁` squeeze point agree on
every field absorbed before `x₁` — only the multiopen and IPA fields are free. -/
theorem preX1SqueezePoint_inj {shape : Shape} (init : List (TranscriptElt Fp G))
    {ps ps' : ProofString shape Fp G} (hwf : PsWellFormed ps) (hwf' : PsWellFormed ps')
    (h : preIpaSqueezePoints init ps 5 = preIpaSqueezePoints init ps' 5) :
    ps = { ps' with
            multiopenQPrime := ps.multiopenQPrime, multiopenU := ps.multiopenU,
            ipaS := ps.ipaS, ipaRounds := ps.ipaRounds, ipaC := ps.ipaC,
            ipaF := ps.ipaF } := by
  obtain ⟨hAdv, hLPI, hLPT, hPP, hLP, hVR, hHP, hIE, hAE, hFE, hVRE, hPCE, hPSE, hLE⟩ :=
    preX1_fields_inj init hwf hwf' (show sqPt5 init ps = sqPt5 init ps' from h)
  exact psExt hAdv hLPI hLPT hPP hLP hVR hHP hIE hAE hFE hVRE hPCE hPSE hLE
    rfl rfl rfl rfl rfl rfl

/-- **`x₂`-prefix injectivity.** The `x₂` point pins the same fields as the `x₁` point (nothing
is absorbed between the two squeezes). -/
theorem preX2SqueezePoint_inj {shape : Shape} (init : List (TranscriptElt Fp G))
    {ps ps' : ProofString shape Fp G} (hwf : PsWellFormed ps) (hwf' : PsWellFormed ps')
    (h : preIpaSqueezePoints init ps 6 = preIpaSqueezePoints init ps' 6) :
    ps = { ps' with
            multiopenQPrime := ps.multiopenQPrime, multiopenU := ps.multiopenU,
            ipaS := ps.ipaS, ipaRounds := ps.ipaRounds, ipaC := ps.ipaC,
            ipaF := ps.ipaF } := by
  have h6 : sqPt6 init ps = sqPt6 init ps' := h
  obtain ⟨hAdv, hLPI, hLPT, hPP, hLP, hVR, hHP, hIE, hAE, hFE, hVRE, hPCE, hPSE, hLE⟩ :=
    preX1_fields_inj init hwf hwf' (List.append_inj' h6 rfl).1
  exact psExt hAdv hLPI hLPT hPP hLP hVR hHP hIE hAE hFE hVRE hPCE hPSE hLE
    rfl rfl rfl rfl rfl rfl

/-- **`x₃`-prefix injectivity.** The `x₃` point additionally pins the multiopen quotient
commitment `q′`. -/
theorem preX3SqueezePoint_inj {shape : Shape} (init : List (TranscriptElt Fp G))
    {ps ps' : ProofString shape Fp G} (hwf : PsWellFormed ps) (hwf' : PsWellFormed ps')
    (h : preIpaSqueezePoints init ps 7 = preIpaSqueezePoints init ps' 7) :
    ps = { ps' with
            multiopenU := ps.multiopenU, ipaS := ps.ipaS, ipaRounds := ps.ipaRounds,
            ipaC := ps.ipaC, ipaF := ps.ipaF } := by
  have h7 : sqPt7 init ps = sqPt7 init ps' := h
  have h7' := List.append_inj' h7 rfl
  have h6q := List.append_inj' h7'.1 rfl
  have h6 : sqPt6 init ps = sqPt6 init ps' := h6q.1
  have hQP : ps.multiopenQPrime = ps'.multiopenQPrime := singleton_point_inj h6q.2
  obtain ⟨hAdv, hLPI, hLPT, hPP, hLP, hVR, hHP, hIE, hAE, hFE, hVRE, hPCE, hPSE, hLE⟩ :=
    preX1_fields_inj init hwf hwf' (List.append_inj' h6 rfl).1
  exact psExt hAdv hLPI hLPT hPP hLP hVR hHP hIE hAE hFE hVRE hPCE hPSE hLE
    hQP rfl rfl rfl rfl rfl

/-- **`x₄`-prefix injectivity.** The `x₄` point additionally pins the multiopen blinder
evaluations `multiopenU` — only the IPA fields are free, matching the IPA splice. -/
theorem preX4SqueezePoint_inj {shape : Shape} (init : List (TranscriptElt Fp G))
    {ps ps' : ProofString shape Fp G} (hwf : PsWellFormed ps) (hwf' : PsWellFormed ps')
    (h : preIpaSqueezePoints init ps 8 = preIpaSqueezePoints init ps' 8) :
    ps = { ps' with
            ipaS := ps.ipaS, ipaRounds := ps.ipaRounds, ipaC := ps.ipaC,
            ipaF := ps.ipaF } := by
  have h8 : sqPt8 init ps = sqPt8 init ps' := h
  have h8' := List.append_inj' h8 rfl
  have h7u := List.append_inj' h8'.1
    (by rw [length_absorbScalars, length_absorbScalars])
  have h7 : sqPt7 init ps = sqPt7 init ps' := h7u.1
  have hMU : ps.multiopenU = ps'.multiopenU := absorbScalars_inj h7u.2
  have h7' := List.append_inj' h7 rfl
  have h6q := List.append_inj' h7'.1 rfl
  have h6 : sqPt6 init ps = sqPt6 init ps' := h6q.1
  have hQP : ps.multiopenQPrime = ps'.multiopenQPrime := singleton_point_inj h6q.2
  obtain ⟨hAdv, hLPI, hLPT, hPP, hLP, hVR, hHP, hIE, hAE, hFE, hVRE, hPCE, hPSE, hLE⟩ :=
    preX1_fields_inj init hwf hwf' (List.append_inj' h6 rfl).1
  exact psExt hAdv hLPI hLPT hPP hLP hVR hHP hIE hAE hFE hVRE hPCE hPSE hLE
    hQP hMU rfl rfl rfl rfl

/-- Extend a bounded transcript table with zero outside the bound. The deployed schedule only reads
in-bound transcripts. -/
def extendO {F G : Type*} [Zero F] {L : ℕ} (O : BTranscript F G L → F) :
    List (TranscriptElt F G) → F :=
  fun l => if h : l.length ≤ L then O ⟨l, h⟩ else 0

/-- Extending a bounded table preserves all pre-IPA and IPA-round challenge reads. -/
theorem roChallenges_extendO_eq_chRecord {shape : Shape} {L : ℕ}
    (O : BTranscript Fp G L → Fp) (init : List (TranscriptElt Fp G))
    (ps : ProofString shape Fp G)
    (hpre : ∀ i : Fin 11, (preIpaSqueezePoints init ps i).length ≤ L)
    (hround : ∀ j : Fin shape.k,
      (roundTranscriptFin (preIpaTranscript init ps) ps.ipaRounds j).length ≤ L) :
    roChallenges (extendO O) init ps
      = chRecord (fun i => O ⟨preIpaSqueezePoints init ps i, hpre i⟩)
          (fun j => O ⟨roundTranscriptFin (preIpaTranscript init ps) ps.ipaRounds j,
            hround j⟩) := by
  rw [roChallenges_eq_chRecord,
    show (fun i => extendO O (preIpaSqueezePoints init ps i))
        = (fun i => O ⟨preIpaSqueezePoints init ps i, hpre i⟩) from
      funext fun i => by simp only [extendO]; exact dif_pos (hpre i),
    show (fun j => extendO O (roundTranscriptFin (preIpaTranscript init ps) ps.ipaRounds j))
        = (fun j => O ⟨roundTranscriptFin (preIpaTranscript init ps) ps.ipaRounds j, hround j⟩)
      from funext fun j => by simp only [extendO]; exact dif_pos (hround j)]

end Zcash.Snark
