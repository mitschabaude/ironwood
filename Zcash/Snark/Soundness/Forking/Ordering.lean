import Zcash.Snark.Verifier.FiatShamir
import Zcash.Snark.Soundness.Forking.Extractor

/-!
# Fiat–Shamir round ordering

`deriveChallenges` appends each IPA round point `(Lⱼ, Rⱼ)` before squeezing its challenge `uⱼ`:

    (List.finRange shape.k).foldl (fun (t, us) j =>
        let t := t ++ [.point Lⱼ, .point Rⱼ, .challenge]
        (t, us ++ [squeeze t])) (t₀, [])

This module proves that the deployed schedule has the prefix ordering assumed by the prover strategy
and rewinding proofs.

* `roundTranscript` is the prefix used to squeeze one round challenge.
* `roundTranscript_succ` and `roundTranscript_prefix_mono` show how those prefixes grow.
* `roundPoint_mem_roundTranscript` shows that the current point is present before its challenge.

Halo2 does not reabsorb squeezed challenges. The `Prover` type separately ensures that each round
point depends only on earlier challenges.
-/

namespace Zcash.Snark

variable {F G : Type*}

/-- The transcript prefix used to squeeze the round-`j` IPA challenge. -/
def roundTranscript (t₀ : List (TranscriptElt F G)) (rounds : ℕ → G × G) :
    ℕ → List (TranscriptElt F G)
  | 0 => t₀ ++ [.point (rounds 0).1, .point (rounds 0).2, .challenge]
  | j + 1 =>
      roundTranscript t₀ rounds j ++ [.point (rounds (j + 1)).1, .point (rounds (j + 1)).2, .challenge]

/-- Extend a round transcript with the next point and challenge marker. -/
theorem roundTranscript_succ (t₀ : List (TranscriptElt F G)) (rounds : ℕ → G × G) (j : ℕ) :
    roundTranscript t₀ rounds (j + 1)
      = roundTranscript t₀ rounds j
        ++ [.point (rounds (j + 1)).1, .point (rounds (j + 1)).2, .challenge] :=
  rfl

/-- The base and earlier round transcripts are prefixes of every later round transcript. -/
theorem roundTranscript_prefix_mono (t₀ : List (TranscriptElt F G)) (rounds : ℕ → G × G) (j : ℕ) :
    t₀ <+: roundTranscript t₀ rounds j
      ∧ roundTranscript t₀ rounds j <+: roundTranscript t₀ rounds (j + 1) := by
  constructor
  · induction j with
    | zero => exact ⟨_, rfl⟩
    | succ j ih => exact ih.trans ⟨_, (roundTranscript_succ t₀ rounds j).symm⟩
  · exact ⟨_, (roundTranscript_succ t₀ rounds j).symm⟩

/-- The round-`j` point is present in the transcript before `uⱼ` is squeezed. -/
theorem roundPoint_mem_roundTranscript (t₀ : List (TranscriptElt F G)) (rounds : ℕ → G × G) (j : ℕ) :
    TranscriptElt.point (rounds j).1 ∈ roundTranscript t₀ rounds j ∧
      TranscriptElt.point (rounds j).2 ∈ roundTranscript t₀ rounds j := by
  cases j <;> exact ⟨by simp [roundTranscript], by simp [roundTranscript]⟩

/-- Squeeze the round-`j` IPA challenge from its round transcript. -/
def roundChallenge (fs : FiatShamir F G) (t₀ : List (TranscriptElt F G)) (rounds : ℕ → G × G)
    (j : ℕ) : F :=
  fs.squeeze (roundTranscript t₀ rounds j)

/-- The transcript part of the deployed IPA `foldl` is the base followed by each round's absorb block. -/
theorem ipaFold_transcript {ι : Type*} (fs : FiatShamir F G) (rp : ι → G × G)
    (L : List ι) (t₀ : List (TranscriptElt F G)) (us₀ : List F) :
    (L.foldl (fun st i =>
        (st.1 ++ [TranscriptElt.point (rp i).1, TranscriptElt.point (rp i).2, TranscriptElt.challenge],
          st.2 ++ [fs.squeeze (st.1 ++ [TranscriptElt.point (rp i).1, TranscriptElt.point (rp i).2,
            TranscriptElt.challenge])])) (t₀, us₀)).1
      = t₀ ++ (L.map (fun i =>
          [TranscriptElt.point (rp i).1, TranscriptElt.point (rp i).2, TranscriptElt.challenge])).flatten := by
  induction L generalizing t₀ us₀ with
  | nil => simp
  | cons i L ih => simp only [List.foldl_cons, ih, List.map_cons, List.flatten_cons, List.append_assoc]

/-! ## The Prover-tree side: each round point is prefix-determined

In `Prover.node`, the round point is fixed before the challenge selects a continuation. The theorem
below states that two paths with the same prefix therefore have the same next round point.
-/

/-- The prover's round point at depth `j` along challenge path `χ`. -/
def proverRoundPoint : {d : ℕ} → Prover F G d → (Fin d → F) → ℕ → Option (G × G)
  | 0, _, _, _ => none
  | _ + 1, .node L R _, _, 0 => some (L, R)
  | _ + 1, .node _ _ cont, χ, j + 1 => proverRoundPoint (cont (χ 0)) (Fin.tail χ) j

/-- The round point at depth `j` depends only on the first `j` challenges. -/
theorem proverRoundPoint_prefix : {d : ℕ} → (P : Prover F G d) → (χ χ' : Fin d → F) → (j : ℕ) →
    (∀ i : Fin d, (i : ℕ) < j → χ i = χ' i) →
    proverRoundPoint P χ j = proverRoundPoint P χ' j
  | 0, .leaf _ _, _, _, _, _ => rfl
  | _ + 1, .node _ _ _, _, _, 0, _ => rfl
  | _ + 1, .node _ _ cont, χ, χ', j + 1, h => by
      have h0 : χ 0 = χ' 0 := h 0 (Nat.succ_pos j)
      show proverRoundPoint (cont (χ 0)) (Fin.tail χ) j = proverRoundPoint (cont (χ' 0)) (Fin.tail χ') j
      rw [h0]
      exact proverRoundPoint_prefix (cont (χ' 0)) (Fin.tail χ) (Fin.tail χ') j
        (fun i hi => h i.succ (by simp only [Fin.val_succ]; omega))

/-! ## Sealing the module to the deployed derivation

The earlier lemmas use a reconstructed round transcript. `deriveChallenges_ipaRound_eq` proves that
the deployed schedule uses exactly that transcript, so any ordering change breaks the theorem.
-/

/-- The transcript prefix before the deployed IPA round fold begins. -/
def preIpaTranscript {shape : Shape} (init : List (TranscriptElt F G)) (ps : ProofString shape F G) :
    List (TranscriptElt F G) :=
  let t := init ++ absorbPoints2 ps.adviceCommitments ++ [.challenge]
  let t := t ++ absorbLookupPermuted ps.lookupPermutedInput ps.lookupPermutedTable ++ [.challenge]
  let t := t ++ [.challenge]
  let t := t ++ absorbPoints2 ps.permutationProduct ++ absorbPoints2 ps.lookupProduct
    ++ [TranscriptElt.point ps.vanishingRandom] ++ [.challenge]
  let t := t ++ absorbPoints ps.hPieces ++ [.challenge]
  let evalElts := absorbScalars2 ps.instanceEvals ++ absorbScalars2 ps.adviceEvals
    ++ absorbScalars ps.fixedEvals ++ [TranscriptElt.scalar ps.vanishingRandomEval]
    ++ absorbScalars ps.permutationCommonEvals
    ++ (List.ofFn (fun p => (List.ofFn (fun s => absorbPermSet (ps.permutationSetEvals p s))).flatten)).flatten
    ++ (List.ofFn (fun p => (List.ofFn (fun l => absorbLookup (ps.lookupEvals p l))).flatten)).flatten
  let t := t ++ evalElts ++ [.challenge]
  let t := t ++ [.challenge]
  let t := t ++ [TranscriptElt.point ps.multiopenQPrime] ++ [.challenge]
  let t := t ++ absorbScalars ps.multiopenU ++ [.challenge]
  let t := t ++ [TranscriptElt.point ps.ipaS] ++ [.challenge]
  let t := t ++ [.challenge]
  t

/-- The challenges produced by the deployed IPA `foldl`. -/
theorem ipaFold_challenges {ι : Type*} (fs : FiatShamir F G) (rp : ι → G × G)
    (L : List ι) (t₀ : List (TranscriptElt F G)) (us₀ : List F) :
    (L.foldl (fun st i =>
        (st.1 ++ [TranscriptElt.point (rp i).1, TranscriptElt.point (rp i).2, TranscriptElt.challenge],
          st.2 ++ [fs.squeeze (st.1 ++ [TranscriptElt.point (rp i).1, TranscriptElt.point (rp i).2,
            TranscriptElt.challenge])])) (t₀, us₀)).2
      = us₀ ++ (List.range L.length).map (fun m =>
          fs.squeeze (t₀ ++ ((L.take (m + 1)).map (fun i =>
            [TranscriptElt.point (rp i).1, TranscriptElt.point (rp i).2,
              TranscriptElt.challenge])).flatten)) := by
  induction L generalizing t₀ us₀ with
  | nil => simp
  | cons i L ih =>
      rw [List.foldl_cons, ih, List.length_cons, List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map, List.take_succ_cons, List.take_zero, List.map_nil,
        List.flatten_cons, List.flatten_nil, Function.comp_def, List.append_assoc,
        List.cons_append, List.nil_append]

/-- Express `roundTranscript` as the base followed by the first `j + 1` absorb blocks. -/
theorem roundTranscript_eq_take (t₀ : List (TranscriptElt F G)) (rounds : ℕ → G × G) (j : ℕ) :
    roundTranscript t₀ rounds j
      = t₀ ++ ((List.range (j + 1)).map (fun i =>
          [TranscriptElt.point (rounds i).1, TranscriptElt.point (rounds i).2,
            TranscriptElt.challenge])).flatten := by
  induction j with
  | zero => simp [roundTranscript]
  | succ j ih =>
      rw [roundTranscript_succ, ih, List.range_succ (n := j + 1), List.map_append,
        List.flatten_append, List.append_assoc]
      simp

/-- The round-`j` transcript for a `Fin`-indexed round vector. -/
def roundTranscriptFin {k : ℕ} (t₀ : List (TranscriptElt F G)) (rounds : Fin k → G × G) (j : Fin k) :
    List (TranscriptElt F G) :=
  t₀ ++ (((List.finRange k).take (j.val + 1)).map (fun i =>
    [TranscriptElt.point (rounds i).1, TranscriptElt.point (rounds i).2,
      TranscriptElt.challenge])).flatten

private theorem length_flatten_map_triple {ι : Type*} (f g h : ι → TranscriptElt F G) :
    ∀ l : List ι, ((l.map (fun i => [f i, g i, h i])).flatten).length = 3 * l.length
  | [] => rfl
  | i :: l => by
      simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons,
        List.length_nil, length_flatten_map_triple f g h l]
      omega

/-- The round-`j` transcript extends the base by `3 · (j + 1)` elements. -/
theorem roundTranscriptFin_length {k : ℕ} (t₀ : List (TranscriptElt F G)) (rounds : Fin k → G × G)
    (j : Fin k) :
    (roundTranscriptFin t₀ rounds j).length = t₀.length + 3 * (j.val + 1) := by
  have hj := j.isLt
  simp only [roundTranscriptFin, List.length_append,
    length_flatten_map_triple (fun i => TranscriptElt.point (rounds i).1)
      (fun i => TranscriptElt.point (rounds i).2) (fun _ => TranscriptElt.challenge),
    List.length_take, List.length_finRange]
  omega

/-- Distinct rounds squeeze from distinct transcript prefixes. -/
theorem roundTranscriptFin_injective {k : ℕ} (t₀ : List (TranscriptElt F G))
    (rounds : Fin k → G × G) :
    Function.Injective (roundTranscriptFin t₀ rounds) := by
  intro a b h
  have hlen := congrArg List.length h
  rw [roundTranscriptFin_length, roundTranscriptFin_length] at hlen
  exact Fin.ext (by omega)

/-- Split the round-`j` transcript into its earlier prefix and final `[L, R, marker]` block. -/
theorem roundTranscriptFin_eq_append {k : ℕ} (t₀ : List (TranscriptElt F G))
    (rounds : Fin k → G × G) (j : Fin k) :
    roundTranscriptFin t₀ rounds j
      = (t₀ ++ (((List.finRange k).take j.val).map (fun i =>
          [TranscriptElt.point (rounds i).1, TranscriptElt.point (rounds i).2,
            TranscriptElt.challenge])).flatten)
        ++ [TranscriptElt.point (rounds j).1, TranscriptElt.point (rounds j).2,
            TranscriptElt.challenge] := by
  rw [roundTranscriptFin, List.take_succ, List.append_assoc]
  congr 1
  rw [List.map_append, List.flatten_append]
  congr 1
  rw [List.getElem?_eq_getElem (by simpa using j.isLt)]
  simp

/-- The pre-block prefix of the round-`j` transcript has length `t₀.length + 3 · j`. -/
theorem roundTranscriptFin_preBlock_length {k : ℕ} (t₀ : List (TranscriptElt F G))
    (rounds : Fin k → G × G) (j : Fin k) :
    (t₀ ++ (((List.finRange k).take j.val).map (fun i =>
        [TranscriptElt.point (rounds i).1, TranscriptElt.point (rounds i).2,
          TranscriptElt.challenge])).flatten).length = t₀.length + 3 * j.val := by
  rw [List.length_append,
    length_flatten_map_triple (fun i => TranscriptElt.point (rounds i).1)
      (fun i => TranscriptElt.point (rounds i).2) (fun _ => TranscriptElt.challenge),
    List.length_take, List.length_finRange]
  have := j.isLt
  omega

/-- Round `j`'s `L` point occurs at position `t₀.length + 3j`. -/
theorem roundTranscriptFin_getElem?_fst {k : ℕ} (t₀ : List (TranscriptElt F G))
    (rounds : Fin k → G × G) (j : Fin k) :
    (roundTranscriptFin t₀ rounds j)[t₀.length + 3 * j.val]?
      = some (TranscriptElt.point (rounds j).1) := by
  rw [roundTranscriptFin_eq_append,
    List.getElem?_append_right (le_of_eq (roundTranscriptFin_preBlock_length t₀ rounds j)),
    roundTranscriptFin_preBlock_length]
  simp

/-- The round-`j` transcript carries round `j`'s own `R` point at position `t₀.length + 3j + 1`. -/
theorem roundTranscriptFin_getElem?_snd {k : ℕ} (t₀ : List (TranscriptElt F G))
    (rounds : Fin k → G × G) (j : Fin k) :
    (roundTranscriptFin t₀ rounds j)[t₀.length + 3 * j.val + 1]?
      = some (TranscriptElt.point (rounds j).2) := by
  rw [roundTranscriptFin_eq_append,
    List.getElem?_append_right (by rw [roundTranscriptFin_preBlock_length]; omega),
    roundTranscriptFin_preBlock_length,
    show t₀.length + 3 * j.val + 1 - (t₀.length + 3 * j.val) = 1 from by omega]
  simp

/-- For `i ≤ j`, the round-`i` transcript is a prefix of the round-`j` transcript. -/
theorem roundTranscriptFin_prefix {k : ℕ} (t₀ : List (TranscriptElt F G))
    (rounds : Fin k → G × G) {i j : Fin k} (hij : i.val ≤ j.val) :
    roundTranscriptFin t₀ rounds i <+: roundTranscriptFin t₀ rounds j := by
  rw [roundTranscriptFin, roundTranscriptFin]
  have h1 : (List.finRange k).take (i.val + 1) <+: (List.finRange k).take (j.val + 1) := by
    rw [show (List.finRange k).take (i.val + 1)
        = ((List.finRange k).take (j.val + 1)).take (i.val + 1) from by
      rw [List.take_take, min_eq_left (by omega)]]
    exact List.take_prefix _ _
  obtain ⟨q, hq⟩ := h1.map (fun i =>
    [TranscriptElt.point (rounds i).1, TranscriptElt.point (rounds i).2,
      TranscriptElt.challenge])
  refine ⟨q.flatten, ?_⟩
  rw [List.append_assoc, ← List.flatten_append, hq]

/-- Truncating a later round transcript at round `i` recovers the round-`i` transcript. -/
theorem roundTranscriptFin_take {k : ℕ} (t₀ : List (TranscriptElt F G))
    (rounds : Fin k → G × G) {i j : Fin k} (hij : i.val ≤ j.val) :
    (roundTranscriptFin t₀ rounds j).take (t₀.length + 3 * (i.val + 1))
      = roundTranscriptFin t₀ rounds i := by
  have h := List.prefix_iff_eq_take.mp (roundTranscriptFin_prefix t₀ rounds hij)
  rw [roundTranscriptFin_length] at h
  exact h.symm

/-- The `Fin`-indexed round transcript equals the recursive `roundTranscript`. -/
theorem roundTranscriptFin_eq_roundTranscript {k : ℕ} (t₀ : List (TranscriptElt F G))
    (rounds : Fin k → G × G) (j : Fin k) :
    roundTranscriptFin t₀ rounds j
      = roundTranscript t₀ (fun i => rounds ⟨i % k, Nat.mod_lt _ j.pos⟩) j.val := by
  rw [roundTranscript_eq_take, roundTranscriptFin]
  congr 2
  apply List.ext_getElem
  · simp only [List.length_map, List.length_take, List.length_finRange, List.length_range]
    have := j.isLt
    omega
  · intro n h1 h2
    simp only [List.length_map, List.length_take, List.length_finRange, List.length_range] at h1 h2
    have hn : n < k := lt_of_lt_of_le (lt_min_iff.mp h1).1 (Nat.succ_le_of_lt j.isLt)
    simp only [List.getElem_map, List.getElem_take, List.getElem_finRange, List.getElem_range]
    refine congrArg (fun x => [TranscriptElt.point (rounds x).1, TranscriptElt.point (rounds x).2,
      TranscriptElt.challenge]) (Fin.ext ?_)
    simp [Nat.mod_eq_of_lt hn]

/-- The deployed round challenge is squeezed from the corresponding `roundTranscriptFin`.

This theorem pins the ordering model to `deriveChallenges`. -/
theorem deriveChallenges_ipaRound_eq {shape : Shape} [Zero F] (fs : FiatShamir F G)
    (init : List (TranscriptElt F G)) (ps : ProofString shape F G) (j : Fin shape.k) :
    (deriveChallenges fs init ps).ipaRound j
      = fs.squeeze (roundTranscriptFin (preIpaTranscript init ps) ps.ipaRounds j) := by
  simp only [deriveChallenges, preIpaTranscript, roundTranscriptFin]
  rw [ipaFold_challenges, List.nil_append, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (by simp)]
  rfl

/-- Restate `deriveChallenges_ipaRound_eq` using `roundChallenge`. -/
theorem deriveChallenges_ipaRound_eq_roundChallenge {shape : Shape} [Zero F] (fs : FiatShamir F G)
    (init : List (TranscriptElt F G)) (ps : ProofString shape F G) (j : Fin shape.k) :
    (deriveChallenges fs init ps).ipaRound j
      = roundChallenge fs (preIpaTranscript init ps)
          (fun i => ps.ipaRounds ⟨i % shape.k, Nat.mod_lt _ j.pos⟩) j.val := by
  rw [deriveChallenges_ipaRound_eq, roundChallenge, roundTranscriptFin_eq_roundTranscript]

/-! ## Sealing the multiopen squeeze points (issue #18's rewinding note)

The multiopen rewinding (`Soundness.Multiopen.Decode`) forks on the batching challenge `x₄`; the
analogue of the round-by-round treatment above needs the same two ingredients at the multiopen
squeeze points: the commit-before-challenge ordering (`q′` is absorbed before `x₃` is squeezed, the
`u` family before `x₄`), and named squeeze prefixes so the oracle can be reprogrammed there
(`Soundness.Forking.reprogramX4`). Mirroring `preIpaTranscript`, `preX3Transcript`/`preX4Transcript`
are fully inlined (not a chain of `++`), so `deriveChallenges_x3_eq`/`_x4_eq` hold by `rfl` and a
single `simp only [preX4Transcript, …]` unfolds the squeeze input in one step — the shape the
reprogramming length proofs use. A refactor of the absorb order breaks the seals. -/

/-- The transcript `deriveChallenges` has absorbed when `x₃` is squeezed: everything through the
`x₂` marker, then the multiopen `q′` commitment and the `x₃` challenge marker. -/
def preX3Transcript {shape : Shape} (init : List (TranscriptElt F G)) (ps : ProofString shape F G) :
    List (TranscriptElt F G) :=
  let t := init ++ absorbPoints2 ps.adviceCommitments ++ [.challenge]
  let t := t ++ absorbLookupPermuted ps.lookupPermutedInput ps.lookupPermutedTable ++ [.challenge]
  let t := t ++ [.challenge]
  let t := t ++ absorbPoints2 ps.permutationProduct ++ absorbPoints2 ps.lookupProduct
    ++ [TranscriptElt.point ps.vanishingRandom] ++ [.challenge]
  let t := t ++ absorbPoints ps.hPieces ++ [.challenge]
  let evalElts := absorbScalars2 ps.instanceEvals ++ absorbScalars2 ps.adviceEvals
    ++ absorbScalars ps.fixedEvals ++ [TranscriptElt.scalar ps.vanishingRandomEval]
    ++ absorbScalars ps.permutationCommonEvals
    ++ (List.ofFn (fun p => (List.ofFn (fun s => absorbPermSet (ps.permutationSetEvals p s))).flatten)).flatten
    ++ (List.ofFn (fun p => (List.ofFn (fun l => absorbLookup (ps.lookupEvals p l))).flatten)).flatten
  let t := t ++ evalElts ++ [.challenge]
  let t := t ++ [.challenge]
  let t := t ++ [TranscriptElt.point ps.multiopenQPrime] ++ [.challenge]
  t

/-- The transcript at the `x₄` squeeze: the `x₃` prefix extended by the multiopen `u` evaluations
and the `x₄` marker (inlined for `rfl` seals and one-step `simp`). -/
def preX4Transcript {shape : Shape} (init : List (TranscriptElt F G)) (ps : ProofString shape F G) :
    List (TranscriptElt F G) :=
  let t := init ++ absorbPoints2 ps.adviceCommitments ++ [.challenge]
  let t := t ++ absorbLookupPermuted ps.lookupPermutedInput ps.lookupPermutedTable ++ [.challenge]
  let t := t ++ [.challenge]
  let t := t ++ absorbPoints2 ps.permutationProduct ++ absorbPoints2 ps.lookupProduct
    ++ [TranscriptElt.point ps.vanishingRandom] ++ [.challenge]
  let t := t ++ absorbPoints ps.hPieces ++ [.challenge]
  let evalElts := absorbScalars2 ps.instanceEvals ++ absorbScalars2 ps.adviceEvals
    ++ absorbScalars ps.fixedEvals ++ [TranscriptElt.scalar ps.vanishingRandomEval]
    ++ absorbScalars ps.permutationCommonEvals
    ++ (List.ofFn (fun p => (List.ofFn (fun s => absorbPermSet (ps.permutationSetEvals p s))).flatten)).flatten
    ++ (List.ofFn (fun p => (List.ofFn (fun l => absorbLookup (ps.lookupEvals p l))).flatten)).flatten
  let t := t ++ evalElts ++ [.challenge]
  let t := t ++ [.challenge]
  let t := t ++ [TranscriptElt.point ps.multiopenQPrime] ++ [.challenge]
  let t := t ++ absorbScalars ps.multiopenU ++ [.challenge]
  t

/-- The deployed `x₃` *is* the squeeze of the named `x₃` prefix — the multiopen analogue of
`deriveChallenges_ipaRound_eq`. -/
theorem deriveChallenges_x3_eq {shape : Shape} [Zero F] (fs : FiatShamir F G)
    (init : List (TranscriptElt F G)) (ps : ProofString shape F G) :
    (deriveChallenges fs init ps).x3 = fs.squeeze (preX3Transcript init ps) := rfl

/-- The deployed `x₄` *is* the squeeze of the named `x₄` prefix. -/
theorem deriveChallenges_x4_eq {shape : Shape} [Zero F] (fs : FiatShamir F G)
    (init : List (TranscriptElt F G)) (ps : ProofString shape F G) :
    (deriveChallenges fs init ps).x4 = fs.squeeze (preX4Transcript init ps) := rfl

/-- Commit-before-challenge at `x₃`: the multiopen `q′` commitment is inside the `x₃` squeeze input,
fixed before the challenge. -/
theorem qPrime_mem_preX3Transcript {shape : Shape} (init : List (TranscriptElt F G))
    (ps : ProofString shape F G) :
    TranscriptElt.point ps.multiopenQPrime ∈ preX3Transcript init ps := by
  simp [preX3Transcript]

/-- Commit-before-challenge at `x₄`: every multiopen `u` evaluation is inside the `x₄` squeeze
input, fixed before the challenge. -/
theorem multiopenU_mem_preX4Transcript {shape : Shape} (init : List (TranscriptElt F G))
    (ps : ProofString shape F G) (i : Fin shape.numPointSets) :
    TranscriptElt.scalar (ps.multiopenU i) ∈ preX4Transcript init ps := by
  simp only [preX4Transcript, absorbScalars, List.mem_append, List.mem_ofFn]
  exact Or.inl (Or.inr ⟨i, rfl⟩)

/-- The pre-IPA base is the `x₄` prefix extended by the IPA `S` commitment and the `ξ`/`z` markers,
so the multiopen squeezes sit strictly inside it. -/
theorem preIpaTranscript_length_eq_preX4 {shape : Shape} (init : List (TranscriptElt F G))
    (ps : ProofString shape F G) :
    (preIpaTranscript init ps).length = (preX4Transcript init ps).length + 3 := by
  simp only [preIpaTranscript, preX4Transcript, List.length_append, List.length_cons,
    List.length_nil]

/-! ## Sealing the compression squeeze points `x₁`/`x₂`

The within-set (`x₁`) rewinding forks one squeeze earlier than the `x₄` collapse: redraw `x₁` and the
rewound prover re-sends the *post-`x₁`* proof fields (`q′`, `u`, the IPA opening), so `x₃`/`x₄`
re-randomize through their squeeze inputs while everything absorbed before `x₁` — the column
commitments and every claimed evaluation — is shared across runs. The seals here supply that ordering:
`preX1Transcript`/`preX2Transcript` name the squeeze inputs (inlined for `rfl` seals, like
`preX3Transcript`), the membership lemmas pin the claimed evaluations before `x₁`, and the length chain
places the compression squeezes strictly inside the multiopen ones. `Soundness.Forking.reprogramX1` is
the reprogramming at this prefix. -/

/-- The transcript `deriveChallenges` has absorbed when `x₁` is squeezed: everything through the `x`
marker, then all claimed evaluations and the `x₁` challenge marker. -/
def preX1Transcript {shape : Shape} (init : List (TranscriptElt F G)) (ps : ProofString shape F G) :
    List (TranscriptElt F G) :=
  let t := init ++ absorbPoints2 ps.adviceCommitments ++ [.challenge]
  let t := t ++ absorbLookupPermuted ps.lookupPermutedInput ps.lookupPermutedTable ++ [.challenge]
  let t := t ++ [.challenge]
  let t := t ++ absorbPoints2 ps.permutationProduct ++ absorbPoints2 ps.lookupProduct
    ++ [TranscriptElt.point ps.vanishingRandom] ++ [.challenge]
  let t := t ++ absorbPoints ps.hPieces ++ [.challenge]
  let evalElts := absorbScalars2 ps.instanceEvals ++ absorbScalars2 ps.adviceEvals
    ++ absorbScalars ps.fixedEvals ++ [TranscriptElt.scalar ps.vanishingRandomEval]
    ++ absorbScalars ps.permutationCommonEvals
    ++ (List.ofFn (fun p => (List.ofFn (fun s => absorbPermSet (ps.permutationSetEvals p s))).flatten)).flatten
    ++ (List.ofFn (fun p => (List.ofFn (fun l => absorbLookup (ps.lookupEvals p l))).flatten)).flatten
  let t := t ++ evalElts ++ [.challenge]
  t

/-- The transcript at the `x₂` squeeze: the `x₁` prefix extended by the `x₂` marker alone — nothing is
absorbed between the two compression squeezes. -/
def preX2Transcript {shape : Shape} (init : List (TranscriptElt F G)) (ps : ProofString shape F G) :
    List (TranscriptElt F G) :=
  let t := init ++ absorbPoints2 ps.adviceCommitments ++ [.challenge]
  let t := t ++ absorbLookupPermuted ps.lookupPermutedInput ps.lookupPermutedTable ++ [.challenge]
  let t := t ++ [.challenge]
  let t := t ++ absorbPoints2 ps.permutationProduct ++ absorbPoints2 ps.lookupProduct
    ++ [TranscriptElt.point ps.vanishingRandom] ++ [.challenge]
  let t := t ++ absorbPoints ps.hPieces ++ [.challenge]
  let evalElts := absorbScalars2 ps.instanceEvals ++ absorbScalars2 ps.adviceEvals
    ++ absorbScalars ps.fixedEvals ++ [TranscriptElt.scalar ps.vanishingRandomEval]
    ++ absorbScalars ps.permutationCommonEvals
    ++ (List.ofFn (fun p => (List.ofFn (fun s => absorbPermSet (ps.permutationSetEvals p s))).flatten)).flatten
    ++ (List.ofFn (fun p => (List.ofFn (fun l => absorbLookup (ps.lookupEvals p l))).flatten)).flatten
  let t := t ++ evalElts ++ [.challenge]
  let t := t ++ [.challenge]
  t

/-- The deployed `x₁` *is* the squeeze of the named `x₁` prefix. -/
theorem deriveChallenges_x1_eq {shape : Shape} [Zero F] (fs : FiatShamir F G)
    (init : List (TranscriptElt F G)) (ps : ProofString shape F G) :
    (deriveChallenges fs init ps).x1 = fs.squeeze (preX1Transcript init ps) := rfl

/-- The deployed `x₂` *is* the squeeze of the named `x₂` prefix — completing the compression pair;
consumed at doc level by the `x₂`-stays-honest argument (`preX2Transcript_length_eq`), no in-tree
proof consumer yet. -/
theorem deriveChallenges_x2_eq {shape : Shape} [Zero F] (fs : FiatShamir F G)
    (init : List (TranscriptElt F G)) (ps : ProofString shape F G) :
    (deriveChallenges fs init ps).x2 = fs.squeeze (preX2Transcript init ps) := rfl

/-- Commit-before-challenge at `x₁`: every claimed advice evaluation is inside the `x₁` squeeze input,
fixed before the compression challenge — so it is shared across `x₁` rewinds. -/
theorem adviceEvals_mem_preX1Transcript {shape : Shape} (init : List (TranscriptElt F G))
    (ps : ProofString shape F G) (p : Fin shape.numProofs) (i : Fin shape.numAdviceQueries) :
    TranscriptElt.scalar (ps.adviceEvals p i) ∈ preX1Transcript init ps := by
  have hmem : TranscriptElt.scalar (ps.adviceEvals p i)
      ∈ absorbScalars2 (F := F) (G := G) ps.adviceEvals := by
    simp only [absorbScalars2, absorbScalars, List.mem_flatten, List.mem_ofFn]
    exact ⟨_, ⟨p, rfl⟩, List.mem_ofFn.mpr ⟨i, rfl⟩⟩
  simp only [preX1Transcript]
  exact List.mem_append_left _ (List.mem_append_right _
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hmem)))))))

/-- Commit-before-challenge at `x₁`: every claimed instance evaluation is inside the `x₁` squeeze
input. -/
theorem instanceEvals_mem_preX1Transcript {shape : Shape} (init : List (TranscriptElt F G))
    (ps : ProofString shape F G) (p : Fin shape.numProofs) (i : Fin shape.numInstanceQueries) :
    TranscriptElt.scalar (ps.instanceEvals p i) ∈ preX1Transcript init ps := by
  have hmem : TranscriptElt.scalar (ps.instanceEvals p i)
      ∈ absorbScalars2 (F := F) (G := G) ps.instanceEvals := by
    simp only [absorbScalars2, absorbScalars, List.mem_flatten, List.mem_ofFn]
    exact ⟨_, ⟨p, rfl⟩, List.mem_ofFn.mpr ⟨i, rfl⟩⟩
  simp only [preX1Transcript]
  exact List.mem_append_left _ (List.mem_append_right _
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hmem)))))))

/-- Commit-before-challenge at `x₁`: every claimed fixed evaluation is inside the `x₁` squeeze
input. -/
theorem fixedEvals_mem_preX1Transcript {shape : Shape} (init : List (TranscriptElt F G))
    (ps : ProofString shape F G) (i : Fin shape.numFixedQueries) :
    TranscriptElt.scalar (ps.fixedEvals i) ∈ preX1Transcript init ps := by
  have hmem : TranscriptElt.scalar (ps.fixedEvals i)
      ∈ absorbScalars (F := F) (G := G) ps.fixedEvals := by
    simp only [absorbScalars, List.mem_ofFn]
    exact ⟨i, rfl⟩
  simp only [preX1Transcript]
  exact List.mem_append_left _ (List.mem_append_right _
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_right _ hmem))))))

/-- The `x₂` prefix is the `x₁` prefix plus its marker: nothing is absorbed between the compression
squeezes, so an `x₁` reprogram leaves the `x₂` input at a different length (and every later squeeze
longer still). -/
theorem preX2Transcript_length_eq {shape : Shape} (init : List (TranscriptElt F G))
    (ps : ProofString shape F G) :
    (preX2Transcript init ps).length = (preX1Transcript init ps).length + 1 := by
  simp only [preX2Transcript, preX1Transcript, List.length_append, List.length_cons,
    List.length_nil]

/-- The `x₃` prefix is the `x₂` prefix extended by the `q′` commitment and the `x₃` marker — the
rewound prover's fresh `q′` is exactly what re-randomizes `x₃` across `x₁` rewinds. -/
theorem preX3Transcript_length_eq {shape : Shape} (init : List (TranscriptElt F G))
    (ps : ProofString shape F G) :
    (preX3Transcript init ps).length = (preX2Transcript init ps).length + 2 := by
  simp only [preX3Transcript, preX2Transcript, List.length_append, List.length_cons,
    List.length_nil]

/-! ## Sealing the gate-check squeeze point `x` (issue #12's derivation note)

The good-challenge derivation (`Soundness.GoodChallenge`, the `_xgood` capstone rungs) spends an
accept measure over the vanishing-check challenge `x`. Tying that measure's runs to the deployed
schedule needs the same two ingredients as the round/multiopen/compression squeezes: the
commit-before-challenge ordering (the column commitments and the quotient `h` pieces are absorbed
before `x` is squeezed — exactly what pins the Schwartz–Zippel difference polynomial before the
challenge samples), and a named squeeze prefix so the oracle can be reprogrammed there
(`Soundness.Forking.reprogramX`). As with the other seals, `preXTranscript` is fully inlined so
`deriveChallenges_x_eq` holds by `rfl`, and a refactor of the absorb order breaks it. -/

/-- The transcript `deriveChallenges` has absorbed when `x` is squeezed: everything through the `y`
marker, then the quotient `h` pieces and the `x` challenge marker. -/
def preXTranscript {shape : Shape} (init : List (TranscriptElt F G)) (ps : ProofString shape F G) :
    List (TranscriptElt F G) :=
  let t := init ++ absorbPoints2 ps.adviceCommitments ++ [.challenge]
  let t := t ++ absorbLookupPermuted ps.lookupPermutedInput ps.lookupPermutedTable ++ [.challenge]
  let t := t ++ [.challenge]
  let t := t ++ absorbPoints2 ps.permutationProduct ++ absorbPoints2 ps.lookupProduct
    ++ [TranscriptElt.point ps.vanishingRandom] ++ [.challenge]
  let t := t ++ absorbPoints ps.hPieces ++ [.challenge]
  t

/-- The deployed `x` *is* the squeeze of the named `x` prefix — the gate-check analogue of
`deriveChallenges_ipaRound_eq`/`deriveChallenges_x4_eq`. -/
theorem deriveChallenges_x_eq {shape : Shape} [Zero F] (fs : FiatShamir F G)
    (init : List (TranscriptElt F G)) (ps : ProofString shape F G) :
    (deriveChallenges fs init ps).x = fs.squeeze (preXTranscript init ps) := rfl

/-- Commit-before-challenge at `x`: every quotient `h` piece is inside the `x` squeeze input, fixed
before the vanishing-check challenge — the `hpoly` side of the Schwartz–Zippel difference is pinned
before `x` samples. -/
theorem hPieces_mem_preXTranscript {shape : Shape} (init : List (TranscriptElt F G))
    (ps : ProofString shape F G) (i : Fin shape.numQuotientPieces) :
    TranscriptElt.point (ps.hPieces i) ∈ preXTranscript init ps := by
  simp only [preXTranscript, absorbPoints, List.mem_append, List.mem_ofFn]
  exact Or.inl (Or.inr ⟨i, rfl⟩)

/-- Commit-before-challenge at `x`: every advice column commitment is inside the `x` squeeze input —
the columns the decode opens are pinned before the vanishing-check challenge samples. -/
theorem adviceCommitments_mem_preXTranscript {shape : Shape} (init : List (TranscriptElt F G))
    (ps : ProofString shape F G) (p : Fin shape.numProofs) (i : Fin shape.numAdviceColumns) :
    TranscriptElt.point (ps.adviceCommitments p i) ∈ preXTranscript init ps := by
  have hmem : TranscriptElt.point (ps.adviceCommitments p i)
      ∈ absorbPoints2 (F := F) (G := G) ps.adviceCommitments := by
    simp only [absorbPoints2, absorbPoints, List.mem_flatten, List.mem_ofFn]
    exact ⟨_, ⟨p, rfl⟩, List.mem_ofFn.mpr ⟨i, rfl⟩⟩
  simp only [preXTranscript, List.mem_append]
  tauto

/-- The `x₁` prefix strictly extends the `x` prefix (by the claimed evaluations and the `x₁`
marker): the gate-check squeeze sits strictly inside every later squeeze input, so an `x` reprogram
leaves them untouched. -/
theorem preXTranscript_length_lt_preX1Transcript {shape : Shape} (init : List (TranscriptElt F G))
    (ps : ProofString shape F G) :
    (preXTranscript init ps).length < (preX1Transcript init ps).length := by
  simp only [preXTranscript, preX1Transcript, List.length_append, List.length_cons,
    List.length_nil]
  omega


end Zcash.Snark
