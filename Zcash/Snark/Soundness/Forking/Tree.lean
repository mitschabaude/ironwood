import Mathlib

/-!
# Multi-round fork-tree extraction

If enough challenge vectors accept, a full `(3,…,3)` tree of accepting vectors exists. The proof is a
counting induction over all rounds, not an iteration of a per-round cubic bound.

`kerr N d` is the threshold count out of `N^d` vectors. As a fraction it is the conservative bound
`3d/N`; requiring nonzero IPA challenges causes the factor `3`. This is a tree-existence threshold,
not the final Fiat–Shamir knowledge error, which must also include random-oracle query loss.

The deployed verifier supplies `acc`. Group-element recovery is handled separately.
-/

namespace Zcash.Snark

variable {α : Type*}

/-- The accepting-vector threshold for a nonzero-challenge `(3,…,3)` tree of depth `d`. -/
def kerr (N : ℕ) : ℕ → ℕ
  | 0 => 0
  | d + 1 => 3 * N ^ d + N * kerr N d

/-- A depth-`d` tree with three distinct nonzero challenges at each node and acceptance at every leaf. -/
def Extractable [Zero α] : {d : ℕ} → ((Fin d → α) → Prop) → Prop
  | 0, acc => acc Fin.elim0
  | _ + 1, acc => ∃ u₁ u₂ u₃ : α, u₁ ≠ u₂ ∧ u₁ ≠ u₃ ∧ u₂ ≠ u₃ ∧ u₁ ≠ 0 ∧ u₂ ≠ 0 ∧ u₃ ≠ 0 ∧
      Extractable (fun rest => acc (Fin.cons u₁ rest)) ∧
      Extractable (fun rest => acc (Fin.cons u₂ rest)) ∧
      Extractable (fun rest => acc (Fin.cons u₃ rest))

/-! ## The round-by-round ladder

An accepted vector either extracts or escapes a nonextractable prefix through at most three
challenges. -/

/-- The challenge vector reaches a doomed state and then draws zero or an extractable
continuation. -/
def LadderEscape [Zero α] : {d : ℕ} → ((Fin d → α) → Prop) → (Fin d → α) → Prop
  | 0, _, _ => False
  | _ + 1, acc, χ =>
      (¬ Extractable acc ∧ (χ 0 = 0 ∨ Extractable (fun rest => acc (Fin.cons (χ 0) rest))))
      ∨ LadderEscape (fun rest => acc (Fin.cons (χ 0) rest)) (Fin.tail χ)

/-- An accepted vector either extracts at the root or escapes at some round. -/
theorem extractable_or_ladderEscape [Zero α] :
    {d : ℕ} → (acc : (Fin d → α) → Prop) → (χ : Fin d → α) → acc χ →
    Extractable acc ∨ LadderEscape acc χ
  | 0, acc, χ, h => Or.inl (by
      have hχ : χ = Fin.elim0 := funext fun i => i.elim0
      rwa [hχ] at h)
  | d + 1, acc, χ, h => by
      have hsub : (fun rest => acc (Fin.cons (χ 0) rest)) (Fin.tail χ) := by
        show acc (Fin.cons (χ 0) (Fin.tail χ))
        rw [Fin.cons_self_tail]
        exact h
      rcases extractable_or_ladderEscape (fun rest => acc (Fin.cons (χ 0) rest)) (Fin.tail χ)
          hsub with hext | hesc
      · by_cases hdoom : Extractable acc
        · exact Or.inl hdoom
        · exact Or.inr (Or.inl ⟨hdoom, Or.inr hext⟩)
      · exact Or.inr (Or.inr hesc)

/-- A nonextractable state's escape set lies in zero and at most two other challenges. -/
theorem escapeSet_subset_triple [Zero α] {d : ℕ} {acc : (Fin (d + 1) → α) → Prop}
    (hdoom : ¬ Extractable acc) :
    ∃ a b : α, {u : α | u = 0 ∨ Extractable (fun rest => acc (Fin.cons u rest))}
      ⊆ {0, a, b} := by
  by_cases hne : ∃ a : α, a ≠ 0 ∧ Extractable (fun rest => acc (Fin.cons a rest))
  · obtain ⟨a, ha0, haE⟩ := hne
    by_cases hb : ∃ b : α, b ≠ 0 ∧ b ≠ a ∧ Extractable (fun rest => acc (Fin.cons b rest))
    · obtain ⟨b, hb0, hba, hbE⟩ := hb
      refine ⟨a, b, fun c hc => ?_⟩
      rcases hc with hc | hc
      · exact Or.inl hc
      · by_cases hc0 : c = 0
        · exact Or.inl hc0
        · by_cases hca : c = a
          · exact Or.inr (Or.inl hca)
          · by_cases hcb : c = b
            · exact Or.inr (Or.inr hcb)
            · exact absurd (⟨c, a, b, hca, hcb, fun h => hba h.symm, hc0, ha0, hb0,
                hc, haE, hbE⟩ : Extractable acc) hdoom
    · refine ⟨a, a, fun c hc => ?_⟩
      rcases hc with hc | hc
      · exact Or.inl hc
      · by_cases hc0 : c = 0
        · exact Or.inl hc0
        · by_cases hca : c = a
          · exact Or.inr (Or.inl hca)
          · exact absurd ⟨c, hc0, hca, hc⟩ hb
  · refine ⟨0, 0, fun c hc => ?_⟩
    rcases hc with hc | hc
    · exact Or.inl hc
    · by_cases hc0 : c = 0
      · exact Or.inl hc0
      · exact absurd ⟨c, hc0, hc⟩ hne

open Classical in
/-- The round-`j` escape set: empty at an extractable state, otherwise zero and the extractable
continuations. It depends only on earlier challenges. -/
def ladderEscapeSet [Zero α] : {d : ℕ} → ((Fin d → α) → Prop) → (Fin d → α) → ℕ → Set α
  | 0, _, _, _ => ∅
  | _ + 1, acc, _, 0 =>
      if Extractable acc then ∅
      else {u : α | u = 0 ∨ Extractable (fun rest => acc (Fin.cons u rest))}
  | _ + 1, acc, χ, j + 1 => ladderEscapeSet (fun rest => acc (Fin.cons (χ 0) rest)) (Fin.tail χ) j

/-- The round-`j` escape set reads only the challenges before round `j`. -/
theorem ladderEscapeSet_congr [Zero α] :
    {d : ℕ} → (acc : (Fin d → α) → Prop) → (χ χ' : Fin d → α) → (j : ℕ) →
    (∀ i : Fin d, (i : ℕ) < j → χ i = χ' i) →
    ladderEscapeSet acc χ j = ladderEscapeSet acc χ' j
  | 0, _, _, _, _, _ => rfl
  | _ + 1, acc, χ, χ', 0, _ => rfl
  | d + 1, acc, χ, χ', j + 1, h => by
      have h0 : χ 0 = χ' 0 := h 0 (Nat.succ_pos j)
      show ladderEscapeSet (fun rest => acc (Fin.cons (χ 0) rest)) (Fin.tail χ) j
          = ladderEscapeSet (fun rest => acc (Fin.cons (χ' 0) rest)) (Fin.tail χ') j
      rw [h0]
      exact ladderEscapeSet_congr _ (Fin.tail χ) (Fin.tail χ') j
        (fun i hi => h i.succ (by simp only [Fin.val_succ]; omega))

/-- A ladder escape locates a round: some round's drawn challenge lies in that round's escape
set. -/
theorem exists_mem_ladderEscapeSet [Zero α] :
    {d : ℕ} → (acc : (Fin d → α) → Prop) → (χ : Fin d → α) → LadderEscape acc χ →
    ∃ j : Fin d, χ j ∈ ladderEscapeSet acc χ (j : ℕ)
  | 0, _, _, h => absurd h not_false
  | d + 1, acc, χ, h => by
      rcases h with ⟨hdoom, hesc⟩ | h
      · refine ⟨0, ?_⟩
        show χ 0 ∈ ladderEscapeSet acc χ 0
        simp only [ladderEscapeSet, if_neg hdoom]
        exact hesc
      · obtain ⟨j, hj⟩ := exists_mem_ladderEscapeSet
          (fun rest => acc (Fin.cons (χ 0) rest)) (Fin.tail χ) h
        exact ⟨j.succ, hj⟩

/-- Every round's escape set lies in at most three challenges. -/
theorem ladderEscapeSet_subset_triple [Zero α] :
    {d : ℕ} → (acc : (Fin d → α) → Prop) → (χ : Fin d → α) → (j : ℕ) →
    ∃ a b : α, ladderEscapeSet acc χ j ⊆ {0, a, b}
  | 0, _, _, _ => ⟨0, 0, by simp [ladderEscapeSet]⟩
  | d + 1, acc, χ, 0 => by
      by_cases hext : Extractable acc
      · exact ⟨0, 0, by simp only [ladderEscapeSet, if_pos hext]; exact Set.empty_subset _⟩
      · obtain ⟨a, b, hab⟩ := escapeSet_subset_triple hext
        exact ⟨a, b, by simp only [ladderEscapeSet, if_neg hext]; exact hab⟩
  | d + 1, acc, χ, j + 1 =>
      ladderEscapeSet_subset_triple (fun rest => acc (Fin.cons (χ 0) rest)) (Fin.tail χ) j


/-- Split the accepting-vector count by the first challenge. -/
theorem card_filter_eq_sum_slice [Fintype α] [DecidableEq α] {d : ℕ}
    (acc : (Fin (d + 1) → α) → Prop) [DecidablePred acc] :
    (Finset.univ.filter acc).card
      = ∑ u : α, (Finset.univ.filter (fun rest => acc (Fin.cons u rest))).card := by
  simp only [Finset.card_filter]
  rw [← (Fin.consEquiv (fun _ : Fin (d + 1) => α)).sum_comp (fun i => if acc i then 1 else 0),
    Fintype.sum_prod_type]
  rfl

/-- If the accepting-vector count exceeds `kerr`, a full `(3,…,3)` accepting tree exists.

The induction finds at least four good first challenges, so three can be chosen nonzero. -/
theorem extractable_of_kerr_lt [Fintype α] [DecidableEq α] [Zero α] :
    ∀ {d : ℕ} (acc : (Fin d → α) → Prop) [DecidablePred acc],
      kerr (Fintype.card α) d < (Finset.univ.filter acc).card → Extractable acc
  | 0, acc, _, h => by
      simp only [kerr] at h
      rw [Finset.card_pos] at h
      obtain ⟨x, hx⟩ := h
      rw [Finset.mem_filter] at hx
      show acc Fin.elim0
      rw [Subsingleton.elim Fin.elim0 x]
      exact hx.2
  | d + 1, acc, _, h => by
      have hslice : (Finset.univ.filter acc).card
          = ∑ u : α, (Finset.univ.filter (fun rest : Fin d → α => acc (Fin.cons u rest))).card :=
        card_filter_eq_sum_slice acc
      have hNd : ∀ u : α, (Finset.univ.filter (fun rest : Fin d → α => acc (Fin.cons u rest))).card
          ≤ Fintype.card α ^ d := fun u =>
        le_trans (Finset.card_filter_le _ _)
          (by rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin])
      have hgood4 : 4 ≤ (Finset.univ.filter (fun u : α =>
          kerr (Fintype.card α) d
            < (Finset.univ.filter (fun rest : Fin d → α => acc (Fin.cons u rest))).card)).card := by
        by_contra hcon
        push Not at hcon
        have hgc : (Finset.univ.filter (fun u : α => kerr (Fintype.card α) d
            < (Finset.univ.filter (fun rest : Fin d → α => acc (Fin.cons u rest))).card)).card ≤ 3 := by
          omega
        have hbc : (Finset.univ.filter (fun u : α => ¬ kerr (Fintype.card α) d
            < (Finset.univ.filter (fun rest : Fin d → α => acc (Fin.cons u rest))).card)).card
            ≤ Fintype.card α :=
          le_trans (Finset.card_filter_le _ _) (le_of_eq Finset.card_univ)
        have h1 := Finset.sum_le_sum (s := Finset.univ.filter (fun u : α => kerr (Fintype.card α) d
            < (Finset.univ.filter (fun rest : Fin d → α => acc (Fin.cons u rest))).card))
            (f := fun u => (Finset.univ.filter (fun rest : Fin d → α => acc (Fin.cons u rest))).card)
            (g := fun _ => Fintype.card α ^ d) (fun u _ => hNd u)
        have h2 := Finset.sum_le_sum (s := Finset.univ.filter (fun u : α => ¬ kerr (Fintype.card α) d
            < (Finset.univ.filter (fun rest : Fin d → α => acc (Fin.cons u rest))).card))
            (f := fun u => (Finset.univ.filter (fun rest : Fin d → α => acc (Fin.cons u rest))).card)
            (g := fun _ => kerr (Fintype.card α) d)
            (fun u hu => not_lt.mp (Finset.mem_filter.mp hu).2)
        rw [Finset.sum_const, smul_eq_mul] at h1 h2
        have hb : (Finset.univ.filter acc).card
            ≤ 3 * Fintype.card α ^ d + Fintype.card α * kerr (Fintype.card α) d := by
          rw [hslice, ← Finset.sum_filter_add_sum_filter_not Finset.univ
            (fun u => kerr (Fintype.card α) d
              < (Finset.univ.filter (fun rest : Fin d → α => acc (Fin.cons u rest))).card)]
          calc _ ≤ _ + _ := add_le_add h1 h2
            _ ≤ 3 * Fintype.card α ^ d + Fintype.card α * kerr (Fintype.card α) d := by
                gcongr
        simp only [kerr] at h
        omega
      set g := Finset.univ.filter (fun u : α => kerr (Fintype.card α) d
          < (Finset.univ.filter (fun rest : Fin d → α => acc (Fin.cons u rest))).card) with hg
      have hg4 : 4 ≤ g.card := hgood4
      have hg0 : 2 < (g.erase 0).card := by
        by_cases h0 : (0 : α) ∈ g
        · have he := Finset.card_erase_add_one h0
          omega
        · rw [Finset.erase_eq_of_notMem h0]; omega
      obtain ⟨u₁, u₂, u₃, hu₁, hu₂, hu₃, h12, h13, h23⟩ := Finset.two_lt_card_iff.mp hg0
      have key : ∀ u, u ∈ g.erase 0 → u ≠ 0 ∧ kerr (Fintype.card α) d
          < (Finset.univ.filter (fun rest : Fin d → α => acc (Fin.cons u rest))).card := by
        intro u hu
        refine ⟨Finset.ne_of_mem_erase hu, ?_⟩
        have hm := Finset.mem_of_mem_erase hu
        rw [hg, Finset.mem_filter] at hm
        exact hm.2
      exact ⟨u₁, u₂, u₃, h12, h13, h23, (key u₁ hu₁).1, (key u₂ hu₂).1, (key u₃ hu₃).1,
        extractable_of_kerr_lt _ (key u₁ hu₁).2,
        extractable_of_kerr_lt _ (key u₂ hu₂).2,
        extractable_of_kerr_lt _ (key u₃ hu₃).2⟩

end Zcash.Snark
