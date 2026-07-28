import Zcash.Snark.Soundness.Forking.Adversary.ExpectedRuns

/-!
# Toward the AFK expected-run bound

Node-level gated and low-rank AFK accounting; the global polynomial bound remains open.
-/

namespace Zcash.Snark

section GatedNode

variable {T F G P ι : Type*} [DecidableEq T] [Field F] [DecidableEq F]
  [AddCommGroup G] [Module F G] [Fintype ι]

variable (basis : ι → G) (k : ℕ) (A : OracleComp T F P) (prefixes : P → Fin k → T)
  (rounds : P → Fin k → AlgebraicPoint (F := F) basis × AlgebraicPoint (F := F) basis)
  (final : P → F × F) (win : (T → F) → P → Prop) (decideWin : ∀ O p, Decidable (win O p))

/-- At the incumbent challenge the reprogrammed candidate *is* the first branch: reprogramming the
table to its own value changes nothing and the trunk is trivially stable. -/
theorem scanCandidate_self [Fintype F] {d m : ℕ} (hmk : m + (d + 1) = k) (O : T → F)
    (childC : F → RecursiveForkCoins F d) :
    scanCandidate basis k A prefixes rounds final win decideWin m hmk O childC
        (O (prefixes (A.run O) ⟨m, by omega⟩))
      = recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin
          (m + 1) (by omega) O (A.run O)
          (childC (O (prefixes (A.run O) ⟨m, by omega⟩))) := by
  simp only [scanCandidate, Function.update_eq_self]
  rw [if_pos trivial]

/-- A *nonzero* incumbent challenge is good exactly when the first branch extracts. -/
theorem self_mem_goodChallenges_iff [Fintype F] {d m : ℕ} (hmk : m + (d + 1) = k) (O : T → F)
    (childC : F → RecursiveForkCoins F d)
    (h0 : O (prefixes (A.run O) ⟨m, by omega⟩) ≠ 0) :
    O (prefixes (A.run O) ⟨m, by omega⟩) ∈
        goodChallenges basis k A prefixes rounds final win decideWin m hmk O childC
      ↔ (recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin (m + 1)
          (by omega) O (A.run O)
          (childC (O (prefixes (A.run O) ⟨m, by omega⟩)))).output.isSome := by
  rw [goodChallenges, Finset.mem_filter,
    scanCandidate_self basis k A prefixes rounds final win decideWin hmk O childC]
  simp [h0]

omit [Field F] in
/-- A candidate's low-rank test only counts *other* challenges sampled before it: its own
membership in the good set is invisible to its rank. -/
theorem scanRank_insert_erase {n : ℕ} (e : Fin n ≃ F) (M : Finset F) (u : F) :
    scanRank e (insert u M) u = scanRank e (insert u (M.erase u)) u := by
  unfold scanRank
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
  constructor
  · rintro ⟨ha, hlt⟩
    refine ⟨?_, hlt⟩
    rcases ha with rfl | ha
    · exact Or.inl rfl
    · by_cases hau : a = u
      · exact Or.inl hau
      · exact Or.inr ⟨hau, ha⟩
  · rintro ⟨ha, hlt⟩
    refine ⟨?_, hlt⟩
    rcases ha with rfl | ⟨_, ha⟩
    · exact Or.inl rfl
    · exact Or.inr ha

/-- Pointwise node accounting in which scan costs are paid only under the gate
`u₁ ≠ 0 ∧ first extracts` — the event whose probability the pairing argument prices. -/
theorem recursiveAlgebraicForkFrom_node_runs_le_gated [Fintype F] {d m : ℕ}
    (hmk : m + (d + 1) = k) (O : T → F) (p : P) (order : Fin (Fintype.card F) ≃ F)
    (childC : F → RecursiveForkCoins F d) :
    (recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin m hmk O p
        (.node (List.ofFn (⇑order)) childC)).runs
      ≤ 1
        + (recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin (m + 1)
            (by omega) O p (childC (O (prefixes (A.run O) ⟨m, by omega⟩)))).runs
        + (if O (prefixes (A.run O) ⟨m, by omega⟩) ≠ 0 ∧
              (recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin (m + 1)
              (by omega) O p (childC (O (prefixes (A.run O) ⟨m, by omega⟩)))).output.isSome
          then
            2 * ∑ u ∈ Finset.univ.filter (fun u : F =>
                scanRank order (insert u ((goodChallenges basis k A prefixes rounds final win
                  decideWin m hmk O childC).erase (O (prefixes (A.run O) ⟨m, by omega⟩)))) u < 2),
              (scanCandidate basis k A prefixes rounds final win decideWin m hmk O childC u).runs
          else 0) := by
  by_cases hgate : O (prefixes (A.run O) ⟨m, by omega⟩) ≠ 0 ∧
      (recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin
      (m + 1) (by omega) O p (childC (O (prefixes (A.run O) ⟨m, by omega⟩)))).output.isSome
  · rw [if_pos hgate]
    exact recursiveAlgebraicForkFrom_node_runs_le basis k A prefixes rounds final win decideWin
      hmk O p order childC
  · rw [if_neg hgate]
    rw [not_and_or, not_ne_iff] at hgate
    simp only [recursiveAlgebraicForkFrom]
    split
    · simp
    · rename_i hu₁
      split
      · simp
      · rename_i c₁ hfirst
        rcases hgate with hz | hns
        · exact absurd hz hu₁
        · exact absurd (by rw [hfirst]; rfl) hns

/-- A scan candidate with an explicit reprogramming anchor, blind at that anchor. -/
def scanCandidateAt (t₀ : T) {d : ℕ} (m : ℕ) (hmk : m + (d + 1) = k) (O : T → F)
    (childC : F → RecursiveForkCoins F d) (u : F) :
    RecursiveForkAttempt (AlgebraicDForkCert (F := F) basis d) :=
  let O' := Function.update O t₀ u
  let p' := A.run O'
  if prefixes p' ⟨m, by omega⟩ = t₀ then
    recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin
      (m + 1) (by omega) O' p' (childC u)
  else { output := none, runs := 1 }

/-- Anchored at the run's actual fork prefix, the explicit-anchor candidate is the scan
candidate. -/
theorem scanCandidateAt_fork {d : ℕ} (m : ℕ) (hmk : m + (d + 1) = k) (O : T → F)
    (childC : F → RecursiveForkCoins F d) :
    scanCandidateAt basis k A prefixes rounds final win decideWin
        (prefixes (A.run O) ⟨m, by omega⟩) m hmk O childC
      = scanCandidate basis k A prefixes rounds final win decideWin m hmk O childC :=
  rfl

/-- The explicit-anchor candidate is blind at its anchor. -/
theorem scanCandidateAt_update (t₀ : T) {d : ℕ} (m : ℕ) (hmk : m + (d + 1) = k) (O : T → F)
    (x : F) (childC : F → RecursiveForkCoins F d) (u : F) :
    scanCandidateAt basis k A prefixes rounds final win decideWin t₀ m hmk
        (Function.update O t₀ x) childC u
      = scanCandidateAt basis k A prefixes rounds final win decideWin t₀ m hmk O childC u := by
  simp only [scanCandidateAt, Function.update_idem]

/-- The good set with the reprogramming anchor explicit: blind at the anchor and independent of
the anchor's table value. -/
noncomputable def goodChallengesAt (t₀ : T) {d : ℕ} (m : ℕ) (hmk : m + (d + 1) = k)
    [Fintype F] (O : T → F) (childC : F → RecursiveForkCoins F d) : Finset F :=
  Finset.univ.filter (fun u : F => u ≠ 0 ∧
    (scanCandidateAt basis k A prefixes rounds final win decideWin
      t₀ m hmk O childC u).output.isSome)

theorem goodChallengesAt_fork [Fintype F] {d : ℕ} (m : ℕ) (hmk : m + (d + 1) = k) (O : T → F)
    (childC : F → RecursiveForkCoins F d) :
    goodChallengesAt basis k A prefixes rounds final win decideWin
        (prefixes (A.run O) ⟨m, by omega⟩) m hmk O childC
      = goodChallenges basis k A prefixes rounds final win decideWin m hmk O childC := by
  ext u
  simp [goodChallengesAt, goodChallenges,
    scanCandidateAt_fork basis k A prefixes rounds final win decideWin m hmk O childC]

theorem goodChallengesAt_update [Fintype F] (t₀ : T) {d : ℕ} (m : ℕ) (hmk : m + (d + 1) = k)
    (O : T → F) (x : F) (childC : F → RecursiveForkCoins F d) :
    goodChallengesAt basis k A prefixes rounds final win decideWin t₀ m hmk
        (Function.update O t₀ x) childC
      = goodChallengesAt basis k A prefixes rounds final win decideWin t₀ m hmk O childC := by
  simp only [goodChallengesAt,
    scanCandidateAt_update basis k A prefixes rounds final win decideWin t₀ m hmk O x childC]

end GatedNode

section RankDoubleCount

variable {F : Type*} [DecidableEq F]

/-- A candidate never precedes itself: its rank against an inserted set only counts the set. -/
theorem scanRank_insert_eq_filter {n : ℕ} (e : Fin n ≃ F) (S : Finset F) (u : F) :
    scanRank e (insert u S) u = (S.filter (fun a => e.symm a < e.symm u)).card := by
  unfold scanRank
  rw [Finset.filter_insert, if_neg (lt_irrefl _)]

/-- A fixed candidate is low-rank against the punctured good set at most four orders' worth of
times, summed over punctures and sampling orders. -/
theorem sum_card_scanRank_erase_lt_le [Fintype F] (G : Finset F) (u : F) :
    ∑ x ∈ G, (Finset.univ.filter (fun order : Fin (Fintype.card F) ≃ F =>
        scanRank order (insert u ((G.erase x).erase u)) u < 2)).card
      ≤ 4 * Fintype.card (Fin (Fintype.card F) ≃ F) := by
  -- swap to per-order counting
  have hswap : ∑ x ∈ G, (Finset.univ.filter (fun order : Fin (Fintype.card F) ≃ F =>
      scanRank order (insert u ((G.erase x).erase u)) u < 2)).card
      = ∑ order : Fin (Fintype.card F) ≃ F,
          (G.filter (fun x => scanRank order (insert u ((G.erase x).erase u)) u < 2)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  rw [hswap]
  -- per-order: at most 2, plus the good set's size when u is low-rank against the full good set
  have hper : ∀ order : Fin (Fintype.card F) ≃ F,
      (G.filter (fun x => scanRank order (insert u ((G.erase x).erase u)) u < 2)).card
        ≤ 2 + (if scanRank order (insert u (G.erase u)) u < 2 then G.card else 0) := by
    intro order
    have hrank : ∀ x, scanRank order (insert u ((G.erase x).erase u)) u
        = (((G.filter (fun a => order.symm a < order.symm u)).erase u).erase x).card := by
      intro x
      rw [scanRank_insert_eq_filter, Finset.filter_erase, Finset.filter_erase,
        Finset.erase_right_comm]
    have hrank' : scanRank order (insert u (G.erase u)) u
        = ((G.filter (fun a => order.symm a < order.symm u)).erase u).card := by
      rw [scanRank_insert_eq_filter, Finset.filter_erase]
    by_cases hb : scanRank order (insert u (G.erase u)) u < 2
    · rw [if_pos hb]
      exact le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (Nat.le_add_left _ _)
    · rw [if_neg hb, Nat.add_zero]
      rw [hrank', not_lt] at hb
      by_cases hb3 : 3 ≤ ((G.filter (fun a => order.symm a < order.symm u)).erase u).card
      · -- at least three preceding goods: no puncture rescues u
        have hempty : G.filter (fun x =>
            scanRank order (insert u ((G.erase x).erase u)) u < 2) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro x _
          rw [hrank x, not_lt]
          have := Finset.pred_card_le_card_erase
            (s := (G.filter (fun a => order.symm a < order.symm u)).erase u) (a := x)
          omega
        rw [hempty]
        simp
      · -- exactly two preceding goods: the puncture must be one of them
        have hsub : G.filter (fun x =>
            scanRank order (insert u ((G.erase x).erase u)) u < 2)
            ⊆ (G.filter (fun a => order.symm a < order.symm u)).erase u := by
          intro x hx
          rw [Finset.mem_filter] at hx
          by_contra hxB
          rw [hrank x, Finset.erase_eq_self.mpr hxB] at hx
          omega
        refine le_trans (Finset.card_le_card hsub) ?_
        omega
  refine le_trans (Finset.sum_le_sum fun order _ => hper order) ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have htwo : ∑ order : Fin (Fintype.card F) ≃ F,
      (if scanRank order (insert u (G.erase u)) u < 2 then G.card else 0)
      ≤ 2 * Fintype.card (Fin (Fintype.card F) ≃ F) := by
    rw [← Finset.sum_filter]
    rw [Finset.sum_const, smul_eq_mul]
    have hmem : u ∈ insert u (G.erase u) := Finset.mem_insert_self u _
    have hcount := card_scanRank_lt_mul_le (n := Fintype.card F) (insert u (G.erase u)) hmem 2
    have hcard : G.card ≤ (insert u (G.erase u)).card := by
      rw [Finset.card_insert_of_notMem (Finset.notMem_erase u G)]
      have := Finset.pred_card_le_card_erase (s := G) (a := u)
      omega
    calc (Finset.univ.filter (fun order : Fin (Fintype.card F) ≃ F =>
            scanRank order (insert u (G.erase u)) u < 2)).card * G.card
        ≤ (Finset.univ.filter (fun order : Fin (Fintype.card F) ≃ F =>
            scanRank order (insert u (G.erase u)) u < 2)).card
            * (insert u (G.erase u)).card := Nat.mul_le_mul_left _ hcard
      _ = (insert u (G.erase u)).card
            * (Finset.univ.filter (fun order : Fin (Fintype.card F) ≃ F =>
              scanRank order (insert u (G.erase u)) u < 2)).card := Nat.mul_comm _ _
      _ ≤ 2 * Fintype.card (Fin (Fintype.card F) ≃ F) := hcount
  omega
