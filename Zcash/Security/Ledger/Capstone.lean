import Mathlib
import Zcash.Security.Ledger.Balance
import Zcash.Security.Ledger.SpendAuthority

/-!
# Probabilistic capstones

The deterministic layer quantifies over valid annotated ledgers. This layer quantifies
over a distribution of them: an adversary is an arbitrary `PMF` over `ValidAnnotated`,
and we do not model the interaction that produced it. That matches the games' stance —
the annotated-ledger quantification is a superset of what a real adversary can reach —
and it keeps the oracle bookkeeping inside the discharge of each per-arm hypothesis,
where the machine models exist.

Restricting the distribution to *valid* ledgers loses no generality. Every game's bad
event requires validity, so mass on invalid ledgers contributes nothing to success:
conditioning any adversary on validity can only increase its success probability, and
a bound for valid-only adversaries implies the bound for all of them.

Events are reduction-branch preimages: "the reduction lands in this arm on this
sample". An existential break predicate would need choice to extract data from; the
branch of a computed reduction needs none. The composition is pure event algebra — the
violation event is contained in the union of the arm events, so its probability is at
most the sum of the per-arm probabilities (`measure_mono` plus `measure_union_le`).
No independence, no counting. Each arm's probability is then bounded by a named ε
hypothesis. The key-binding arm's ε is discharged in `KeyBindingArm.lean` against the
key-binding layer's probability bound (`toInterface_break_measure_le`), for a ledger
adversary in the oracle model. Connecting that bound to this layer's named-ε slot — an
oracle machine against a `PMF` over valid annotated ledgers — is still open, as are the
Merkle and note-commitment arms (against Sinsemilla/DLR hardness).
-/

namespace Zcash.Security.Ledger.Model

open scoped ENNReal

variable {F : Type*}
variable {G : Type*}
variable {IVK NK RHO PSI MHASH MENC MSG SIG : Type*} {KW : Type*}

/-! ## Event algebra -/

/-- Union bound over two events: an event contained in a union is bounded by the sum
of the two measures. -/
theorem toOuterMeasure_le_add₂ {α : Type*} (p : PMF α) {E B₁ B₂ : Set α}
    (h : E ⊆ B₁ ∪ B₂) :
    p.toOuterMeasure E ≤ p.toOuterMeasure B₁ + p.toOuterMeasure B₂ :=
  le_trans (MeasureTheory.measure_mono h) (MeasureTheory.measure_union_le _ _)

/-- Union bound over three events: an event contained in a triple union is bounded by
the sum of the three measures. -/
theorem toOuterMeasure_le_add₃ {α : Type*} (p : PMF α) {E B₁ B₂ B₃ : Set α}
    (h : E ⊆ B₁ ∪ B₂ ∪ B₃) :
    p.toOuterMeasure E
      ≤ p.toOuterMeasure B₁ + p.toOuterMeasure B₂ + p.toOuterMeasure B₃ :=
  le_trans (MeasureTheory.measure_mono h)
    (le_trans (MeasureTheory.measure_union_le _ _)
      (add_le_add (MeasureTheory.measure_union_le _ _) le_rfl))

section Validity

variable [Field F] [AddCommGroup G] [Module F G]
variable {P : Primitives F G IVK NK RHO PSI MHASH MENC MSG SIG}
variable {kv : KeyBindingInterface KW G IVK NK}
variable {issuance : ℕ → ℕ} {maxActions : ℕ}

variable (P kv issuance maxActions) in
/-- The adversary's sample space: a valid witness-annotated ledger, with its validity
proof. Bundling validity is a convenience, not a restriction — a bad event requires
validity, so conditioning any distribution on validity can only increase its success
probability, and a bound over this space implies the bound over bare ledgers. -/
abbrev ValidAnnotated :=
  {ledger : Ledger KW F G RHO PSI MHASH MENC MSG SIG P.depth //
    ValidLedger P kv issuance maxActions ledger}

/-! ## Balance-value -/

/-- The value-premiss arm event: the samples on which the per-transaction value
premiss hands the conservation reduction a break of the abstract type `VB`. -/
def valueBreakEvent {VB : Type*}
    (perTx : ∀ ω : ValidAnnotated P kv issuance maxActions,
      (tx : Tx KW F G RHO PSI MHASH MENC MSG SIG P.depth) → tx ∈ ω.1 →
        (txNetValue tx = tx.vBalance) ⊕' VB) (i : ℕ) :
    Set (ValidAnnotated P kv issuance maxActions) :=
  {ω | ∃ b : VB, valueConservationOrBreak (issuance := issuance) (perTx ω) i = .inr b}

/-- The value-conservation violation event: the shielded pool plus the transparent
pool differs from the minted issuance after the first `i` transactions. -/
def valueConservationViolation (i : ℕ) :
    Set (ValidAnnotated P kv issuance maxActions) :=
  {ω | poolValueBalance ω.1 i + transparentPoolBalance issuance ω.1 i
    ≠ issuanceTotal issuance ω.1 i}

/-- The Balance-value violation event: the shielded pool exceeds the minted issuance
after the first `i` transactions. -/
def balanceValueViolation (i : ℕ) :
    Set (ValidAnnotated P kv issuance maxActions) :=
  {ω | ¬ poolValueBalance ω.1 i ≤ issuanceTotal issuance ω.1 i}

/-- A conservation-violating sample lands in the value-premiss arm: on it, the
conservation reduction cannot return the equation. -/
theorem valueConservationViolation_subset {VB : Type*}
    (perTx : ∀ ω : ValidAnnotated P kv issuance maxActions,
      (tx : Tx KW F G RHO PSI MHASH MENC MSG SIG P.depth) → tx ∈ ω.1 →
        (txNetValue tx = tx.vBalance) ⊕' VB) (i : ℕ) :
    valueConservationViolation (P := P) (kv := kv) (maxActions := maxActions) i
      ⊆ valueBreakEvent perTx i := by
  intro ω hω
  rcases h : valueConservationOrBreak (issuance := issuance) (perTx ω) i with heq | b
  · exact absurd heq hω
  · exact ⟨b, h⟩

/-- A balance-violating sample lands in the value-premiss arm too: if the reduction
returned the conservation equation, transparent nonnegativity would force the bound. -/
theorem balanceValueViolation_subset {VB : Type*}
    (perTx : ∀ ω : ValidAnnotated P kv issuance maxActions,
      (tx : Tx KW F G RHO PSI MHASH MENC MSG SIG P.depth) → tx ∈ ω.1 →
        (txNetValue tx = tx.vBalance) ⊕' VB) (i : ℕ) :
    balanceValueViolation (P := P) (kv := kv) (maxActions := maxActions) i
      ⊆ valueBreakEvent perTx i := by
  intro ω hω
  rcases h : valueConservationOrBreak (issuance := issuance) (perTx ω) i with heq | b
  · exact absurd (by have := ω.2.transparent_nonneg i; omega) hω
  · exact ⟨b, h⟩

/-- **Value conservation, probabilistically.** For any adversary, the probability that
the value ledger fails to balance is at most the value-premiss arm's ε. -/
theorem valueConservation_measure_le {VB : Type*}
    (A : PMF (ValidAnnotated P kv issuance maxActions))
    (perTx : ∀ ω : ValidAnnotated P kv issuance maxActions,
      (tx : Tx KW F G RHO PSI MHASH MENC MSG SIG P.depth) → tx ∈ ω.1 →
        (txNetValue tx = tx.vBalance) ⊕' VB) (i : ℕ) {εvb : ℝ≥0∞}
    (hvb : A.toOuterMeasure (valueBreakEvent perTx i) ≤ εvb) :
    A.toOuterMeasure (valueConservationViolation i) ≤ εvb :=
  le_trans (MeasureTheory.measure_mono (valueConservationViolation_subset perTx i)) hvb

/-- **Balance-value, probabilistically.** For any adversary, the probability that the
shielded pool exceeds the minted issuance is at most the value-premiss arm's ε. -/
theorem balanceValue_measure_le {VB : Type*}
    (A : PMF (ValidAnnotated P kv issuance maxActions))
    (perTx : ∀ ω : ValidAnnotated P kv issuance maxActions,
      (tx : Tx KW F G RHO PSI MHASH MENC MSG SIG P.depth) → tx ∈ ω.1 →
        (txNetValue tx = tx.vBalance) ⊕' VB) (i : ℕ) {εvb : ℝ≥0∞}
    (hvb : A.toOuterMeasure (valueBreakEvent perTx i) ≤ εvb) :
    A.toOuterMeasure (balanceValueViolation i) ≤ εvb :=
  le_trans (MeasureTheory.measure_mono (balanceValueViolation_subset perTx i)) hvb

/-! ## Balance-subset -/

/-- The three arms of a `BalanceBreak`, as a plain tag for naming the arm events. -/
inductive BalanceArm
  | merkle
  | noteCommit
  | keyBinding

/-- The arm a break lies in. -/
def BalanceBreak.arm : BalanceBreak P kv → BalanceArm
  | .merkle _ => .merkle
  | .noteCommit _ => .noteCommit
  | .keyBinding _ _ _ => .keyBinding

section BalanceSubset

variable [DecidableEq F] [DecidableEq G] [DecidableEq RHO] [DecidableEq PSI]
  [DecidableEq MHASH] [DecidableEq MENC] [DecidableEq NK] [NoZeroSMulDivisors F G]

/-- The branch-preimage event for one arm: the samples on which the Balance-subset
reduction lands in that arm. -/
def balanceSubsetBreakEvent (i : ℕ) (arm : BalanceArm) :
    Set (ValidAnnotated P kv issuance maxActions) :=
  {ω | ∃ b : BalanceBreak P kv, balanceSubsetOrBreak ω.2 i = .inr b ∧ b.arm = arm}

/-- The Balance-subset violation event: the nonzero spends of the first `i + 1`
transactions are not covered by the positioned outputs of the first `i`. -/
def balanceSubsetViolation (i : ℕ) : Set (ValidAnnotated P kv issuance maxActions) :=
  {ω | ¬ nonZeroSpends ω.1 (i + 1) ≤ ↑(positionedOutputs ω.1 i)}

/-- A violating sample lands in one of the three arms: on it, the reduction cannot
return the subset proof, so it returns a break, and the break's arm classifies it. -/
theorem balanceSubsetViolation_subset (i : ℕ) :
    balanceSubsetViolation (P := P) (kv := kv) (issuance := issuance)
        (maxActions := maxActions) i
      ⊆ balanceSubsetBreakEvent i .merkle ∪ balanceSubsetBreakEvent i .noteCommit
        ∪ balanceSubsetBreakEvent i .keyBinding := by
  intro ω hω
  rcases h : balanceSubsetOrBreak ω.2 i with hle | b
  · exact absurd hle hω
  · cases b with
    | merkle c => exact Or.inl (Or.inl ⟨_, h, rfl⟩)
    | noteCommit nb => exact Or.inl (Or.inr ⟨_, h, rfl⟩)
    | keyBinding w₁ w₂ hbr => exact Or.inr ⟨_, h, rfl⟩

/-- **Balance-subset, probabilistically.** For any adversary — a distribution over
valid annotated ledgers — the probability that the nonzero spends of the first `i + 1`
transactions are not covered by the positioned outputs of the first `i` is at most the
sum of the three break-arm probabilities, each bounded by its named ε hypothesis. -/
theorem balanceSubset_measure_le (A : PMF (ValidAnnotated P kv issuance maxActions))
    (i : ℕ) {εm εnc εkb : ℝ≥0∞}
    (hm : A.toOuterMeasure (balanceSubsetBreakEvent i .merkle) ≤ εm)
    (hnc : A.toOuterMeasure (balanceSubsetBreakEvent i .noteCommit) ≤ εnc)
    (hkb : A.toOuterMeasure (balanceSubsetBreakEvent i .keyBinding) ≤ εkb) :
    A.toOuterMeasure (balanceSubsetViolation i) ≤ εm + εnc + εkb :=
  le_trans (toOuterMeasure_le_add₃ A (balanceSubsetViolation_subset i))
    (add_le_add (add_le_add hm hnc) hkb)

end BalanceSubset

/-! ## Spend Authority -/

section SpendAuthority

variable [DecidableEq G] [NoZeroSMulDivisors F G]

/-- The forgery arm event, for a victim key witness `wV` with signing history
`Signed`: the samples with an Action spending a note addressed to `wV` in a
transaction with an unsigned sighash, on which the Spend Authority reduction lands in
the forgery arm. -/
def spendAuthorityForgeryEvent (wV : KW) (hKB : kv.KB wV) (Signed : MSG → Prop) :
    Set (ValidAnnotated P kv issuance maxActions) :=
  {ω | ∃ tx, ∃ htx : tx ∈ ω.1, ∃ a, ∃ ha : a ∈ tx.actions,
    ∃ hrecv : a.w.note_old.pkd = P.emb (kv.ivk wV) • a.w.note_old.gd,
    ∃ hfresh : ¬ Signed tx.sighash, ∃ f,
    spendAuthorityOrBreak ω.2 htx ha hKB hrecv hfresh = .inl f}

/-- The key-binding arm event: as `spendAuthorityForgeryEvent`, with the reduction
landing in the break arm. -/
def spendAuthorityBreakEvent (wV : KW) (hKB : kv.KB wV) (Signed : MSG → Prop) :
    Set (ValidAnnotated P kv issuance maxActions) :=
  {ω | ∃ tx, ∃ htx : tx ∈ ω.1, ∃ a, ∃ ha : a ∈ tx.actions,
    ∃ hrecv : a.w.note_old.pkd = P.emb (kv.ivk wV) • a.w.note_old.gd,
    ∃ hfresh : ¬ Signed tx.sighash, ∃ b,
    spendAuthorityOrBreak ω.2 htx ha hKB hrecv hfresh = .inr b}

/-- The Spend Authority violation event: some Action spends a note addressed to `wV`
in a transaction whose sighash the holder of `wV` never signed. -/
def spendAuthorityViolation (wV : KW) (Signed : MSG → Prop) :
    Set (ValidAnnotated P kv issuance maxActions) :=
  {ω | ∃ tx ∈ ω.1, ∃ a ∈ tx.actions,
    a.w.note_old.pkd = P.emb (kv.ivk wV) • a.w.note_old.gd ∧ ¬ Signed tx.sighash}

/-- A violating sample lands in the forgery arm or the break arm: the reduction runs
on the violating Action, and its branch classifies the sample. -/
theorem spendAuthorityViolation_subset (wV : KW) (hKB : kv.KB wV)
    (Signed : MSG → Prop) :
    spendAuthorityViolation (P := P) (kv := kv) (issuance := issuance)
        (maxActions := maxActions) wV Signed
      ⊆ spendAuthorityForgeryEvent wV hKB Signed ∪ spendAuthorityBreakEvent wV hKB Signed := by
  rintro ω ⟨tx, htx, a, ha, hrecv, hfresh⟩
  rcases h : spendAuthorityOrBreak ω.2 htx ha hKB hrecv hfresh with f | b
  · exact Or.inl ⟨tx, htx, a, ha, hrecv, hfresh, f, h⟩
  · exact Or.inr ⟨tx, htx, a, ha, hrecv, hfresh, b, h⟩

/-- **Spend Authority, probabilistically.** For any adversary, the probability that
some Action spends a note addressed to `wV` over an unsigned sighash is at most the
forgery arm's ε plus the key-binding arm's ε. -/
theorem spendAuthority_measure_le (A : PMF (ValidAnnotated P kv issuance maxActions))
    (wV : KW) (hKB : kv.KB wV) (Signed : MSG → Prop) {εf εkb : ℝ≥0∞}
    (hf : A.toOuterMeasure (spendAuthorityForgeryEvent wV hKB Signed) ≤ εf)
    (hkb : A.toOuterMeasure (spendAuthorityBreakEvent wV hKB Signed) ≤ εkb) :
    A.toOuterMeasure (spendAuthorityViolation wV Signed) ≤ εf + εkb :=
  le_trans (toOuterMeasure_le_add₂ A (spendAuthorityViolation_subset wV hKB Signed))
    (add_le_add hf hkb)

end SpendAuthority

end Validity

end Zcash.Security.Ledger.Model
