import Mathlib
import Zcash.Security.Ledger.Balance
import Zcash.Security.BindingSignature.Balance

-- This lint enforces Mathlib's minimal-hypothesis style, from which we deliberately depart.
set_option linter.unusedSectionVars false

/-!
# The value-premiss discharge at the Pedersen shape

Balance-value's per-transaction premiss — the witnessed net value matches the declared
`vBalance`, or a break of the abstract type `VB` is exhibited — is discharged here
against the binding-signature layer, with `VB` concretely the nontrivial `(V, R)`
discrete-log relation.

`ValueShape` is the Pedersen shape of the value commitment over the scalar field
`ZMod r`: `ValueCommit_rcv(v) = v • V + rcv • R` for fixed independent bases `V` and
`R` (𝒱^Orchard and ℛ^Orchard at the intended instantiation). The shape is that of the
deployed construction, but the bases stay abstract — the concrete Pallas
instantiation (Sinsemilla-derived bases, RedDSA on Pallas) is deferred, per the
abstract-route plan. On a statement-satisfying transaction the model's
binding verification key `Tx.bvk` — the sum of the actions' `cv_net`s minus a
zero-randomness commitment to `vBalance` — is then the binding-signature layer's
`bindingVK` of the witnessed bundle (`bvk_eq`, via `cv_net_eq`).

`ValueShape.premissOrBreak` produces the premiss: it decides the net-value equation, and on
failure computes the relation with `NontrivialRelation.ofBundleIntImbalance`. Its
no-overflow bound comes from the statement's value ranges, validity's action count and
`vBalance` range, and one numeric hypothesis `(maxActions + 1) * valueBound ≤ r`
(deployed: `(maxActions + 1) · 2^64 ≪ r ≈ 2^254`). The extraction input — `bvk` is a
known multiple of `R` — is the function-typed named form of RedDSA extractability
(`extractBsk`/`hextract`), applied to validity's binding-signature conjunct. The total
form carries no computational content on its own: in a cyclic group every `bvk` is some
multiple of `R`, so a total `hextract` holds for a choose-the-witness `extractBsk` no one
can run. It stands in for the forking extractor with a knowledge error — an `extractBsk`
efficient against a binding-signature forger, delivering the relation only with the
extractor's success probability. Proving it by forking is #22's scope (#107/#67 track the
restructuring into the knowledge-error form).

`ValueShape.balanceOrBreak` and `ValueShape.conservationOrBreak` compose
the premiss into the Balance-value capstones: the shielded pool exceeding the minted
issuance (or the value ledger failing to balance) computes a nontrivial `(V, R)`
relation.
-/

namespace Zcash.Security.Ledger.Model

open Zcash.Security.BindingSignature

variable {r : ℕ} [Fact (Nat.Prime r)]
variable {G : Type*} [AddCommGroup G] [Module (ZMod r) G]
variable {IVK NK RHO PSI MHASH MENC MSG SIG : Type*} {KW : Type*} {d : ℕ}
variable {P : Primitives (ZMod r) G IVK NK RHO PSI MHASH MENC MSG SIG}
variable {kv : KeyBindingInterface KW G IVK NK}

/-- The Pedersen shape of the value commitment, over the scalar field `ZMod r`:
`ValueCommit_rcv(v) = v • V + rcv • R` for fixed independent bases `V` and `R`
(𝒱^Orchard and ℛ^Orchard at the intended instantiation). -/
structure ValueShape (P : Primitives (ZMod r) G IVK NK RHO PSI MHASH MENC MSG SIG) where
  V : G
  R : G
  commit_eq : ∀ (v : ℤ) (rcv : ZMod r),
    P.valueCommit v rcv = (v : ZMod r) • V + rcv • R

/-- A transaction's witnessed integer bundle: per action, the net value it releases
and its commitment randomness. -/
def txBundle (tx : Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG d) : List (ℤ × ZMod r) :=
  tx.actions.map fun a => ((a.w.note_old.v : ℤ) - a.w.note_new.v, a.w.rcv)

/-- The bundle's value sum is the transaction's witnessed net value. -/
theorem txBundle_fst_sum (tx : Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG d) :
    ((txBundle tx).map Prod.fst).sum = txNetValue tx := by
  simp [txBundle, txNetValue, List.map_map, Function.comp_def]

/-- On a statement-satisfying transaction, the model's binding verification key is the
binding-signature layer's `bindingVK` of the witnessed bundle. -/
theorem bvk_eq (S : ValueShape P)
    {tx : Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P.depth}
    (hsat : ∀ a ∈ tx.actions, ActionSatisfied P kv a.inst a.w) :
    tx.bvk P
      = bindingVK S.V S.R (castBundle (txBundle tx)) [] (tx.vBalance : ZMod r) := by
  have hsum : (tx.actions.map fun a => a.inst.cv_net).sum
      = ((castBundle (txBundle tx)).map fun p => valueCommit S.V S.R p.1 p.2).sum := by
    simp only [castBundle, txBundle, List.map_map]
    refine congrArg List.sum (List.map_congr_left fun a ha => ?_)
    rw [Function.comp_apply, Function.comp_apply, (hsat a ha).cv_net_eq, S.commit_eq]
    rfl
  have hvb : P.valueCommit tx.vBalance 0 = (tx.vBalance : ZMod r) • S.V := by
    rw [S.commit_eq]
    simp
  rw [Tx.bvk, bindingVK, hsum, hvb]
  simp

/-- The witnessed net value of a satisfied transaction is bounded by the action count
times the value bound. -/
theorem txNetValue_natAbs_le
    {tx : Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P.depth}
    (hsat : ∀ a ∈ tx.actions, ActionSatisfied P kv a.inst a.w) :
    (txNetValue tx).natAbs ≤ tx.actions.length * P.valueBound := by
  suffices h : ∀ L : List (Action KW (ZMod r) G RHO PSI MHASH MENC SIG P.depth),
      (∀ a ∈ L, ActionSatisfied P kv a.inst a.w) →
      ((L.map fun x => (x.w.note_old.v : ℤ) - x.w.note_new.v).sum).natAbs
        ≤ L.length * P.valueBound by
    exact h tx.actions hsat
  intro L hL
  induction L with
  | nil => simp
  | cons a t ih =>
      have h1 : ((a.w.note_old.v : ℤ) - a.w.note_new.v).natAbs ≤ P.valueBound := by
        have hv1 := (hL a (by simp)).v_old_lt
        have hv2 := (hL a (by simp)).v_new_lt
        omega
      have h2 := ih fun x hx => hL x (by simp [hx])
      calc (((a :: t).map fun x => (x.w.note_old.v : ℤ) - x.w.note_new.v).sum).natAbs
          ≤ ((a.w.note_old.v : ℤ) - a.w.note_new.v).natAbs
            + ((t.map fun x => (x.w.note_old.v : ℤ) - x.w.note_new.v).sum).natAbs := by
            simp only [List.map_cons, List.sum_cons]
            exact Int.natAbs_add_le _ _
        _ ≤ P.valueBound + t.length * P.valueBound := Nat.add_le_add h1 h2
        _ = (a :: t).length * P.valueBound := by
            simp only [List.length_cons]
            ring

/-- **The value-premiss discharge.** Decide the per-transaction net-value equation;
on failure, compute the nontrivial `(V, R)` relation from the witnessed bundle. The
no-overflow bound is discharged from the statement's value ranges and validity's
action-count and `vBalance` range rules; the extraction input applies the named
RedDSA-extractability form (`extractBsk`/`hextract`) to validity's binding-signature
conjunct. `hextract` is a placeholder, not a theorem: as a total hypothesis it is
classically satisfiable, computational only relative to an efficient `extractBsk` (see
the module doc). -/
def ValueShape.premissOrBreak {issuance : ℕ → ℕ} {maxActions : ℕ}
    {ledger : Ledger KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P.depth}
    (S : ValueShape P)
    (hval : ValidLedger P kv issuance maxActions ledger)
    (hr : (maxActions + 1) * P.valueBound ≤ r)
    (extractBsk : G → MSG → SIG → ZMod r)
    (hextract : ∀ bvk msg sig, P.bindingVerify bvk msg sig
      → bvk = extractBsk bvk msg sig • S.R)
    (tx : Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P.depth) (htx : tx ∈ ledger) :
    (txNetValue tx = tx.vBalance) ⊕' BindingSignature.NontrivialRelation (F := ZMod r) S.V S.R :=
  if heq : txNetValue tx = tx.vBalance then .inl heq
  else
    .inr (NontrivialRelation.ofBundleIntImbalance S.V S.R (txBundle tx) [] tx.vBalance
      (extractBsk (tx.bvk P) tx.sighash tx.bindingSig)
      (by
        simp only [List.map_nil, List.sum_nil, sub_zero, txBundle_fst_sum]
        exact sub_ne_zero.mpr heq)
      (by
        simp only [List.map_nil, List.sum_nil, sub_zero, txBundle_fst_sum]
        have h1 := txNetValue_natAbs_le (P := P) (kv := kv) (hval.satisfied tx htx)
        have h2 := hval.vbalance_bound tx htx
        have hb : tx.actions.length * P.valueBound ≤ maxActions * P.valueBound :=
          Nat.mul_le_mul_right _ (hval.action_bound tx htx)
        calc (txNetValue tx - tx.vBalance).natAbs
            ≤ (txNetValue tx).natAbs + tx.vBalance.natAbs := Int.natAbs_sub_le _ _
          _ < maxActions * P.valueBound + P.valueBound :=
              Nat.add_lt_add_of_le_of_lt (le_trans h1 hb) h2
          _ = (maxActions + 1) * P.valueBound := by ring
          _ ≤ r := hr)
      ((bvk_eq S (hval.satisfied tx htx)).symm.trans
        (hextract _ _ _ (hval.binding_verified tx htx))))

/-- **Value conservation at the Pedersen shape.** The value ledger failing to balance
computes a nontrivial `(V, R)` relation. -/
def ValueShape.conservationOrBreak {issuance : ℕ → ℕ} {maxActions : ℕ}
    {ledger : Ledger KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P.depth}
    (S : ValueShape P)
    (hval : ValidLedger P kv issuance maxActions ledger)
    (hr : (maxActions + 1) * P.valueBound ≤ r)
    (extractBsk : G → MSG → SIG → ZMod r)
    (hextract : ∀ bvk msg sig, P.bindingVerify bvk msg sig
      → bvk = extractBsk bvk msg sig • S.R) (i : ℕ) :
    (poolValueBalance ledger i + transparentPoolBalance issuance ledger i
        = issuanceTotal issuance ledger i)
      ⊕' BindingSignature.NontrivialRelation (F := ZMod r) S.V S.R :=
  valueConservationOrBreak (S.premissOrBreak hval hr extractBsk hextract) i

/-- **Balance-value at the Pedersen shape.** The shielded pool exceeding the minted
issuance computes a nontrivial `(V, R)` relation — the Balance-value chain composed,
with the abstract `VB` instantiated at the shape level. -/
def ValueShape.balanceOrBreak {issuance : ℕ → ℕ} {maxActions : ℕ}
    {ledger : Ledger KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P.depth}
    (S : ValueShape P)
    (hval : ValidLedger P kv issuance maxActions ledger)
    (hr : (maxActions + 1) * P.valueBound ≤ r)
    (extractBsk : G → MSG → SIG → ZMod r)
    (hextract : ∀ bvk msg sig, P.bindingVerify bvk msg sig
      → bvk = extractBsk bvk msg sig • S.R) (i : ℕ) :
    (poolValueBalance ledger i ≤ issuanceTotal issuance ledger i)
      ⊕' BindingSignature.NontrivialRelation (F := ZMod r) S.V S.R :=
  balanceValueOrBreak hval (S.premissOrBreak hval hr extractBsk hextract) i

end Zcash.Security.Ledger.Model
