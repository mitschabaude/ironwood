import Zcash.Security.Ledger.Bridge
import Zcash.Security.Ledger.SinsemillaDLR
import Zcash.Meta.AxiomCheck

/-!
# Regression checks for the Action-to-ledger boundary

These small theorems intentionally exercise the protocol distinctions that are
easy to erase in a type-correct refinement: signed value semantics, scalar
randomization, raw (rather than reduced-field) Merkle encodings, the dummy-spend
Merkle guard, and the three-valued cross-address flag behaviour.
-/

namespace Zcash.Security.Ledger.BridgeTests

open Zcash.Circuits
open Zcash.Circuits.Action
open Zcash.Circuits.Action.Circuit
open Zcash.Circuits.Specs.Sinsemilla
open Zcash.Security.Concrete
open Zcash.Security.Ledger
open Zcash.Security.Ledger.Pool
open Zcash.Security.Ledger.Bridge
open CompElliptic.Fields.Pasta (PALLAS_BASE_CARD)
open Halo2

/-- The ordinary positive signed-magnitude direction has the ledger integer meaning. -/
theorem value_positive {vOld vNew magnitude : Fp}
    (hvNew : vNew.val < 2 ^ 64)
    (hMagnitude : magnitude.val < 2 ^ 64)
    (h : vOld - vNew = magnitude) :
    (vOld.val : ℤ) - (vNew.val : ℤ) = (magnitude.val : ℤ) :=
  int_sub_eq_of_fp_sub_eq hvNew hMagnitude h

/-- The negative direction reverses the bounded subtraction without field wraparound. -/
theorem value_negative {vOld vNew magnitude : Fp}
    (hvOld : vOld.val < 2 ^ 64)
    (hMagnitude : magnitude.val < 2 ^ 64)
    (h : vOld - vNew = -magnitude) :
    (vOld.val : ℤ) - (vNew.val : ℤ) = -(magnitude.val : ℤ) := by
  have hrev : vNew - vOld = magnitude := by
    linear_combination -h
  have h' := int_sub_eq_of_fp_sub_eq hvOld hMagnitude hrev
  omega

/-- Equal bounded field values have equal integer representatives. -/
theorem value_equal {vOld vNew : Fp}
    (hvNew : vNew.val < 2 ^ 64) (h : vOld - vNew = 0) :
    (vOld.val : ℤ) - (vNew.val : ℤ) = 0 := by
  simpa using int_sub_eq_of_fp_sub_eq hvNew (by simp) h

/-- The public-key randomizer uses the full `Fq` scalar, not its base-field value. -/
theorem alpha_scaling (α : Fq) (ak : PallasGroup) :
    PallasGroup.toPoint (randomizePublic α ak) =
      α.val • Ecc.MulFixed.Certs.spendAuthG.point + PallasGroup.toPoint ak :=
  toPoint_randomizePublic α ak

/-- Positive integer values use the circuit's canonical `Fq` magnitude scalar. -/
theorem value_commit_positive_scaling (magnitude : ℕ) (rcv : Fq) :
    PallasGroup.toPoint (valueCommit ((magnitude : ℤ)) rcv) =
      (magnitude : Fq).val • Ecc.MulFixed.Certs.valueCommitV.point +
        rcv.val • Ecc.MulFixed.Certs.valueCommitR.point := by
  simpa [intScalar] using toPoint_valueCommit (magnitude : ℤ) rcv

/-- Negative integer values use the circuit's negative scalar representation. -/
theorem value_commit_negative_scaling (magnitude : ℕ) (rcv : Fq) :
    PallasGroup.toPoint (valueCommit (-(magnitude : ℤ)) rcv) =
      (-(magnitude : Fq)).val • Ecc.MulFixed.Certs.valueCommitV.point +
        rcv.val • Ecc.MulFixed.Certs.valueCommitR.point := by
  simpa [intScalar] using toPoint_valueCommit (-(magnitude : ℤ)) rcv

/-- Two legal 255-bit representations of zero in `Fp`: the canonical one and one
reduced modulo the Pallas base modulus. -/
def canonicalZero : Encoding := ⟨0, by norm_num⟩

def noncanonicalZero : Encoding := ⟨PALLAS_BASE_CARD, by
  norm_num [PALLAS_BASE_CARD]⟩

theorem zero_encodings_distinct : canonicalZero ≠ noncanonicalZero := by
  intro h
  have hval := congrArg Subtype.val h
  norm_num [canonicalZero, noncanonicalZero, PALLAS_BASE_CARD] at hval

theorem zero_encodings_decode_equal :
    decode canonicalZero = decode noncanonicalZero := by
  change (0 : Fp) = (PALLAS_BASE_CARD : Fp)
  exact (ZMod.natCast_self PALLAS_BASE_CARD).symm

/-- The dummy-spend condition makes the ledger Merkle premise vacuous.  This is
the exact conditional in `ActionSatisfied`, so a bridge must not demand a path
when the spent note has value zero. -/
theorem dummy_spend_merkle_vacuous
    {F G IVK NK RHO PSI MHASH MENC MSG SIG KW : Type*}
    [Field F] [AddCommGroup G] [Module F G]
    {P : Primitives F G IVK NK RHO PSI MHASH MENC MSG SIG}
    {inst : ActionInstance G MHASH RHO}
    {w : ActionWitness KW F G RHO PSI MHASH MENC P.depth}
    (hzero : w.note_old.v = 0) :
    w.note_old.v ≠ 0 →
      Merkle.Path P.merkle (P.extract w.cm_old) inst.rt w.path w.side := by
  simp [hzero]

/-- Path validity now certifies per-layer definedness: no escaped compression can occur
inside a valid path.  This is the guarantee that distinguishes the partial
(`Option`-valued) compressor from a totalized one, and it is recoverable directly from the
`Merkle.Path` fact rather than a separate bridge invariant. -/
theorem path_layers_defined
    {B E : Type*} {P : Merkle.MerklePrimitives B E} {leaf root : B}
    {children : Fin P.depth → E × E} {side : Fin P.depth → Bool}
    (h : Merkle.Path P leaf root children side) (i : Fin P.depth) :
    ∃ b, P.compress i (children i) = some b :=
  Merkle.Path.compress_isSome h i

/-- Flag zero leaves the post-NU6.3 address condition inert. -/
theorem cross_address_flag_zero (wit : ActionData) (w : LedgerWitness)
    (hzero : wit.disableCrossAddress = 0) : CrossAddressSatisfied wit w := by
  intro h
  exact False.elim (h hzero)

/-- Flag one activates the exact old/new address equality obligation. -/
theorem cross_address_flag_one (wit : ActionData) (w : LedgerWitness)
    (_hone : wit.disableCrossAddress = 1)
    (haddr : w.note_old.gd = w.note_new.gd ∧ w.note_old.pkd = w.note_new.pkd) :
    CrossAddressSatisfied wit w := fun _ => haddr

/-- Any nonzero field flag, not only one, activates that same obligation. -/
theorem cross_address_flag_arbitrary_nonzero (wit : ActionData) (w : LedgerWitness)
    (_henabled : wit.disableCrossAddress ≠ 0)
    (haddr : w.note_old.gd = w.note_new.gd ∧ w.note_old.pkd = w.note_new.pkd) :
    CrossAddressSatisfied wit w := fun _ => haddr

/-- A disabled spend flag (any value other than one), together with the exported
`EnableFlagsSatisfied` side fact, forces the spent note value to zero. -/
theorem enable_spend_disabled_forces_zero (wit : ActionData) (w : LedgerWitness)
    (hdis : wit.enableSpend ≠ 1) (h : EnableFlagsSatisfied wit w) :
    w.note_old.v = 0 := by
  by_contra hv
  exact hdis (h.1 hv)

/-- A disabled output flag likewise forces the output note value to zero. -/
theorem enable_output_disabled_forces_zero (wit : ActionData) (w : LedgerWitness)
    (hdis : wit.enableOutput ≠ 1) (h : EnableFlagsSatisfied wit w) :
    w.note_new.v = 0 := by
  by_contra hv
  exact hdis (h.2 hv)

/-- The or-break disjunction is provably no stronger than the guarded ⊥-model
export: the named equivalence, instantiated at the deployed `Commit^ivk` domain
point.  This is the audit point for the exported-spec/reduction split. -/
theorem or_break_iff_guarded_smoke (wit : ActionData) (P : Point Fp → Prop) :
    SpecOrBreak orchardGenerators.S orchardBases.ivkQ P
        (hashToPointB orchardGenerators.S orchardBases.ivkQ (ivkQuery wit)) ↔
      HashGuarded orchardGenerators.S orchardBases.ivkQ (ivkQuery wit) P :=
  specOrBreak_hashToPointB_iff_guarded (Or.inl orchardBases.ivkQ_onCurve)
    (fun _ hm => orchardGenerators.S_onCurve (chunksOf_mem_lt hm))

/-- The strict/guarded Merkle split is lossless: the named equivalence, instantiated
at the deployed pool's compression.  This is the Merkle-side audit point mirroring
`or_break_iff_guarded_smoke` for the Sinsemilla or-break/guarded split. -/
theorem path_iff_guarded_smoke
    (leaf root : Fp) (children : Fin Pool.merkle.depth → Pool.Encoding × Pool.Encoding)
    (side : Fin Pool.merkle.depth → Bool) :
    Merkle.Path Pool.merkle leaf root children side ↔
      Merkle.GuardedPath Pool.merkle leaf root children side ∧
        ∀ i, ∃ b, Pool.merkle.compress i (children i) = some b :=
  Merkle.path_iff_guarded_defined

/-- The circuit-level postcondition refines directly to the ledger action alternative. -/
theorem spec_post_bridge_smoke {MSG SIG : Type*}
    (verify bverify : PallasGroup → MSG → SIG → Prop)
    {input : Halo2.Value PrivateInputs Fp} {wit : ActionData}
    (h : SpecPost orchardGenerators orchardBases input () wit) :
    ActionBreak wit ∨
      ∃ inst w, PublicProjection wit inst ∧
        ActionSatisfied (Pool.primitives verify bverify) Pool.keyBinding inst w ∧
        CrossAddressSatisfied wit w ∧
        EnableFlagsSatisfied wit w :=
  specPost_to_ledger verify bverify h

/-- Keep the exported end-to-end soundness theorem at its intended public shape. -/
open Zcash.Meta


-- The circuit-to-ledger reduction is a computation: a plain `def`, compiled by
-- the Lean compiler — so `Classical.choice` cannot contribute to the computed
-- break data.  The `+choice` allowance is forced by Mathlib's `ZMod` instances:
-- even the deployed constants (`Action.ivkQ` is a bare point literal) carry
-- `Classical.choice` inside erased `Prop` proof fields of the numeral and
-- field-arithmetic instances.  The plain-`def` check is what certifies that
-- choice stays erased: had it touched the data path, the definition could not
-- have compiled (`Zcash.Meta.AxiomCheck` documents this convention).
assert_computable Zcash.Security.Ledger.Bridge.classifyMerkle +choice
assert_computable Zcash.Security.Ledger.Bridge.classifyAction +choice

assert_axioms Zcash.Security.Ledger.BridgeTests.value_positive
assert_axioms Zcash.Security.Ledger.BridgeTests.value_negative
assert_axioms Zcash.Security.Ledger.BridgeTests.value_equal
assert_axioms Zcash.Security.Ledger.BridgeTests.zero_encodings_distinct
assert_axioms Zcash.Security.Ledger.BridgeTests.zero_encodings_decode_equal
assert_axioms Zcash.Security.Ledger.BridgeTests.dummy_spend_merkle_vacuous
assert_axioms Zcash.Security.Ledger.BridgeTests.path_layers_defined
assert_axioms Zcash.Security.Ledger.BridgeTests.cross_address_flag_zero
assert_axioms Zcash.Security.Ledger.BridgeTests.cross_address_flag_one
assert_axioms Zcash.Security.Ledger.BridgeTests.cross_address_flag_arbitrary_nonzero
assert_axioms Zcash.Security.Ledger.BridgeTests.enable_spend_disabled_forces_zero
assert_axioms Zcash.Security.Ledger.BridgeTests.enable_output_disabled_forces_zero

-- The refinements instantiated at the deployed Pallas bases sit one tier up: their proofs
-- consume `native_decide` certificates — the fixed-base window tables and CompElliptic's
-- Pallas point count (`pallas_natCard`) — so `+native` is the whole of the extra budget.
assert_axioms Zcash.Security.Ledger.BridgeTests.alpha_scaling +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check)
assert_axioms Zcash.Security.Ledger.BridgeTests.value_commit_positive_scaling +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check)
assert_axioms Zcash.Security.Ledger.BridgeTests.value_commit_negative_scaling +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check)
assert_axioms Zcash.Security.Ledger.BridgeTests.or_break_iff_guarded_smoke +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check)
assert_axioms Zcash.Security.Ledger.BridgeTests.path_iff_guarded_smoke
assert_axioms Zcash.Security.Ledger.Bridge.guardedPath_of_exact +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check)
assert_axioms Zcash.Security.Ledger.BridgeTests.spec_post_bridge_smoke +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  Zcash.Security.Concrete.PallasGroup.pallas_base_card_lt_scalar_card,
  Zcash.Security.Ledger.Pool.unc_thirteen_not_isSquare,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check)

-- The onward reduction from classified break data to the games-facing
-- discrete-log-relation object is likewise a computation: the coefficients are a
-- plain compiled `def` over the break datum, with the relation and nontriviality
-- facts in erased `Prop` fields (same `+choice` reading as the classifier above).
assert_computable Zcash.Security.Ledger.Bridge.breakCoeffs +choice
-- `relationOfBreakData` and `classifyRelation` are likewise plain compiled `def`s, asserted
-- computable per the breaks-as-computed-data convention.  Their erased `Prop` fields
-- additionally carry the deployed base points' on-curve certificates, which are
-- `native_decide` checks, so they sit one tier up at `+choice +native`.
assert_computable Zcash.Security.Ledger.Bridge.relationOfBreakData +choice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check)
assert_computable Zcash.Security.Ledger.Bridge.classifyRelation +choice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  Zcash.Circuits.Ecc.MulFixed.Certs.commitIvkRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.noteCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.nullifierKCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.spendAuthGCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitRCert_check,
  Zcash.Circuits.Ecc.MulFixed.Certs.valueCommitVCert_check)

end Zcash.Security.Ledger.BridgeTests
