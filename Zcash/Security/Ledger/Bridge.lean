import Zcash.Circuits.Action.Bundle
import Zcash.Circuits.Action.RealBases
import Zcash.Circuits.Specs.Pallas
import Zcash.Security.Ledger.Pool

/-!
# The post-NU6.3 Action-to-ledger refinement boundary

This module is deliberately the only place which translates the extracted Action
circuit witness into the games-facing ledger statement — and the only place where
Sinsemilla escapes become break statements.  The circuit exports its specification
in the guarded ⊥-model (`HashGuarded`, `ExactMerklePathData`): concrete properties
of the partial hash function, with no or-break disjunctions
(`specOrBreak_hashToPointB_iff_guarded` is the audit point for that split).  Here
the witness's four exact Sinsemilla query families are re-evaluated with the
Σ-refined chain `hashToPointB` by a computable classifier (`classifyAction`), and
`validBreak_of_inr` certifies any escape as an exhibited break.  A circuit witness
is not a ledger action until every query lands in its defined branch.

The Action circuit represents the signed net value by a 64-bit magnitude and a
field element sign (`1` or `-1`).  The ledger statement uses integer
subtraction.  The arithmetic bridges near the top discharge the only subtlety in
passing between those views: the circuit equation lives in `Fp`, so its use at
the ledger layer requires ruling out reduction modulo the Pallas base modulus.
-/

namespace Zcash.Security.Ledger.Bridge

open Zcash.Circuits
open Zcash.Circuits.Action
open Zcash.Circuits.Action.Circuit
open Zcash.Circuits.Specs.Sinsemilla
open Zcash.Security.Concrete
open CompElliptic.Fields.Pasta (PALLAS_BASE_CARD)
open Halo2

/- The Action circuit neither constrains nor witnesses spend-authorization
signatures, so every bridge statement holds for an arbitrary sighash/signature
scheme; the concrete RedPallas instantiation composes downstream. -/
variable {MSG SIG : Type*}

/-- A positive 64-bit difference in `Fp` is the corresponding difference in
the integers.  The sum on the right is below `2^65`, hence below the Pallas
base modulus. -/
theorem int_sub_eq_of_fp_sub_eq
    {vOld vNew magnitude : Fp}
    (hvNew : vNew.val < 2 ^ 64)
    (hMagnitude : magnitude.val < 2 ^ 64)
    (h : vOld - vNew = magnitude) :
    (vOld.val : ℤ) - (vNew.val : ℤ) = (magnitude.val : ℤ) := by
  have heq : vOld = vNew + magnitude := sub_eq_iff_eq_add'.mp h
  have hsum : vNew.val + magnitude.val < PALLAS_BASE_CARD := by
    have hp : 2 ^ 64 + 2 ^ 64 < PALLAS_BASE_CARD := by
      norm_num [PALLAS_BASE_CARD]
    omega
  have hcast :
      (vOld.val : Fp) = ((vNew.val + magnitude.val : ℕ) : Fp) := by
    rw [ZMod.natCast_zmod_val, heq, Nat.cast_add, ZMod.natCast_zmod_val,
      ZMod.natCast_zmod_val]
  have hv : vOld.val = vNew.val + magnitude.val := by
    calc
      vOld.val = ZMod.val (vOld.val : Fp) := by
        rw [ZMod.val_natCast_of_lt (ZMod.val_lt vOld)]
      _ = ZMod.val ((vNew.val + magnitude.val : ℕ) : Fp) :=
        congrArg ZMod.val hcast
      _ = vNew.val + magnitude.val := ZMod.val_natCast_of_lt hsum
  omega

/-- The signed-magnitude equation enforced by the circuit agrees with the
integer net value consumed by `ActionSatisfied`. -/
theorem signedMagnitude_eq_int_sub
    {vOld vNew magnitude sign : Fp}
    (hvOld : vOld.val < 2 ^ 64)
    (hvNew : vNew.val < 2 ^ 64)
    (hMagnitude : magnitude.val < 2 ^ 64)
    (hSign : sign = 1 ∨ sign = -1)
    (hValue : vOld - vNew = magnitude * sign) :
    ((vOld.val : ℤ) - (vNew.val : ℤ) =
        if sign = 1 then (magnitude.val : ℤ) else -(magnitude.val : ℤ)) := by
  rcases hSign with hpos | hneg
  · subst sign
    simp only [mul_one] at hValue ⊢
    exact int_sub_eq_of_fp_sub_eq hvNew hMagnitude hValue
  · have hnot : sign ≠ 1 := by
      subst sign
      -- `(-1 : Fp) = 1` would make the odd base modulus divide `2`.
      intro h
      have h2 : (2 : Fp) = 0 := by linear_combination -h
      have hdvd : (PALLAS_BASE_CARD : ℕ) ∣ 2 := by
        have : ((2 : ℕ) : Fp) = 0 := by exact_mod_cast h2
        exact (ZMod.natCast_eq_zero_iff 2 _).mp this
      have hle := Nat.le_of_dvd (by norm_num) hdvd
      revert hle
      norm_num [PALLAS_BASE_CARD]
    rw [if_neg hnot]
    have hrev : vNew - vOld = magnitude := by
      rw [hneg, mul_neg, mul_one] at hValue
      linear_combination -hValue
    have h := int_sub_eq_of_fp_sub_eq hvOld hMagnitude hrev
    omega

abbrev LedgerWitness :=
  ActionWitness (KeyBinding.Pool.Witness Fq PallasGroup Fp) Fq PallasGroup Fp Fp Fp
    Pool.Encoding 32

/-- Coordinate equality is preserved by the checked affine-to-group adapter. -/
theorem lift_eq_of_point_eq {p q : Point Fp} (hp : p.Valid) (hq : q.Valid)
    (h : p = q) : PallasGroup.ofPoint p hp = PallasGroup.ofPoint q hq := by
  subst q
  rfl

/-- The affine view of the Pallas wrapper is injective. -/
private theorem pallasGroup_ext {p q : PallasGroup}
    (h : PallasGroup.toPoint p = PallasGroup.toPoint q) : p = q := by
  rw [← PallasGroup.ofPoint_toPoint p, ← PallasGroup.ofPoint_toPoint q]
  congr

/-- Translate the Action circuit's natural scalar multiplication into the
ledger wrapper's embedded base-field scalar action. -/
private theorem ofPoint_eq_embed_smul {p q : Point Fp} {s : Fp}
    (hp : p.Valid) (hq : q.Valid) (h : p = s.val • q) :
    PallasGroup.ofPoint p hp =
      PallasGroup.embedFp s • PallasGroup.ofPoint q hq := by
  apply pallasGroup_ext
  simpa only [PallasGroup.toPoint_smul, PallasGroup.toPoint_ofPoint,
    PallasGroup.embedFp_val] using h

/-- The circuit and ledger modules expose the same deployed domain points under
different names.  Keeping these tiny definitional bridges named prevents the
main refinement proof from unfolding their large coordinate literals. -/
private theorem orchard_ivkQ_eq : Pool.ivkQ = orchardBases.ivkQ := rfl
private theorem orchard_noteQ_eq : Pool.noteQ = orchardBases.noteQ := rfl

/-- Transport a successful Action note-commitment hash into the concrete ledger
primitive, after the circuit equation has been normalized to the certified
`noteCommitR.point`. -/
private theorem noteCommit_of_action_hash {gd pkd bp cm : Point Fp}
    {v rho psi : Fp} {rcm : Fq}
    (hgd : gd.OnCurve) (hpkd : pkd.OnCurve) (hcm : cm.Valid)
    (hh : hashToPoint orchardGenerators.S orchardBases.noteQ
      (NoteCommit.noteScalars gd pkd v rho psi).chunks = some bp)
    (heq : cm = bp + rcm.val • Ecc.MulFixed.Certs.noteCommitR.point) :
    Pool.noteCommit rcm
      { gd := PallasGroup.ofPoint gd (.inl hgd),
        pkd := PallasGroup.ofPoint pkd (.inl hpkd),
        v := v.val, ρ := rho, ψ := psi } = some (PallasGroup.ofPoint cm hcm) := by
  refine Pool.noteCommit_eq_some_of_hashToPoint (bp := bp) ?_ heq hcm
  simpa only [Pool.noteHash, Pool.noteScalars, Pool.notePoint,
    PallasGroup.toPoint_ofPoint, ZMod.natCast_zmod_val, orchard_noteQ_eq] using hh

/-- Transport a successful Action `Commit^ivk` hash into the concrete ledger
key-binding hash. -/
private theorem commitIvkHash_of_action_hash {ak nk : Fp} {bp : Point Fp}
    (hbp : hashToPoint orchardGenerators.S orchardBases.ivkQ
      (commitIvkChunks ak.val nk.val) = some bp) :
    Pool.commitIvkHash ak nk = some (PallasGroup.ofPoint bp
      (hashToPoint_valid (Or.inl orchardBases.ivkQ_onCurve)
        (fun _ hm => chunksOf_mem_lt hm) hbp)) := by
  apply Pool.commitIvkHash_eq_some_of_hashToPoint
  rw [orchard_ivkQ_eq]
  exact hbp

/-- The circuit's randomized-key public coordinates are the affine view of the
concrete ledger randomization. -/
theorem public_rk_eq_randomizePublic (verify bverify : PallasGroup → MSG → SIG → Prop)
    {wit : ActionData}
    (hak : wit.akP.OnCurve)
    (h : ({ x := wit.rkX, y := wit.rkY } : Point Fp) =
      wit.alpha.2 • orchardBases.spendAuthG + wit.akP) :
    PallasGroup.toPoint
      ((Pool.primitives verify bverify).randomizePublic wit.alpha.2
        (PallasGroup.ofPoint wit.akP (.inl hak))) =
      ({ x := wit.rkX, y := wit.rkY } : Point Fp) := by
  change PallasGroup.toPoint
      (Pool.randomizePublic wit.alpha.2
        (PallasGroup.ofPoint wit.akP (.inl hak))) =
      ({ x := wit.rkX, y := wit.rkY } : Point Fp)
  simpa [Pool.randomizePublic, orchardBases,
    Ecc.MulFixed.FixedBase.scalarMul] using h.symm

/-- The circuit's signed-magnitude value-commitment equation has the same
affine public coordinates as the ledger's integer-valued commitment.  The
64-bit bounds are precisely what make the field subtraction no-wrap. -/
theorem public_cv_net_eq_valueCommit (verify bverify : PallasGroup → MSG → SIG → Prop)
    {wit : ActionData}
    (hvOld : wit.vOld.val < 2 ^ 64) (hvNew : wit.vNew.val < 2 ^ 64)
    (hmag : wit.magnitude.val < 2 ^ 64)
    (hvalue : wit.vOld - wit.vNew = wit.magnitude * wit.sign)
    (hcv :
      (wit.sign = 1 ∧ ({ x := wit.cvX, y := wit.cvY } : Point Fp) =
        (wit.magnitude.val : Fq) • orchardBases.valueCommitV +
          wit.rcv.2 • orchardBases.valueCommitR) ∨
      (wit.sign = -1 ∧ ({ x := wit.cvX, y := wit.cvY } : Point Fp) =
        -(wit.magnitude.val : Fq) • orchardBases.valueCommitV +
          wit.rcv.2 • orchardBases.valueCommitR)) :
    PallasGroup.toPoint
      ((Pool.primitives verify bverify).valueCommit
        ((wit.vOld.val : ℤ) - (wit.vNew.val : ℤ)) wit.rcv.2) =
      ({ x := wit.cvX, y := wit.cvY } : Point Fp) := by
  change PallasGroup.toPoint
      (Pool.valueCommit ((wit.vOld.val : ℤ) - (wit.vNew.val : ℤ)) wit.rcv.2) =
      ({ x := wit.cvX, y := wit.cvY } : Point Fp)
  rcases hcv with ⟨hsign, hcv⟩ | ⟨hsign, hcv⟩
  · have hdiff : (wit.vOld.val : ℤ) - (wit.vNew.val : ℤ) =
        (wit.magnitude.val : ℤ) := by
      simpa [hsign] using
        signedMagnitude_eq_int_sub hvOld hvNew hmag
          (Or.inl hsign) hvalue
    rw [Pool.toPoint_valueCommit, hdiff]
    simpa [Pool.intScalar, orchardBases,
      Ecc.MulFixed.Short.FixedBase.scalarMul,
      Ecc.MulFixed.FixedBase.scalarMul] using hcv.symm
  · have hdiff : (wit.vOld.val : ℤ) - (wit.vNew.val : ℤ) =
        -(wit.magnitude.val : ℤ) := by
      simpa [hsign] using
        signedMagnitude_eq_int_sub hvOld hvNew hmag
          (Or.inr hsign) hvalue
    rw [Pool.toPoint_valueCommit, hdiff]
    simpa [Pool.intScalar, orchardBases,
      Ecc.MulFixed.Short.FixedBase.scalarMul,
      Ecc.MulFixed.FixedBase.scalarMul] using hcv.symm

/-- The canonical data-preserving Merkle contract, specialized to the exact
`ActionData` exports.  Its raw inputs intentionally remain natural-number
encodings, so a noncanonical 255-bit child is never reduced prematurely. -/
abbrev ExactMerklePathData (wit : ActionData) (root : Fp) : Prop :=
  Sinsemilla.Merkle.ExactMerklePathData orchardGenerators orchardBases.merkleQ 0 32
    wit.cmOld.x root
    (merkleLeftEncoding wit) (merkleRightEncoding wit) (merkleSide wit)

private theorem merkleLeftEncoding_fin (wit : ActionData) (i : Fin 32) :
    merkleLeftEncoding wit i.1 = wit.leftEncoding i := by
  simp [merkleLeftEncoding]

private theorem merkleRightEncoding_fin (wit : ActionData) (i : Fin 32) :
    merkleRightEncoding wit i.1 = wit.rightEncoding i := by
  simp [merkleRightEncoding]

private theorem merkleSide_fin (wit : ActionData) (i : Fin 32) :
    merkleSide wit i.1 = wit.merkleSide i := by
  simp [merkleSide]

/-- The five public values consumed by the ledger games are exactly the corresponding
Action primary inputs.  The enable rows deliberately do not occur in the ledger
instance. -/
def PublicProjection (wit : ActionData) (inst : ActionInstance PallasGroup Fp Fp) : Prop :=
  inst.rt = wit.anchor ∧
  inst.nf_old = wit.nfOld ∧
  PallasGroup.toPoint inst.rk = ({ x := wit.rkX, y := wit.rkY } : Point Fp) ∧
  PallasGroup.toPoint inst.cv_net = ({ x := wit.cvX, y := wit.cvY } : Point Fp) ∧
  inst.cmx_new = wit.cmx

/-- Preserve the post-NU6.3 cross-address gate with its actual field semantics:
every nonzero value of `disableCrossAddress`, not merely the value one, activates
the address equality. -/
def CrossAddressSatisfied (wit : ActionData) (w : LedgerWitness) : Prop :=
  wit.disableCrossAddress ≠ 0 →
    w.note_old.gd = w.note_new.gd ∧ w.note_old.pkd = w.note_new.pkd

/-- The spend/output enable gates, preserved with their exact circuit semantics: a
disabled flag (any value other than one) forces the corresponding note value to zero. -/
def EnableFlagsSatisfied (wit : ActionData) (w : LedgerWitness) : Prop :=
  (w.note_old.v ≠ 0 → wit.enableSpend = 1) ∧
  (w.note_new.v ≠ 0 → wit.enableOutput = 1)

/-! ### The witness's exact Sinsemilla queries

Everything below — the break vocabulary, the computable classifier, and the success
predicates — is stated over these same four query families, so the specification,
the classifier, and the correctness theorems cannot silently drift apart.  The
Merkle queries consume the raw 255-bit child encodings verbatim; a noncanonical
representative is never reduced before hashing. -/

/-- The exact `Commit^ivk` chunk query of a witness. -/
abbrev ivkQuery (wit : ActionData) : List ℕ :=
  commitIvkChunks wit.akP.x.val wit.nk.val

/-- The exact old-note commitment chunk query. -/
abbrev noteOldQuery (wit : ActionData) : List ℕ :=
  (NoteCommit.noteScalars wit.gdOld wit.pkdOld wit.vOld wit.rhoOld wit.psiOld).chunks

/-- The exact new-note commitment chunk query (`ρ_new = nf_old`). -/
abbrev noteNewQuery (wit : ActionData) : List ℕ :=
  (NoteCommit.noteScalars wit.gdNew wit.pkdNew wit.vNew wit.nfOld wit.psiNew).chunks

/-- The exact layer-`i` Merkle chunk query, over the raw 255-bit child encodings. -/
abbrev merkleQuery (wit : ActionData) (i : Fin 32) : List ℕ :=
  merkleChunks i.1 (wit.leftEncoding i) (wit.rightEncoding i)

/-- The four circuit-facing exceptional outcomes, each tied to the witness's own
exact Sinsemilla hash query via a `hashToPointB … = .inr br` equation and certified
as a `ValidBreak`.  This is the Prop-level break statement consumed by the
refinement theorems; the computational witness is the classifier's
`ActionBreakData` output, connected by `actionBreak_of_classify`. -/
inductive ActionBreak (wit : ActionData) : Prop
  | commitIvk (br : BreakData) :
      hashToPointB orchardGenerators.S orchardBases.ivkQ (ivkQuery wit) = .inr br →
      ValidBreak orchardGenerators.S orchardBases.ivkQ br → ActionBreak wit
  | noteCommitOld (br : BreakData) :
      hashToPointB orchardGenerators.S orchardBases.noteQ (noteOldQuery wit) = .inr br →
      ValidBreak orchardGenerators.S orchardBases.noteQ br → ActionBreak wit
  | noteCommitNew (br : BreakData) :
      hashToPointB orchardGenerators.S orchardBases.noteQ (noteNewQuery wit) = .inr br →
      ValidBreak orchardGenerators.S orchardBases.noteQ br → ActionBreak wit
  | merkle (i : Fin 32) (br : BreakData) :
      hashToPointB orchardGenerators.S orchardBases.merkleQ (merkleQuery wit i) = .inr br →
      ValidBreak orchardGenerators.S orchardBases.merkleQ br → ActionBreak wit

private theorem merkle_chunk_onCurve {i lv rv m : ℕ}
    (hm : m ∈ merkleChunks i lv rv) : (orchardGenerators.S m).OnCurve := by
  apply orchardGenerators.S_onCurve
  simp only [merkleChunks, List.mem_map, List.mem_range] at hm
  obtain ⟨j, -, rfl⟩ := hm
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

private theorem ivk_chunk_onCurve {wit : ActionData} {m : ℕ}
    (hm : m ∈ ivkQuery wit) : (orchardGenerators.S m).OnCurve :=
  orchardGenerators.S_onCurve (chunksOf_mem_lt hm)

private theorem note_chunk_onCurve {gd pkd : Point Fp} {v rho psi : Fp} {m : ℕ}
    (hm : m ∈ (NoteCommit.noteScalars gd pkd v rho psi).chunks) :
    (orchardGenerators.S m).OnCurve :=
  orchardGenerators.S_onCurve (chunksOf_mem_lt hm)

/-- Package a `Commit^ivk` escape of the witness's exact query.  The escape is
certified with no circuit hypothesis: `validBreak_of_inr` needs only the fixed-base
validity facts. -/
theorem commitIvk_break_of_inr {wit : ActionData} (br : BreakData)
    (hb : hashToPointB orchardGenerators.S orchardBases.ivkQ (ivkQuery wit) = .inr br) :
    ActionBreak wit :=
  .commitIvk br hb
    (validBreak_of_inr (Or.inl orchardBases.ivkQ_onCurve)
      (fun _ hm => ivk_chunk_onCurve hm) hb)

/-- Package an old-note commitment escape of the witness's exact query. -/
theorem noteCommitOld_break_of_inr {wit : ActionData} (br : BreakData)
    (hb : hashToPointB orchardGenerators.S orchardBases.noteQ (noteOldQuery wit) = .inr br) :
    ActionBreak wit :=
  .noteCommitOld br hb
    (validBreak_of_inr (Or.inl orchardBases.noteQ_onCurve)
      (fun _ hm => note_chunk_onCurve hm) hb)

/-- Package a new-note commitment escape of the witness's exact query. -/
theorem noteCommitNew_break_of_inr {wit : ActionData} (br : BreakData)
    (hb : hashToPointB orchardGenerators.S orchardBases.noteQ (noteNewQuery wit) = .inr br) :
    ActionBreak wit :=
  .noteCommitNew br hb
    (validBreak_of_inr (Or.inl orchardBases.noteQ_onCurve)
      (fun _ hm => note_chunk_onCurve hm) hb)

/-- Package an exact raw-encoding Merkle escape in the circuit-facing break
vocabulary.  The `hashToPointB` equation certifies that this is the escape of the
exact witness query, exactly as for the three note/key openings. -/
theorem merkle_break_of_inr {wit : ActionData} (i : Fin 32) (br : BreakData)
    (hb : hashToPointB orchardGenerators.S orchardBases.merkleQ
      (merkleQuery wit i) = .inr br) :
    ActionBreak wit :=
  .merkle i br hb
    (validBreak_of_inr (Or.inl orchardBases.merkleQ_onCurve)
      (fun _ hm => merkle_chunk_onCurve hm) hb)

/-! ### The computable break classifier

The reduction from a circuit witness to break data is a computation, not a case
split inside a proof: `classifyAction` re-evaluates the witness's four Sinsemilla
query families with the Σ-refined chain `hashToPointB` and returns the first escape
as `Type`-valued data.  It is a plain `def` over the raw deployed constants
(`ivkQ`/`noteQ`/`merkleQ` and the generator table) — computability is
compiler-enforced, and `BridgeTests` asserts it via `assert_computable`: the
break data is genuinely computed, and `Classical.choice` cannot contribute to it.
(Choice does appear in erased `Prop` positions — Mathlib's `ZMod` numeral and
field-arithmetic instances carry it in their proof fields, so even the deployed
point literals depend on it — but the plain-`def` check certifies it stays
erased.)  `actionBreak_of_classify` and `classify_none_defined` are the
Prop-level correctness theorems tying its two outcomes to the refinement. -/

/-- The four Sinsemilla sites of an Action witness. -/
inductive BreakSite
  | commitIvk
  | noteCommitOld
  | noteCommitNew
  | merkle (i : Fin 32)
deriving DecidableEq, Repr

/-- A classified escape: the site, together with the escape data of the witness's
own exact hash query at that site.  The onward reduction to the games-facing
discrete-log-relation object is the plain `def` `relationOfBreakData`
(`Zcash/Security/Ledger/SinsemillaDLR.lean`). -/
structure ActionBreakData where
  site : BreakSite
  data : BreakData
deriving Repr

/-- Scan the 32 exact Merkle layer queries for the first escape. -/
def classifyMerkle (wit : ActionData) : Option ActionBreakData :=
  (List.finRange 32).findSome? fun i =>
    match hashToPointB orchardGenerators.S merkleQ (merkleQuery wit i) with
    | .inl _ => none
    | .inr br => some ⟨.merkle i, br⟩

/-- The computable reduction at the Action boundary: the first escape among the
witness's Sinsemilla queries, or `none` when every hash is defined. -/
def classifyAction (wit : ActionData) : Option ActionBreakData :=
  match hashToPointB orchardGenerators.S ivkQ (ivkQuery wit) with
  | .inr br => some ⟨.commitIvk, br⟩
  | .inl _ =>
    match hashToPointB orchardGenerators.S noteQ (noteOldQuery wit) with
    | .inr br => some ⟨.noteCommitOld, br⟩
    | .inl _ =>
      match hashToPointB orchardGenerators.S noteQ (noteNewQuery wit) with
      | .inr br => some ⟨.noteCommitNew, br⟩
      | .inl _ => classifyMerkle wit

/-- A classified Merkle escape is an exhibited break of the witness's own query. -/
theorem actionBreak_of_classifyMerkle {wit : ActionData} {br : ActionBreakData}
    (h : classifyMerkle wit = some br) : ActionBreak wit := by
  obtain ⟨i, -, hi⟩ := List.exists_of_findSome?_eq_some h
  cases hb : hashToPointB orchardGenerators.S merkleQ (merkleQuery wit i) with
  | inl B => simp [hb] at hi
  | inr brd => exact merkle_break_of_inr i brd hb

/-- A `none` Merkle verdict leaves every layer's hash defined. -/
theorem classifyMerkle_none_defined {wit : ActionData}
    (h : classifyMerkle wit = none) :
    ∀ i : Fin 32, ∃ B, hashToPoint orchardGenerators.S orchardBases.merkleQ
      (merkleQuery wit i) = some B := by
  intro i
  have hi := List.findSome?_eq_none_iff.mp h i (List.mem_finRange i)
  cases hb : hashToPointB orchardGenerators.S merkleQ (merkleQuery wit i) with
  | inl B => exact ⟨B, hashToPointB_inl hb⟩
  | inr brd => simp [hb] at hi

/-- **Classifier soundness**: a classified escape is an exhibited break of the
witness's own exact hash query. -/
theorem actionBreak_of_classify {wit : ActionData} {br : ActionBreakData}
    (h : classifyAction wit = some br) : ActionBreak wit := by
  unfold classifyAction at h
  cases hivk : hashToPointB orchardGenerators.S ivkQ (ivkQuery wit) with
  | inr brd => exact commitIvk_break_of_inr brd hivk
  | inl Bi =>
    simp only [hivk] at h
    cases hold : hashToPointB orchardGenerators.S noteQ (noteOldQuery wit) with
    | inr brd => exact noteCommitOld_break_of_inr brd hold
    | inl Bo =>
      simp only [hold] at h
      cases hnew : hashToPointB orchardGenerators.S noteQ (noteNewQuery wit) with
      | inr brd => exact noteCommitNew_break_of_inr brd hnew
      | inl Bn =>
        simp only [hnew] at h
        exact actionBreak_of_classifyMerkle h

/-- **Classifier completeness**: a `none` verdict leaves every Sinsemilla query of
the witness defined, so each guarded circuit clause lands in its successful
branch. -/
theorem classify_none_defined {wit : ActionData} (h : classifyAction wit = none) :
    (∃ B, hashToPoint orchardGenerators.S orchardBases.ivkQ
      (ivkQuery wit) = some B) ∧
    (∃ B, hashToPoint orchardGenerators.S orchardBases.noteQ
      (noteOldQuery wit) = some B) ∧
    (∃ B, hashToPoint orchardGenerators.S orchardBases.noteQ
      (noteNewQuery wit) = some B) ∧
    ∀ i : Fin 32, ∃ B, hashToPoint orchardGenerators.S orchardBases.merkleQ
      (merkleQuery wit i) = some B := by
  unfold classifyAction at h
  cases hivk : hashToPointB orchardGenerators.S ivkQ (ivkQuery wit) with
  | inr brd => simp [hivk] at h
  | inl Bi =>
    simp only [hivk] at h
    cases hold : hashToPointB orchardGenerators.S noteQ (noteOldQuery wit) with
    | inr brd => simp [hold] at h
    | inl Bo =>
      simp only [hold] at h
      cases hnew : hashToPointB orchardGenerators.S noteQ (noteNewQuery wit) with
      | inr brd => simp [hnew] at h
      | inl Bn =>
        simp only [hnew] at h
        exact ⟨⟨Bi, hashToPointB_inl hivk⟩, ⟨Bo, hashToPointB_inl hold⟩,
          ⟨Bn, hashToPointB_inl hnew⟩, classifyMerkle_none_defined h⟩

/-- **The Prop-level break and the computed classifier cannot diverge, at the consumer
boundary either**: an exhibited `ActionBreak` holds exactly when the classifier reports
an escape.  A consumer landing in the break arm of `specPost_to_ledger` can
therefore pass to `classifyAction`'s (and hence `classifyRelation`'s) computed data
without reconstructing the glue: forward, each break constructor's
`hashToPointB … = .inr` equation contradicts the defined hashes of a `none` verdict;
backward is classifier soundness. -/
theorem actionBreak_iff_classify_isSome {wit : ActionData} :
    ActionBreak wit ↔ (classifyAction wit).isSome := by
  constructor
  · intro hb
    cases hcl : classifyAction wit with
    | some _ => rfl
    | none =>
      obtain ⟨⟨Bi, hBi⟩, ⟨Bo, hBo⟩, ⟨Bn, hBn⟩, hMk⟩ := classify_none_defined hcl
      cases hb with
      | commitIvk br heq _ =>
        rw [hashToPoint_of_inr heq] at hBi
        exact absurd hBi (by simp)
      | noteCommitOld br heq _ =>
        rw [hashToPoint_of_inr heq] at hBo
        exact absurd hBo (by simp)
      | noteCommitNew br heq _ =>
        rw [hashToPoint_of_inr heq] at hBn
        exact absurd hBn (by simp)
      | merkle i br heq _ =>
        obtain ⟨B, hB⟩ := hMk i
        rw [hashToPoint_of_inr heq] at hB
        exact absurd hB (by simp)
  · intro h
    obtain ⟨abr, habr⟩ := Option.isSome_iff_exists.mp h
    exact actionBreak_of_classify habr

/-- Successful `Commit^ivk` information: the defined branch of the guarded
`Commit^ivk` clause, on the witness's exact query. -/
def CommitIvkSuccess (wit : ActionData) : Prop :=
  ∃ ivk : Fp, ∃ hashPoint : Point Fp,
    hashToPoint orchardGenerators.S orchardBases.ivkQ
      (commitIvkChunks wit.akP.x.val wit.nk.val) = some hashPoint ∧
    ivk = (hashPoint + wit.rivk.2 • orchardBases.commitIvkR).x ∧
    wit.pkdOld = ivk.val • wit.gdOld

/-- The successful incoming viewing key cannot be zero.  This is a circuit fact,
not an additional ledger assumption: the address-integrity equation would otherwise
make the witnessed, on-curve `pkdOld` the affine identity sentinel. -/
theorem CommitIvkSuccess.ivk_ne {wit : ActionData} {ivk : Fp}
    (hpkd : wit.pkdOld.OnCurve)
    (h : ∃ hashPoint : Point Fp,
      hashToPoint orchardGenerators.S orchardBases.ivkQ
        (commitIvkChunks wit.akP.x.val wit.nk.val) = some hashPoint ∧
      ivk = (hashPoint + wit.rivk.2 • orchardBases.commitIvkR).x ∧
      wit.pkdOld = ivk.val • wit.gdOld) : ivk ≠ 0 := by
  rcases h with ⟨_, _, _, hpkdEq⟩
  intro hiz
  have hval : ivk.val = 0 := by simp [hiz]
  have hzero : wit.pkdOld = 0 := by
    rw [hpkdEq, hval]
    rfl
  exact Point.ne_zero_of_onCurve hpkd hzero

/-- Convert the successful `Commit^ivk` branch into the exact deployed Orchard
key-binding witness used by the ledger statement.  The returned equations keep
the affine Action points available in their Pallas-wrapper form for the final
address and spend-authority fields. -/
theorem commitIvkSuccess_to_ledger {wit : ActionData}
    (hgd : wit.gdOld.OnCurve) (hak : wit.akP.OnCurve)
    (hpkd : wit.pkdOld.OnCurve) (h : CommitIvkSuccess wit) :
    ∃ (ivk : Fp) (kw : KeyBinding.Pool.Witness Fq PallasGroup Fp),
      Pool.keyBinding.KB kw ∧
      Pool.keyBinding.ivk kw ≠ 0 ∧
      Pool.keyBinding.ivk kw = ivk ∧
      Pool.keyBinding.nk kw = wit.nk ∧
      Pool.keyBinding.akP kw = PallasGroup.ofPoint wit.akP (.inl hak) ∧
      PallasGroup.ofPoint wit.pkdOld (.inl hpkd) =
        PallasGroup.embedFp (Pool.keyBinding.ivk kw) •
          PallasGroup.ofPoint wit.gdOld (.inl hgd) := by
  rcases h with ⟨ivk, bp, hbp, hivk, hpkdEq⟩
  have hbpValid : bp.Valid :=
    hashToPoint_valid (Or.inl orchardBases.ivkQ_onCurve)
      (fun _ hm => chunksOf_mem_lt hm) hbp
  let kw : KeyBinding.Pool.Witness Fq PallasGroup Fp :=
    { ivk := ivk,
      akP := PallasGroup.ofPoint wit.akP (.inl hak),
      nk := wit.nk,
      rivk := wit.rivk.2,
      hashPoint := PallasGroup.ofPoint bp hbpValid }
  have hivk' : ivk =
      (bp + wit.rivk.2.val • Ecc.MulFixed.Certs.commitIvkR.point).x := by
    simpa [orchardBases, Ecc.MulFixed.FixedBase.scalarMul] using hivk
  have hkb : Pool.keyBinding.KB kw := by
    change KeyBinding.Pool.KB Pool.extract Pool.commitIvkHash
      (PallasGroup.ofPoint Ecc.MulFixed.Certs.commitIvkR.point
        (Or.inl Ecc.MulFixed.Certs.commitIvkR.onCurve)) kw
    refine ⟨?_, ?_, ?_⟩
    · dsimp [kw]
      exact commitIvkHash_of_action_hash hbp
    · dsimp [kw]
      simpa only [Pool.extract, PallasGroup.toPoint_add,
        PallasGroup.toPoint_smul, PallasGroup.toPoint_nsmul,
        PallasGroup.toPoint_ofPoint] using hivk'
    · dsimp [kw]
      apply CommitIvkSuccess.ivk_ne hpkd
      exact ⟨bp, hbp, hivk, hpkdEq⟩
  refine ⟨ivk, kw, hkb, hkb.ivk_ne, rfl, rfl, rfl, ?_⟩
  · exact ofPoint_eq_embed_smul (.inl hpkd) (.inl hgd) hpkdEq

/-- Successful old-note Sinsemilla opening. -/
def NoteCommitOldSuccess (wit : ActionData) : Prop :=
  ∃ hashPoint : Point Fp,
    hashToPoint orchardGenerators.S orchardBases.noteQ
      (NoteCommit.noteScalars wit.gdOld wit.pkdOld wit.vOld wit.rhoOld wit.psiOld).chunks
        = some hashPoint ∧
    wit.cmOld = hashPoint + wit.rcmOld.2 • orchardBases.noteCommitR

/-- Successful new-note Sinsemilla opening. -/
def NoteCommitNewSuccess (wit : ActionData) : Prop :=
  ∃ hashPoint : Point Fp,
    hashToPoint orchardGenerators.S orchardBases.noteQ
      (NoteCommit.noteScalars wit.gdNew wit.pkdNew wit.vNew wit.nfOld wit.psiNew).chunks
        = some hashPoint ∧
    wit.cmx = (hashPoint + wit.rcmNew.2 • orchardBases.noteCommitR).x

/-- Turn the successful output-note opening retained by the Action statement
into the concrete ledger commitment.  Unlike the circuit public input, the
ledger keeps the full commitment point; this lemma supplies that point together
with the coordinate equation used for `cmx_new_eq`. -/
theorem noteCommitNewSuccess_to_ledger (verify bverify : PallasGroup → MSG → SIG → Prop)
    {wit : ActionData}
    (hgd : wit.gdNew.OnCurve) (hpkd : wit.pkdNew.OnCurve)
    (h : NoteCommitNewSuccess wit) :
    ∃ (cmNewP : Point Fp) (hcmNewP : cmNewP.Valid),
      cmNewP.x = wit.cmx ∧
      (Pool.primitives verify bverify).noteCommit wit.rcmNew.2
        { gd := PallasGroup.ofPoint wit.gdNew (.inl hgd),
          pkd := PallasGroup.ofPoint wit.pkdNew (.inl hpkd),
          v := wit.vNew.val, ρ := wit.nfOld, ψ := wit.psiNew } =
        some (PallasGroup.ofPoint cmNewP hcmNewP) := by
  rcases h with ⟨bp, hbp, hcmx⟩
  have hbpValid : bp.Valid :=
    hashToPoint_valid (Or.inl orchardBases.noteQ_onCurve)
      (fun _ hm => chunksOf_mem_lt hm) hbp
  let cmNewP : Point Fp :=
    bp + wit.rcmNew.2.val • Ecc.MulFixed.Certs.noteCommitR.point
  have hcmNewP : cmNewP.Valid := by
    dsimp [cmNewP]
    exact Point.valid_add hbpValid
      (Point.valid_nsmul (Or.inl Ecc.MulFixed.Certs.noteCommitR.onCurve) _)
  refine ⟨cmNewP, hcmNewP, ?_, ?_⟩
  · simpa [cmNewP, orchardBases, Ecc.MulFixed.FixedBase.scalarMul] using hcmx.symm
  · change Pool.noteCommit wit.rcmNew.2
      { gd := PallasGroup.ofPoint wit.gdNew (.inl hgd),
        pkd := PallasGroup.ofPoint wit.pkdNew (.inl hpkd),
        v := wit.vNew.val, ρ := wit.nfOld, ψ := wit.psiNew } =
        some (PallasGroup.ofPoint cmNewP hcmNewP)
    apply noteCommit_of_action_hash hgd hpkd hcmNewP hbp
    rfl

/-- The successful Merkle outcome as consumed by the ledger refinement: the exact
raw-encoding path together with every layer's hash landing in its defined branch,
and the dummy-spend anchor gate.  The raw child encodings are tied to these defined
hashes before any `Merkle.Path` is constructed. -/
def MerkleSuccess (wit : ActionData) : Prop :=
  ∃ root : Fp,
    ExactMerklePathData wit root ∧
    (∀ i : Fin 32, ∃ B, hashToPoint orchardGenerators.S orchardBases.merkleQ
      (merkleChunks i.1 (wit.leftEncoding i) (wit.rightEncoding i)) = some B) ∧
    wit.vOld * (root - wit.anchor) = 0

/-- Split all four exceptional sites in the circuit statement at once, by running
the classifier: either the witness's own queries compute an exhibited break, or
every query is defined and each guarded clause of `SpecPost` lands in its
successful branch. -/
theorem successes_or_break {wit : ActionData}
    (h : SpecPost orchardGenerators orchardBases () () wit) :
    (CommitIvkSuccess wit ∧ NoteCommitOldSuccess wit ∧ NoteCommitNewSuccess wit ∧
      MerkleSuccess wit) ∨ ActionBreak wit := by
  cases hcl : classifyAction wit with
  | some br => exact Or.inr (actionBreak_of_classify hcl)
  | none =>
    obtain ⟨⟨Bi, hBi⟩, ⟨Bo, hBo⟩, ⟨Bn, hBn⟩, hMk⟩ := classify_none_defined hcl
    rcases h.1 with ⟨_, _, _, _, _, _, _, _, _, _, _, ⟨ivk, hivk, hpkd⟩,
      hold, hnew, ⟨root, hexact, hanchor⟩, _, _, _⟩
    exact Or.inl ⟨⟨ivk, Bi, hBi, hivk Bi hBi, hpkd⟩,
      ⟨Bo, hBo, hold Bo hBo⟩, ⟨Bn, hBn, hnew Bn hBn⟩,
      ⟨root, hexact, hMk, hanchor⟩⟩

/-- If the caller rules out all four exhibited exceptional cases, the circuit's
guarded clauses reduce to their successful openings.  The exact-Merkle export
subsequently turns the final component into a ledger `Merkle.Path`. -/
theorem successes_of_noBreak {wit : ActionData}
    (h : SpecPost orchardGenerators orchardBases () () wit)
    (hno : ¬ ActionBreak wit) :
    CommitIvkSuccess wit ∧ NoteCommitOldSuccess wit ∧ NoteCommitNewSuccess wit ∧
      MerkleSuccess wit :=
  (successes_or_break h).resolve_right hno

/-- Recover the successful Sinsemilla hash underlying a defined Merkle
compression: the converse direction of `Pool.merkleCompress_eq_of_hashToPoint`,
used to turn a guard hypothesis `merkleCompress … = some b` back into the exact
hash query that the exported chain pins. -/
private theorem hashToPoint_of_merkleCompress {i : Fin 32}
    {children : Pool.Encoding × Pool.Encoding} {b : Fp}
    (h : Pool.merkleCompress i children = some b) :
    ∃ B, hashToPoint orchardGenerators.S Pool.merkleQ
      (merkleChunks i.1 children.1.1 children.2.1) = some B ∧ b = B.x := by
  simp only [Pool.merkleCompress, Option.map_eq_some_iff] at h
  obtain ⟨B, hB, hbx⟩ := h
  exact ⟨B, hB, hbx.symm⟩

/-- The exact circuit Merkle chain, transferred into the ledger's guarded
(⊥-model) path.  No definedness hypothesis is needed: each guarded clause is
only asked to fire on an *already defined* running node, and the exported
existential chain (`nodes`, its selected-child equations, and its per-layer hash
steps) supplies exactly that node.  Pairing this with per-layer definedness gives
the strict `Merkle.Path` (`merkle_path_of_exact`). -/
theorem guardedPath_of_exact {wit : ActionData} {root : Fp}
    (hpath : ExactMerklePathData wit root) :
    Merkle.GuardedPath Pool.merkle wit.cmOld.x root
      (fun i : Fin 32 =>
        (⟨wit.leftEncoding i, by
            rcases hpath with ⟨_, _, _, hsteps⟩
            simpa only [merkleLeftEncoding_fin] using (hsteps i i.isLt).1⟩,
         ⟨wit.rightEncoding i, by
            rcases hpath with ⟨_, _, _, hsteps⟩
            simpa only [merkleRightEncoding_fin] using (hsteps i i.isLt).2.1⟩))
      wit.merkleSide := by
  rcases hpath with ⟨nodes, hstart, hroot, hsteps⟩
  -- A defined compression at height `k`, over the exact encodings, pins the next
  -- running node via the exported hash step of the chain.
  have hstepAt : ∀ (k : Fin 32) (c : Pool.Encoding × Pool.Encoding) {b : Fp},
      c.1.1 = wit.leftEncoding k → c.2.1 = wit.rightEncoding k →
      Pool.merkleCompress k c = some b → nodes (k.1 + 1) = b := by
    intro k c b hcl hcr hcomp
    obtain ⟨B, hB, hbB⟩ := hashToPoint_of_merkleCompress hcomp
    rw [hcl, hcr] at hB
    have hB' : hashToPoint orchardGenerators.S orchardBases.merkleQ
        (merkleChunks (0 + k.1) (merkleLeftEncoding wit k.1) (merkleRightEncoding wit k.1))
          = some B := by
      rw [merkleLeftEncoding_fin, merkleRightEncoding_fin]
      simpa [orchardBases, Zcash.Circuits.Action.merkleQ, Pool.merkleQ] using hB
    exact ((hsteps k.1 k.isLt).2.2.2 B hB').trans hbB.symm
  refine ⟨fun i b hb => ?_, fun b hb => ?_⟩
  · -- Selected-child clause: the decoded selected child is the recorded node,
    -- and the guard hypothesis pins that node to `b`.
    have hs := (hsteps i.1 i.isLt).2.2.1
    rw [merkleSide_fin, merkleLeftEncoding_fin, merkleRightEncoding_fin] at hs
    have hnodeval : nodes i.1 = b := by
      rcases i with ⟨iv, hi⟩
      cases iv with
      | zero =>
        have hc : Fin.castSucc (⟨0, hi⟩ : Fin Pool.merkle.depth) = 0 := by apply Fin.ext; simp
        rw [hc] at hb
        show nodes 0 = b
        rw [hstart]
        simpa [Merkle.node] using hb
      | succ j =>
        have hi32 : j + 1 < 32 := hi
        have hj : j < 32 := by omega
        have hc : Fin.castSucc (⟨j + 1, hi⟩ : Fin Pool.merkle.depth)
            = Fin.succ (⟨j, hj⟩ : Fin Pool.merkle.depth) := by
          apply Fin.ext; simp
        rw [hc] at hb
        simp only [Merkle.node, Fin.cases_succ, Pool.merkle] at hb
        exact hstepAt ⟨j, hj⟩ _ rfl rfl hb
    rw [Merkle.selectedChild, apply_ite Pool.merkle.decode]
    simp only [Pool.merkle, Pool.decode]
    exact hs.trans hnodeval
  · -- Root clause: the final defined compression is the recorded root.
    have hlast : (Fin.last Pool.merkle.depth) = Fin.succ (⟨31, by decide⟩ : Fin Pool.merkle.depth) := by
      apply Fin.ext; simp [Pool.merkle]
    rw [hlast] at hb
    simp only [Merkle.node, Fin.cases_succ, Pool.merkle] at hb
    exact ((hstepAt ⟨31, by omega⟩ _ rfl rfl hb).symm.trans hroot)

/-- An exact, escape-free circuit Merkle chain yields the ledger's raw
authentication path.  The raw encodings are retained verbatim: the only
conversion is the ledger decoder from a bounded 255-bit representative to its
field element.  The proof is the guarded split: transfer the exact chain into the
⊥-model path (`guardedPath_of_exact`), then reinstate strictness from the
per-layer definedness supplied by `hhash`. -/
theorem merkle_path_of_exact {wit : ActionData} {root : Fp}
    (hpath : ExactMerklePathData wit root)
    (hhash : ∀ i : Fin 32, ∃ B,
      hashToPoint orchardGenerators.S orchardBases.merkleQ
        (merkleChunks i.1 (wit.leftEncoding i) (wit.rightEncoding i)) = some B) :
    Merkle.Path Pool.merkle wit.cmOld.x root
      (fun i : Fin 32 =>
        (⟨wit.leftEncoding i, by
            rcases hpath with ⟨_, _, _, hsteps⟩
            simpa only [merkleLeftEncoding_fin] using (hsteps i i.isLt).1⟩,
         ⟨wit.rightEncoding i, by
            rcases hpath with ⟨_, _, _, hsteps⟩
            simpa only [merkleRightEncoding_fin] using (hsteps i i.isLt).2.1⟩))
      wit.merkleSide :=
  Merkle.Path.of_guarded_of_defined (guardedPath_of_exact hpath) fun i => by
    obtain ⟨B, hB⟩ := hhash i
    exact ⟨B.x, Pool.merkleCompress_eq_of_hashToPoint (by
      simpa [orchardBases, Zcash.Circuits.Action.merkleQ, Pool.merkleQ] using hB)⟩

/-- The Action postcondition refines to either one of its explicitly exhibited
Sinsemilla escapes or a fully satisfied concrete Orchard ledger action.  The ledger
alternative additionally reports the spend/output enable gates as a side fact
(`EnableFlagsSatisfied`), with their exact circuit semantics. -/
theorem specPost_to_ledger (verify bverify : PallasGroup → MSG → SIG → Prop)
    {wit : ActionData}
    (h : SpecPost orchardGenerators orchardBases () () wit) :
    ActionBreak wit ∨
      ∃ inst w, PublicProjection wit inst ∧
        ActionSatisfied (Pool.primitives verify bverify) Pool.keyBinding inst w ∧
        CrossAddressSatisfied wit w ∧
        EnableFlagsSatisfied wit w := by
  rcases successes_or_break h with hs | hbreak
  · rcases hs with ⟨hivk, hold, hnew, hmerkle⟩
    rcases hmerkle with ⟨root, hpath, hhash, hanchor⟩
    rcases h.1 with ⟨hcmOld, hgdOld, hakP, hpkdOld, hgdNew, hpkdNew,
      hvOld, hvNew, hvc, hnf, hrk, -, -, -, -, hvalue, hes, heo⟩
    rcases hvc with ⟨hmag, hcv⟩
    rcases hold with ⟨bold, hbold, hcmOldEq⟩
    rcases commitIvkSuccess_to_ledger hgdOld hakP hpkdOld hivk with
      ⟨ivk, kw, hkb, hivne, hkwivk, hkwNk, hkwAk, hpkdLedger⟩
    have hkwNk' : kw.nk = wit.nk := hkwNk
    rcases noteCommitNewSuccess_to_ledger verify bverify hgdNew hpkdNew hnew with
      ⟨cmNewP, hcmNewP, hcmNewX, hcommitNew⟩
    have hcmOldEq' : wit.cmOld =
        bold + wit.rcmOld.2.val • Ecc.MulFixed.Certs.noteCommitR.point := by
      simpa [orchardBases, Ecc.MulFixed.FixedBase.scalarMul] using hcmOldEq
    have hnf' : wit.nfOld =
        (wit.cmOld +
          ((Poseidon.Hash.ConstantLength.value #v[wit.nk, wit.rhoOld] +
            wit.psiOld).val : Fq).val •
            Ecc.MulFixed.Certs.nullifierK.point).x := by
      simpa [orchardBases, Ecc.MulFixed.FixedBase.scalarMul] using hnf
    have hcommitOld : Pool.noteCommit wit.rcmOld.2
        { gd := PallasGroup.ofPoint wit.gdOld (.inl hgdOld),
          pkd := PallasGroup.ofPoint wit.pkdOld (.inl hpkdOld),
          v := wit.vOld.val, ρ := wit.rhoOld, ψ := wit.psiOld } =
        some (PallasGroup.ofPoint wit.cmOld hcmOld) :=
      noteCommit_of_action_hash hgdOld hpkdOld hcmOld hbold hcmOldEq'
    let path : Fin 32 → Pool.Encoding × Pool.Encoding := fun i =>
      (⟨wit.leftEncoding i, by
          rcases hpath with ⟨_, _, _, hsteps⟩
          simpa only [merkleLeftEncoding_fin] using (hsteps i i.isLt).1⟩,
       ⟨wit.rightEncoding i, by
          rcases hpath with ⟨_, _, _, hsteps⟩
          simpa only [merkleRightEncoding_fin] using (hsteps i i.isLt).2.1⟩)
    let inst : ActionInstance PallasGroup Fp Fp :=
      { rt := wit.anchor,
        nf_old := wit.nfOld,
        rk := (Pool.primitives verify bverify).randomizePublic wit.alpha.2
          (PallasGroup.ofPoint wit.akP (.inl hakP)),
        cv_net := (Pool.primitives verify bverify).valueCommit
          ((wit.vOld.val : ℤ) - (wit.vNew.val : ℤ)) wit.rcv.2,
        cmx_new := wit.cmx }
    let w : LedgerWitness :=
      { path := path,
        side := wit.merkleSide,
        note_old :=
          { gd := PallasGroup.ofPoint wit.gdOld (.inl hgdOld),
            pkd := PallasGroup.ofPoint wit.pkdOld (.inl hpkdOld),
            v := wit.vOld.val, ρ := wit.rhoOld, ψ := wit.psiOld },
        note_new :=
          { gd := PallasGroup.ofPoint wit.gdNew (.inl hgdNew),
            pkd := PallasGroup.ofPoint wit.pkdNew (.inl hpkdNew),
            v := wit.vNew.val, ρ := wit.nfOld, ψ := wit.psiNew },
        cm_old := PallasGroup.ofPoint wit.cmOld hcmOld,
        cm_new := PallasGroup.ofPoint cmNewP hcmNewP,
        kw := kw,
        α := wit.alpha.2,
        rcv := wit.rcv.2,
        rcm_old := wit.rcmOld.2,
        rcm_new := wit.rcmNew.2 }
    refine Or.inr ⟨inst, w, ?_, ?_, ?_, ?_⟩
    · refine ⟨rfl, rfl, ?_, ?_, rfl⟩
      · simpa [inst] using public_rk_eq_randomizePublic verify bverify hakP hrk
      · simpa [inst] using
          public_cv_net_eq_valueCommit verify bverify hvOld hvNew hmag hvalue hcv
    · refine
        { commit_old := ?_,
          merkle_path := ?_,
          nf_old_eq := ?_,
          key_binding := ?_,
          pkd_eq := ?_,
          gd_ne := ?_,
          rk_eq := ?_,
          commit_new := ?_,
          cmx_new_eq := ?_,
          ρ_new_eq := ?_,
          v_old_lt := ?_,
          v_new_lt := ?_,
          cv_net_eq := ?_ }
      · simpa [w] using hcommitOld
      · intro hv
        have hv' : wit.vOld ≠ 0 := by
          intro hz
          apply hv
          dsimp [w]
          simp [hz]
        have hroot : root = wit.anchor := by
          have hz : root - wit.anchor = 0 :=
            (mul_eq_zero.mp hanchor).resolve_left hv'
          exact sub_eq_zero.mp hz
        have hp := merkle_path_of_exact hpath hhash
        simpa [w, inst, path, Pool.extract, hroot] using hp
      · simpa [inst, w, Pool.primitives, Pool.keyBinding,
          KeyBinding.Pool.toInterface, hkwNk', Pool.deriveNullifier] using hnf'
      · simpa [w] using hkb
      · simpa [w, Pool.primitives, hkwivk] using hpkdLedger
      · intro hzero
        have hpzero : wit.gdOld = 0 := by
          have hz := congrArg PallasGroup.toPoint hzero
          simpa [w] using hz
        exact Point.ne_zero_of_onCurve hgdOld hpzero
      · change (Pool.primitives verify bverify).randomizePublic wit.alpha.2
            (PallasGroup.ofPoint wit.akP (.inl hakP)) =
          (Pool.primitives verify bverify).randomizePublic wit.alpha.2
            (Pool.keyBinding.akP kw)
        rw [hkwAk]
      · simpa [w] using hcommitNew
      · change wit.cmx = cmNewP.x
        exact hcmNewX.symm
      · rfl
      · exact hvOld
      · exact hvNew
      · rfl
    · intro henabled
      rcases h.2 henabled with ⟨hgd, hpkd⟩
      change
        PallasGroup.ofPoint wit.gdOld (.inl hgdOld) =
            PallasGroup.ofPoint wit.gdNew (.inl hgdNew) ∧
          PallasGroup.ofPoint wit.pkdOld (.inl hpkdOld) =
            PallasGroup.ofPoint wit.pkdNew (.inl hpkdNew)
      exact ⟨lift_eq_of_point_eq (.inl hgdOld) (.inl hgdNew) hgd,
        lift_eq_of_point_eq (.inl hpkdOld) (.inl hpkdNew) hpkd⟩
    · refine ⟨fun hv => ?_, fun hv => ?_⟩
      · have hvOld0 : wit.vOld ≠ 0 := by
          intro hz
          apply hv
          dsimp [w]
          simp [hz]
        exact (sub_eq_zero.mp ((mul_eq_zero.mp hes).resolve_left hvOld0)).symm
      · have hvNew0 : wit.vNew ≠ 0 := by
          intro hz
          apply hv
          dsimp [w]
          simp [hz]
        exact (sub_eq_zero.mp ((mul_eq_zero.mp heo).resolve_left hvNew0)).symm
  · exact Or.inl hbreak

end Zcash.Security.Ledger.Bridge
