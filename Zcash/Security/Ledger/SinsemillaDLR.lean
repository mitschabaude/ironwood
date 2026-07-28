import Zcash.Security.Ledger.Bridge
import Zcash.Common.DiscreteLogRelation

/-!
# The games-facing Sinsemilla discrete-log-relation object

The onward reduction step for the classified Action escapes: a plain `def`
converting an `ActionBreakData` — the site and escape datum computed by
`classifyAction` — into a `NontrivialRelationOne`, the games-facing
discrete-log-relation break among the deployed Sinsemilla generator table and the
escaped site's domain point.  This is protocol-spec Theorem 5.4.4 made
computational end to end: the coefficients of the relation are read off the break
datum's consumed prefix (`breakCoeffs`), and its `Prop` fields are discharged from
`ValidBreak` alone.

The mathematical content is the chain-combination lemma `ofPoint_hashToPoint`: a
defined Sinsemilla chain value is the explicit generator combination
`2^n • Q + ∑ⱼ 2^(n−1−j) • S(mⱼ)` in the Pallas group.  Substituting it into the
resolved escape equation of a `ValidBreak` yields, for every escape kind, a linear
relation whose `Q`-coefficient is a power of two — nonzero in the odd-order scalar
field — or, for a `genZero` escape, a bare identity generator with coefficient one.

Like `classifyAction`, everything data-producing here is a plain compiled `def`
(`assert_computable … +choice` in `BridgeTests`): `Classical.choice` enters only
through erased `Prop` fields.
-/

namespace Zcash.Security.Ledger.Bridge

open Zcash.Circuits
open Zcash.Circuits.Action
open Zcash.Circuits.Action.Circuit
open Zcash.Circuits.Specs (K)
open Zcash.Circuits.Specs.Sinsemilla
open Zcash.Security.Concrete

/-! ## The lifted generator table -/

/-- The deployed Sinsemilla generator table, lifted into the Pallas group.  Total on
`ℕ` for convenient use under chunk lists; off-table indices (never produced by a
`K`-bit chunk) map to the identity. -/
def pallasSAt (m : ℕ) : PallasGroup :=
  if h : m < 2 ^ K then
    PallasGroup.ofPoint (orchardGenerators.S m) (orchardGenerators.valid h)
  else 0

/-- The generator family of the discrete-log-relation object: the table restricted
to its index range. -/
def pallasS (t : Fin (2 ^ K)) : PallasGroup := pallasSAt t.1

theorem pallasSAt_of_lt {m : ℕ} (h : m < 2 ^ K) :
    pallasSAt m =
      PallasGroup.ofPoint (orchardGenerators.S m) (orchardGenerators.valid h) :=
  dif_pos h

/-! ## The chain-combination lemma -/

/-- One chain step in the Pallas group: a defined double-and-add step maps
`acc ↦ 2·acc + S(m)`. -/
private theorem ofPointChain_step {m : ℕ} (hm : m < 2 ^ K) {Q Q' : Point Fp}
    (hQ : Q.Valid) (hQ' : Q'.Valid)
    (hs : step orchardGenerators.S m Q = some Q') :
    PallasGroup.ofPoint Q' hQ' = 2 • PallasGroup.ofPoint Q hQ + pallasSAt m := by
  have hSm : (orchardGenerators.S m).Valid := orchardGenerators.valid hm
  have eq : Q' = (Q + orchardGenerators.S m) + Q := by
    simp only [step, Point.doubleAndAdd, Option.bind_eq_bind] at hs
    by_cases hc₁ : Q = 0 ∨ orchardGenerators.S m = 0 ∨ Q.x = (orchardGenerators.S m).x
    · rw [Point.incompleteAdd_def, if_pos hc₁] at hs; simp at hs
    rw [Point.incompleteAdd_def, if_neg hc₁] at hs
    rw [show ((some (Q + orchardGenerators.S m)).bind fun t => Point.incompleteAdd t Q)
      = Point.incompleteAdd (Q + orchardGenerators.S m) Q from rfl] at hs
    by_cases hc₂ : Q + orchardGenerators.S m = 0 ∨ Q = 0 ∨ (Q + orchardGenerators.S m).x = Q.x
    · rw [Point.incompleteAdd_def, if_pos hc₂] at hs; simp at hs
    rw [Point.incompleteAdd_def, if_neg hc₂] at hs
    exact (Option.some.inj hs).symm
  subst eq
  show PallasGroup.ofPoint ((Q + orchardGenerators.S m) + Q)
      (Point.valid_add (Point.valid_add hQ hSm) hQ) = 2 • PallasGroup.ofPoint Q hQ + pallasSAt m
  rw [PallasGroup.ofPoint_add (Point.valid_add hQ hSm) hQ,
    PallasGroup.ofPoint_add hQ hSm, pallasSAt_of_lt hm, two_nsmul]
  abel

/-- The chain-combination lemma, in the `∀`-form convenient for forward induction. -/
private theorem ofPointChain_hash : ∀ (chunks : List ℕ) {Q acc : Point Fp} (hQ : Q.Valid),
    (∀ m ∈ chunks, m < 2 ^ K) →
    hashToPoint orchardGenerators.S Q chunks = some acc → ∀ (hacc : acc.Valid),
    PallasGroup.ofPoint acc hacc =
      2 ^ chunks.length • PallasGroup.ofPoint Q hQ +
        ∑ j ∈ Finset.range chunks.length,
          2 ^ (chunks.length - 1 - j) • pallasSAt (chunks.getD j 0) := by
  intro chunks
  induction chunks with
  | nil =>
    intro Q acc hQ hb h hacc
    rw [hashToPoint_nil, Option.some.injEq] at h
    subst h
    simp only [List.length_nil, pow_zero, one_smul, Finset.range_zero, Finset.sum_empty, add_zero]
  | cons m rest ih =>
    intro Q acc hQ hb h hacc
    cases hs : step orchardGenerators.S m Q with
    | none =>
      rw [hashToPoint_cons, hs] at h
      simp at h
    | some Q' =>
      have h' : hashToPoint orchardGenerators.S Q' rest = some acc := by
        rw [hashToPoint_cons, hs] at h; exact h
      have hm : m < 2 ^ K := hb m (by simp)
      have hQ' : Q'.Valid := step_valid hQ hm hs
      have hbrest : ∀ k ∈ rest, k < 2 ^ K := fun k hk => hb k (List.mem_cons_of_mem m hk)
      have IH := ih hQ' hbrest h' hacc
      rw [IH, ofPointChain_step hm hQ hQ' hs]
      simp only [List.length_cons]
      rw [Finset.sum_range_succ', List.getD_cons_zero]
      have hsum : ∑ j ∈ Finset.range rest.length,
            2 ^ (rest.length + 1 - 1 - (j + 1)) • pallasSAt ((m :: rest).getD (j + 1) 0)
          = ∑ j ∈ Finset.range rest.length,
            2 ^ (rest.length - 1 - j) • pallasSAt (rest.getD j 0) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [List.getD_cons_succ,
          show rest.length + 1 - 1 - (j + 1) = rest.length - 1 - j from by omega]
      rw [hsum, show rest.length + 1 - 1 - 0 = rest.length from by omega,
        pow_succ, mul_smul, smul_add]
      abel

/-- A defined Sinsemilla chain value is the explicit generator combination
`2^n • Q + ∑ⱼ 2^(n−1−j) • S(mⱼ)` (`n = chunks.length`), in the Pallas group.  This
is the "explicit combination" reading of the honest prefix chain used informally by
`ValidBreak`'s documentation, now as a theorem. -/
theorem ofPoint_hashToPoint {Q acc : Point Fp} (hQ : Q.Valid) {chunks : List ℕ}
    (hb : ∀ m ∈ chunks, m < 2 ^ K)
    (h : hashToPoint orchardGenerators.S Q chunks = some acc) (hacc : acc.Valid) :
    PallasGroup.ofPoint acc hacc =
      2 ^ chunks.length • PallasGroup.ofPoint Q hQ +
        ∑ j ∈ Finset.range chunks.length,
          2 ^ (chunks.length - 1 - j) • pallasSAt (chunks.getD j 0) :=
  ofPointChain_hash chunks hQ hb h hacc

/-! ## Relation coefficients -/

/-- The table coefficient contributed by the consumed prefix `l`: generator `t`
receives `2^(n−1−j)` for every position `j` of `l` holding chunk value `t`. -/
def preCoeffs (l : List ℕ) (t : Fin (2 ^ K)) : Fq :=
  ∑ j ∈ Finset.range l.length,
    if l.getD j 0 = t.1 then (2 : Fq) ^ (l.length - 1 - j) else 0

/-- The indicator coefficient vector of a single table generator. -/
def indicator (c t : Fin (2 ^ K)) : Fq := if t = c then 1 else 0

/-- The escape chunk as a table index.  The reduction only consumes it under the
`< 2^K` bound of the real query families, where the reduction is the identity. -/
def chunkIdx (br : BreakData) : Fin (2 ^ K) :=
  ⟨br.chunk % 2 ^ K, Nat.mod_lt _ (Nat.two_pow_pos K)⟩

theorem chunkIdx_of_lt {br : BreakData} (h : br.chunk < 2 ^ K) :
    (chunkIdx br).1 = br.chunk :=
  Nat.mod_eq_of_lt h

private theorem coeffs_two_ne_zero : (2 : Fq) ≠ 0 := by
  intro h
  have hdvd : (CompElliptic.Fields.Pasta.PALLAS_SCALAR_CARD : ℕ) ∣ 2 := by
    have : ((2 : ℕ) : Fq) = 0 := by exact_mod_cast h
    exact (ZMod.natCast_eq_zero_iff 2 _).mp this
  have hle := Nat.le_of_dvd (by norm_num) hdvd
  revert hle
  norm_num [CompElliptic.Fields.Pasta.PALLAS_SCALAR_CARD]

/-- Scalar-field power-of-two coefficients act as the corresponding natural
multiplicities. -/
theorem two_pow_smul_eq_nsmul (e : ℕ) (P : PallasGroup) :
    (2 : Fq) ^ e • P = 2 ^ e • P := by
  have : (2 : Fq) ^ e = ((2 ^ e : ℕ) : Fq) := by push_cast; ring
  rw [this, Nat.cast_smul_eq_nsmul]

/-- Powers of two are nonzero in the odd-order Pallas scalar field — the
nontriviality witness for every escape kind with an honest prefix chain. -/
theorem two_pow_ne_zero (e : ℕ) : ((2 : Fq) ^ e) ≠ 0 :=
  pow_ne_zero e coeffs_two_ne_zero

/-- Summing the prefix coefficients against the table recovers the prefix's own
generator sum. -/
theorem sum_preCoeffs_smul {l : List ℕ} (hb : ∀ m ∈ l, m < 2 ^ K) :
    ∑ t : Fin (2 ^ K), preCoeffs l t • pallasS t =
      ∑ j ∈ Finset.range l.length,
        (2 : Fq) ^ (l.length - 1 - j) • pallasSAt (l.getD j 0) := by
  simp only [preCoeffs, Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  have hjlt : j < l.length := Finset.mem_range.mp hj
  have hbound : l.getD j 0 < 2 ^ K := by
    apply hb
    rw [List.getD_eq_getElem l 0 hjlt]
    exact List.getElem_mem _
  rw [Finset.sum_eq_single (⟨l.getD j 0, hbound⟩ : Fin (2 ^ K))]
  · simp [pallasS]
  · intro t _ hne
    rw [if_neg, zero_smul]
    intro heq
    exact hne (Fin.ext heq.symm)
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Summing an indicator against the table picks out its generator. -/
theorem sum_indicator_smul (c : Fin (2 ^ K)) :
    ∑ t : Fin (2 ^ K), indicator c t • pallasS t = pallasS c := by
  simp only [indicator, ite_smul, one_smul, zero_smul]
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]

/-! ## The coefficients of a break datum -/

/-- The relation coefficients `(a, α)` computed from a break datum: the table
vector and the domain-point coefficient of the escape's resolved point equation,
after substituting the prefix chain's explicit generator combination.  Data only —
correctness is `breakCoeffs_relation`, nontriviality `breakCoeffs_nontrivial`. -/
def breakCoeffs (br : BreakData) : (Fin (2 ^ K) → Fq) × Fq :=
  match br.kind with
  | .accZero => (preCoeffs br.pre, 2 ^ br.pre.length)
  | .genZero => (indicator (chunkIdx br), 0)
  | .collision neg =>
      (fun t => preCoeffs br.pre t + (if neg then 1 else -1) * indicator (chunkIdx br) t,
        2 ^ br.pre.length)
  | .sumZero =>
      (fun t => preCoeffs br.pre t + indicator (chunkIdx br) t, 2 ^ br.pre.length)
  | .doubleCollision =>
      (fun t => 2 * preCoeffs br.pre t + indicator (chunkIdx br) t,
        2 ^ (br.pre.length + 1))

/-- The computed coefficients are never all zero: every kind but `genZero` carries
the power-of-two domain coefficient, and `genZero`'s table vector is an
indicator. -/
theorem breakCoeffs_nontrivial (br : BreakData) :
    (breakCoeffs br).1 ≠ 0 ∨ (breakCoeffs br).2 ≠ 0 := by
  rcases hbr : br.kind with _ | _ | neg | _ | _ <;>
    simp only [breakCoeffs, hbr]
  · exact Or.inr (two_pow_ne_zero _)
  · refine Or.inl ?_
    intro h
    have := congrFun h (chunkIdx br)
    simp only [indicator, if_pos, Pi.zero_apply] at this
    exact one_ne_zero this
  · exact Or.inr (two_pow_ne_zero _)
  · exact Or.inr (two_pow_ne_zero _)
  · exact Or.inr (two_pow_ne_zero _)

/-- **Correctness of the computed coefficients**: for a valid break of a bounded
query, the coefficients satisfy the discrete-log relation in the Pallas group. -/
theorem breakCoeffs_relation {Qpt : Point Fp} (hQ : Qpt.Valid) {br : BreakData}
    (hvb : ValidBreak orchardGenerators.S Qpt br)
    (hpre : ∀ m ∈ br.pre, m < 2 ^ K) (hchunk : br.chunk < 2 ^ K) :
    (∑ t : Fin (2 ^ K), (breakCoeffs br).1 t • pallasS t) +
      (breakCoeffs br).2 • PallasGroup.ofPoint Qpt hQ = 0 := by
  obtain ⟨hchain, hPointEq⟩ := hvb
  have hacc : br.acc.Valid :=
    hashToPoint_valid_of_mem hQ (fun m hm => orchardGenerators.valid (hpre m hm)) hchain
  -- The prefix chain as the explicit table combination, in the reduction's coefficients.
  have hAcc : PallasGroup.ofPoint br.acc hacc =
      2 ^ br.pre.length • PallasGroup.ofPoint Qpt hQ +
        ∑ t : Fin (2 ^ K), preCoeffs br.pre t • pallasS t := by
    rw [sum_preCoeffs_smul hpre, ofPoint_hashToPoint hQ hpre hchain hacc]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => (two_pow_smul_eq_nsmul _ _).symm)
  -- The escape chunk generator, as a table element.
  have hSC : pallasS (chunkIdx br) =
      PallasGroup.ofPoint (orchardGenerators.S br.chunk) (orchardGenerators.valid hchunk) := by
    show pallasSAt (chunkIdx br).1 = _
    rw [chunkIdx_of_lt hchunk, pallasSAt_of_lt hchunk]
  cases hkind : br.kind with
  | accZero =>
    simp only [BreakData.PointEq, hkind] at hPointEq
    have hA0 : PallasGroup.ofPoint br.acc hacc = 0 :=
      PallasGroup.ofPoint_eq_zero hacc hPointEq
    rw [hAcc] at hA0
    simp only [breakCoeffs, hkind]
    rw [two_pow_smul_eq_nsmul, ← hA0]
    abel
  | genZero =>
    simp only [BreakData.PointEq, hkind] at hPointEq
    simp only [breakCoeffs, hkind]
    rw [sum_indicator_smul, zero_smul, add_zero, hSC]
    exact PallasGroup.ofPoint_eq_zero (orchardGenerators.valid hchunk) hPointEq
  | collision neg =>
    simp only [BreakData.PointEq, hkind] at hPointEq
    simp only [breakCoeffs, hkind]
    simp_rw [add_smul]
    rw [Finset.sum_add_distrib]
    simp_rw [mul_smul]
    rw [← Finset.smul_sum, sum_indicator_smul, two_pow_smul_eq_nsmul]
    cases neg with
    | false =>
      simp only [Bool.false_eq_true, if_false] at hPointEq ⊢
      have hAeq : PallasGroup.ofPoint br.acc hacc = pallasS (chunkIdx br) := by
        rw [hSC]; exact lift_eq_of_point_eq hacc (orchardGenerators.valid hchunk) hPointEq
      rw [hAcc] at hAeq
      rw [neg_one_smul, ← hAeq]
      abel
    | true =>
      simp only [if_true] at hPointEq ⊢
      have hAeq : PallasGroup.ofPoint br.acc hacc = -pallasS (chunkIdx br) := by
        rw [hSC, ← PallasGroup.ofPoint_neg (orchardGenerators.valid hchunk)]
        exact lift_eq_of_point_eq hacc _ hPointEq
      rw [hAcc] at hAeq
      rw [one_smul]
      have hz : 2 ^ br.pre.length • PallasGroup.ofPoint Qpt hQ +
          (∑ t : Fin (2 ^ K), preCoeffs br.pre t • pallasS t) + pallasS (chunkIdx br) = 0 := by
        rw [hAeq]; abel
      rw [← hz]; abel
  | sumZero =>
    simp only [BreakData.PointEq, hkind] at hPointEq
    simp only [breakCoeffs, hkind]
    simp_rw [add_smul]
    rw [Finset.sum_add_distrib, sum_indicator_smul, two_pow_smul_eq_nsmul]
    have hKind0 : PallasGroup.ofPoint br.acc hacc + pallasS (chunkIdx br) = 0 := by
      rw [hSC, ← PallasGroup.ofPoint_add hacc (orchardGenerators.valid hchunk)]
      exact PallasGroup.ofPoint_eq_zero _ hPointEq
    rw [hAcc] at hKind0
    rw [← hKind0]; abel
  | doubleCollision =>
    simp only [BreakData.PointEq, hkind] at hPointEq
    simp only [breakCoeffs, hkind]
    simp_rw [add_smul]
    rw [Finset.sum_add_distrib]
    simp_rw [mul_smul]
    rw [← Finset.smul_sum, sum_indicator_smul, two_pow_smul_eq_nsmul]
    have h2Pre := two_pow_smul_eq_nsmul 1 (∑ t : Fin (2 ^ K), preCoeffs br.pre t • pallasS t)
    simp only [pow_one] at h2Pre
    rw [h2Pre]
    have hKind0 : (2 : ℕ) • PallasGroup.ofPoint br.acc hacc + pallasS (chunkIdx br) = 0 := by
      rw [hSC, ← PallasGroup.ofPoint_nsmul 2 br.acc hacc,
        ← PallasGroup.ofPoint_add (Point.valid_nsmul hacc 2) (orchardGenerators.valid hchunk)]
      exact PallasGroup.ofPoint_eq_zero _ hPointEq
    rw [hAcc, smul_add, smul_smul] at hKind0
    rw [pow_succ, mul_comm (2 ^ br.pre.length) 2, ← hKind0]
    abel

/-- Package a valid bounded break as the games-facing relation object.  The data
fields are the computed `breakCoeffs`; the `Prop` fields are discharged from the
break's validity alone. -/
def relationOfValidBreak {Qpt : Point Fp} (hQ : Qpt.Valid) (br : BreakData)
    (hvb : ValidBreak orchardGenerators.S Qpt br)
    (hpre : ∀ m ∈ br.pre, m < 2 ^ K) (hchunk : br.chunk < 2 ^ K) :
    NontrivialRelationOne (F := Fq) pallasS (PallasGroup.ofPoint Qpt hQ) where
  a := (breakCoeffs br).1
  α := (breakCoeffs br).2
  nontrivial := breakCoeffs_nontrivial br
  relation := breakCoeffs_relation hQ hvb hpre hchunk

/-! ## Site dispatch

The classifier records which of the four query families escaped; each site fixes a
domain point and the witness's exact query at that site.  These dispatchers are
shared by the conversion and its correctness statement, so the produced relation is
tied to the same query the classifier evaluated. -/

/-- The domain point of a break site. -/
def siteQ : BreakSite → Point Fp
  | .commitIvk => orchardBases.ivkQ
  | .noteCommitOld => orchardBases.noteQ
  | .noteCommitNew => orchardBases.noteQ
  | .merkle _ => orchardBases.merkleQ

theorem siteQ_valid (s : BreakSite) : (siteQ s).Valid := by
  cases s with
  | commitIvk => exact .inl orchardBases.ivkQ_onCurve
  | noteCommitOld => exact .inl orchardBases.noteQ_onCurve
  | noteCommitNew => exact .inl orchardBases.noteQ_onCurve
  | merkle _ => exact .inl orchardBases.merkleQ_onCurve

/-- The domain point of a break site, in the Pallas group. -/
def sitePoint (s : BreakSite) : PallasGroup :=
  PallasGroup.ofPoint (siteQ s) (siteQ_valid s)

/-- The witness's exact Sinsemilla query at a break site. -/
def siteQuery (wit : ActionData) : BreakSite → List ℕ
  | .commitIvk => ivkQuery wit
  | .noteCommitOld => noteOldQuery wit
  | .noteCommitNew => noteNewQuery wit
  | .merkle i => merkleQuery wit i

/-- Every chunk of every site query indexes the generator table. -/
theorem siteQuery_bounded (wit : ActionData) (s : BreakSite) :
    ∀ m ∈ siteQuery wit s, m < 2 ^ K := by
  cases s with
  | commitIvk => intro m hm; exact chunksOf_mem_lt hm
  | noteCommitOld => intro m hm; exact chunksOf_mem_lt hm
  | noteCommitNew => intro m hm; exact chunksOf_mem_lt hm
  | merkle i =>
    intro m hm
    simp only [siteQuery, merkleQuery, merkleChunks, List.mem_map, List.mem_range] at hm
    obtain ⟨j, -, rfl⟩ := hm
    exact Nat.mod_lt _ (Nat.two_pow_pos K)

/-! ## From classified break data to the relation -/

/-- **Classifier inversion**: a classified escape is the escape of the witness's own
exact query at the recorded site. -/
theorem classify_query_inr {wit : ActionData} {abr : ActionBreakData}
    (h : classifyAction wit = some abr) :
    hashToPointB orchardGenerators.S (siteQ abr.site) (siteQuery wit abr.site) =
      .inr abr.data := by
  unfold classifyAction at h
  cases hivk : hashToPointB orchardGenerators.S ivkQ (ivkQuery wit) with
  | inr brd =>
    simp only [hivk] at h
    injection h with h'; subst h'
    exact hivk
  | inl Bi =>
    simp only [hivk] at h
    cases hold : hashToPointB orchardGenerators.S noteQ (noteOldQuery wit) with
    | inr brd =>
      simp only [hold] at h
      injection h with h'; subst h'
      exact hold
    | inl Bo =>
      simp only [hold] at h
      cases hnew : hashToPointB orchardGenerators.S noteQ (noteNewQuery wit) with
      | inr brd =>
        simp only [hnew] at h
        injection h with h'; subst h'
        exact hnew
      | inl Bn =>
        simp only [hnew] at h
        unfold classifyMerkle at h
        obtain ⟨i, -, hi⟩ := List.exists_of_findSome?_eq_some h
        cases hm : hashToPointB orchardGenerators.S merkleQ (merkleQuery wit i) with
        | inl B => simp [hm] at hi
        | inr br =>
          simp only [hm] at hi
          injection hi with hi'; subst hi'
          exact hm

/-- The escape datum of a site query is bounded: its prefix and escape chunk are
chunks of the query itself. -/
theorem break_bounds {wit : ActionData} {s : BreakSite} {br : BreakData}
    (h : hashToPointB orchardGenerators.S (siteQ s) (siteQuery wit s) = .inr br) :
    (∀ m ∈ br.pre, m < 2 ^ K) ∧ br.chunk < 2 ^ K := by
  obtain ⟨hsplit, -, -⟩ := hashToPointB_inr h
  have hb := siteQuery_bounded wit s
  rw [hsplit] at hb
  exact ⟨fun m hm => hb m (List.mem_append_left _ hm),
    hb br.chunk (List.mem_append_right _ List.mem_cons_self)⟩

/-- **Reduction from a classified `ActionBreakData` into the games-facing
discrete-log-relation** at the escaped site's domain point.  The hypothesis ties the
datum to the witness's own query; `classify_query_inr` discharges it for the
classifier's output. -/
def relationOfBreakData (wit : ActionData) (abr : ActionBreakData)
    (h : hashToPointB orchardGenerators.S (siteQ abr.site) (siteQuery wit abr.site) =
      .inr abr.data) :
    NontrivialRelationOne (F := Fq) pallasS (sitePoint abr.site) :=
  relationOfValidBreak (siteQ_valid abr.site) abr.data
    (validBreak_of_inr (siteQ_valid abr.site)
      (fun m hm => orchardGenerators.S_onCurve (siteQuery_bounded wit abr.site m hm)) h)
    (break_bounds h).1 (break_bounds h).2

/-- A classified Action escape reduced onward: the site together with a nontrivial
discrete-log relation among the deployed generator table and that site's domain
point. -/
structure ActionDLBreak where
  site : BreakSite
  rel : NontrivialRelationOne (F := Fq) pallasS (sitePoint site)

/-- End-to-end computable reduction at the Action boundary: classify the witness's
four query families and reduce the first escape to its discrete-log relation. -/
def classifyRelation (wit : ActionData) : Option ActionDLBreak :=
  match h : classifyAction wit with
  | none => none
  | some abr => some ⟨abr.site, relationOfBreakData wit abr (classify_query_inr h)⟩

/-- The reduction succeeds exactly when the classifier reports an escape. -/
theorem classifyRelation_isSome_iff (wit : ActionData) :
    (classifyRelation wit).isSome ↔ (classifyAction wit).isSome := by
  unfold classifyRelation
  split <;> simp_all

/-- The reduction reports the classifier's own site. -/
theorem classifyRelation_site {wit : ActionData} {dlb : ActionDLBreak}
    (h : classifyRelation wit = some dlb) :
    ∃ abr, classifyAction wit = some abr ∧ dlb.site = abr.site := by
  unfold classifyRelation at h
  split at h
  · exact absurd h (by simp)
  · next abr heq => exact ⟨abr, heq, by injection h with h'; rw [← h']⟩

end Zcash.Security.Ledger.Bridge
