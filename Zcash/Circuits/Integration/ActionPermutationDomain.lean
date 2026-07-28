import Zcash.Circuits.Integration.ActionPermutationDomainCompute
import Zcash.Circuits.Integration.PermutationCompiler
import Zcash.Snark.Soundness.Canonical.ConstraintModel
import Zcash.Circuits.Integration.TopLevelAssignment

/-!
# Action permutation domain and verifier layout

This module discharges the domain and chunk-layout premises retained by the
generic permutation semantics for the verifying key derived from
`actionCircuit`.

The keygen permutation itself belongs to the separate replay/assembly layer.
`cycleOfKeygenColumns` therefore accepts `fullSigma`, its active restriction,
the restriction equation, and the common-column identification explicitly.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (deltaFp omegaOf omegaOf_isPrimitiveRoot powFast_eq_pow scalarFieldOrder)

open Polynomial
open Halo2
open Zcash.Circuits.Action (actionCircuit)

namespace ActionPermutationDomain

variable {G : Type} [AddCommGroup G] [Inhabited G]

abbrev actionShape (pp : Keygen.ProofParams) : Shape :=
  pp.mergeDerived actionCircuit

abbrev actionVk (pp : Keygen.ProofParams) (urs : URS G) :
    VerifyingKey (actionShape pp) Zcash.Circuits.Fp G :=
  Halo2.TopLevelCircuit.toVerifierKey
    actionCircuit pp urs

/-- The permutation chunks of every derived Action VK are `[7, 7, 1]`, with
the verifier's exact query-layout and common-column indices. -/
theorem permutationChunks_eq (pp : Keygen.ProofParams) (urs : URS G) :
    (actionVk pp urs).permutationChunks =
      [[(.instance 0, 0), (.advice 0, 1), (.advice 1, 2),
          (.advice 2, 3), (.advice 3, 4), (.advice 4, 5),
          (.advice 5, 6)],
        [(.advice 6, 7), (.advice 7, 8), (.advice 8, 9),
          (.advice 9, 10), (.fixed 0, 11), (.fixed 7, 12),
          (.fixed 8, 13)],
        [(.fixed 9, 14)]] := by
  change
    Keygen.permutationChunksOf actionCircuit.selectorMap
        actionCircuit.constraintSystem = _
  exact chunks_eq

set_option maxRecDepth 100000 in
/-- The derived Action VK has one verifier permutation set per chunk. -/
theorem chunkCount (pp : Keygen.ProofParams) (urs : URS G) :
    (actionVk pp urs).permutationChunks.length =
      (actionShape pp).numPermutationSets := by
  rw [permutationChunks_eq]
  change 3 =
    (actionCircuit.constraintSystem.permutationColumns.length +
      actionCircuit.constraintSystem.chunkLen - 1) /
      actionCircuit.constraintSystem.chunkLen
  have hcolumns :
      actionCircuit.constraintSystem.permutationColumns.length = 15 :=
    congrArg Prod.fst columnCount_chunkLen_eq
  have hchunkLen :
      actionCircuit.constraintSystem.chunkLen = 7 :=
    congrArg Prod.snd columnCount_chunkLen_eq
  rw [hcolumns, hchunkLen]

set_option maxRecDepth 100000 in
/-- The Action verifier's permutation chunk family is nonempty. -/
theorem nonempty (pp : Keygen.ProofParams) :
    0 < (actionShape pp).numPermutationSets := by
  change 0 <
    (actionCircuit.constraintSystem.permutationColumns.length +
      actionCircuit.constraintSystem.chunkLen - 1) /
      actionCircuit.constraintSystem.chunkLen
  have hcolumns :
      actionCircuit.constraintSystem.permutationColumns.length = 15 :=
    congrArg Prod.fst columnCount_chunkLen_eq
  have hchunkLen :
      actionCircuit.constraintSystem.chunkLen = 7 :=
    congrArg Prod.snd columnCount_chunkLen_eq
  rw [hcolumns, hchunkLen]
  decide

/-- The concrete chunk widths retained for consumers that need their exact values. -/
theorem chunkLengths (pp : Keygen.ProofParams) (urs : URS G) :
    (actionVk pp urs).permutationChunks.map List.length = [7, 7, 1] := by
  rw [permutationChunks_eq]
  decide

set_option maxRecDepth 100000 in
/-- Every derived Action permutation chunk has width at most `vk.chunkLen`. -/
theorem chunkLength_le (pp : Keygen.ProofParams) (urs : URS G) :
    ∀ i, i < (actionShape pp).numPermutationSets →
      ((actionVk pp urs).permutationChunks.getD i []).length ≤
        (actionVk pp urs).chunkLen := by
  intro i hi
  rw [permutationChunks_eq]
  change
    ([[((.instance 0, 0) : ColumnRef × ℕ), (.advice 0, 1), (.advice 1, 2),
          (.advice 2, 3), (.advice 3, 4), (.advice 4, 5),
          (.advice 5, 6)],
        [(.advice 6, 7), (.advice 7, 8), (.advice 8, 9),
          (.advice 9, 10), (.fixed 0, 11), (.fixed 7, 12),
          (.fixed 8, 13)],
        [(.fixed 9, 14)]].getD i []).length ≤
      actionCircuit.constraintSystem.chunkLen
  have hdata := columnCount_chunkLen_eq
  have hsets : (actionShape pp).numPermutationSets = 3 := by
    simpa using (chunkCount pp urs).symm.trans (by simp [permutationChunks_eq])
  rw [hsets] at hi
  have hlen :
      actionCircuit.constraintSystem.chunkLen = 7 :=
    congrArg Prod.snd hdata
  rw [hlen]
  interval_cases i <;> decide

/-- Resolver pairing preserves each concrete VK chunk's width. -/
theorem resolverPairsLength_le
    (pp : Keygen.ProofParams) (urs : URS G)
    (poly : CommitmentId → Polynomial Fp)
    (p : Fin (actionShape pp).numProofs) :
    ∀ i, i < (actionShape pp).numPermutationSets →
      (ResolverPermutationPairs (actionVk pp urs) poly p i).length ≤
        (actionVk pp urs).chunkLen := by
  intro i hi
  simpa [ResolverPermutationPairs, permutationChunkPairsOfResolver] using
    chunkLength_le pp urs i hi

set_option maxRecDepth 100000 in
/-- Every chunk value reference selects an in-range rotation-zero query-layout
entry, and every common-permutation index is in range. -/
theorem routingCoherent_of_derived
    (pp : Keygen.ProofParams) (urs : URS G) :
    PermutationChunkRoutingCoherent (actionVk pp urs) := by
  have hadviceLayout :
      (actionVk pp urs).adviceQueryLayout =
        actionCircuit.pinnedCS.adviceQueryLayout :=
    (actionCircuit.toVerifierKey_adviceQueryLayout_derived
      pp urs).trans adviceQueryLayout_eq
  have hfixedLayout :
      (actionVk pp urs).fixedQueryLayout =
        actionCircuit.pinnedCS.fixedQueryLayout :=
    (actionCircuit.toVerifierKey_fixedQueryLayout_derived
      pp urs).trans fixedQueryLayout_eq
  have hinstanceLayout :
      (actionVk pp urs).instanceQueryLayout =
        actionCircuit.pinnedCS.instanceQueryLayout :=
    (actionCircuit.toVerifierKey_instanceQueryLayout_derived
      pp urs).trans instanceQueryLayout_eq
  rintro chunk hchunk ⟨ref, common⟩ href
  have hroute := routingCoherent chunk hchunk (ref, common) href
  rcases hroute with ⟨hrefCoherent, hcommon⟩
  constructor
  · cases ref with
    | advice i =>
        rcases hrefCoherent with ⟨hi, hrotation⟩
        change PermutationColumnRef.Coherent
          (actionVk pp urs) (.advice i)
        simp only [PermutationColumnRef.Coherent]
        refine ⟨?_, ?_, ?_⟩
        · rw [← actionCircuit.toVerifierKey_adviceQueryCount
            pp urs, hadviceLayout]
          exact hi
        · simpa only [hadviceLayout] using hi
        · simpa only [hadviceLayout] using hrotation
    | fixed i =>
        rcases hrefCoherent with ⟨hi, hrotation⟩
        change PermutationColumnRef.Coherent
          (actionVk pp urs) (.fixed i)
        simp only [PermutationColumnRef.Coherent]
        refine ⟨?_, ?_, ?_⟩
        · rw [← actionCircuit.toVerifierKey_fixedQueryCount
            pp urs, hfixedLayout]
          exact hi
        · simpa only [hfixedLayout] using hi
        · simpa only [hfixedLayout] using hrotation
    | «instance» i =>
        rcases hrefCoherent with ⟨hi, hrotation⟩
        change PermutationColumnRef.Coherent
          (actionVk pp urs) (.instance i)
        simp only [PermutationColumnRef.Coherent]
        refine ⟨?_, ?_, ?_⟩
        · rw [← actionCircuit.toVerifierKey_instanceQueryCount
            pp urs, hinstanceLayout]
          exact hi
        · simpa only [hinstanceLayout] using hi
        · simpa only [hinstanceLayout] using hrotation
  · simpa [actionShape, Keygen.ProofParams.mergeDerived] using hcommon

/--
Flattening the derived verifier chunks and decoding their query references
recovers the compiler's original permutation-column order.
-/
theorem permutationColumnAddresses_eq
    (pp : Keygen.ProofParams) (urs : URS G) :
    ((actionVk pp urs).permutationChunks.flatten.map
        (fun reference =>
          permutationColumnAddress (actionVk pp urs) reference.1)) =
      (Keygen.permColsOf
        actionCircuit.constraintSystem).map
          Halo2.Layout.ColRef.toAny := by
  exact topLevelPermutationColumnAddresses_eq
    actionCircuit pp urs
      (routingCoherent_of_derived pp urs)

/-! ## Pasta permutation-name cosets -/

/-- The odd factor of `|Fpˣ|`, after removing Pasta's `2^32` root-of-unity
subgroup. -/
def pastaOddFactor : ℕ := (scalarFieldOrder - 1) / 2 ^ 32

theorem scalarFieldOrder_sub_one_factorization :
    2 ^ 32 * pastaOddFactor = scalarFieldOrder - 1 := by
  norm_num [pastaOddFactor, scalarFieldOrder,
    CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]

/-- `deltaFp = 5^(2^32)` lies in the odd-order factor of `Fpˣ`. -/
theorem deltaFp_pow_pastaOddFactor :
    deltaFp ^ pastaOddFactor = 1 := by
  rw [deltaFp, powFast_eq_pow, ← pow_mul,
    scalarFieldOrder_sub_one_factorization]
  exact ZMod.pow_card_sub_one_eq_one (by decide : (5 : Fp) ≠ 0)

theorem pastaOddFactor_coprime_actionDomain :
    Nat.Coprime (2 ^ 11) pastaOddFactor := by
  norm_num [pastaOddFactor, scalarFieldOrder,
    CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]

/-- The 21 padded Action column names `deltaFp^j` occupy distinct cosets of
the size-2048 evaluation subgroup. -/
theorem deltaFp_actionCosets
    (j j' : Fin 21) (t : ℕ)
    (h :
      deltaFp ^ (j : ℕ) =
        omegaOf 11 ^ t * deltaFp ^ (j' : ℕ)) :
    j = j' := by
  have hj :
      (deltaFp ^ (j : ℕ)) ^ pastaOddFactor = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul,
      deltaFp_pow_pastaOddFactor, one_pow]
  have hj' :
      (deltaFp ^ (j' : ℕ)) ^ pastaOddFactor = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul,
      deltaFp_pow_pastaOddFactor, one_pow]
  have hpow := congrArg (fun x : Fp => x ^ pastaOddFactor) h
  change (deltaFp ^ (j : ℕ)) ^ pastaOddFactor =
    (omegaOf 11 ^ t * deltaFp ^ (j' : ℕ)) ^ pastaOddFactor at hpow
  rw [hj, mul_pow, hj', mul_one] at hpow
  have htMul : omegaOf 11 ^ (t * pastaOddFactor) = 1 := by
    rw [pow_mul]
    exact hpow.symm
  have hprimitive : IsPrimitiveRoot (omegaOf 11) (2 ^ 11) :=
    omegaOf_isPrimitiveRoot 11 (by omega)
  have hdvdMul : 2 ^ 11 ∣ t * pastaOddFactor :=
    (hprimitive.pow_eq_one_iff_dvd _).mp htMul
  have hdvd : 2 ^ 11 ∣ t :=
    pastaOddFactor_coprime_actionDomain.dvd_of_dvd_mul_right hdvdMul
  have ht : omegaOf 11 ^ t = 1 :=
    (hprimitive.pow_eq_one_iff_dvd _).mpr hdvd
  rw [ht, one_mul] at h
  exact deltaPowers_injective h

/-! ## Derived evaluation-domain facts -/

theorem rowsInjective (pp : Keygen.ProofParams) (urs : URS G) :
    Function.Injective fun i : Fin (actionVk pp urs).n =>
      (actionVk pp urs).omega ^ (i : ℕ) := by
  change Function.Injective fun i :
      Fin (2 ^ actionCircuit.domainExponent) =>
    omegaOf actionCircuit.domainExponent ^ (i : ℕ)
  exact TopLevelAssignment.domainRowsInjective domainExponent_lt

theorem root (pp : Keygen.ProofParams) (urs : URS G) :
    (actionVk pp urs).omega ^ (actionVk pp urs).n = 1 := by
  change omegaOf actionCircuit.domainExponent ^
    (2 ^ actionCircuit.domainExponent) = 1
  exact TopLevelAssignment.domainRoot domainExponent_lt

theorem blindingFactors_lt (pp : Keygen.ProofParams) (urs : URS G) :
    (actionVk pp urs).blindingFactors < (actionVk pp urs).n := by
  change actionCircuit.blindingFactors <
    2 ^ actionCircuit.domainExponent
  exact TopLevelAssignment.blindingFactors_lt_domainSize

/-- The active permutation prefix ends at the last usable Action row. -/
abbrev activeRows (pp : Keygen.ProofParams) (urs : URS G) : ℕ :=
  (actionVk pp urs).n - (actionVk pp urs).blindingFactors - 1

theorem activeRows_le (pp : Keygen.ProofParams) (urs : URS G) :
    activeRows pp urs ≤ (actionVk pp urs).n := by
  unfold activeRows
  omega

/-- Canonical selectors and the derived usable-row count form the complete
generic permutation-domain record. In particular its `lastRotation` field is
the verifier's `omega^(-(blindingFactors + 1))` rotation. -/
theorem domain
    (pp : Keygen.ProofParams) (urs : URS G)
    (ch : Challenges (actionShape pp).k Fp)
    (poly : CommitmentId → Polynomial Fp) :
    let hblinding := blindingFactors_lt pp urs
    let model :=
      canonicalConstraintModelOfPermutationResolver
        (actionVk pp urs) ch poly hblinding
    ResolverPermutationDomain (actionVk pp urs)
      model.l0 model.lLast model.lBlind
      (actionVk pp urs).n
      ((actionVk pp urs).n - (actionVk pp urs).blindingFactors - 1) := by
  exact ResolverPermutationDomain.ofCanonicalConstraintModel
    (actionVk pp urs) ch poly (blindingFactors_lt pp urs)
      (rowsInjective pp urs) (root pp urs) (nonempty pp)
      (chunkCount pp urs)

/-- The last usable Action row is exactly the verifier's negative rotation. -/
theorem lastRowRotation (pp : Keygen.ProofParams) (urs : URS G) :
    (actionVk pp urs).omega ^
        ((actionVk pp urs).n - (actionVk pp urs).blindingFactors - 1) =
      (actionVk pp urs).omega ^
        (-(((actionVk pp urs).blindingFactors : ℤ) + 1)) := by
  let ch : Challenges (actionShape pp).k Fp :=
    { theta := 0
      beta := 0
      gamma := 0
      y := 0
      x := 0
      x1 := 0
      x2 := 0
      x3 := 0
      x4 := 0
      xi := 0
      z := 0
      ipaRound := fun _ => 0 }
  let poly : CommitmentId → Polynomial Fp := fun _ => 0
  exact (domain pp urs ch poly).lastRotation

set_option maxRecDepth 100000 in
/-- Action chunk names are injective on any active prefix of the derived
evaluation domain. This is the `hnames` premise retained by
`ResolverPermutationCycle.ofKeygenColumns`. -/
theorem namesInjective
    (pp : Keygen.ProofParams) (urs : URS G)
    (poly : CommitmentId → Polynomial Fp)
    (p : Fin (actionShape pp).numProofs)
    {activeRows : ℕ} (hactive : activeRows ≤ (actionVk pp urs).n) :
    Function.Injective fun c :
        ResolverPermutationCell (actionVk pp urs) poly p activeRows =>
      chunkRowName (actionVk pp urs).omega (actionVk pp urs).delta
        (actionVk pp urs).chunkLen c.1 c.2.1 c.2.2 := by
  have hfull :
      Function.Injective fun c :
          ResolverPermutationCell (actionVk pp urs) poly p
            (actionVk pp urs).n =>
        chunkRowName (actionVk pp urs).omega (actionVk pp urs).delta
          (actionVk pp urs).chunkLen c.1 c.2.1 c.2.2 := by
    apply chunkRowName_injective_of_coset
      (resolverPairsLength_le pp urs poly p)
    · intro j
      apply pow_ne_zero
      change deltaFp ≠ 0
      rw [deltaFp, powFast_eq_pow]
      exact pow_ne_zero _ (by decide : (5 : Fp) ≠ 0)
    · exact root pp urs
    · intro i i' hi hi' heq
      have hfin :
          (⟨i, hi⟩ : Fin (actionVk pp urs).n) =
            ⟨i', hi'⟩ :=
        rowsInjective pp urs heq
      exact Fin.ext_iff.mp hfin
    · intro j j' t hcoset
      change
        deltaFp ^ (j : ℕ) =
          omegaOf actionCircuit.domainExponent ^ t *
            deltaFp ^ (j' : ℕ) at hcoset
      rw [domainExponent_eq] at hcoset
      have hsize :
          (actionShape pp).numPermutationSets *
              (actionVk pp urs).chunkLen = 21 := by
        change
          ((actionCircuit.constraintSystem.permutationColumns.length +
              actionCircuit.constraintSystem.chunkLen - 1) /
              actionCircuit.constraintSystem.chunkLen) *
            actionCircuit.constraintSystem.chunkLen = 21
        have hcolumns :
            actionCircuit.constraintSystem.permutationColumns.length = 15 :=
          congrArg Prod.fst columnCount_chunkLen_eq
        have hchunkLen :
            actionCircuit.constraintSystem.chunkLen = 7 :=
          congrArg Prod.snd columnCount_chunkLen_eq
        rw [hcolumns, hchunkLen]
      have hj : (j : ℕ) < 21 := by
        have hlt := j.isLt
        omega
      have hj' : (j' : ℕ) < 21 := by
        have hlt := j'.isLt
        omega
      apply Fin.ext
      have heq21 :
          (⟨j, hj⟩ : Fin 21) = ⟨j', hj'⟩ :=
        deltaFp_actionCosets ⟨j, hj⟩ ⟨j', hj'⟩ t hcoset
      exact congrArg (fun x : Fin 21 => x.val) heq21
  intro c d hname
  have hwiden := widenPermutationChunkCell_injective
    (nc := (actionShape pp).numPermutationSets)
    (width := fun i =>
      (ResolverPermutationPairs (actionVk pp urs) poly p i).length)
    hactive
  have hwname :
      chunkRowName (actionVk pp urs).omega (actionVk pp urs).delta
          (actionVk pp urs).chunkLen
          (widenPermutationChunkCell hactive c).1
          (widenPermutationChunkCell hactive c).2.1
          (widenPermutationChunkCell hactive c).2.2 =
        chunkRowName (actionVk pp urs).omega (actionVk pp urs).delta
          (actionVk pp urs).chunkLen
          (widenPermutationChunkCell hactive d).1
          (widenPermutationChunkCell hactive d).2.1
          (widenPermutationChunkCell hactive d).2.2 := by
    simpa only [widenPermutationChunkCell_fst,
      widenPermutationChunkCell_row,
      widenPermutationChunkCell_column] using hname
  exact hwiden (hfull hwname)

/-- Assemble the semantic cycle at any active-row prefix preserved by the
replayed full permutation. -/
noncomputable def cycleOfKeygenColumnsAt
    (pp : Keygen.ProofParams) (urs : URS G)
    (poly : CommitmentId → Polynomial Fp)
    (p : Fin (actionShape pp).numProofs)
    {m : ℕ}
    (hactive : m ≤ (actionVk pp urs).n)
    (fullSigma : Equiv.Perm
      (ResolverPermutationCell (actionVk pp urs) poly p
        (actionVk pp urs).n))
    (sigma : Equiv.Perm
      (ResolverPermutationCell (actionVk pp urs) poly p
        m))
    (hcolumns : ∀
      (chunk : Fin (actionShape pp).numPermutationSets)
      (column : Fin
        (ResolverPermutationPairs (actionVk pp urs) poly p chunk).length),
      (ResolverPermutationPairs
          (actionVk pp urs) poly p chunk)[column].2 =
        keygenSigmaColumn
          (actionVk pp urs).omega (actionVk pp urs).delta
          (actionVk pp urs).chunkLen fullSigma chunk column)
    (hrestrict : ∀ c :
        ResolverPermutationCell (actionVk pp urs) poly p m,
      widenPermutationChunkCell hactive (sigma c) =
        fullSigma
          (widenPermutationChunkCell hactive c)) :
    ResolverPermutationCycle (actionVk pp urs) poly p m :=
  ResolverPermutationCycle.ofKeygenColumns
    (actionVk pp urs) poly p hactive fullSigma sigma
      (rowsInjective pp urs) hcolumns hrestrict
      (namesInjective pp urs poly p hactive)

/-- Assemble the semantic cycle at the verifier-derived active-row boundary. -/
noncomputable def cycleOfKeygenColumns
    (pp : Keygen.ProofParams) (urs : URS G)
    (poly : CommitmentId → Polynomial Fp)
    (p : Fin (actionShape pp).numProofs)
    (fullSigma : Equiv.Perm
      (ResolverPermutationCell (actionVk pp urs) poly p
        (actionVk pp urs).n))
    (sigma : Equiv.Perm
      (ResolverPermutationCell (actionVk pp urs) poly p
        (activeRows pp urs)))
    (hcolumns : ∀
      (chunk : Fin (actionShape pp).numPermutationSets)
      (column : Fin
        (ResolverPermutationPairs (actionVk pp urs) poly p chunk).length),
      (ResolverPermutationPairs
          (actionVk pp urs) poly p chunk)[column].2 =
        keygenSigmaColumn
          (actionVk pp urs).omega (actionVk pp urs).delta
          (actionVk pp urs).chunkLen fullSigma chunk column)
    (hrestrict : ∀ c :
        ResolverPermutationCell (actionVk pp urs) poly p
          (activeRows pp urs),
      widenPermutationChunkCell (activeRows_le pp urs) (sigma c) =
        fullSigma
          (widenPermutationChunkCell (activeRows_le pp urs) c)) :
    ResolverPermutationCycle (actionVk pp urs) poly p
      (activeRows pp urs) :=
  cycleOfKeygenColumnsAt pp urs poly p (activeRows_le pp urs)
    fullSigma sigma hcolumns hrestrict

assert_no_sorry permutationChunks_eq
assert_no_sorry routingCoherent_of_derived
assert_no_sorry deltaFp_actionCosets
assert_no_sorry domain
assert_no_sorry namesInjective
assert_no_sorry cycleOfKeygenColumnsAt
assert_no_sorry cycleOfKeygenColumns

end ActionPermutationDomain

end Zcash.Snark
