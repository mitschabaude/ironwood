import Zcash.Circuits.Integration.FixedColumns
import Zcash.Common.RelationWitness
import Zcash.Circuits.Integration.ActionPermutationDomain
import Zcash.Circuits.Integration.CopyListMembership

/-!
# The Action copy-replay witness

The concrete copy adapter: Action's permutation cells, the endpoint encoding (cells
through the placement, instance endpoints at absolute rows, constants at their
allocated constants-column cells), the cell valuation (the environment read of the
cell's permutation column), and the witness constructor feeding
`CopyReplayWitness.ofPairValues` with kind-dispatched pair facts — non-constant copies
through the keygen copy list and the σ-semantics value transport, constant copies
through the allocation zip and the constants-column reads.
-/

namespace Zcash.Snark

open Halo2 Halo2.Layout Zcash.Circuits Zcash.Circuits.Action
open Keygen

/-- Action's permutation columns, in verifying-key order. -/
def actionPermCols : List ColRef :=
  permColsOf actionCircuit.constraintSystem

/-- The permutation-column count (15 for the deployed Action circuit). -/
def actionNumPermCols : ℕ := actionPermCols.length

/-- The evaluation-domain size at the derived exponent. -/
def actionDomainSize : ℕ := 2 ^ actionCircuit.domainExponent

/-- The V1 constants allocation of the Action operation stream. -/
def actionConsts : List (ℕ × ℕ × ℕ) :=
  constantCopyEntries actionCircuit.constraintSystem
    (actionCircuit.operations)

/-- The keygen copy list of the Action operation stream. -/
def actionCopyRaw : List (ℕ × ℕ × ℕ × ℕ) :=
  Halo2.Layout.V1.copyList actionPermCols
    actionCircuit.regionStarts
    (actionCircuit.operations) actionConsts

/-- The last usable row of the circuit-derived Action domain. -/
def actionActiveRows : ℕ :=
  actionCircuit.usableRowsAt
    actionCircuit.domainExponent

theorem actionNumPermCols_pos : 0 < actionNumPermCols := by
  native_decide

theorem actionDomainSize_pos : 0 < actionDomainSize :=
  Nat.two_pow_pos _

@[simp]
theorem actionDomainSize_eq
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G) :
    actionDomainSize = (ActionPermutationDomain.actionVk pp urs).n := by
  simp [actionDomainSize]

theorem actionActiveRows_le_domainSize :
    actionActiveRows ≤ actionDomainSize := by
  unfold actionActiveRows TopLevelCircuit.usableRowsAt
  exact le_trans (Nat.sub_le _ _) (Nat.sub_le _ _)

@[simp]
theorem actionActiveRows_eq
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G) :
    actionActiveRows = ActionPermutationDomain.activeRows pp urs := by
  simp [actionActiveRows, ActionPermutationDomain.activeRows,
    TopLevelCircuit.usableRowsAt]

/-- Every keygen copy tuple is in range: 15 permutation columns, `2^11` rows. -/
theorem actionCopyBounds : ∀ t ∈ actionCopyRaw, t.1 < actionNumPermCols ∧
    t.2.1 < actionDomainSize ∧ t.2.2.1 < actionNumPermCols ∧
    t.2.2.2 < actionDomainSize := by
  native_decide

/-- The decoded Action copy list. -/
def actionCopies :
    List (FlatCell actionNumPermCols actionDomainSize ×
      FlatCell actionNumPermCols actionDomainSize) :=
  decodeCopies actionNumPermCols actionDomainSize actionCopyRaw actionCopyBounds

/-- Decoded copy pairs whose endpoints escape the usable-row prefix. -/
def actionCopyActiveRowFailures :
    List (FlatCell actionNumPermCols actionDomainSize ×
      FlatCell actionNumPermCols actionDomainSize) :=
  actionCopies.filter fun pair =>
    decide (¬ (
      (pair.1.2 : ℕ) < actionActiveRows ∧
        (pair.2.2 : ℕ) < actionActiveRows))

/-- Every Action keygen copy endpoint lies in the usable-row prefix. -/
theorem actionCopyActiveRowFailures_eq_nil :
    actionCopyActiveRowFailures = [] := by
  native_decide

/-- Pointwise usable-row bounds extracted from the finite copy diagnostic. -/
theorem actionCopyRowsActive
    (pair : FlatCell actionNumPermCols actionDomainSize ×
      FlatCell actionNumPermCols actionDomainSize)
    (hpair : pair ∈ actionCopies) :
    (pair.1.2 : ℕ) < actionActiveRows ∧
      (pair.2.2 : ℕ) < actionActiveRows := by
  by_contra hnot
  have hfailure : pair ∈ actionCopyActiveRowFailures := by
    rw [actionCopyActiveRowFailures, List.mem_filter]
    exact ⟨hpair, decide_eq_true hnot⟩
  rw [actionCopyActiveRowFailures_eq_nil] at hfailure
  simp at hfailure

/-- Action keygen replays preserve the usable-row prefix. -/
theorem actionReplayPreservesActive
    (cell : FlatCell actionNumPermCols actionDomainSize)
    (hcell : (cell.2 : ℕ) < actionActiveRows) :
    ((replayKeygenPermutation actionCopies cell).2 : ℕ) <
      actionActiveRows := by
  apply replayKeygenPermutation_preserves actionCopies
    (fun candidate => (candidate.2 : ℕ) < actionActiveRows)
  · intro pair hpair
    exact actionCopyRowsActive pair hpair
  · exact hcell

set_option maxRecDepth 100000 in
/-- The Action permutation argument has three chunks. -/
theorem actionNumPermutationSets_eq
    (pp : ProofParams) :
    (ActionPermutationDomain.actionShape pp).numPermutationSets = 3 := by
  change
    (actionCircuit.constraintSystem.permutationColumns.length +
        actionCircuit.constraintSystem.chunkLen - 1) /
      actionCircuit.constraintSystem.chunkLen = 3
  have hdata := ActionPermutationDomain.columnCount_chunkLen_eq
  have hcolumns :
      actionCircuit.constraintSystem.permutationColumns.length =
        15 :=
    congrArg Prod.fst hdata
  have hchunkLen :
      actionCircuit.constraintSystem.chunkLen = 7 :=
    congrArg Prod.snd hdata
  rw [hcolumns, hchunkLen]

/-- The Action permutation argument has 15 columns. -/
theorem actionNumPermCols_eq : actionNumPermCols = 15 := by
  native_decide

set_option maxRecDepth 100000 in
/-- The Action permutation chunk width is seven. -/
theorem actionChunkLen_eq
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G) :
    (ActionPermutationDomain.actionVk pp urs).chunkLen = 7 := by
  change actionCircuit.constraintSystem.chunkLen = 7
  exact congrArg Prod.snd
    ActionPermutationDomain.columnCount_chunkLen_eq

set_option maxRecDepth 100000 in
/-- Resolver-backed Action permutation chunks have the exact `[7,7,1]` widths. -/
theorem actionResolverChunkWidth
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → Polynomial Fp)
    (proofIndex :
      Fin (ActionPermutationDomain.actionShape pp).numProofs)
    (chunk :
      Fin (ActionPermutationDomain.actionShape pp).numPermutationSets) :
    (ResolverPermutationPairs
        (ActionPermutationDomain.actionVk pp urs)
        poly proofIndex chunk).length =
      min (ActionPermutationDomain.actionVk pp urs).chunkLen
        (actionNumPermCols -
          (chunk : ℕ) *
            (ActionPermutationDomain.actionVk pp urs).chunkLen) := by
  simp only [ResolverPermutationPairs,
    permutationChunkPairsOfResolver, List.length_map]
  rw [ActionPermutationDomain.permutationChunks_eq,
    actionChunkLen_eq, actionNumPermCols_eq]
  have hchunk : (chunk : ℕ) < 3 := by
    simpa only [actionNumPermutationSets_eq] using chunk.isLt
  have hcases :
      (chunk : ℕ) = 0 ∨ (chunk : ℕ) = 1 ∨ (chunk : ℕ) = 2 := by
    omega
  rcases hcases with hzero | hone | htwo
  · simp [hzero]
  · simp [hone]
  · simp [htwo]

/-- Flatten the derived `[7,7,1]` Action chunks to `(row, global column)`. -/
noncomputable def actionChunkFlatten
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → Polynomial Fp)
    (proofIndex :
      Fin (ActionPermutationDomain.actionShape pp).numProofs) :
    ResolverPermutationCell
        (ActionPermutationDomain.actionVk pp urs)
        poly proofIndex actionDomainSize ≃
      Fin actionDomainSize × Fin actionNumPermCols :=
  Layout.Asm.chunkFlatten
    (ActionPermutationDomain.actionShape pp).numPermutationSets
    actionNumPermCols
    (ActionPermutationDomain.actionVk pp urs).chunkLen
    actionDomainSize
    (fun chunk =>
      (ResolverPermutationPairs
        (ActionPermutationDomain.actionVk pp urs)
        poly proofIndex chunk).length)
    (by rw [actionChunkLen_eq]; decide)
    (by
      rw [actionNumPermCols_eq, actionNumPermutationSets_eq,
        actionChunkLen_eq]
      decide)
    (actionResolverChunkWidth pp urs poly proofIndex)

/-- The full-domain Action keygen permutation in resolver chunk coordinates. -/
noncomputable def actionFullSigma
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → Polynomial Fp)
    (proofIndex :
      Fin (ActionPermutationDomain.actionShape pp).numProofs) :
    Equiv.Perm
      (ResolverPermutationCell
        (ActionPermutationDomain.actionVk pp urs)
        poly proofIndex actionDomainSize) :=
  chunkPermutationOfFlat
    (actionChunkFlatten pp urs poly proofIndex)
    ((Equiv.prodComm
        (Fin actionNumPermCols) (Fin actionDomainSize)).permCongr
      (replayKeygenPermutation actionCopies))

/-- The full-domain Action replay sends active chunk cells to active chunk
cells. This is structural after the finite endpoint-row certificate: flattening
and unflattening preserve the row coordinate. -/
theorem actionFullSigma_preservesActive
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → Polynomial Fp)
    (proofIndex :
      Fin (ActionPermutationDomain.actionShape pp).numProofs)
    (cell : ResolverPermutationCell
      (ActionPermutationDomain.actionVk pp urs)
      poly proofIndex actionActiveRows) :
    (((actionFullSigma pp urs poly proofIndex)
        (widenPermutationChunkCell actionActiveRows_le_domainSize cell)).2.1 :
      ℕ) < actionActiveRows := by
  let flat : FlatCell actionNumPermCols actionDomainSize :=
    (Equiv.prodComm (Fin actionNumPermCols) (Fin actionDomainSize)).symm
      (actionChunkFlatten pp urs poly proofIndex
        (widenPermutationChunkCell actionActiveRows_le_domainSize cell))
  have hflat : (flat.2 : ℕ) < actionActiveRows := by
    change
      (((actionChunkFlatten pp urs poly proofIndex)
        (widenPermutationChunkCell actionActiveRows_le_domainSize cell)).1 :
        ℕ) < actionActiveRows
    simpa only [actionChunkFlatten,
      _root_.Zcash.Snark.Layout.Asm.chunkFlatten_apply_row,
      widenPermutationChunkCell_row] using cell.2.1.isLt
  have hreplay := actionReplayPreservesActive flat hflat
  simpa only [actionFullSigma, chunkPermutationOfFlat_apply,
    Equiv.permCongr_apply, Equiv.prodComm_apply, actionChunkFlatten,
    _root_.Zcash.Snark.Layout.Asm.chunkFlatten_symm_apply_row, flat] using hreplay

/-- Restrict the full Action keygen replay to the usable-row prefix. -/
noncomputable def actionActiveSigma
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → Polynomial Fp)
    (proofIndex :
      Fin (ActionPermutationDomain.actionShape pp).numProofs) :
    Equiv.Perm
      (ResolverPermutationCell
        (ActionPermutationDomain.actionVk pp urs)
        poly proofIndex actionActiveRows) :=
  Layout.Asm.restrictActivePerm actionActiveRows_le_domainSize
    (actionFullSigma pp urs poly proofIndex)
    (actionFullSigma_preservesActive pp urs poly proofIndex)

/-- The active Action replay is the restriction of its full-domain replay. -/
theorem actionActiveSigma_widen
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → Polynomial Fp)
    (proofIndex :
      Fin (ActionPermutationDomain.actionShape pp).numProofs)
    (cell : ResolverPermutationCell
      (ActionPermutationDomain.actionVk pp urs)
      poly proofIndex actionActiveRows) :
    widenPermutationChunkCell actionActiveRows_le_domainSize
        (actionActiveSigma pp urs poly proofIndex cell) =
      actionFullSigma pp urs poly proofIndex
        (widenPermutationChunkCell actionActiveRows_le_domainSize cell) :=
  Layout.Asm.restrictActivePerm_widen
    actionActiveRows_le_domainSize
    (actionFullSigma pp urs poly proofIndex)
    (actionFullSigma_preservesActive pp urs poly proofIndex)
    cell

/-- Re-express an active flat keygen cell in resolver chunk coordinates. -/
noncomputable def actionActiveChunkCell
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → Polynomial Fp)
    (proofIndex :
      Fin (ActionPermutationDomain.actionShape pp).numProofs)
    (flat : FlatCell actionNumPermCols actionDomainSize)
    (hrow : (flat.2 : ℕ) < actionActiveRows) :
    ResolverPermutationCell
      (ActionPermutationDomain.actionVk pp urs)
      poly proofIndex actionActiveRows :=
  let full :=
    (actionChunkFlatten pp urs poly proofIndex).symm (flat.2, flat.1)
  ⟨full.1,
    ⟨(full.2.1 : ℕ), by
      simpa only [actionChunkFlatten,
        _root_.Zcash.Snark.Layout.Asm.chunkFlatten_symm_apply_row] using hrow⟩,
    full.2.2⟩

/-- Widening the active chunk encoding recovers the full inverse flattening. -/
theorem actionActiveChunkCell_widen
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → Polynomial Fp)
    (proofIndex :
      Fin (ActionPermutationDomain.actionShape pp).numProofs)
    (flat : FlatCell actionNumPermCols actionDomainSize)
    (hrow : (flat.2 : ℕ) < actionActiveRows) :
    widenPermutationChunkCell actionActiveRows_le_domainSize
        (actionActiveChunkCell pp urs poly proofIndex flat hrow) =
      (actionChunkFlatten pp urs poly proofIndex).symm
        (flat.2, flat.1) := by
  apply _root_.Zcash.Snark.Layout.Asm.chunkCell_ext <;> rfl

/-- Flattening the resolver encoding of an active flat cell returns `(row,column)`. -/
theorem actionActiveChunkCell_flatten
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → Polynomial Fp)
    (proofIndex :
      Fin (ActionPermutationDomain.actionShape pp).numProofs)
    (flat : FlatCell actionNumPermCols actionDomainSize)
    (hrow : (flat.2 : ℕ) < actionActiveRows) :
    actionChunkFlatten pp urs poly proofIndex
        (widenPermutationChunkCell actionActiveRows_le_domainSize
          (actionActiveChunkCell pp urs poly proofIndex flat hrow)) =
      (flat.2, flat.1) := by
  rw [actionActiveChunkCell_widen, Equiv.apply_symm_apply]

/-- The Action cell valuation: the environment read of the cell's permutation column
at the cell's absolute row. -/
def actionCopyValue (env : Environment Fp)
    (fc : FlatCell actionNumPermCols actionDomainSize) : Fp :=
  env.get (ColRef.toAny (actionPermCols.getD (fc.1 : ℕ) (.advice 0)))
    (((fc.2 : ℕ) : ℕ) : ℤ)

/--
The resolver chunk coordinate obtained from an active flat Action cell decodes
to the same concrete column as the flat cell's global permutation-column
index.
-/
theorem actionActiveChunkCell_columnAddress
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → Polynomial Fp)
    (proofIndex :
      Fin (ActionPermutationDomain.actionShape pp).numProofs)
    (flat : FlatCell actionNumPermCols actionDomainSize)
    (hrow : (flat.2 : ℕ) < actionActiveRows) :
    let cell :=
      actionActiveChunkCell pp urs poly proofIndex flat hrow
    permutationColumnAddress
        (ActionPermutationDomain.actionVk pp urs)
        (((ActionPermutationDomain.actionVk pp urs).permutationChunks.getD
          cell.1 []).getD cell.2.2 ((.advice 0), 0)).1 =
      ColRef.toAny
        (actionPermCols.getD flat.1 (.advice 0)) := by
  let vk := ActionPermutationDomain.actionVk pp urs
  let cell :=
    actionActiveChunkCell pp urs poly proofIndex flat hrow
  have hchunk :
      (cell.1 : ℕ) < vk.permutationChunks.length := by
    rw [ActionPermutationDomain.chunkCount]
    exact cell.1.isLt
  have hcolumn :
      (cell.2.2 : ℕ) <
        (vk.permutationChunks.getD cell.1 []).length := by
    simpa only [cell, vk, ResolverPermutationPairs,
      permutationChunkPairsOfResolver, List.length_map] using
        cell.2.2.isLt
  have hglobal :
      (flat.1 : ℕ) <
        (actionPermCols.map ColRef.toAny).length := by
    simpa only [List.length_map] using flat.1.isLt
  have hcoordinate :
      (cell.1 : ℕ) * 7 + (cell.2.2 : ℕ) = (flat.1 : ℕ) := by
    have hflatten :=
      actionActiveChunkCell_flatten
        pp urs poly proofIndex flat hrow
    have hsecond :=
      congrArg (fun coordinate => (coordinate.2 : ℕ)) hflatten
    simpa only [actionChunkFlatten,
      _root_.Zcash.Snark.Layout.Asm.chunkFlatten,
      actionChunkLen_eq, cell] using hsecond
  have hindex :
      (vk.permutationChunks.take cell.1).flatten.length +
          (cell.2.2 : ℕ) =
        (flat.1 : ℕ) := by
    have hcellChunk : (cell.1 : ℕ) < 3 := by
      simpa only [cell, actionNumPermutationSets_eq] using cell.1.isLt
    have hcases :
        (cell.1 : ℕ) = 0 ∨ (cell.1 : ℕ) = 1 ∨
          (cell.1 : ℕ) = 2 := by
      omega
    rw [ActionPermutationDomain.permutationChunks_eq]
    rcases hcases with hzero | hone | htwo
    · simp only [hzero, List.take_zero, List.flatten_nil,
        List.length_nil, Nat.zero_add]
      simpa only [hzero, Nat.zero_mul, Nat.zero_add] using hcoordinate
    · simp only [hone, List.take_succ_cons, List.take_zero,
        List.flatten_cons, List.flatten_nil, List.append_nil,
        List.length_cons, List.length_nil, Nat.reduceAdd]
      simpa only [hone, Nat.one_mul] using hcoordinate
    · simp only [htwo, List.take_succ_cons, List.take_zero,
        List.flatten_cons, List.flatten_nil, List.append_nil,
        List.length_append, List.length_cons, List.length_nil,
        Nat.reduceAdd]
      simpa only [htwo, Nat.reduceMul] using hcoordinate
  have hdecoded := decodedChunkAddress_eq_sourceColumn
    (fun reference =>
      permutationColumnAddress vk reference.1)
    ((.advice 0), 0)
    (ColRef.toAny (.advice 0))
    vk.permutationChunks
    (actionPermCols.map ColRef.toAny)
    (by
      simpa only [vk, actionPermCols] using
        ActionPermutationDomain.permutationColumnAddresses_eq pp urs)
    cell.1 cell.2.2 flat.1
    hchunk hcolumn hglobal hindex
  have hmap :
      (actionPermCols.map ColRef.toAny).getD flat.1
          (ColRef.toAny (.advice 0)) =
        ColRef.toAny (actionPermCols.getD flat.1 (.advice 0)) :=
    List.getD_map actionPermCols (.advice 0) ColRef.toAny
  simpa only [vk, cell] using hdecoded.trans hmap

/--
The Action flat-cell valuation in the canonical resolver environment is exactly
the verifier-native `chunkRowValue` at its active resolver chunk coordinate.
-/
theorem actionCopyValue_eq_activeChunkRowValue
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → Polynomial Fp)
    (proofIndex :
      Fin (ActionPermutationDomain.actionShape pp).numProofs)
    (flat : FlatCell actionNumPermCols actionDomainSize)
    (hrow : (flat.2 : ℕ) < actionActiveRows) :
    let vk := ActionPermutationDomain.actionVk pp urs
    let cell :=
      actionActiveChunkCell pp urs poly proofIndex flat hrow
    actionCopyValue
        (resolverEnvironment vk poly proofIndex actionActiveRows) flat =
      chunkRowValue vk.omega
        (ResolverPermutationPairs vk poly proofIndex)
        cell.1 cell.2.1 cell.2.2 := by
  let vk := ActionPermutationDomain.actionVk pp urs
  let cell :=
    actionActiveChunkCell pp urs poly proofIndex flat hrow
  change
    actionCopyValue
        (resolverEnvironment vk poly proofIndex actionActiveRows) flat =
      chunkRowValue vk.omega
        (ResolverPermutationPairs vk poly proofIndex)
        cell.1 cell.2.1 cell.2.2
  have hchunk :
      (cell.1 : ℕ) < vk.permutationChunks.length := by
    rw [ActionPermutationDomain.chunkCount]
    exact cell.1.isLt
  have hcolumn :
      (cell.2.2 : ℕ) <
        (vk.permutationChunks.getD cell.1 []).length := by
    simpa only [cell, vk, ResolverPermutationPairs,
      permutationChunkPairsOfResolver, List.length_map] using
        cell.2.2.isLt
  have hchunkMem :
      vk.permutationChunks.getD cell.1 [] ∈
        vk.permutationChunks := by
    rw [List.getD_eq_getElem _ _ hchunk]
    exact List.getElem_mem ..
  have hreferenceMem :
      (vk.permutationChunks.getD cell.1 [])[cell.2.2] ∈
        vk.permutationChunks.getD cell.1 [] :=
    List.getElem_mem ..
  have hcoherent :
      PermutationColumnRef.Coherent vk
        ((vk.permutationChunks.getD cell.1 [])[cell.2.2]).1 :=
    (ActionPermutationDomain.routingCoherent_of_derived pp urs
      _ hchunkMem _ hreferenceMem).1
  have hresolver :=
    chunkRowValue_eq_resolverEnvironment
      vk poly proofIndex actionActiveRows
      cell.1 cell.2.1 cell.2.2 hcolumn hcoherent
  have haddress :=
    actionActiveChunkCell_columnAddress
      pp urs poly proofIndex flat hrow
  dsimp only at haddress
  change
    permutationColumnAddress vk
        ((vk.permutationChunks.getD cell.1 []).getD
          cell.2.2 ((.advice 0), 0)).1 =
      ColRef.toAny
        (actionPermCols.getD flat.1 (.advice 0)) at haddress
  rw [List.getD_eq_getElem _ _ hcolumn] at haddress
  have hcellRow : (cell.2.1 : ℕ) = (flat.2 : ℕ) := by
    have hflatten :=
      actionActiveChunkCell_flatten
        pp urs poly proofIndex flat hrow
    have hfirst :=
      congrArg (fun coordinate => (coordinate.1 : ℕ)) hflatten
    simpa only [actionChunkFlatten,
      _root_.Zcash.Snark.Layout.Asm.chunkFlatten_apply_row,
      widenPermutationChunkCell_row, cell] using hfirst
  calc
    actionCopyValue
        (resolverEnvironment vk poly proofIndex actionActiveRows) flat =
      (resolverEnvironment vk poly proofIndex actionActiveRows).get
        (ColRef.toAny (actionPermCols.getD flat.1 (.advice 0)))
        (flat.2 : ℤ) := rfl
    _ = (resolverEnvironment vk poly proofIndex actionActiveRows).get
        (permutationColumnAddress vk
          ((vk.permutationChunks.getD cell.1 [])[cell.2.2]).1)
        (cell.2.1 : ℤ) := by
          rw [← hcellRow]
          congr 1
          exact haddress.symm
    _ = chunkRowValue vk.omega
        (ResolverPermutationPairs vk poly proofIndex)
        cell.1 cell.2.1 cell.2.2 := hresolver.symm

/--
Every decoded Action keygen-copy pair has equal values in the canonical
resolver environment once the generic permutation premises hold.

`hcycleSigma` records the construction provenance intentionally omitted from
the abstract `ResolverPermutationCycle`: the cycle is the Action active replay.
-/
theorem actionCopyPairValue_of_resolverPermutation
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G)
    (ch : Challenges (ActionPermutationDomain.actionShape pp).k Fp)
    (poly : CommitmentId → Polynomial Fp)
    (l0 lLast lBlind : Polynomial Fp)
    (proofIndex :
      Fin (ActionPermutationDomain.actionShape pp).numProofs)
    {n : ℕ}
    (hsat : ConstraintSatisfaction
      (constraintModelOfPermutationResolver
        (ActionPermutationDomain.actionVk pp urs)
        ch poly l0 lLast lBlind) n)
    (hdom : ResolverPermutationDomain
      (ActionPermutationDomain.actionVk pp urs)
      l0 lLast lBlind n actionActiveRows)
    (hcycle : ResolverPermutationCycle
      (ActionPermutationDomain.actionVk pp urs)
      poly proofIndex actionActiveRows)
    (hcycleSigma :
      hcycle.sigma =
        actionActiveSigma pp urs poly proofIndex)
    (hgood : ResolverPermutationGoodChallenges
      (ActionPermutationDomain.actionVk pp urs)
      ch poly proofIndex actionActiveRows) :
    ∀ pair ∈ actionCopies,
      actionCopyValue
          (resolverEnvironment
            (ActionPermutationDomain.actionVk pp urs)
            poly proofIndex actionActiveRows)
          pair.1 =
        actionCopyValue
          (resolverEnvironment
            (ActionPermutationDomain.actionVk pp urs)
            poly proofIndex actionActiveRows)
          pair.2 := by
  intro pair hpair
  let vk := ActionPermutationDomain.actionVk pp urs
  have hrows := actionCopyRowsActive pair hpair
  let left :=
    actionActiveChunkCell pp urs poly proofIndex pair.1 hrows.1
  let right :=
    actionActiveChunkCell pp urs poly proofIndex pair.2 hrows.2
  have hrestrict :
      ∀ cell : ResolverPermutationCell
          vk poly proofIndex actionActiveRows,
        widenPermutationChunkCell actionActiveRows_le_domainSize
            (hcycle.sigma cell) =
          chunkPermutationOfFlat
            (actionChunkFlatten pp urs poly proofIndex)
            ((Equiv.prodComm
              (Fin actionNumPermCols)
              (Fin actionDomainSize)).permCongr
                (replayKeygenPermutation actionCopies))
            (widenPermutationChunkCell
              actionActiveRows_le_domainSize cell) := by
    intro cell
    rw [hcycleSigma]
    simpa only [actionFullSigma] using
      actionActiveSigma_widen pp urs poly proofIndex cell
  have hchunkValues :=
    Layout.Asm.chunkRowValue_eq_of_mem_copies
      vk ch poly l0 lLast lBlind proofIndex
      hsat hdom hcycle hgood
      actionActiveRows_le_domainSize actionCopies
      (actionChunkFlatten pp urs poly proofIndex)
      hrestrict
      pair.1 pair.2 hpair left right
      (by
        simpa only [left] using
          actionActiveChunkCell_flatten
            pp urs poly proofIndex pair.1 hrows.1)
      (by
        simpa only [right] using
          actionActiveChunkCell_flatten
            pp urs poly proofIndex pair.2 hrows.2)
  calc
    actionCopyValue
        (resolverEnvironment vk poly proofIndex actionActiveRows)
        pair.1 =
      chunkRowValue vk.omega
        (ResolverPermutationPairs vk poly proofIndex)
        left.1 left.2.1 left.2.2 := by
          simpa only [vk, left] using
            actionCopyValue_eq_activeChunkRowValue
              pp urs poly proofIndex pair.1 hrows.1
    _ = chunkRowValue vk.omega
        (ResolverPermutationPairs vk poly proofIndex)
        right.1 right.2.1 right.2.2 := hchunkValues
    _ = actionCopyValue
        (resolverEnvironment vk poly proofIndex actionActiveRows)
        pair.2 := by
          symm
          simpa only [vk, right] using
            actionCopyValue_eq_activeChunkRowValue
              pp urs poly proofIndex pair.2 hrows.2

/-- A raw coordinate pair as a typed Action permutation cell (`mod` totalization —
the identity on every in-range coordinate, and every declared coordinate is). -/
def mkActionCell (p : ℕ × ℕ) : FlatCell actionNumPermCols actionDomainSize :=
  (⟨p.1 % actionNumPermCols, Nat.mod_lt _ actionNumPermCols_pos⟩,
    ⟨p.2 % actionDomainSize, Nat.mod_lt _ actionDomainSize_pos⟩)

/-- The Action endpoint encoding: region cells through the placement, instance
endpoints at their absolute rows, constants at their first allocated
constants-column cell. -/
def actionCopyEncode : CopyEndpoint Fp → FlatCell actionNumPermCols actionDomainSize
  | .cell c => mkActionCell
      (resolveCell actionPermCols actionCircuit.regionStarts c)
  | .instance col row => mkActionCell (permIndex actionPermCols col.toAny, row)
  | .constant v => mkActionCell
      (match actionConsts.find? (fun e => e.1 = v.val) with
        | some e => (permIndex actionPermCols (ColRef.toAny (.fixed e.2.1)), e.2.2)
        | none => (0, 0))

/-- The concrete column/row denoted directly by an Action copy endpoint. -/
def actionEndpointAddress : CopyEndpoint Fp → AnyColumn × ℕ
  | .cell c =>
      (c.column,
        actionCircuit.regionStarts.getD c.regionIndex 0 +
          c.rowOffset)
  | .instance column row => (column.toAny, row)
  | .constant value =>
      match actionConsts.find? (fun entry => entry.1 = value.val) with
      | some entry => (ColRef.toAny (.fixed entry.2.1), entry.2.2)
      | none => (ColRef.toAny (.advice 0), 0)

/-- The concrete column/row recovered after encoding an Action endpoint. -/
def actionEncodedAddress (endpoint : CopyEndpoint Fp) : AnyColumn × ℕ :=
  let encoded := actionCopyEncode endpoint
  (ColRef.toAny
      (actionPermCols.getD (encoded.1 : ℕ) (.advice 0)),
    encoded.2)

/-- Every endpoint occurring in the declared Action copy stream. -/
def actionDeclaredEndpoints : List (CopyEndpoint Fp) :=
  (operationDeclaredCopies
      (actionCircuit.operations)).flatMap
    fun copy => [copy.1, copy.2]

/--
Finite diagnostic for declared endpoints whose encoded permutation cell does not
decode to the endpoint's concrete column and row.
-/
def actionCopyAddressFailures : List (CopyEndpoint Fp) :=
  let endpoints := actionDeclaredEndpoints
  endpoints.filter fun endpoint =>
    decide (actionEncodedAddress endpoint ≠ actionEndpointAddress endpoint)

/-- Whether a constant endpoint has a V1 constants allocation. -/
def actionConstantAllocated : CopyEndpoint Fp → Bool
  | .constant value =>
      (actionConsts.find? (fun entry => entry.1 = value.val)).isSome
  | _ => true

/-- Declared endpoints whose constant value has no V1 allocation. -/
def actionMissingConstantAllocations : List (CopyEndpoint Fp) :=
  let endpoints := actionDeclaredEndpoints
  endpoints.filter fun endpoint => !actionConstantAllocated endpoint

/-- Positional Action constant sites paired with their V1 allocation entries. -/
def actionConstantAllocations :
    List ((Cell × Fp) × (ℕ × ℕ × ℕ)) :=
  (operationConstSites (actionCircuit.operations)).zip
    actionConsts

/-- Positional constant allocations whose stored natural value disagrees with the site. -/
def actionConstantValueFailures :
    List ((Cell × Fp) × (ℕ × ℕ × ℕ)) :=
  actionConstantAllocations.filter fun allocation =>
    decide (allocation.2.1 ≠ allocation.1.2.val)

/-- Decode a raw Action permutation coordinate back to its concrete column and row. -/
def actionRawCellAddress (coordinate : ℕ × ℕ) : AnyColumn × ℕ :=
  let cell := mkActionCell coordinate
  (ColRef.toAny
      (actionPermCols.getD (cell.1 : ℕ) (.advice 0)),
    cell.2)

/-- Allocated constant cells that fail the permutation-column address roundtrip. -/
def actionConstantCellAddressFailures : List (ℕ × ℕ × ℕ) :=
  actionConsts.filter fun entry =>
    decide (
      actionRawCellAddress
          (permIndex actionPermCols
              (ColRef.toAny (.fixed entry.2.1)),
            entry.2.2) ≠
        (ColRef.toAny (.fixed entry.2.1), entry.2.2))

/--
The Action layout compiler preserves the concrete address of every declared
copy endpoint through finite permutation-cell encoding.
-/
theorem actionCopyAddressFailures_eq_nil :
    actionCopyAddressFailures = [] := by
  native_decide

/-- Every declared Action constant endpoint has a V1 constants allocation. -/
theorem actionMissingConstantAllocations_eq_nil :
    actionMissingConstantAllocations = [] := by
  native_decide

/-- V1 allocates at least one fixed cell for every Action constant site. -/
theorem actionConstantSites_fit :
    (operationConstSites
        (actionCircuit.operations)).length ≤
      actionConsts.length := by
  native_decide

/-- The positional V1 allocation stores the value of every Action constant site. -/
theorem actionConstantValueFailures_eq_nil :
    actionConstantValueFailures = [] := by
  native_decide

/-- Every allocated Action constant cell survives permutation-coordinate encoding. -/
theorem actionConstantCellAddressFailures_eq_nil :
    actionConstantCellAddressFailures = [] := by
  native_decide

/-- A member of the positional allocation zip stores its site's field value. -/
theorem actionConstantAllocation_value
    {site : Cell × Fp} {entry : ℕ × ℕ × ℕ}
    (hallocation : (site, entry) ∈ actionConstantAllocations) :
    entry.1 = site.2.val := by
  by_contra hne
  have hfailure : (site, entry) ∈ actionConstantValueFailures := by
    rw [actionConstantValueFailures, List.mem_filter]
    exact ⟨hallocation, decide_eq_true hne⟩
  rw [actionConstantValueFailures_eq_nil] at hfailure
  simp at hfailure

/-- An allocated Action constant cell has the expected concrete address. -/
theorem actionConstantCellAddress
    {entry : ℕ × ℕ × ℕ} (hentry : entry ∈ actionConsts) :
    actionRawCellAddress
        (permIndex actionPermCols
            (ColRef.toAny (.fixed entry.2.1)),
          entry.2.2) =
      (ColRef.toAny (.fixed entry.2.1), entry.2.2) := by
  by_contra hne
  have hfailure : entry ∈ actionConstantCellAddressFailures := by
    rw [actionConstantCellAddressFailures, List.mem_filter]
    exact ⟨hentry, decide_eq_true hne⟩
  rw [actionConstantCellAddressFailures_eq_nil] at hfailure
  simp at hfailure

/-- Either endpoint of a declared copy occurs in `actionDeclaredEndpoints`. -/
theorem mem_actionDeclaredEndpoints
    {copy : DeclaredCopy Fp}
    (hcopy : copy ∈ operationDeclaredCopies
      (actionCircuit.operations)) :
    copy.1 ∈ actionDeclaredEndpoints ∧
      copy.2 ∈ actionDeclaredEndpoints := by
  constructor
  · rw [actionDeclaredEndpoints, List.mem_flatMap]
    exact ⟨copy, hcopy, by simp⟩
  · rw [actionDeclaredEndpoints, List.mem_flatMap]
    exact ⟨copy, hcopy, by simp⟩

/-- Declared endpoint encoding preserves its concrete address. -/
theorem actionEncodedAddress_eq
    {endpoint : CopyEndpoint Fp}
    (hendpoint : endpoint ∈ actionDeclaredEndpoints) :
    actionEncodedAddress endpoint = actionEndpointAddress endpoint := by
  by_contra hne
  have hfailure : endpoint ∈ actionCopyAddressFailures := by
    rw [actionCopyAddressFailures, List.mem_filter]
    exact ⟨hendpoint, decide_eq_true hne⟩
  rw [actionCopyAddressFailures_eq_nil] at hfailure
  simp at hfailure

/-- A declared constant endpoint has a concrete allocation entry of that value. -/
theorem exists_actionConst_of_declared
    {value : Fp}
    (hendpoint :
      CopyEndpoint.constant value ∈ actionDeclaredEndpoints) :
    ∃ entry ∈ actionConsts, entry.1 = value.val := by
  have hnotMissing :
      CopyEndpoint.constant value ∉ actionMissingConstantAllocations := by
    rw [actionMissingConstantAllocations_eq_nil]
    simp
  have hisSome :
      (actionConsts.find? (fun entry => entry.1 = value.val)).isSome = true := by
    cases hfind :
        actionConsts.find? (fun entry => entry.1 = value.val) with
    | none =>
        exfalso
        apply hnotMissing
        rw [actionMissingConstantAllocations, List.mem_filter]
        exact ⟨hendpoint, by
          simp [actionConstantAllocated, hfind]⟩
    | some entry =>
        simp
  obtain ⟨entry, hfind⟩ :
      ∃ entry,
        actionConsts.find? (fun entry => entry.1 = value.val) = some entry := by
    exact Option.isSome_iff_exists.mp hisSome
  have hmem : entry ∈ actionConsts :=
    List.mem_of_find?_eq_some hfind
  have hvalue :
      entry.1 = value.val := by
    simpa using List.find?_some hfind
  exact ⟨entry, hmem, hvalue⟩

/--
A declared Action constant copy has its positional V1 allocation and the
corresponding raw keygen copy tuple.
-/
theorem actionConstantRawPair
    {cell : Cell} {value : Fp}
    (hcopy :
      (CopyEndpoint.cell cell, CopyEndpoint.constant value) ∈
        operationDeclaredCopies
          (actionCircuit.operations)) :
    ∃ entry ∈ actionConsts,
      entry.1 = value.val ∧
        (permIndex actionPermCols
            (ColRef.toAny (.fixed entry.2.1)),
          entry.2.2,
          (resolveCell actionPermCols
            actionCircuit.regionStarts cell).1,
          (resolveCell actionPermCols
            actionCircuit.regionStarts cell).2) ∈
          actionCopyRaw := by
  have hsite :
      (cell, value) ∈
        operationConstSites
          (actionCircuit.operations) :=
    mem_operationConstSites_of_declared_constant
      (actionCircuit.operations) cell value hcopy
  obtain ⟨entry, hallocation⟩ :=
    exists_mem_zip_of_mem_left
      (operationConstSites
        (actionCircuit.operations))
      actionConsts actionConstantSites_fit hsite
  have hentry : entry ∈ actionConsts :=
    (List.of_mem_zip hallocation).2
  have hvalue : entry.1 = value.val :=
    actionConstantAllocation_value hallocation
  refine ⟨entry, hentry, hvalue, ?_⟩
  have hgo :=
    (V1_go_snd_eq actionPermCols
      actionCircuit.regionStarts
      (actionCircuit.operations)
      actionConsts actionConstantSites_fit).1
  have hmapped :
      (permIndex actionPermCols
          (ColRef.toAny (.fixed entry.2.1)),
        entry.2.2,
        (resolveCell actionPermCols
          actionCircuit.regionStarts cell).1,
        (resolveCell actionPermCols
          actionCircuit.regionStarts cell).2) ∈
        ((operationConstSites
            (actionCircuit.operations)).zip
          actionConsts).map (fun siteEntry =>
            (permIndex actionPermCols
                (ColRef.toAny (.fixed siteEntry.2.2.1)),
              siteEntry.2.2.2,
              (resolveCell actionPermCols
                actionCircuit.regionStarts
                siteEntry.1.1).1,
              (resolveCell actionPermCols
                actionCircuit.regionStarts
                siteEntry.1.1).2)) := by
    exact List.mem_map.mpr ⟨((cell, value), entry), hallocation, rfl⟩
  rw [← hgo] at hmapped
  rw [actionCopyRaw, Halo2.Layout.V1.copyList]
  exact List.mem_append_right _ hmapped

/-- Decode membership in the raw Action copy list to a typed copy pair. -/
theorem exists_actionCopy_of_raw
    {tuple : ℕ × ℕ × ℕ × ℕ} (hraw : tuple ∈ actionCopyRaw) :
    ∃ pair ∈ actionCopies,
      pair.1.pair = (tuple.1, tuple.2.1) ∧
        pair.2.pair = (tuple.2.2.1, tuple.2.2.2) := by
  have hrawMap :
      actionCopyRaw = actionCopies.map
        (fun pair =>
          (pair.1.pair.1, pair.1.pair.2,
            pair.2.pair.1, pair.2.pair.2)) :=
    (decodeCopies_map actionNumPermCols actionDomainSize
      actionCopyRaw actionCopyBounds).symm
  rw [hrawMap, List.mem_map] at hraw
  obtain ⟨pair, hpair, htuple⟩ := hraw
  refine ⟨pair, hpair, ?_, ?_⟩
  · rw [← htuple]
  · rw [← htuple]

/-- `actionCopyValue` is exactly the environment read at the encoded address. -/
theorem actionCopyValue_eq_encodedAddress
    (env : Environment Fp) (endpoint : CopyEndpoint Fp) :
    actionCopyValue env (actionCopyEncode endpoint) =
      env.get (actionEncodedAddress endpoint).1
        ((actionEncodedAddress endpoint).2 : ℤ) := by
  rfl

/-- `actionCopyValue` at a raw coordinate reads its decoded concrete address. -/
theorem actionCopyValue_mkActionCell
    (env : Environment Fp) (coordinate : ℕ × ℕ) :
    actionCopyValue env (mkActionCell coordinate) =
      env.get (actionRawCellAddress coordinate).1
        ((actionRawCellAddress coordinate).2 : ℤ) := by
  rfl

/--
Cell and instance endpoints read back directly after Action permutation-cell
encoding. Constant endpoints additionally need committed fixed-row realization.
-/
theorem actionNonconstantEndpointRead
    (env : Environment Fp)
    {endpoint : CopyEndpoint Fp}
    (hendpoint : endpoint ∈ actionDeclaredEndpoints)
    (hnonconstant : ∀ value, endpoint ≠ .constant value) :
    endpoint.eval actionCircuit.placement env =
      actionCopyValue env (actionCopyEncode endpoint) := by
  have haddress := actionEncodedAddress_eq hendpoint
  rw [actionCopyValue_eq_encodedAddress, haddress]
  cases endpoint with
  | cell cell =>
      rfl
  | «instance» column row =>
      rfl
  | constant value =>
      exact absurd rfl (hnonconstant value)

/--
A declared constant endpoint reads back through its allocated fixed cell, or the
shared fixed-commitment exceptional branch fires.
-/
def actionConstantEndpointRead_or_bad
    (env : Environment Fp) {Bad : Type}
    (fixedRead : ∀ {column row value : ℕ},
      (column, row, value) ∈
          topLevelRequiredFixedEntries actionCircuit →
        env.fixed ⟨column⟩ (row : ℤ) = (value : Fp) ⊕' Bad)
    (value : Fp)
    (hendpoint :
      CopyEndpoint.constant value ∈ actionDeclaredEndpoints) :
    (CopyEndpoint.constant value).eval
        actionCircuit.placement env =
          actionCopyValue env
            (actionCopyEncode (.constant value)) ⊕'
      Bad := by
  cases hfind :
      actionConsts.find? (fun entry => entry.1 = value.val) with
  | none =>
      exfalso
      obtain ⟨witness, hwitnessMem, hwitnessValue⟩ :=
        exists_actionConst_of_declared hendpoint
      have hsome :
          (actionConsts.find? (fun entry => entry.1 = value.val)).isSome =
            true := by
        exact List.find?_isSome.mpr
          ⟨witness, hwitnessMem, decide_eq_true hwitnessValue⟩
      simp [hfind] at hsome
  | some entry =>
      have hentryMem : entry ∈ actionConsts :=
        List.mem_of_find?_eq_some hfind
      have hentryValue : entry.1 = value.val := by
        simpa using List.find?_some hfind
      have hconstantEntry :
          (entry.2.1, entry.2.2, entry.1) ∈
            topLevelConstantEntries actionCircuit := by
        rw [topLevelConstantEntries, Layout.constantsFixed, List.mem_map]
        exact ⟨entry, hentryMem, rfl⟩
      have hrequired :
          (entry.2.1, entry.2.2, entry.1) ∈
            topLevelRequiredFixedEntries actionCircuit := by
        simp only [topLevelRequiredFixedEntries, List.mem_append]
        exact Or.inl (Or.inl (Or.inr hconstantEntry))
      refine bindOrRelationWitness (fixedRead hrequired) fun hread => ?_
      have haddress := actionEncodedAddress_eq hendpoint
      rw [actionCopyValue_eq_encodedAddress, haddress,
        actionEndpointAddress, hfind]
      change value = env.fixed ⟨entry.2.1⟩ (entry.2.2 : ℤ)
      simpa [hentryValue] using hread.symm

/-- A typed cell is its raw coordinate pair, so the `mod` totalization is inert. -/
theorem mkActionCell_eq_of_pair {fc : FlatCell actionNumPermCols actionDomainSize}
    {p : ℕ × ℕ} (h : fc.pair = p) : mkActionCell p = fc := by
  rcases fc with ⟨a, b⟩
  subst h
  show (⟨(a : ℕ) % actionNumPermCols, _⟩, ⟨(b : ℕ) % actionDomainSize, _⟩) = (a, b)
  refine Prod.ext_iff.mpr ⟨Fin.ext ?_, Fin.ext ?_⟩
  · exact Nat.mod_eq_of_lt a.isLt
  · exact Nat.mod_eq_of_lt b.isLt

/-- **Declared-copy linkage.** Every resolvable declared copy's encoded endpoints are
linked by the decoded keygen copy list: membership through the floor planner, decoding
through the bounds certificate, and the replay pair link. -/
theorem actionCopyLink :
    ∀ copy ∈ operationDeclaredCopies (actionCircuit.operations),
      ∀ tuple, resolveDeclared actionPermCols
          actionCircuit.regionStarts copy = some tuple →
        (replayKeygenPermutation actionCopies).SameCycle
          (actionCopyEncode copy.1) (actionCopyEncode copy.2) := by
  intro copy hcopy tuple hres
  have hmem : tuple ∈ actionCopyRaw :=
    mem_V1_copyList_of_declared actionPermCols
      actionCircuit.regionStarts
      (actionCircuit.operations) actionConsts copy tuple hres hcopy
  have hraw : actionCopyRaw = actionCopies.map
      (fun p => (p.1.pair.1, p.1.pair.2, p.2.pair.1, p.2.pair.2)) :=
    (decodeCopies_map actionNumPermCols actionDomainSize actionCopyRaw
      actionCopyBounds).symm
  rw [hraw, List.mem_map] at hmem
  obtain ⟨pr, hpr, henc⟩ := hmem
  have hlinked := replayKeygenPermutation_pair_linked actionCopies hpr
  have hp1 : pr.1.pair = (tuple.1, tuple.2.1) := by
    rw [← henc]
  have hp2 : pr.2.pair = (tuple.2.2.1, tuple.2.2.2) := by
    rw [← henc]
  -- identify the encoded endpoints with the decoded pair, by copy kind
  rcases copy with ⟨e1, e2⟩
  cases e1 with
  | cell l =>
      cases e2 with
      | cell r =>
          simp only [resolveDeclared] at hres
          obtain rfl := Option.some.inj hres
          rw [show actionCopyEncode (.cell l) = pr.1 from
              mkActionCell_eq_of_pair (by rw [hp1]),
            show actionCopyEncode (.cell r) = pr.2 from
              mkActionCell_eq_of_pair (by rw [hp2])]
          exact hlinked
      | «instance» col row =>
          simp only [resolveDeclared] at hres
          obtain rfl := Option.some.inj hres
          rw [show actionCopyEncode (.cell l) = pr.1 from
              mkActionCell_eq_of_pair (by rw [hp1]),
            show actionCopyEncode (.instance col row) = pr.2 from
              mkActionCell_eq_of_pair (by rw [hp2])]
          exact hlinked
      | constant v => simp [resolveDeclared] at hres
  | «instance» col row => simp [resolveDeclared] at hres
  | constant v => simp [resolveDeclared] at hres

/-- **The Action copy-replay witness.** Kind-dispatched from three leaf families over
the concrete data: value agreement along each decoded keygen copy (the σ-semantics
transport), value agreement of each declared constant copy (two constants-column
reads), and the declared-endpoint read equations (resolution coordinates). -/
noncomputable def actionCopyReplayWitness
    (env : Environment Fp) {Bad : Type}
    (hpairval : ∀ pr ∈ actionCopies,
      actionCopyValue env pr.1 = actionCopyValue env pr.2 ⊕' Bad)
    (hconstval : ∀ copy ∈ operationDeclaredCopies
        (actionCircuit.operations),
      ∀ c v, copy = (.cell c, .constant v) →
        actionCopyValue env (actionCopyEncode (.cell c)) =
          actionCopyValue env (actionCopyEncode (.constant v)) ⊕' Bad)
    (hread : ∀ copy ∈ operationDeclaredCopies
        (actionCircuit.operations),
      copy.1.eval actionCircuit.placement env =
          actionCopyValue env (actionCopyEncode copy.1) ∧
        copy.2.eval actionCircuit.placement env =
          actionCopyValue env (actionCopyEncode copy.2)) :
    CopyReplayWitness actionCircuit.placement env
      (actionCircuit.operations)
      (FlatCell actionNumPermCols actionDomainSize) Bad :=
  Zcash.Snark.Layout.Asm.CopyReplayWitness.ofPairValues actionCopyEncode (actionCopyValue env)
    (by
      classical
      intro pr hpr
      rw [encodeDeclaredCopies, List.mem_map] at hpr
      -- `ofPairValues` wants the alternative per pair, so the declaring copy has to be recovered
      -- here; `hpr` is an `∃` and the pair value is data, so it is recovered by choice.
      let copy := Classical.choose hpr
      have hcopy : copy ∈ operationDeclaredCopies (actionCircuit.operations) :=
        (Classical.choose_spec hpr).1
      have henc :
          (actionCopyEncode copy.1, actionCopyEncode copy.2) = pr :=
        (Classical.choose_spec hpr).2
      rw [← henc]
      -- Dispatch on the resolution itself, an `Option`; `declared_shape` is an `Or` and only
      -- serves to name the constant shape once resolution has already failed.
      match hres : resolveDeclared actionPermCols actionCircuit.regionStarts copy with
      | some tuple =>
          exact Zcash.Snark.Layout.Asm.value_eq_or_bad_of_replay_sameCycle (actionCopyValue env) _
            hpairval (actionCopyLink copy hcopy tuple hres)
      | none =>
          have hconstant : ∃ c v, copy = (.cell c, .constant v) := by
            rcases declared_shape (actionCircuit.operations)
                actionPermCols actionCircuit.regionStarts copy hcopy with
              ⟨tuple, htuple⟩ | hshape
            · rw [hres] at htuple
              exact absurd htuple (by simp)
            · exact hshape
          have hcv := Classical.choose_spec (Classical.choose_spec hconstant)
          rw [hcv]
          exact hconstval copy hcopy _ _ hcv)
    hread

/--
The value of a declared constant-copy cell agrees with the canonical encoded
constant cell, or the shared exceptional branch fires.

The keygen copy pair relates the advice cell to its *positional* constant
allocation. Both that allocation and the canonical same-value allocation read
the declared literal through fixed-row coherence.
-/
noncomputable def actionConstantCopyValue_or_bad
    (env : Environment Fp) {Bad : Type}
    (hpairval : ∀ pair ∈ actionCopies,
      actionCopyValue env pair.1 = actionCopyValue env pair.2 ⊕' Bad)
    (fixedRead : ∀ {column row value : ℕ},
      (column, row, value) ∈
          topLevelRequiredFixedEntries actionCircuit →
        env.fixed ⟨column⟩ (row : ℤ) = (value : Fp) ⊕' Bad)
    (copy : DeclaredCopy Fp)
    (hcopy : copy ∈ operationDeclaredCopies
      (actionCircuit.operations))
    (cell : Cell) (value : Fp)
    (hshape : copy = (.cell cell, .constant value)) :
    actionCopyValue env (actionCopyEncode (.cell cell)) =
        actionCopyValue env (actionCopyEncode (.constant value)) ⊕'
      Bad := by
  classical
  subst copy
  -- The allocated constant entry and its replay pair are recovered by choice, as elsewhere in
  -- this stack: both provably exist, and the break itself is still computed downstream.
  have hrawPair := actionConstantRawPair hcopy
  let entry := Classical.choose hrawPair
  have hentry : entry ∈ actionConsts := (Classical.choose_spec hrawPair).1
  have hentryValue : entry.1 = value.val := (Classical.choose_spec hrawPair).2.1
  have hraw := (Classical.choose_spec hrawPair).2.2
  have hcopyPair := exists_actionCopy_of_raw hraw
  let pair := Classical.choose hcopyPair
  have hpair : pair ∈ actionCopies := (Classical.choose_spec hcopyPair).1
  have hpairLeft := (Classical.choose_spec hcopyPair).2.1
  have hpairRight := (Classical.choose_spec hcopyPair).2.2
  have hconstantEntry :
      (entry.2.1, entry.2.2, entry.1) ∈
        topLevelConstantEntries actionCircuit := by
    rw [topLevelConstantEntries, Layout.constantsFixed, List.mem_map]
    exact ⟨entry, hentry, rfl⟩
  have hrequired :
      (entry.2.1, entry.2.2, entry.1) ∈
        topLevelRequiredFixedEntries actionCircuit := by
    simp only [topLevelRequiredFixedEntries, List.mem_append]
    exact Or.inl (Or.inl (Or.inr hconstantEntry))
  have hendpoint :
      CopyEndpoint.constant value ∈ actionDeclaredEndpoints :=
    (mem_actionDeclaredEndpoints hcopy).2
  -- Sequence the three reductions this proof consumes before descending into `Prop`.
  rcases hpairval pair hpair with hpairvalue | hbad
  swap
  · exact PSum.inr hbad
  rcases fixedRead hrequired with hfixed | hbad
  swap
  · exact PSum.inr hbad
  rcases actionConstantEndpointRead_or_bad env fixedRead value hendpoint with
    hcanonical | hbad
  swap
  · exact PSum.inr hbad
  refine PSum.inl ?_
  let constantCoordinate : ℕ × ℕ :=
    (permIndex actionPermCols
        (ColRef.toAny (.fixed entry.2.1)),
      entry.2.2)
  let cellCoordinate : ℕ × ℕ :=
    resolveCell actionPermCols
      actionCircuit.regionStarts cell
  have hleft :
      mkActionCell constantCoordinate = pair.1 := by
    apply mkActionCell_eq_of_pair
    simpa [constantCoordinate] using hpairLeft
  have hright :
      actionCopyEncode (.cell cell) = pair.2 := by
    apply mkActionCell_eq_of_pair
    simpa [actionCopyEncode, cellCoordinate] using hpairRight
  have hpairEq :
      actionCopyValue env (mkActionCell constantCoordinate) =
        actionCopyValue env (actionCopyEncode (.cell cell)) := by
    simpa only [hleft, hright] using hpairvalue
  have hpositional :
      actionCopyValue env (mkActionCell constantCoordinate) = value := by
    rw [actionCopyValue_mkActionCell,
      show actionRawCellAddress constantCoordinate =
          (ColRef.toAny (.fixed entry.2.1), entry.2.2) by
        simpa [constantCoordinate] using actionConstantCellAddress hentry]
    change env.fixed ⟨entry.2.1⟩ (entry.2.2 : ℤ) = value
    simpa [hentryValue] using hfixed
  exact hpairEq.symm.trans (hpositional.trans hcanonical)

/--
Construct the Action copy witness, or return the shared exceptional branch,
without asking the caller for declared-endpoint read equations.

Nonconstant reads follow from the certified endpoint-address roundtrip. Constant
reads follow from the fixed compiler's allocated-constant realization. The two
remaining semantic inputs are pairwise σ-copy value agreement and linkage of a
constant declaration to its allocated copy pair.
-/
noncomputable def actionCopyReplayWitness_or_bad
    (env : Environment Fp) {Bad : Type}
    (hpairval : ∀ pr ∈ actionCopies,
      actionCopyValue env pr.1 = actionCopyValue env pr.2 ⊕' Bad)
    (hconstval : ∀ copy ∈ operationDeclaredCopies
        (actionCircuit.operations),
      ∀ c v, copy = (.cell c, .constant v) →
        actionCopyValue env (actionCopyEncode (.cell c)) =
          actionCopyValue env (actionCopyEncode (.constant v)) ⊕' Bad)
    (fixedRead : ∀ {column row value : ℕ},
      (column, row, value) ∈
          topLevelRequiredFixedEntries actionCircuit →
        env.fixed ⟨column⟩ (row : ℤ) = (value : Fp) ⊕' Bad) :
    CopyReplayWitness actionCircuit.placement env
        (actionCircuit.operations)
        (FlatCell actionNumPermCols actionDomainSize) Bad ⊕'
      Bad := by
  classical
  refine bindOrRelationWitness
    (listForallOrRelationWitness
      (operationDeclaredCopies (actionCircuit.operations))
      fun copy hcopy => ?_)
    (fun hread => actionCopyReplayWitness env hpairval hconstval hread)
  have hendpoints := mem_actionDeclaredEndpoints hcopy
  have hshape := declared_shape
    (actionCircuit.operations)
    actionPermCols actionCircuit.regionStarts
    copy hcopy
  -- Dispatch on the copy's own constructors rather than on `declared_shape`, which is an `Or`
  -- and so cannot be eliminated into the witness. The shapes it rules out are discharged as
  -- `False` instead, entirely within `Prop`.
  rcases copy with ⟨left, right⟩
  cases left with
  | cell leftCell =>
      cases right with
      | cell rightCell =>
          exact PSum.inl
            ⟨actionNonconstantEndpointRead env hendpoints.1
              (by intro value h; cases h),
             actionNonconstantEndpointRead env hendpoints.2
              (by intro value h; cases h)⟩
      | «instance» column row =>
          exact PSum.inl
            ⟨actionNonconstantEndpointRead env hendpoints.1
              (by intro value h; cases h),
             actionNonconstantEndpointRead env hendpoints.2
              (by intro value h; cases h)⟩
      | constant value =>
          refine bindOrRelationWitness
            (actionConstantEndpointRead_or_bad
              env fixedRead value hendpoints.2) fun hconst => ?_
          exact
            ⟨actionNonconstantEndpointRead env hendpoints.1
              (by intro other h; cases h), hconst⟩
  | «instance» column row =>
      exfalso
      rcases hshape with ⟨tuple, hresolve⟩ | ⟨c, v, hcv⟩
      · simp [resolveDeclared] at hresolve
      · simp at hcv
  | constant value =>
      exfalso
      rcases hshape with ⟨tuple, hresolve⟩ | ⟨c, v, hcv⟩
      · simp [resolveDeclared] at hresolve
      · simp at hcv

/--
The Action copy witness from the sole remaining semantic leaf: value agreement
on each decoded keygen copy pair. Constant-copy linkage and all declared endpoint
reads are derived internally from the compiler pipeline and fixed-row realization.
-/
noncomputable def actionCopyReplayWitness_ofPairValues_or_bad
    (env : Environment Fp) {Bad : Type}
    (hpairval : ∀ pair ∈ actionCopies,
      actionCopyValue env pair.1 = actionCopyValue env pair.2 ⊕' Bad)
    (fixedRead : ∀ {column row value : ℕ},
      (column, row, value) ∈
          topLevelRequiredFixedEntries actionCircuit →
        env.fixed ⟨column⟩ (row : ℤ) = (value : Fp) ⊕' Bad) :
    CopyReplayWitness actionCircuit.placement env
        (actionCircuit.operations)
        (FlatCell actionNumPermCols actionDomainSize) Bad ⊕'
      Bad :=
  actionCopyReplayWitness_or_bad env hpairval
    (fun copy hcopy cell value hshape =>
      actionConstantCopyValue_or_bad
        env hpairval fixedRead copy hcopy cell value hshape)
    fixedRead

end Zcash.Snark
