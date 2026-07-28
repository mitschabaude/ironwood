import Zcash.Circuits.Integration.ResolverQueryEnvironment
import Zcash.Snark.Keygen.Pipeline

/-!
# Permutation compiler round trips

The keygen compiler turns equality-enabled Clean columns into verifier query
references, attaches their global σ-column indices, and splits the result into
permutation chunks. This module proves that the transformation loses no column
information: flattening the chunks and decoding coherent query references
recovers the original permutation-column order.

The result follows from the compiler pipeline itself. It does not inspect a
concrete circuit or use a full-circuit computation certificate.
-/

namespace Zcash.Snark

open Halo2

set_option maxHeartbeats 20000

/-- Flattening the accumulator implementation of `List.toChunks` preserves its
processed prefix and unprocessed suffix. -/
theorem listToChunksGo_flatten {α : Type} (n : ℕ)
    (xs : List α) (current : Array α) (chunks : Array (List α)) :
    (List.toChunks.go n xs current chunks).flatten =
      chunks.toList.flatten ++ current.toList ++ xs := by
  induction xs generalizing current chunks with
  | nil =>
      simp [List.toChunks.go]
  | cons x xs ih =>
      simp only [List.toChunks.go]
      split
      · rw [ih]
        simp [List.flatten_append, List.append_assoc]
      · rw [ih]
        simp [List.append_assoc]

/-- Splitting a list into chunks and flattening it is the identity, including
the `chunkSize = 0` convention. -/
theorem listToChunks_flatten {α : Type} (chunkSize : ℕ) (xs : List α) :
    (xs.toChunks chunkSize).flatten = xs := by
  cases chunkSize with
  | zero =>
      cases xs <;> simp [List.toChunks]
  | succ chunkSize =>
      cases xs with
      | nil => simp [List.toChunks]
      | cons x xs =>
          rw [List.toChunks]
          rw [listToChunksGo_flatten]
          simp_all
          all_goals omega

/-- An in-range `findIdx` decodes to the element it searched for. -/
theorem getD_findIdx_eq_target
    {α : Type} [DecidableEq α]
    (xs : List α) (target fallback : α)
    (hin : xs.findIdx (· = target) < xs.length) :
    xs.getD (xs.findIdx (· = target)) fallback = target := by
  rw [List.getD_eq_getElem _ _ hin]
  have hfound :=
    List.findIdx_getElem
      (xs := xs) (p := fun value => value = target) (w := hin)
  simpa using hfound

/-- Reading one inner list is the same as reading the flattened list after the
complete prefix of earlier inner lists. -/
theorem flatten_getD_at_chunk
    {α : Type*} (fallback : α) (chunks : List (List α))
    (chunk column : ℕ)
    (hchunk : chunk < chunks.length)
    (hcolumn : column < (chunks.getD chunk []).length) :
    chunks.flatten.getD
        ((chunks.take chunk).flatten.length + column) fallback =
      (chunks.getD chunk []).getD column fallback := by
  induction chunks generalizing chunk with
  | nil =>
      simp at hchunk
  | cons head tail ih =>
      cases chunk with
      | zero =>
          simp only [List.take_zero, List.flatten_nil, List.length_nil,
            Nat.zero_add, List.getD_cons_zero, List.flatten_cons]
          exact List.getD_append head tail.flatten fallback column hcolumn
      | succ chunk =>
          have hchunkTail : chunk < tail.length := by
            simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hchunk
          have hcolumnTail :
              column < (tail.getD chunk []).length := by
            simpa only [List.getD_cons_succ] using hcolumn
          simp only [List.take_succ_cons, List.flatten_cons,
            List.length_append, List.getD_cons_succ]
          rw [List.getD_append_right]
          · have hindex :
                head.length +
                    (tail.take chunk).flatten.length + column -
                    head.length =
                  (tail.take chunk).flatten.length + column := by
                omega
            rw [hindex]
            exact ih chunk hchunkTail hcolumnTail
          · omega

/--
If decoding flattened compiler chunks yields the source-column list, a local
`(chunk,column)` reference decodes to the source column at its flattened index.
-/
theorem decodedChunkAddress_eq_sourceColumn
    {Reference Address : Type*}
    (decode : Reference → Address)
    (referenceFallback : Reference) (addressFallback : Address)
    (chunks : List (List Reference)) (columns : List Address)
    (hdecoded : chunks.flatten.map decode = columns)
    (chunk column global : ℕ)
    (hchunk : chunk < chunks.length)
    (hcolumn : column < (chunks.getD chunk []).length)
    (hglobal : global < columns.length)
    (hindex :
      (chunks.take chunk).flatten.length + column = global) :
    decode ((chunks.getD chunk []).getD column referenceFallback) =
      columns.getD global addressFallback := by
  have hflatGlobal : global < chunks.flatten.length := by
    have hlength := congrArg List.length hdecoded
    have : chunks.flatten.length = columns.length := by
      simpa only [List.length_map] using hlength
    omega
  have hmapGlobal : global < (chunks.flatten.map decode).length := by
    simpa only [List.length_map] using hflatGlobal
  have hlocal :=
    flatten_getD_at_chunk referenceFallback chunks chunk column hchunk hcolumn
  calc
    decode ((chunks.getD chunk []).getD column referenceFallback) =
        decode (chunks.flatten.getD global referenceFallback) := by
          rw [hindex] at hlocal
          exact congrArg decode hlocal.symm
    _ = (chunks.flatten.map decode).getD global addressFallback := by
          rw [List.getD_eq_getElem _ _ hflatGlobal,
            List.getD_eq_getElem _ _ hmapGlobal]
          simp only [List.getElem_map]
    _ = columns.getD global addressFallback := by rw [hdecoded]

/-- The verifier query reference assigned by the permutation compiler to one
concrete column. -/
def permutationQueryReference
    (projected : CsFixture Fp) : AnyColumn → ColumnRef
  | ⟨.advice, index⟩ =>
      .advice (projected.adviceQueryLayout.findIdx (· = (index, 0)))
  | ⟨.fixed, index⟩ =>
      .fixed (projected.fixedQueryLayout.findIdx (· = (index, 0)))
  | ⟨.instance, index⟩ =>
      .instance (projected.instanceQueryLayout.findIdx (· = (index, 0)))

/-- The compiler's variable-width chunking preserves its indexed reference
stream exactly. -/
theorem permutationChunksOf_flatten
    (map : SelCompressMap) (cs : ConstraintSystem Fp) :
    (Keygen.permutationChunksOf map cs).flatten =
      (cs.permutationColumns.map
        (permutationQueryReference (projectCS map cs))).zipIdx := by
  unfold Keygen.permutationChunksOf
  rw [listToChunks_flatten]
  congr 2
  funext column
  rcases column with ⟨kind, index⟩
  cases kind <;> rfl

/-- A coherent compiled query reference decodes to the concrete column from
which the compiler created it. -/
theorem permutationColumnAddress_queryReference
    {shape : Shape} {F G : Type}
    (vk : VerifyingKey shape F G) (projected : CsFixture Fp)
    (hadvice :
      vk.adviceQueryLayout = projected.adviceQueryLayout)
    (hfixed :
      vk.fixedQueryLayout = projected.fixedQueryLayout)
    (hinstance :
      vk.instanceQueryLayout = projected.instanceQueryLayout)
    (column : AnyColumn)
    (hcoherent :
      PermutationColumnRef.Coherent vk
        (permutationQueryReference projected column)) :
    permutationColumnAddress vk
        (permutationQueryReference projected column) = column := by
  rcases column with ⟨kind, index⟩
  cases kind with
  | advice =>
      rcases hcoherent with ⟨-, hin, -⟩
      simp only [permutationQueryReference, permutationColumnAddress]
      rw [hadvice] at hin ⊢
      rw [getD_findIdx_eq_target projected.adviceQueryLayout
        (index, 0) (0, 0) hin]
  | fixed =>
      rcases hcoherent with ⟨-, hin, -⟩
      simp only [permutationQueryReference, permutationColumnAddress]
      rw [hfixed] at hin ⊢
      rw [getD_findIdx_eq_target projected.fixedQueryLayout
        (index, 0) (0, 0) hin]
  | «instance» =>
      rcases hcoherent with ⟨-, hin, -⟩
      simp only [permutationQueryReference, permutationColumnAddress]
      rw [hinstance] at hin ⊢
      rw [getD_findIdx_eq_target projected.instanceQueryLayout
        (index, 0) (0, 0) hin]

/--
For every closed top-level circuit, coherent routing makes the permutation
compiler's column encoding a round trip.
-/
theorem topLevelPermutationColumnAddresses_eq
    {G : Type} [AddCommGroup G] [Inhabited G]
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : Keygen.ProofParams) (urs : URS G)
    (hcoherent :
      PermutationChunkRoutingCoherent (top.toVerifierKey pp urs)) :
    (Keygen.permutationChunksOf
        top.selectorMap top.constraintSystem).flatten.map
          (fun reference =>
            permutationColumnAddress (top.toVerifierKey pp urs) reference.1) =
      (Keygen.permColsOf top.constraintSystem).map
        Halo2.Layout.ColRef.toAny := by
  rw [permutationChunksOf_flatten]
  change
    List.map
        (permutationColumnAddress (top.toVerifierKey pp urs) ∘ Prod.fst)
        _ =
      _
  rw [← List.map_map, List.zipIdx_map_fst]
  simp only [Keygen.permColsOf, List.map_map]
  apply List.map_congr_left
  intro column hcolumn
  simp only [Function.comp_apply]
  let projected :=
    projectCS top.selectorMap top.constraintSystem
  let reference :=
    permutationQueryReference projected column
  have hreference :
      reference ∈
        top.constraintSystem.permutationColumns.map
          (permutationQueryReference projected) :=
    List.mem_map.mpr ⟨column, hcolumn, rfl⟩
  have hindexed :
      ∃ indexed ∈
          (top.constraintSystem.permutationColumns.map
            (permutationQueryReference projected)).zipIdx,
        indexed.1 = reference := by
    have hfst :
        reference ∈
          ((top.constraintSystem.permutationColumns.map
            (permutationQueryReference projected)).zipIdx).map Prod.fst := by
      rw [List.zipIdx_map_fst]
      exact hreference
    simpa only using List.mem_map.mp hfst
  obtain ⟨indexed, hindexed, hindexedReference⟩ := hindexed
  have hindexedFlat :
      indexed ∈
        (Keygen.permutationChunksOf
          top.selectorMap top.constraintSystem).flatten := by
    rw [permutationChunksOf_flatten]
    simpa only [projected] using hindexed
  obtain ⟨chunk, hchunk, hindexedChunk⟩ :=
    List.mem_flatten.mp hindexedFlat
  have hvkChunks :
      (top.toVerifierKey pp urs).permutationChunks =
        Keygen.permutationChunksOf
          top.selectorMap top.constraintSystem := by
    rfl
  have hrouted := hcoherent chunk (by
    rw [hvkChunks]
    exact hchunk) indexed hindexedChunk
  have hreferenceCoherent :
      PermutationColumnRef.Coherent
        (top.toVerifierKey pp urs) reference := by
    rw [← hindexedReference]
    exact hrouted.1
  have hdecoded :
      permutationColumnAddress (top.toVerifierKey pp urs) reference =
        column :=
    permutationColumnAddress_queryReference
      (top.toVerifierKey pp urs) projected
      (top.toVerifierKey_adviceQueryLayout_derived pp urs)
      (top.toVerifierKey_fixedQueryLayout_derived pp urs)
      (top.toVerifierKey_instanceQueryLayout_derived pp urs)
      column hreferenceCoherent
  rcases column with ⟨kind, index⟩
  cases kind <;>
    simpa [reference, projected, permutationQueryReference,
      Halo2.Layout.ColRef.toAny] using hdecoded

end Zcash.Snark
