import Zcash.Snark.Fixtures.MultiAction.Fixture

/-!
# Shape and VK faithfulness checks for the multi-action capture

The generated fixture remains the Rust/Lean boundary: Lean does not re-run Orchard key generation.
The Orchard capture now re-runs key generation, compares that exact key against the checked-in
canonical Post-NU6.3 `PinnedVerificationKey`, and passes the same key to verification and the fixture
dumper; `Fixtures.PostNu63` pins the emitted transcript representation in Lean. These checks make the
remaining generated boundary less silent by verifying that the named captured lists, typed accessors,
query layouts, expression indices, and captured transcript prefix agree with the generated `shape`.

In particular this catches the totalization hazards called out in `Verifier.Assemble`: an
out-of-range query index would otherwise route through `finFn`/`finFnG` and alias `0`/`default`.
-/

namespace Zcash.Snark.Fixture2

open Zcash.Snark

def capturedInstanceCommitmentPrefix : List (TranscriptElt Fp G) :=
  (List.ofFn (fun p : Fin shape.numProofs =>
    (List.ofFn (fun i : Fin capturedNumInstanceColumns =>
      TranscriptElt.point (vk.instanceCommitment p i.val))))).flatten

def capturedInitStartsWithScalar : Bool :=
  match capturedInit with
  | TranscriptElt.scalar _ :: _ => true
  | _ => false

theorem capturedInit_has_vk_scalar_and_instance_commitments :
    capturedInitStartsWithScalar = true
      ∧ capturedInit.drop 1 = capturedInstanceCommitmentPrefix
      ∧ capturedInit.length = 1 + capturedInstanceCommitmentPrefix.length := by
  native_decide

theorem captured_list_lengths_match_shape :
    -- Fixed commitments are per *column* and fixed evals per *query*; the counts coincide (29) for
    -- this Orchard VK because every fixed column is queried exactly once. The load-bearing guard for
    -- out-of-range columns is `query_layout_columns_in_range` below.
    capturedFixedCommitments.length = capturedFixedEvals.length
      ∧ capturedInstanceCommitments.length = shape.numProofs * capturedNumInstanceColumns
      ∧ capturedPermutationCommonCommitments.length = shape.numPermutationColumns
      ∧ capturedPermutationCommonEvals.length = shape.numPermutationColumns
      ∧ capturedAdviceCommitments.length = shape.numProofs * shape.numAdviceColumns
      ∧ capturedLookupPermutedInput.length = shape.numProofs * shape.numLookups
      ∧ capturedLookupPermutedTable.length = shape.numProofs * shape.numLookups
      ∧ capturedPermutationProducts.length = shape.numProofs * shape.numPermutationSets
      ∧ capturedLookupProducts.length = shape.numProofs * shape.numLookups
      ∧ capturedHPieces.length = shape.numQuotientPieces
      ∧ capturedInstanceEvals.length = shape.numProofs * shape.numInstanceQueries
      ∧ capturedAdviceEvals.length = shape.numProofs * shape.numAdviceQueries
      ∧ capturedFixedEvals.length = shape.numFixedQueries
      ∧ capturedPermutationSetEvals.length = shape.numProofs * shape.numPermutationSets
      ∧ capturedLookupEvals.length = shape.numProofs * shape.numLookups
      ∧ capturedMultiopenU.length = shape.numPointSets
      ∧ capturedIpaRounds.length = shape.k := by
  native_decide

def layoutColumnsInRange (bound : ℕ) (layout : List (ℕ × ℤ)) : Bool :=
  layout.all fun entry => decide (entry.1 < bound)

theorem query_layout_columns_in_range :
    layoutColumnsInRange capturedNumInstanceColumns vk.instanceQueryLayout = true
      ∧ layoutColumnsInRange shape.numAdviceColumns vk.adviceQueryLayout = true
      ∧ layoutColumnsInRange capturedFixedCommitments.length vk.fixedQueryLayout = true := by
  native_decide

def columnRefInRange : ColumnRef → Bool
  | .advice i => decide (i < shape.numAdviceQueries)
  | .fixed i => decide (i < shape.numFixedQueries)
  | .instance i => decide (i < shape.numInstanceQueries)

def exprRefsInRange : Expr Fp → Bool
  | .constant _ => true
  | .fixed i => decide (i < shape.numFixedQueries)
  | .advice i => decide (i < shape.numAdviceQueries)
  | .instance i => decide (i < shape.numInstanceQueries)
  | .negated e => exprRefsInRange e
  | .sum a b => exprRefsInRange a && exprRefsInRange b
  | .product a b => exprRefsInRange a && exprRefsInRange b
  | .scaled e _ => exprRefsInRange e

def exprListRefsInRange (xs : List (Expr Fp)) : Bool :=
  xs.all exprRefsInRange

def lookupExprRefsInRange (exprs : Fin shape.numLookups → List (Expr Fp)) : Bool :=
  (List.ofFn (fun l : Fin shape.numLookups => exprListRefsInRange (exprs l))).all fun b => b

def permutationChunksRefsInRange : Bool :=
  vk.permutationChunks.all fun chunk =>
    chunk.all fun cr => columnRefInRange cr.1 && decide (cr.2 < shape.numPermutationColumns)

theorem vk_expression_refs_in_range :
    exprListRefsInRange vk.gates = true
      ∧ lookupExprRefsInRange vk.lookupInputExprs = true
      ∧ lookupExprRefsInRange vk.lookupTableExprs = true
      ∧ permutationChunksRefsInRange = true := by
  native_decide

theorem permutation_chunks_match_shape :
    vk.permutationChunks.length = shape.numPermutationSets
      ∧ (vk.permutationChunks.map List.length).sum = shape.numPermutationColumns := by
  native_decide

theorem vk_domain_size_matches_shape :
    vk.n = 2 ^ shape.k := by
  native_decide

end Zcash.Snark.Fixture2
