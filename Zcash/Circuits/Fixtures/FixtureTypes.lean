import Zcash.Circuits.Ecc.Basic
import Zcash.Common.Expr
import Clean.Halo2.Keygen
import Clean.Halo2.Keygen.Layout

/-!
# VK-matching fixture types

The record shapes for comparing a Halo2-Clean `ConstraintSystem` projection against a
fixture dumped from the actual Rust circuit. The symbolic CS shapes — `CsFixture`,
`LookupFixture`, `SelCompress`, `SelCompressMap` — are now the Clean-core pinned types
(`Clean.Halo2.Keygen`), re-exported here as `Fp`-specialised abbreviations so the fixture
data literals (`AddPost.lean`, `MulPost.lean`, the `actionPost.json` codec) and the layout
tests keep addressing them unqualified. Gate polynomials are the pinned AST
`Halo2.RichExpression Fp`; the verifier's own `Zcash.Snark.Expr` coincides on the shared
constructors and converts at the VK boundary (`Zcash/Common/ExprRich.lean`).

The dumper (`halo2_proofs::plonk::dump_lean`) emits `CsFixture` literals into
`AddPost.lean` in this namespace.
-/

namespace Zcash.Circuits.Fixtures

/-- Build an `Fp` from four little-endian u64 limbs, matching the ironwood fixture's `mkFp`
and the Rust dumper's `to_repr()` limb encoding. -/
def mkFp (a b c d : ℕ) : Fp :=
  (a : Fp) + (b : Fp) * (2 : Fp) ^ 64 + (c : Fp) * (2 : Fp) ^ 128 + (d : Fp) * (2 : Fp) ^ 192

/-- One projected lookup argument (the pinned `(lookupInputExprs, lookupTableExprs)`
per-lookup shape). Both sides are index-based `RichExpression`s. -/
abbrev LookupFixture := Halo2.LookupFixture Fp

/-- The constraint-system data a Halo2-Clean projection must reproduce (the pinned/verifier
CS-field shape), specialised to a single circuit's dump. Gate polynomials are the pinned
`Halo2.RichExpression Fp`. -/
abbrev CsFixture := Halo2.CsFixture Fp

/-- One selector's compression datum from `compress_selectors`: packed fixed-column index,
combination length, and this selector's assigned root. -/
abbrev SelCompress := Halo2.SelCompress

/-- The whole selector-compression map: the new packed-column count and per selector its
`SelCompress`. -/
abbrev SelCompressMap := Halo2.SelCompressMap

/-! ## Phase 2: layout fixtures (permutation σ + fixed values + region placements)

The `CsFixture` above captures the *symbolic* constraint system. `LayoutFixture` captures the
**keygen-view layout** the CS dump elides — the products of running the harness circuit's
`synthesize` exactly as `plonk::keygen::keygen_vk` does. Kept intentionally minimal and
`DecidableEq`-friendly: everything is `ℕ`, `String`, and flat tuples of `ℕ`. Field values are
`ℕ` literals — canonical Pallas-base representatives (the same `to_repr()` integer `mkFp`
decodes, but decimal, so no field arithmetic is forced during elaboration). -/

/-- A permutation-argument column reference, in `cs.permutation.get_columns()` order —
upstreamed to Clean (`Halo2.Layout.ColRef`); re-exposed here for the fixture records. -/
abbrev ColRef := Halo2.Layout.ColRef

/-- One floor-planner region placement: creation-order `index`, region `name`, and `start`
row. `start` is the minimum absolute row the region touches, which equals the
`SimpleFloorPlanner`/`V1` `region_start` for every `halo2_gadgets` region (each assigns its
first row at relative offset 0). -/
structure RegionPlacement where
  index : ℕ
  name : String
  start : ℕ
deriving DecidableEq, Repr

/-- The keygen-view layout of one harness circuit, dumped by `halo2 dump_lean` Phase 2.

* `regions` — floor-planner placements, in creation order.
* `permColumns` — the permutation column order (`cs.permutation.get_columns()`); the column
  indices in `copyList` and `sigma` index into this list.
* `copyList` — the **ordered** raw `copy(leftCol, leftRow, rightCol, rightRow)` calls the keygen
  `Assembly` received, IN ORDER, before any cycle merge (flat `ℕ` quadruples, col indices into
  `permColumns`). keygen's cycle-merge (`permutation/keygen.rs`) produces different cycle
  rotations for different copy orders, so the Lean side checks its own copy sequence
  element-for-element (strict, order-sensitive — pinpoints placement/ordering bugs) BEFORE σ.
* `sigma` — the **sparse** permutation mapping σ (the exact keygen cycle structure, the semantic
  object built FROM `copyList`): each entry `(colIdx, row, colIdx', row')` is a cell where
  `mapping[colIdx][row] = (colIdx', row') ≠ (colIdx, row)`. Flat `ℕ` quadruples for compact
  elaboration; grouped `((colIdx, row), (colIdx', row'))` conceptually.
* `constants` — the floor-planner's constants allocation, in assignment order:
  `(value, constantsColIdx, row)`. `constrain_constant` / `assign_advice_from_constant` route
  through rows of the constants fixed column that the planner picks; those rows are not derivable
  Lean-side, so they are pinned here (like `regions`). These cells also appear in `copyList`,
  `sigma`, and `fixed` — expected and wanted. `value` is a decimal `ℕ` (canonical Pallas base).
* `fixed` — the **sparse** fixed-column assignments `(fixedColIdx, row, value)`: constants
  (`assign_fixed` / `assign_advice_from_constant`), any loaded lookup-table columns, and the
  post-compression packed-selector columns (`compress_selectors` output polys, indexed
  `numFixedBefore + j`). `value` is a canonical Pallas-base representative as a decimal `ℕ`. -/
structure LayoutFixture where
  k : ℕ
  n : ℕ
  regions : List RegionPlacement
  permColumns : List ColRef
  copyList : List (ℕ × ℕ × ℕ × ℕ)
  sigma : List (ℕ × ℕ × ℕ × ℕ)
  constants : List (ℕ × ℕ × ℕ)
  fixed : List (ℕ × ℕ × ℕ)
deriving DecidableEq, Repr

end Zcash.Circuits.Fixtures
