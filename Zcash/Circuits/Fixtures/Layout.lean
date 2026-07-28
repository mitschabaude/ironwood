import Zcash.Circuits.Fixtures.FixtureTypes
import Clean.Halo2.Keygen.Layout

/-!
# Fixture-side layout glue

The reusable keygen layout semantics (planner copy lists, the keygen `Assembly`
replay, fixed contents) live upstream in `Clean.Halo2.Keygen.Layout` (`Halo2.Layout`).
This module keeps only the fixture-bound piece: reading region start rows off a
`LayoutFixture`'s placement dump via the lockstep region-slot walk.
-/

namespace Zcash.Circuits.Fixtures.Layout

open Halo2 Halo2.Layout

variable {F : Type}

/-- Start rows indexed by Halo2-Clean `assignRegion` index, obtained by zipping the region
slots with the fixture's `regions` (in index order): each slot consumes one placement; only
real regions contribute a start. -/
def regionStarts (ops : Operations F) (fx : LayoutFixture) : List ℕ :=
  let sorted := fx.regions.toArray.qsort (·.index < ·.index) |>.toList
  ((regionSlots ops).zip sorted).filterMap fun ((isRegion, _), pl) =>
    if isRegion then some pl.start else none

end Zcash.Circuits.Fixtures.Layout
