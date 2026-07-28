import Clean.Halo2.Keygen
import Zcash.Circuits.Tests.TestVkLayoutAdd
import Zcash.Circuits.Tests.TestVkLayoutMul
import Zcash.Circuits.Tests.TestVkLayoutAction
import Zcash.Circuits.Tests.TestVkLayoutActionBase

/-!
# Floor-planner derivation test: region starts computed from the operation stream

Closes "phase B": the region `starts` that `Fixtures/Layout.lean` used to read from the
Rust-dumped layout fixture are now DERIVED from the Halo2-Clean `Operations` by the ported
floor planners (`Clean.Halo2.Keygen.FloorPlanner`), and checked EQUAL to the fixture placements:

* `SimpleFloorPlanner.starts` == the Add/Mul layout fixtures' per-region starts;
* `V1.starts` == the Action / Action-base layout fixtures' per-region starts (the legacy
  pdqsort tie-order reproduced — see `FloorPlanner.Pdqsort`);
* `V1.constantAssignments` == the Action fixtures' `constants` allocation (rows derived
  from the planner's column allocations, no longer read from the fixture).

`TestSelMapDerivation` consumes these derived starts (see its header).
-/

namespace Zcash.Circuits.Fixtures.Test.FloorPlannerDeriv

open Halo2 Fixtures Halo2.FloorPlanner

/-! ## SimpleFloorPlanner: Add and Mul -/

-- Add harness: two regions, no table.
#guard SimpleFloorPlanner.starts LayoutAdd.ops = addLayout.regions.map (·.start)

-- Mul harness: derived starts equal the fixture's non-table placements.
#guard SimpleFloorPlanner.starts Test.Layout.ops
  = (mulLayout.regions.filter (·.name ≠ "table_idx")).map (·.start)

/-! ## V1: the full Action circuit (ironwood + pre-ironwood base)

The derived starts / constants are checked against the JSON fixtures at `#eval` time; the
fixtures are loaded by name through their SHA-256 pins (see `Fixtures/Json.lean`). Orchard's
constants column is fixed column 3 (`enable_constant`; the only constants column). -/

#eval show IO Unit from do
  let fx ← Json.loadLayoutFixture "actionLayout.json"
  let ops : Operations Fp := Test.LayoutAction.aProgram.operations
  let fixtureStarts : List ℕ := (fx.regions.filter (·.name ≠ "generator_table")).map (·.start)
  Json.runChecks [
    ("V1 derived starts = actionLayout placements",
      V1.starts ops == fixtureStarts),
    ("V1 derived constants allocation = actionLayout constants",
      (V1.constantAssignments ops [3]).map
        (fun (value, column, row) => (value.val, column, row)) == fx.constants)]

#eval show IO Unit from do
  let fx ← Json.loadLayoutFixture "actionBaseLayout.json"
  let ops : Operations Fp := Test.LayoutAction.aProgramBase.operations
  let fixtureStarts : List ℕ := (fx.regions.filter (·.name ≠ "generator_table")).map (·.start)
  Json.runChecks [
    ("V1 derived starts = actionBaseLayout placements",
      V1.starts ops == fixtureStarts),
    ("V1 derived constants allocation = actionBaseLayout constants",
      (V1.constantAssignments ops [3]).map
        (fun (value, column, row) => (value.val, column, row)) == fx.constants)]

end Zcash.Circuits.Fixtures.Test.FloorPlannerDeriv
