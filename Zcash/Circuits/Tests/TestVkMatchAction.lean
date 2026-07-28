import Clean.Halo2.Keygen
import Zcash.Circuits.Fixtures.ActionSelMap
import Zcash.Circuits.Fixtures.Json
import Zcash.Circuits.Specs.SinsemillaGenerators
import Zcash.Circuits.Action.Circuit

/-!
# VK-match test: the full Orchard Action circuit `configure`

Projects the `ConstraintSystem` produced by the ported `Action.Circuit.configure` to the
`CsFixture` shape — via the Rust-dumped selector map applied mechanically — and checks it
EQUAL to the fixture dumped from the actual Rust circuit after `compress_selectors`
(`actionPost.json`). `configure` is version-independent (post-NU 6.2 and 6.3 share the
CS), so this single test covers both top-level circuits.

The fixtures are JSON data files loaded by name at `#eval` time (see `Fixtures/Json.lean`
for the codec, the SHA-256 pinning scheme, and why the data is not a Lean term); a
mismatch or failed load is a build failure, exactly like the former `#guard`s.
-/

namespace Zcash.Circuits.Fixtures.Test.MatchAction

open Halo2
open Fixtures.Json

def actionCS : ConstraintSystem Fp :=
  (Action.Circuit.configure Specs.Sinsemilla.orchardGenerators {}).2

#eval show IO Unit from do
  let actionPost ← loadCsFixture "actionPost.json"
  runChecks [
    -- Every gate's/lookup's `queriedCells` registered faithfully; the layout equality
    -- below then certifies the recorded order against the Rust dump.
    ("action: no ill-formed queriedCells", actionCS.invalidQueriedCells.isEmpty),
    -- The Rust-dumped selector map, applied mechanically to the configure-recorded CS,
    -- yields exactly the dumped CS.
    ("actionPost: projected CS = dump",
      projectCS actionSelMap actionCS == actionPost)]

end Zcash.Circuits.Fixtures.Test.MatchAction
