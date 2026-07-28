/-!
# The circuit fixture content stamp

GENERATED from `SHA256SUMS` by `stamp.sh` in this directory. Do not edit by hand.

The SHA-256 pins as Lean data. Nothing here recomputes a hash — CI's `sha256sum -c`
enforces the pins. This module is what carries a fixture change into Lake's import graph,
and the table `Json.pinnedPath` resolves a fixture name through; `Json.lean`'s header
carries both stories.
-/

namespace Zcash.Circuits.Fixtures.Stamp

/-- The committed `SHA256SUMS` pins, as `(file, SHA-256)` pairs. -/
def entries : List (String × String) := [
  ("actionPost.json", "a6083ecd2abc72ea3641fa0d066aabcd91ecb89a1554ef31aa31ab6d7591ff68"),
  ("actionLayout.json", "7ac082324c93ef6c097ad26dfe7a166d1a74e41a5a6b4c0e250bf3e3d2163a87"),
  ("actionBaseLayout.json", "1c155864b0256ad93b9c4d09394dcf7b302ef5fcf9a7ac356ae15988ba09aa08")
]

end Zcash.Circuits.Fixtures.Stamp
