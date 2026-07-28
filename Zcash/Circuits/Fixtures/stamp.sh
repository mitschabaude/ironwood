#!/bin/sh
# Renders SHA256SUMS as Stamp.lean, the Lean-side handle on the fixture content pins.
#
# Lake tracks a module's imports, not the `.json` data files a `#eval` reads, so a
# regenerated fixture on its own leaves the consuming check cached and unrun on a local
# incremental build. Refreshing SHA256SUMS (which CI's `sha256sum -c` obliges) and this
# stamp with it turns a fixture change into a source change Lake does follow.
#
# Usage, from this directory:  ./stamp.sh > Stamp.lean
# CI diffs the committed Stamp.lean against this script's output, so the rendering must
# stay deterministic: entries are emitted in SHA256SUMS' own line order.
set -eu
cd "$(dirname "$0")"

cat <<'HEADER'
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
HEADER

awk 'NR > 1 { printf ",\n" } { printf "  (\"%s\", \"%s\")", $2, $1 } END { printf "\n" }' \
  SHA256SUMS

cat <<'FOOTER'
]

end Zcash.Circuits.Fixtures.Stamp
FOOTER
