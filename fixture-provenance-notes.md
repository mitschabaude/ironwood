# Fixture provenance — what the dumps are and what they are not

(Companion note to `Zcash/Circuits/Fixtures/PROVENANCE.md` on the `pr98-audit-fixes`
branch.)

**What they are.** The `Zcash/Circuits/Fixtures/` artifacts were produced by running
instrumented checkouts of the actual `zcash/halo2` (halo2_proofs 0.3.2) and
`zcash/orchard` code: the dump tooling (`halo2_proofs::plonk::dump_lean`,
`layout_dump`) hooks the real `Circuit::configure` / `keygen_vk` path and serializes
the real constraint system, selector-compression map, permutation σ, and fixed cells.
They are not hand-written and not from a reimplementation. For the post-NU 6.3
circuit there is no deployed source in any case — the orchard ironwood branch *is*
the circuit-in-development, and that is what was dumped.

**What's missing.** Any machine-checkable proof of that lineage. The instrumented
forks were never published and their commit hashes never recorded, so the generation
cannot currently be re-run to confirm the checked-in bytes correspond to
orchard 0.14.0 / the ironwood branch as claimed. Those claims exist only as prose in
test docstrings. `PROVENANCE.md` therefore marks the fork commits **UNKNOWN**
rather than inventing pins.

**What limits the damage.** Two independent corroborations:

1. The Lean `configure` was ported by hand from the orchard source (with line-level
   citations), and the projected constraint system matches the dump exactly — now
   build-verified by the `CircuitVkCheck` target. A fabricated or drifted dump would
   have to coincidentally agree with an independent port of the real source across
   193 gate polynomials, all lookup arguments, the query layouts, ~3,000 ordered copy
   constraints, and ~17k fixed cells.
2. The Lean gate definitions were separately diffed term-for-term against
   halo2_gadgets / orchard source during review. Dump, port, and upstream source all
   agree; the missing link is only the *reproducibility* of the dump.

**Follow-ups.**

- Publish the instrumented halo2/orchard branches (or upstream the dump tooling
  behind a feature flag), record the exact commits in `PROVENANCE.md`, and add a CI
  job that regenerates the JSON fixtures from those pins and diffs them against the
  checked-in bytes — the circuit-side analogue of what `fixtures.yml` already does
  for the `Zcash/Snark/Fixtures/` verifier-fingerprint captures (pinned
  orchard 0.15.1 / halo2 0.3.3 via `orchard-fingerprint-instances`).
- For the base (pre-NU 6.3) circuit, a stronger check is available: verify the
  dumped constraint system against the actual mainnet Orchard verifying key — a
  fixed public artifact — tying the chain to the deployed network rather than to
  any checkout.
