# Fixture provenance

The files in this directory are the empirical binding between the Lean circuit model
(`Zcash/Circuits/Action/Circuit.lean` and the isolated Add/Mul chains) and the actual
Rust halo2 circuit. They were dumped from instrumented Rust checkouts, **not** written
by hand, and are consumed by the `CircuitCheck` build target
(`Zcash/Circuits/Tests/TestVk*`). This file records where each artifact came from, how
it is pinned, and what is — and is not — currently reproducible.

## Generator tooling

Two custom dump entry points, living in **sibling checkouts** of the Rust repositories
(not in this repository):

| Tool | Location (in the instrumented checkout) | Produces |
|---|---|---|
| `dump_lean` | `halo2_proofs::plonk::dump_lean` (a fork of github.com/zcash/halo2, halo2_proofs 0.3.2 era — not upstream `main`) | `CsFixture` / `LayoutFixture` dumps: `AddPre/AddPost/MulPre/MulPost.lean`, `AddLayout/MulLayout.lean`, `actionPost.json`, `action{,Base}Layout.json` |
| `layout_dump` | `halo2_gadgets/src/ecc/chip/layout_dump.rs` (`dump_layout_add`, `dump_layout_mul`) and `dump_layout_action` (orchard checkout) | the `*SelMap.lean` selector-compression maps |

Example regeneration command (Add chain, from the instrumented halo2 checkout):

```
cargo test --release -p halo2_gadgets --lib ecc::chip::layout_dump::dump_layout_add -- --nocapture
```

The isolated Mul chain uses `MulDumpCircuit` (`halo2_gadgets/src/ecc/chip/dump.rs`):
one real variable-base scalar mul, `Value::unknown()` witnesses, `k = 11`, run through
the `SimpleFloorPlanner` exactly as `keygen_vk` does.

## Source versions

| Fact | Status |
|---|---|
| halo2_proofs version | 0.3.2 (github.com/zcash/halo2) — recorded in `Layout.lean` |
| Base (pre-NU 6.3) circuit | orchard 0.14.0 — the `actionBase` dump is byte-identical to the 0.14.0 circuit, verified on the ironwood branch (`TestVkLayoutActionBase.lean`) |
| Post (NU 6.3 / ironwood) circuit | the orchard ironwood branch (`Circuit::synthesize` with `synthesize_cross_address_checks`) |
| Instrumented halo2 / orchard commit hashes | Not pinned to a public commit. The `dump_lean` / `layout_dump` / `dump_layout_action` instrumentation is one-off tooling in local checkouts of halo2/orchard — it exists only to emit these fixtures for the VK-match tests, is not production code, and by decision is not being upstreamed to main. So there is no public commit to pin and no byte-for-byte regeneration from public sources. |

Note that zcash/halo2#922 does **not** close this: it concerns the *separate*
verifier-fingerprint exporter (`dump_vesta_lean_fixture` → `Zcash/Snark/Fixtures/`), not
this circuit-VK dump pipeline.

Because the dump instrumentation is intentionally unpublished, these fixtures are **not**
reproducible from pinned public sources the way the `Zcash/Snark/Fixtures/` verifier
fingerprint captures are (those regenerate in CI from a pinned orchard release —
`.github/workflows/fixtures.yml`). What certifies them instead is the pair of guards under
[Content pinning](#content-pinning): the SHA-256 pin in `SHA256SUMS` (a CI `sha256sum -c`
drift/tamper guard) and the `CircuitCheck` reconstruction (`TestVk*`), which asserts the
projected Lean CS/layout equals the dumped bytes — a divergence on either side fails the
build. Making regeneration reproducible would mean upstreaming the dump behind a feature
flag; there is no current plan to do that.

## Content pinning

Every JSON fixture is pinned by a SHA-256 content hash in
[`SHA256SUMS`](./SHA256SUMS) (standard `sha256sum` format), enforced in CI by the
`Fixtures/*.json` guard in [`.github/workflows/lean.yml`](../../../.github/workflows/lean.yml)
(`sha256sum -c`, the OS tool). SHA-256 — a cryptographic hash — means the pin resists a
crafted swap, not just accidental drift. The hash is **not** recomputed inside the Lean
build: no fast SHA-256 exists in the toolchain (Clean's `Specs.SHA256` reference spec does
not finish over even the 33 KB fixture at `#eval` time), and a hand-rolled one is not worth
maintaining. Regenerate the pins with `sha256sum <files> > SHA256SUMS` from this directory,
then refresh the Lean stamp below with `./stamp.sh > Stamp.lean`. Current artifacts:

| File | SHA-256 | Bytes | Consumed by |
|---|---|---|---|
| `actionPost.json` | `a6083ecd2abc72ea3641fa0d066aabcd91ecb89a1554ef31aa31ab6d7591ff68` | 67,143 | `TestVkMatchAction.lean` |
| `actionLayout.json` | `7ac082324c93ef6c097ad26dfe7a166d1a74e41a5a6b4c0e250bf3e3d2163a87` | 943,608 | `TestVkLayoutAction.lean` |
| `actionBaseLayout.json` | `1c155864b0256ad93b9c4d09394dcf7b302ef5fcf9a7ac356ae15988ba09aa08` | 941,568 | `TestVkLayoutActionBase.lean` |

The Add/Mul fixtures and the SelMaps are small enough to live as Lean literals; they
are pinned by being source files (any edit is a reviewable diff), and their headers
carry the generating tool.

**Rebuild tracking.** Lake tracks a module's imports, not the `.json` files a `#eval`
reads, so a regenerated fixture on its own leaves the `CircuitCheck` reconstruction
cached and unrun on a local incremental build. [`Stamp.lean`](./Stamp.lean) — the pins
rendered as Lean data by [`stamp.sh`](./stamp.sh) and imported by the loader the tests go
through — puts the fixture content in the import graph, so refreshing `SHA256SUMS` and the
stamp together is a source change Lake follows and the check re-runs. CI diffs the stamp
against a fresh rendering, so it cannot fall behind `SHA256SUMS` unnoticed. The loaders
also resolve a fixture by name through the stamp, so a file `SHA256SUMS` does not list
cannot be read by a test at all.

**What the hash does and does not guarantee.** The pin guarantees the bytes have not
drifted since the hash was recorded; it does **not** by itself certify the bytes were
produced from the claimed circuit. That certification rests on the one-time generation
event plus the `CircuitCheck` equality checks (the projected Lean CS must equal the
dump — a divergence in either side surfaces as a build failure). Reproducing the bytes
from public sources would need the dump instrumentation upstreamed, which is not planned
(see [Source versions](#source-versions)).
