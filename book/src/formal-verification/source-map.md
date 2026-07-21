# Source Map

A directory-by-directory index of the Lean development under [`Zcash/`](https://github.com/zcash/ironwood/tree/main/Zcash):
what each subtree contains and where to start reading. It is the source-tree companion
to the [proof map](proof-map.md) (which traces how the results connect) and the
[glossary](glossary.md) (which defines the coined terms).

The development has two layers. **`Zcash/Snark/`** is verifier soundness for the deployed
Halo 2 verifier — an accepting proof is bound to a witness satisfying the circuit, or else
an explicit break of a hardness assumption is computed. **`Zcash/Security/`** is the
protocol security-property layer — the binding-signature balance, key-binding, and
ledger-model games built on top of that verifier. A small set of shared foundations
(`Zcash/Common/`, `Zcash/Meta/`) and library-wide trust census (`Zcash/TrustBoundary.lean`)
support both.

Each `.lean` file carries a module docstring with the details; this page stays at the
directory level, naming the notable modules as entry points.

## Top level — `Zcash/`

- **`Common/`** — shared cryptographic primitives. `DiscreteLogRelation` carries a
  nontrivial `F`-linear (discrete-log) relation among a family of generators as *computed
  data* — the coefficients — so the reduction-style security arguments can produce a break
  rather than merely assert one exists (see *breaks as computed data* on the
  [Formal Verification](../formal-verification.md) page).
- **`Meta/`** — build-time metaprogramming. `AxiomCheck` provides `assert_axioms`, a sibling
  of Mathlib's `assert_no_sorry` that asserts an *upper bound* on a declaration's trusted
  base without hard-coding the pretty-printed axiom list, so the trust pins stay green across
  toolchain bumps that rename the `native_decide` axiom.
- **`TrustBoundary.lean`** — the library-wide census that makes the trust claims build-time
  checks rather than prose: a change that widens any checked declaration's trusted base — a
  reachable `sorry`, an unexpected axiom, or `native_decide` where none was permitted — fails
  the build here.

## Verifier soundness — `Zcash/Snark/`

### `Core/` — the verifier's objects

The nouns the verifier operates on, modeled abstractly so most proofs stay generic over the
field and group. `Field` fixes the scalar field `F_p` (Vesta's scalar = Pallas base) and its
cardinality; `Group` fixes the verifier group `E_q` (Vesta) and the uniform reference string,
as an `F`-module; `Msm` is the fingerprint multiscalar multiplication the verifier collapses
its whole check into, mirroring halo2's `MSM<C>`; `ProofString` is the proof as opaque field
and group elements after canonical decoding; `Challenges` records the verifier's challenges
(`θ, β, γ, y, x`, the multiopen `x₁…x₄`, and the IPA `ξ, z` and round challenges `uⱼ`).

### `Verifier/` — the MSM assembly

The pure function that assembles the fingerprint MSM in the exact order of halo2's
`plonk/verifier.rs` — the Lean image of the interactive verifier. `Assemble` and `Checks`
compose the building blocks; `Queries` builds the per-argument opening queries; `Expressions`
recomputes the vanishing argument's `expected_h_eval`; `Ipa` is the inner-product-argument
opening (`compute_s` / `compute_b`); `FiatShamir` models halo2's Blake2b challenge schedule as
an abstract `squeeze`; `Parametric` proves the assembly and schedule traverse every sub-proof
for an arbitrary proof count (every consensus-valid Orchard action count is one instance).

### `Fingerprint/` — the cross-check and its soundness

`Match` is the fingerprint match: running the deployed Rust verifier and the Lean `assemble`
on the same proof and challenges and comparing the assembled MSMs coefficient-for-coefficient
— the cross-check that validates the Lean assembly in place of a line-by-line translation
proof. `SchwartzZippel` and `Batch` supply the soundness bounds: a fingerprint agrees with a
random evaluation, and a random-linear-combination batch is the identity, only with negligible
probability.

### `Fixtures/` — captured proofs and boundary checks

Concrete Orchard captures that exercise the assembly end-to-end and make the Rust/Lean boundary
less silent. `MaxShape` specializes the verifier shape to the captured column and query
dimensions while leaving the action count free; `ScheduleMarker` re-encodes captured
Fiat–Shamir schedules into the model's marker form. `SingleAction/` and `MultiAction/` hold the
captured single- and multi-action proofs with their shape/VK **faithfulness** checks,
**Fiat–Shamir** schedule checks, adversarial **negative** fixtures, and — for the single-action
capture — the checked `TrustBoundary` that turns the fingerprint match into build-time
obligations (this subtree is the `FixtureCheck` lake target).

### `Soundness/` — the soundness argument

The core argument that an accepting proof yields a witness or a computed break. The top-level
modules cover the argument end to end: `Main` (conditional soundness and the deployed-acceptance
route), `KnowledgeSoundness` (the `SnarkRelation` knowledge-soundness relation), `Constraints`
(Schwartz–Zippel soundness of the vanishing check), the permutation/lookup stack
(`GrandProduct` — the shared grand-product-to-multiset kernel — `Permutation`,
`PermutationConstruction`, `Lookup`), the IPA stack (`InnerProduct`, `IpaSoundness`,
`Extraction`, `Consistency`, `CommitFold`), the `Vesta` instantiation that pins the abstract
group to the actual Vesta curve, and the `TrustBoundary` for the binding reductions. Three
subtrees carry the heavier machinery:

- **`AGM/`** — the algebraic-group-model layer. It turns the relation coefficients computed
  from algebraic prover data (`Peel`, `Capstone`) into a discrete-log solution over the
  augmented basis `(g, U, W)` (`Adapter`, following Fuchsbauer–Kiltz–Loss), feeds the
  binding-signature relations in as AGM inputs (`BindingSignature`), adds the algebraic
  coefficients to the forking-certificate interfaces (`Prover`), and bounds the probability
  loss of the fixed-challenge-slot DL reduction (`Probability`, `ProbabilityCoins`,
  `ProbabilityVesta`), all under a checked `TrustBoundary`.
- **`Forking/`** — the reusable Fiat–Shamir forking kernel: random-oracle primitives
  (`Oracle`), the deployed round ordering and rewinding (`Ordering`, `Rewind`), fork-tree
  existence and the forking-lemma probability bound (`Tree`, `Probability`), and the transcript
  assembly and extraction that turn forked transcripts into a deployed IPA tree (`Assembly`,
  `Extractor`). **`Forking/Adversary/`** builds the querying-adversary reduction on top: the
  `Q`-query adaptive adversary model (`OracleComp`), executable recursive forking from a finite
  tape (`Recursive`), the Fiat–Shamir-to-AGM handoff (`Algebraic`), oracle-domain reduction to
  finite support (`DomainReduction`), the adaptive interface and pre-IPA query accounting
  (`Adaptive`, `PreIpa`, `Provenance`), and the expected-run bookkeeping (`ExpectedRuns`,
  `ExpectedRunsPoly` — an unconditional polynomial bound remains open).
- **`Deployed/`** — the bridge from the clean, abstract soundness onto halo2's actual deployed
  IPA. It models the deployed IPA's `U`/`W` apparatus and peels it onto the clean recursive IPA
  (`Ipa`, `IpaPeel`), unfolds the flattened deployed MSM into the recursive generator fold
  (`Fold`), shows deployed acceptance implies halo2's explicit IPA verifier equation
  (`Verification`), and reduces binding over the augmented generators to discrete-log-relation
  hardness (`Binding`), under a checked `TrustBoundary`.

## Protocol security — `Zcash/Security/`

The security-property games layered on the verifier, all in the reduction style: a property
violation *exhibits* a concrete break (a hash collision or a discrete-log relation), carried as
computed data.

- **`Common/`** — the classical random-oracle foundation shared by the games. `RandomOracle`
  is the collision vocabulary (the `Collision` / `CollisionUpToSign` structures); `Birthday`
  is the birthday-bound counting for random-oracle ±-collisions, in the counting-fraction style
  used throughout (no probability monad).
- **`BindingSignature/`** — the binding-signature *balance* argument (spec §4.13 Sapling /
  §4.14 Orchard). `Balance` is the shared algebraic core over an arbitrary `F`-module;
  `Orchard` and `Sapling` add the per-pool no-overflow bounds that keep the value sums below
  the scalar-field order.
- **`KeyBinding/`** — the key-binding theorem (ZIP 2005, ROM). `Basic` is the deterministic
  layer: a verifying Recovery-Statement witness pins the key components (`ak` up to y-sign,
  `nk`, and the `qk`/`sk` branch) to `ivk` unless an explicit break is computed. `Instance`
  bridges that concrete development to the games' `KeyBindingInterface`.
- **`Ledger/`** — the ledger-model games. `Statement` transcribes the games-relevant conjuncts
  of an Orchard-shaped Action statement over abstract primitives — the interface the Balance,
  Spendability, and Spend-Authority games consume — and `Merkle` proves fixed-depth Merkle
  trees are position-binding up to an exhibited tree-hash collision.
