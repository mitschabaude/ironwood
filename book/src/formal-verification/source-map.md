# Source Map

A directory-by-directory index of the Lean development under [`Zcash/`](https://github.com/zcash/ironwood/tree/main/Zcash):
what each subtree contains and where to start reading. It is the source-tree companion
to the [proof map](proof-map.md) (which traces how the results connect), the
[security definitions](security-definitions.md) (which state the properties being proven),
and the [glossary](glossary.md) (which defines the coined terms).

The development has three layers. **`Zcash/Snark/`** is verifier soundness for the deployed
Halo 2 verifier — an accepting proof is bound to a witness satisfying the circuit, or else
an explicit break of a hardness assumption is computed. **`Zcash/Circuits/`** is the circuit
layer — a port of the Orchard Action circuit onto Clean's Halo 2 formalization, saying what
satisfying that circuit means in protocol terms. **`Zcash/Security/`** is the protocol
security-property layer — the binding-signature balance, key-binding, and ledger-model games
built on top. A small set of shared foundations (`Zcash/Common/`, `Zcash/Meta/`) and a
library-wide trust census (`Zcash/TrustBoundary.lean`) support all three.

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
  the build here. The SNARK-side censuses were consolidated into this one file, so apart from
  the per-capture fixture boundaries below it is the single place the trust claims are pinned.

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
less silent. This whole subtree is the `FixtureCheck` lake target, kept out of `lake build Zcash`
(the captures are large, generated, and slow) but built by CI. `MaxShape` specializes the verifier
shape to the captured column and query dimensions while leaving the action count free;
`ScheduleMarker` re-encodes captured Fiat–Shamir schedules into the model's marker form;
`PostNu63` pins the canonical post-NU 6.3 verifying key and URS so fixture drift is visible here.
`SingleAction/` and `MultiAction/` hold the captured single- and multi-action proofs, each with
its **Fiat–Shamir** schedule check and its checked `TrustBoundary` turning the fingerprint match
into build-time obligations; the multi-action capture additionally carries the shape/VK
**faithfulness** checks and the adversarial **negative** fixtures.

### `Soundness/` — the soundness argument

The core argument that an accepting proof yields a witness or a computed break. The top-level
modules cover the argument end to end: `Main` (conditional soundness and the deployed-acceptance
route), `KnowledgeSoundness` (the `SnarkRelation` knowledge-soundness relation), `Constraints`
(Schwartz–Zippel soundness of the vanishing check) with `FoldSplit` (recovering the individual
constraints from the verifier's `y`-fold), `ConstraintRelations` (what the capstone's satisfaction
predicate buys the row-level results), and `GoodChallenge`/`ChallengePricing` (deriving the
good-challenge exclusions from challenge uniformity rather than assuming them). The
permutation/lookup stack is `GrandProduct` — the shared grand-product-to-multiset kernel —
with `RunningProduct` (telescoping the running product), `GrandProductBridge` (the two
Schwartz–Zippel steps from the verifier's evaluated check to the multiset identity),
`Permutation`, `PermutationConstruction`, `PermutationRows`, `Lookup`, and `LookupAssembly`.
The IPA stack is `InnerProduct`, `IpaSoundness`, `Extraction`, `Consistency`, `CommitFold`.
`Vesta` pins the abstract group to the actual Vesta curve, and `VestaBudget` restates its
capstone against a single joint accept floor. Five subtrees carry the heavier machinery:

- **`AGM/`** — the algebraic-group-model layer. It turns the relation coefficients computed
  from algebraic prover data (`Peel`, `Capstone`) into a discrete-log solution over the
  augmented basis `(g, U, W)` (`Adapter`, following Fuchsbauer–Kiltz–Loss), feeds the
  binding-signature relations in as AGM inputs (`BindingSignature`), adds the algebraic
  coefficients to the forking-certificate interfaces (`Prover`), and bounds the probability
  loss of the fixed-challenge-slot DL reduction (`Probability`, `ProbabilityCoins`,
  `ProbabilityVesta`).
- **`Forking/`** — the reusable Fiat–Shamir forking kernel: random-oracle primitives
  (`Oracle`), the deployed round ordering and rewinding (`Ordering`, `Rewind`), fork-tree
  existence and the forking-lemma probability bound (`Tree`, `Probability`), the closed form
  of that bound (`KnowledgeError`), the query-loss coupling between the coin draw and the
  multiopen challenge draw (`AdaptiveCoupling`), and the transcript assembly and extraction
  that turn forked transcripts into a deployed IPA tree (`Assembly`, `Extractor`).
  **`Forking/Adversary/`** builds the querying-adversary reduction on top: the `Q`-query
  adaptive adversary model (`OracleComp`), executable recursive forking from a finite tape
  (`Recursive`), the Fiat–Shamir-to-AGM handoff (`Algebraic`), oracle-domain reduction to
  finite support (`DomainReduction`), the adaptive interface and pre-IPA query accounting
  (`Adaptive`, `PreIpa`, `Provenance`), and the expected-run bookkeeping (`ExpectedRuns`,
  `ExpectedRunsPoly` — an unconditional polynomial bound remains open).
- **`Deployed/`** — the bridge from the clean, abstract soundness onto halo2's actual deployed
  IPA. It models the deployed IPA's `U`/`W` apparatus and peels it onto the clean recursive IPA
  (`Ipa`, `IpaPeel`), unfolds the flattened deployed MSM into the recursive generator fold
  (`Fold`), shows deployed acceptance implies halo2's explicit IPA verifier equation
  (`Verification`), reduces binding over the augmented generators to discrete-log-relation
  hardness (`Binding`), and reads the fork-tree knowledge error off the deployed Orchard
  parameters as a concrete number (`ConcreteBounds`, at recursion depth `k = 11`).
- **`Multiopen/`** — the multiopen argument's value binding. `Decode`/`DecodeFixture` and
  `Compat` recover the deployed multiopen structure; `RPoly` supplies the interpolation core
  (Mathlib's `Lagrange.interpolate`, plus the bridge to the deployed `foldl`); `Claimed`,
  `Opened`, `ValueCheck`, `ValueCheckDeployed`, and `NodeBinding` bind each decoded aggregate
  column to its claimed evaluation; `BudgetedExtraction` and `FloorBudget` re-prove the nested
  extraction from one joint accept floor over the four fresh challenges.
- **`Composition/`** — joining the two architecturally disjoint halves. `Bridge` identifies the
  algebraic forking extraction's clean opening with the deployed decoded capstone's opened
  commitment; `Decomposition` splits the knowledge-error bound unconditionally into the priced
  clean-opening failure plus a measured clean-but-not-extracted residual (`Residual`), with
  `Prefixes`, `Assembly`, and `Completeness` supplying the supporting pieces.

## Circuit layer — `Zcash/Circuits/`

A port of the Orchard Action circuit onto [Clean](https://github.com/Verified-zkEVM/clean)'s
Halo 2 formalization, with elliptic-curve arithmetic from
[CompElliptic](https://github.com/daira/CompElliptic). Each chip is ported from the actual Rust
(`orchard@0.14.0`, `halo2_gadgets-0.5.0`) rather than from memory, and the module docstrings cite
the source lines. Where the Sinsemilla incomplete-addition escapes can fire, the statements carry
them as data (`SpecOrBreak`) rather than assuming them away.

- **`Specs/`** — the value-level protocol specifications the circuits are proven against:
  Orchard data shapes (`Types`), the Pallas curve and its certified arithmetic (`Pallas`,
  `PallasCert`, `CompEllipticExtras`), bit-range arithmetic (`Bitrange`), and the Sinsemilla
  hash with its generators and break structure (`Sinsemilla`, `SinsemillaGenerators`,
  `SinsemillaBreak`).
- **`Utilities/`** — the shared gadgets: `LookupRangeCheck` (the first lookup-consuming gadget
  ported, generic over `K`), `RunningSum`/`DecomposeRunningSum`, `CondSwap`, and `AddChip`.
- **`Ecc/`** — the ECC chip. Point witnessing (`WitnessPoint`), complete and incomplete addition
  (`Add`, `AddIncomplete`), variable-base multiplication in its incomplete/complete/overflow
  phases (`Mul`, `MulIncomplete`, `MulIncompleteRound`, `MulComplete`, `MulOverflow`,
  `DoubleAndAdd`), and fixed-base multiplication (`MulFixed/`, with full-width, short, and
  base-field-element variants). **`MulFixed/Certs/`** holds the six deployed fixed bases with
  their window-table certificates, checked through `CertCheck`'s `ℕ`-literal evaluator.
- **`Sinsemilla/`** — the Sinsemilla chip: the `2^K` generator table (`Basic`), one hash piece
  and its rounds (`HashPiece`, `HashPieceRound`), the `⊥`-propagating chain (`Chain`,
  `HashToPoint`), the commit domain (`CommitDomain`), and the fixed-depth Merkle path (`Merkle`).
- **`Poseidon/`** — the Poseidon chip: the `pow5` S-box and round structure (`Pow5`, `Rounds`,
  `Constants`), the permutation (`Permute`), and the sponge/hash at `ConstantLength<2>` (`Hash`).
- **`NoteCommit/`** and **`CommitIvk/`** — the two commitment circuits, each as pieces and
  decompositions, the gate set, the canonicity checks, and the assembled `Main`/`MainBundle`
  contract at the extracted window scalar.
- **`Action/`** — the top-level Orchard Action circuit. `Circuit` is the ironwood `configure`
  and `synthesize` in exact region-creation order; `CircuitPreIronwood` is the post-NU 6.2
  circuit without the cross-address region (both share `configure`, hence all VK fixtures);
  `RealBases` instantiates everything at the actual deployed constants; the per-check modules
  are `ValueCommit`, `DeriveNullifier`, `SpendAuthority`, and `AddressIntegrity`; and `Bundle`
  is the end-to-end statement against protocol spec §4.17.4.
- **`Fixtures/`** and **`Tests/`** — the VK cross-check against Rust. `Fixtures/` reconstructs,
  purely and computably, the layout products a keygen-view dump pins (the ordered copy list, the
  permutation σ, the fixed assignments) from a circuit's `Operations`, with the dumps carried as
  JSON data files (`Json`); `Tests/` checks the ported `configure` equal to those dumps both pre-
  and post-`compress_selectors`.

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
  bridges that concrete development to the games' `KeyBindingInterface`, and `Probability`
  adds the whole-table random-oracle model that turns the counting facts into a probability
  bound.
- **`Ledger/`** — the ledger-model games. `Statement` transcribes the games-relevant conjuncts
  of an Orchard-shaped Action statement over abstract primitives — the interface the games
  consume — and `Model` is the witness-annotated ledger they quantify over, with `Effects`
  reading off the outputs, spends, and shielded-pool balance. The games themselves:
  `Balance` (every nonzero spend is a committed output of a strictly earlier transaction, or a
  Merkle/note-commitment break is computed), `Spendability` (the Faerie-Gold core — nullifiers
  pin note tuples — plus persistence), and `SpendAuthority` (an unsigned spend yields a
  signature forgery or a key-binding break). `Merkle` proves fixed-depth Merkle trees are
  position-binding up to an exhibited tree-hash collision.
