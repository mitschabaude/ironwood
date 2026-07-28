# The Clean boundary: architecture rule

Status: agreed by the maintainer (2026-07-24). This note is normative for how
Clean-originated concepts appear in the ironwood codebase; it exists so concurrent
workstreams converge on one structure instead of each growing local bridge plumbing.

## The principle

Ironwood is the host, Clean is a guest. Ironwood has its own first-class vocabulary —
`VerifyingKey`, `Expr`, `Shape`, its satisfaction notions, its polynomial environments —
and the guest must not scatter *its* vocabulary (`Halo2.ConstraintSystem`, `Operations`,
`Gate`, `Expression F Query`, `RichExpression`, …) through the host's rooms.

Everything Clean produces is funneled through **one concept: `TopLevelCircuit`**, which
carries everything downstream needs and is instantiated once per concrete circuit
(`actionCircuit`).

`TopLevelCircuit` is deliberately two-sided:

* It is a **Clean-native core concept** (it may well migrate into Clean itself —
  `TopLevelKeygen` already consumes only Clean and could follow). Its Clean-typed
  methods (`constraintSystem`, `operations`, `config`, …) are legitimate and public —
  *for the boundary implementation*.
* Ironwood defines an **ironwood-native interface on top of it**, and that interface is
  the only thing non-boundary ironwood code may consume. Its outputs are ironwood-typed;
  a reader never needs to know Clean exists to use it.

The canonical example of the pattern is

```
TopLevelCircuit.toVerifierKey : TopLevelCircuit → ProofParams → URS G → VerifyingKey …
```

— *the* core Clean concept bridged to a core ironwood concept in one method, with every
Clean internal invisible in the signature.

## The ironwood-native interface (target surface)

On `TopLevelCircuit`, defined ironwood-side in the designated boundary modules:

* `toVerifierKey (pp : ProofParams) (urs : URS G) : VerifyingKey (pp.mergeDerived top) …`
  — keygen, with the derived `Shape` in the return type (no lawfulness side condition).
* Shape/domain data as needed by consumers (`ProofParams.mergeDerived`, domain scalars).
* An `Expr`-typed pinned-constraint-system view (the boundary applies
  `RichExpression.toExpr` internally, exactly as `toVerifierKey` already does for the
  VK's `gates`).
* **A satisfaction contract in ironwood terms**: an ironwood-decoded assignment
  satisfying the circuit's derived key implies the circuit's public statement. The
  internal generic proof may pass through `top.Statement` over a reconstructed Clean
  environment, but that environment and the whole satisfaction-integration cluster
  are implementation details rather than a public seam.

## The rule (enforceable, greppable)

> Clean identifiers may appear only under `Zcash/Circuits/` and inside the designated
> boundary modules. Every other `Zcash/Snark/` (and `Common/`, `Security/`) signature
> mentions only `TopLevelCircuit` and ironwood types.

Review test: *would a reader of this file need to know Clean exists to understand it?
If yes and it is not a boundary module, it is misplaced.*

## Worked example of the anti-pattern

`Zcash/Common/ExprRich.lean`. `RichExpression` exists precisely because ripping
ironwood's `Expr` out of ironwood for Clean's use would have been rude in the other
direction — the type was deliberately duplicated so the clone stays on the guest's side
of the wall. Installing its conversion (`ofExpr`/`toExpr`/`eval_ofExpr`) in the host's
`Common/` un-quarantines it: it presents a Clean-side clone as a core ironwood concept.
(Contrast `Common/Expr.lean` in the same folder — ironwood's own shared AST — which is
exactly what `Common` is for.) The conversion belongs inside the boundary as private
plumbing; with an `Expr`-typed pinned view on the interface, nothing outside the
boundary mentions `RichExpression` at all.

## Current leak inventory (migration backlog)

1. `Zcash/Bridge/` — dissolves. It is imported *by* Snark modules, so it is not a layer,
   just a junk drawer: pasta domain scalars (`omegaOf`/`deltaFp`/`powFast`) →
   `Snark/Core`; `VerifyingKey.gates_eval_of_gates_eq` → restate as an interface lemma
   (its current hypothesis is spelled in `flatGates`/`substSelectorMap`/`queryWalkInit`
   — maximal leakage); Action keygen instances (`actionCS`, `actionOperations`,
   `actionSelMapDerived`, `actionK`) → superseded by `TopLevelCircuit` methods.
2. `Zcash/Snark/VkCommit/` → rename `Snark/Keygen/` (mirroring Clean's `Halo2/Keygen`,
   same concept on the group side); this is a designated boundary module family.
   `Fast/ParMap` (fully generic) → `Common/`. `Common/ExprRich` → into the boundary.
3. `Snark/Fixtures/SingleAction/{PinnedCsMatch,VkMatch}` — restate over the interface
   (`Certificate.lean` already demonstrates the style: it speaks only `vk`,
   `derivedActionVk`, and `TopLevelCircuit` methods).
4. The cross-language satisfaction seam (`Operation*`, `TopLevel*`, `Resolver*`,
   the Clean-facing part of `PolynomialEnvironment`, coherence files, …) moves under
   `Zcash/Circuits/Integration/`, capped by the interface satisfaction theorem. Clean
   types are allowed inside this directory and remain invisible above it. Pure
   verifier-native modules such as `CanonicalConstraintModel` do not move with the seam.
5. Cross-repo: `Circuits/Fixtures/Layout.lean`'s keygen semantics (`V1.copyList`,
   `runAssembly`, fixed contents) → Clean `Halo2/Keygen`; and eventually
   `Circuits/TopLevel{,Keygen}.lean` themselves → Clean core.

Sequencing: items 1–3 are mechanical and ironwood-local; 4 wants co-design with the
circuit-soundness workstream (the satisfaction-contract shape); 5 rides the next Clean
pin cycle. Module renames should land as a dedicated cleanup commit, coordinated, not
mid-workstream.

## Review addendum: drawing the boundary precisely

The directory boundary is a dependency boundary, not merely a collection of files
created during the circuit-integration work.

### What stays verifier-native

The following concepts speak only the ironwood verifier's language and remain under
`Zcash/Snark/Soundness/`:

* `ConstraintSatisfaction` and `ConstraintPolyModel`;
* `CanonicalConstraintModel` and the canonical domain-selector mathematics;
* permutation and lookup instantiation and semantics;
* the decoded multiopen constraint resolver.

In particular, `CanonicalConstraintModel` takes a `VerifyingKey`, challenges, and an
ironwood `CommitmentId → Polynomial` resolver and produces an ironwood
`ConstraintPolyModel`. It does not know about a Clean circuit and is an input to the
boundary, not part of its implementation.

Some existing files need splitting rather than moving wholesale. For example,
`PolynomialEnvironment` currently contains both the verifier-native interpolation
construction (`rowPolynomial` and its algebraic facts) and the Clean-facing constructor
of a `Halo2.Environment`. The former stays in `Snark/Soundness`; only the latter moves
into `Circuits/Integration`.

### What lives in `Zcash/Circuits/Integration`

This directory contains the implementation that is forced to understand both sides:

* extracting the gate, copy, lookup, and fixed-data obligations of Clean operations;
* interpreting ironwood resolver polynomials as a placed Clean environment;
* connecting selector compression and query layouts to Clean gate evaluation;
* reassembling those families as Clean's authoritative `Halo2.Constraints`;
* applying `TopLevelCircuit.soundness`;
* specializing the generic result to a concrete circuit statement such as Orchard
  Action.

Pure Clean compiler semantics should instead live in `Zcash/Circuits/` or, preferably
when reusable, upstream in Clean itself. Pure ironwood soundness stays in
`Zcash/Snark/Soundness/`.

### Deployed specializations stay with soundness

A theorem that relies on the large captured VK artifacts—`Fixture.shape`,
`Fixture.vk`, `capturedURS`, or the certificate equating those values with
circuit-derived keygen output—belongs under `Zcash/Snark/Soundness/Deployed/`, not in
this directory. Such a theorem may import the boundary's public circuit-derived
terminal, but it should not re-establish Clean semantics itself. Conversely,
`Circuits/Integration` should not import the fixture dumps merely to advertise the
final deployed capstone.

### The public satisfaction contract has two levels

`TopLevelCircuit` declares a `PublicInput` type and an injective layout of its encoded
elements in instance cells. That one layout derives both extraction from a Clean
environment and the cell/value assignments consumed by verifier integration. The
top-level circuit separately extracts a private witness, recombines public and private
data into its formal-circuit witness, and proves that this factorization agrees with
the formal circuit's native extractor. Its `Spec` receives public and private data
explicitly; only `Statement public` existentially hides the private witness.

The boundary therefore exposes two theorem levels:

1. a boundary-internal generic theorem taking satisfaction of the circuit-derived key
   to `top.Statement` at the public input extracted through the declared layout;
2. a public theorem phrased only in ironwood-decoded data and the concrete circuit's
   public statement, for example the structured Orchard Action public inputs.

No caller of the public theorem should construct a Clean environment or mention
`Operations`, `ConstraintSystem`, selector compression, placement, or
`RichExpression`.

### Consequence of circuit-derived key generation

For `vk := top.toVerifierKey pp urs`, the gate and lookup expressions, query layouts,
shape counts, domain parameters, permutation chunks, and commitment families are
outputs of the same circuit-owned keygen pipeline. Their correspondence must not be
reintroduced as an arbitrary caller-supplied coherence record.

The current `TopLevelGateCoherence` is useful scaffolding while the adapter is being
built, but it should not survive as part of the public interface. Its definitional
fields should be discharged directly from `toVerifierKey`; genuine semantic facts
such as selector allocation, supported domain size, and degree bounds remain internal
circuit/compiler obligations. Gate well-formedness is already intrinsic to `Gate`.
The remaining facts should be derived or packaged once inside the boundary rather
than supplied beside every soundness call.
