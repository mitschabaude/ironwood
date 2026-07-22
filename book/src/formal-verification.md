# Formal Verification

Ironwood's formal verification is a Lean 4 development (over Mathlib) in this repository:
verifier soundness for the deployed Halo 2 verifier under `Zcash/Snark/`, and the protocol
security-property layers (binding-signature balance, key binding, and the ledger-model
security games) under `Zcash/Security/`. This page documents two development-wide
conventions: how security breaks are represented, and what the development is allowed to
trust.

## Breaks as computed data

The security arguments are reduction-style: a theorem shows that a violation of a protocol
property *exhibits* a concrete break of an underlying primitive — a discrete-log relation, a
hash collision, a commitment-opening collision. Hardness assumptions are consumed only at
the computational layer, against the exhibited break.

Care is needed in how "exhibits" is stated. In a prime-order group, a nontrivial
discrete-log relation between any two elements always *exists*; for any compressing hash,
collisions always *exist* by pigeonhole. So a `Prop` that existentially quantifies over the
break data ("there exist distinct inputs with equal outputs") is simply *true* at every
instantiation of interest. A theorem concluding `property ∨ ∃-break` is then vacuous, and a
hypothesis `¬ ∃-break` is unsatisfiable. Proof irrelevance makes this unrecoverable: even
when a proof constructs the break honestly, a consumer of the statement cannot extract it.

The convention:

* **Break events are structures carrying the breaking data** (the colliding queries, the
  relation coefficients), with `Prop` certificates attached. Examples:
  `RandomOracle.Collision` and `RandomOracle.CollisionUpToSign` (the ±-collision shape produced by
  coordinate-extractor arguments — and the Merkle tree-hash collision computed by `Merkle.collisionOfWrongLeaf` is a `Collision` directly), `Ledger.NoteCommitBreak`, and
  `BindingSignature.NontrivialRelation` (the discrete-log relation computed from a
  non-balancing verifying bundle).
* **Reductions are plain computable `def`s** producing them, such as
  `Merkle.collisionOfWrongLeaf`, `noteCommitBreakOfNe`, and the
  `NontrivialRelation.ofImbalance` family (through to the per-pool Orchard and Sapling
  bundle capstones, whose balance statements are the contrapositives under discrete-log
  relation hardness). A structure with data fields
  cannot be inhabited by proof-irrelevant existence, and a plain `def` cannot conjure the
  data from mere existence via choice — the compiler enforces this, so `noncomputable` is
  not permitted for these definitions.
* Efficiency of a reduction is the one property Lean cannot express; it is established by
  inspection. The constructions here are straight-line manipulations of their inputs.
* Predicates over *named* witnesses (for example, a key-binding break of two specific
  witnesses) keep their content as `Prop`s: the breaking pair is bound in the statement
  rather than existentially closed.

The principle's scope is **computational reductions**: it applies wherever the argument is
that an efficient adversary achieving some effect would thereby violate a computational
assumption. For that argument to have content, the reduction must be the kind of object an
adversary's output can be fed through — a computable function producing the break the
assumption forbids. It is not a constructivism requirement on the development at large.
`Classical.choice` is used throughout Mathlib and throughout the `Prop`-valued reasoning
here, and Lean is not intended to support purely constructive proofs. The point is that
choice must not be what *produces the break data*: a `noncomputable` reduction could
satisfy its type by using classical choice to "find" the break, proving nothing about
efficient adversaries. Ordinary theorems, and the `Prop` certificate fields inside break
structures, remain freely classical.

## Trust discipline

Following the pattern of CompElliptic's
[trust discipline](https://github.com/daira/CompElliptic#trust-discipline), the development
distinguishes general theorems from concrete, closed computational facts, and holds them to
different trust standards.

**General, quantified theorems** (the soundness statements and security reductions) rest, in
their abstract form over an arbitrary `Fp`-module, only on the standard classical axioms
`propext`, `Classical.choice`, and `Quot.sound` — no `sorry`, no additional axioms, no compiler
trust. Instantiated at the concrete Vesta curve they additionally inherit one compiler-trust
axiom: CompElliptic's curve point-count, a closed computational fact discharged by `native_decide`
(below). The per-theorem `#print axioms` pins record exactly which endpoints carry it.

**Concrete, closed facts with no free variables** may additionally use `native_decide`
(which discharges a goal by running compiled native code, adding a compiler-trust axiom) and
the kernel's GMP-backed bignum arithmetic. The principal such fact in this repository is the
captured fingerprint match `fingerprint_matches`: a single numeric check that the Lean
verifier's assembled multi-scalar multiplication equals the Rust verifier's on a captured
proof. The CompElliptic dependency applies the same discipline to its concrete
curve-arithmetic facts (cardinalities, primality certificates). Such facts are independently
re-checkable (another implementation, or hand computation, would compute the same result),
so a miscompiled or buggy oracle could in principle be caught by disagreement.

These boundaries are *checked at build time*, not merely documented:

* `Zcash.Snark.Fingerprint.TrustBoundary` pins the fingerprint match: `assert_no_sorry`
  walks the elaborated dependency graph, so a `sorry` hidden in any transitive dependency
  fails the build; and a `#guard_msgs`-pinned `#print axioms` freezes the exact axiom set,
  so a newly introduced axiom fails the build. The pin also documents precisely *which*
  compiler-trust axiom `native_decide` adds — on this toolchain a per-declaration axiom
  (`…_native.native_decide.ax_1_1`), where older Lean versions used the global
  `Lean.ofReduceBool`. Pinning it keeps that claim verified rather than remembered, which
  is the point of the discipline: unpinned claims about the trusted base drift silently as
  toolchains change.
* `Zcash.Snark.Soundness.AGM.TrustBoundary`, `Zcash.Snark.Soundness.TrustBoundary`, and
  `Zcash.Snark.Soundness.Deployed.TrustBoundary` pin the AGM/Fiat–Shamir soundness stack —
  the executable forking extractor, the knowledge-soundness and binding endpoints across
  all adversary models, and the DL capstones — with the same `assert_no_sorry` +
  guarded-`#print axioms` discipline.
* `Zcash.Security.Ledger.TrustBoundary` and
  `Zcash.Security.BindingSignature.TrustBoundary` pin the break reductions the same way.
  The ledger reductions rest on `propext` and `Quot.sound` only; the binding-signature
  relation reductions additionally record `Classical.choice`, entering only through erased
  `Prop` certificate fields — in both cases the definitions compile as plain `def`s, so the
  break data cannot have been conjured from mere propositional existence.
* CI builds both as part of the default targets, and `fingerprint_matches`'s
  `native_decide` compiles and runs the verifier, so anything `noncomputable` on the
  assembled-verifier path fails the build.

Coined terms and shorthand for the development, including the two conventions above, are
collected in the [glossary](formal-verification/glossary.md).
