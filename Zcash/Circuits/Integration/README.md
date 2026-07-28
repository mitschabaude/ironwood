# Clean-to-Ironwood integration boundary

This directory is the designated implementation boundary between Clean formal
circuits and ironwood's verifier and soundness development.

Modules here may import and reason about both vocabularies. Their job is to translate
a closed `TopLevelCircuit` and its circuit-derived keygen data into ironwood-native
interfaces:

* an ironwood `VerifyingKey` and pinned constraint view;
* reconstruction of Clean operation satisfaction from ironwood polynomial
  satisfaction;
* semantic projection of configured lookup tuples into the verifier's
  query-index expression language;
* a final circuit statement expressed without exposing Clean implementation details
  to verifier or soundness callers.

This directory is not a home for generally useful code merely because that code was
written during circuit integration:

* pure verifier algebra, decoded constraint models, permutation/lookup semantics, and
  challenge arguments remain under `Zcash/Snark/`;
* pure circuit definitions and semantics remain under `Zcash/Circuits/`, and reusable
  Halo2 compiler facts should migrate upstream to Clean;
* only code that genuinely translates between the two sides belongs here.

The normative architecture rule and current migration guidance are in
[`clean-boundary.md`](clean-boundary.md). The next compiler-lawfulness arc is
specified in
[`lawfulness-and-certificate-elimination.md`](lawfulness-and-certificate-elimination.md):
it inventories the Action-specific computational certificates and the correctness
obligations currently hidden by synthesis closure, then proposes the local laws and
generic compiler proofs that should replace them.

The lookup bridge is split deliberately:

* `LookupProjection.lean` proves the query-erasure and selector-substitution
  compiler semantics for configured lookups;
* `LookupSelectorRows.lean` derives exact expression-level selector projection from
  singleton packed-selector cells and the shared fixed-row realization boundary;
  `ActionLookupSelectorRows.lean` merely instantiates that generic boundary with
  Action's fixed coherence;
* `TopLevelLookups.lean` routes synthesis-enabled lookups through the
  circuit-derived verifying key, derives selector coverage, table freedom, tuple
  arity, and activation-row fit from Clean's top-level keygen invariants, reduces
  the remaining projection boundary to exact packed-selector values, packages the
  bundle-wide `β`/`γ`/`θ` exclusions into the per-proof witness conditions, and
  constructs the deployed witnesses consumed by the generic full-circuit bridge.
* `TopLevelBridge.lean` is the generic join: it derives gate and lookup families
  from the canonical circuit-owned constraint model and combines them with the
  fixed/table and copy-replay streams into `FullCircuitBridge`.
* `TopLevelCorrectness.lean` is the interface exported to core soundness. It
  packages the named gate, fixed/selector, copy, and lookup representation facts
  for one canonical assignment, but contains neither the desired circuit statement
  nor an opaque encoding implication.
* `TopLevelInstanceCommitment.lean` derives the verifier's instance commitments
  from any top-level circuit's public-input layout and binds accepted instance
  polynomials back to the supplied public inputs, for arbitrary column and proof
  counts.
* `TopLevelAcceptedModel.lean` composes canonical circuit satisfaction, generic
  circuit correctness, and public-instance binding into the circuit's statements.
* `ActionCorrectness.lean` contains only the genuinely Action-specific
  construction of `TopLevelCircuitCorrectness`.
* `ActionTerminal.lean` retains the accepted-node-binding specialization. It
  specializes the verifier-native decoded-model terminal to the circuit-derived
  Action verification key and produces `Action.BundleStatement` or a computed
  augmented-basis relation. No Clean type is introduced into
  `Zcash/Snark/Soundness/Canonical/Terminal.lean`.

The core terminals live outside this boundary. `Snark/Soundness/TopLevelTerminal`
turns canonical constraint satisfaction plus `TopLevelCircuitCorrectness` into the
circuit-owned statement for every proof. `Snark/Soundness/TopLevelVesta` composes
that result with the verifier-native Vesta terminal for an arbitrary
`TopLevelCircuit`. `Snark/Soundness/ActionVesta` supplies only the Action
correctness constructor to that generic capstone, while
`Snark/Soundness/Deployed/ActionVesta` only transports captured artifacts. None of
these public capstones has a free semantic proposition, encoding callback, decoder,
or column-feed choice.
