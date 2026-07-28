import Mathlib

/-!
# Nontrivial linear (discrete-log) relations, as computed data

Shared primitive for the reduction-style security arguments (breaks as computed data — see
`Zcash.Security.RandomOracle`): a nontrivial `F`-linear relation among a family of generators
`g : Fin n → G` together with two distinguished generators `U`, `W`, carried as *data* (the
coefficients) so a reduction can compute it rather than merely assert its existence. In a
prime-order group such a relation always *exists* propositionally, so an ∃-closed `Prop` would be
vacuous; the content is that a reduction produces one, discharged against discrete-log-relation
hardness at the computational layer.

Both crypto layers instantiate this: the binding-signature reduction
(`Zcash.Security.BindingSignature`) and the deployed-verifier soundness peel (`Zcash.Snark`).
Each use site documents its own reading of the generators.
-/

namespace Zcash

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- A nontrivial `F`-linear (discrete-log) relation among the generators `(g, U, W)`, as data:
coefficients `(a, α, β)` not all zero that the generators send to `0`. -/
structure NontrivialRelation {n : ℕ} (g : Fin n → G) (U W : G) where
  a : Fin n → F
  α : F
  β : F
  nontrivial : a ≠ 0 ∨ α ≠ 0 ∨ β ≠ 0
  relation : (∑ i, a i • g i) + α • U + β • W = 0

/-- The one-distinguished-generator variant: a nontrivial `F`-linear relation among the
family `g` and a single distinguished generator `U`.  This is the shape of a Sinsemilla
discrete-log break (protocol spec Theorem 5.4.4): a relation among the per-chunk generator
table and the domain point `Q`, produced as data by the escape reduction
(`Zcash.Security.Ledger.Bridge.relationOfBreakData`). -/
structure NontrivialRelationOne {n : ℕ} (g : Fin n → G) (U : G) where
  a : Fin n → F
  α : F
  nontrivial : a ≠ 0 ∨ α ≠ 0
  relation : (∑ i, a i • g i) + α • U = 0

end Zcash
