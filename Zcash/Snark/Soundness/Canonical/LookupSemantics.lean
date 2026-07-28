import Zcash.Snark.Soundness.Canonical.LookupInstantiation
import Zcash.Snark.Soundness.GoodChallenge
import Zcash.Snark.Soundness.Canonical.DomainSelectors

/-!
# Semantic endpoint for resolver-backed lookup constraints

`LookupInstantiation` extracts the five polynomial divisibility facts for a selected lookup from
full constraint satisfaction.  This file joins those facts to the evaluation-domain and
good-challenge premises of `deployed_lookup_subset_of_nonzero_challenges`, producing the scalar
row-membership theorem consumed by the operation-level tuple bridge.
-/

namespace Zcash.Snark

open Polynomial Finset
open scoped ENNReal

set_option maxHeartbeats 20000

/-- Evaluation-domain facts shared by every resolver-backed lookup in one circuit. -/
structure ResolverLookupDomain
    {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G)
    (l0 lLast lBlind : Polynomial Fp) (n u : ℕ) : Prop where
  omegaNonzero : vk.omega ≠ 0
  root : vk.omega ^ n = 1
  active : ∀ i < u + 1,
    1 - (lLast.eval (vk.omega ^ i) + lBlind.eval (vk.omega ^ i)) ≠ 0
  firstSelector : l0.eval (vk.omega ^ 0) ≠ 0
  lastSelector : lLast.eval (vk.omega ^ (u + 1)) ≠ 0

/--
Build the lookup-domain record with the canonical first, last-usable, and
blinding-row selectors. The selector evaluations are independent of the lookup
and of the circuit being instantiated.
-/
theorem ResolverLookupDomain.ofCanonicalSelectors
    {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G) {n u : ℕ}
    (hlast : u + 1 < n)
    (hrows : Function.Injective fun i : Fin n => vk.omega ^ (i : ℕ))
    (homega : vk.omega ≠ 0)
    (hroot : vk.omega ^ n = 1) :
    ResolverLookupDomain vk
      (rowSelectorPolynomial vk.omega ⟨0, lt_trans (Nat.zero_lt_succ u) hlast⟩)
      (rowSelectorPolynomial vk.omega ⟨u + 1, hlast⟩)
      (blindSelectorPolynomial vk.omega ⟨u + 1, hlast⟩) n u where
  omegaNonzero := homega
  root := hroot
  active i hi := by
    exact last_add_blind_active ⟨u + 1, hlast⟩
      ⟨i, lt_trans hi hlast⟩ hi hrows
  firstSelector :=
    firstSelectorPolynomial_nonzero
      ⟨0, lt_trans (Nat.zero_lt_succ u) hlast⟩ rfl hrows
  lastSelector :=
    lastSelectorPolynomial_nonzero ⟨u + 1, hlast⟩ hrows

/-- The product-difference polynomial whose roots are excluded at the selected lookup's `γ`
squeeze.  It is fixed after `β`. -/
noncomputable def resolverLookupProductDifference
    {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → Polynomial Fp)
    (p : Fin shape.numProofs) (l : Fin shape.numLookups) (u : ℕ) :
    Polynomial (Polynomial Fp) :=
  lookupProdDiff
    (Finset.univ.val.map
      (lookupColumnRows vk.omega (poly (.lookupPermInput p l)) (u + 1)))
    (Finset.univ.val.map
      (lookupColumnRows vk.omega (poly (.lookupPermTable p l)) (u + 1)))
    (Finset.univ.val.map
      (lookupColumnRows vk.omega
        (lookupInputPolyOfResolver vk ch poly p l) (u + 1)))
    (Finset.univ.val.map
      (lookupColumnRows vk.omega
        (lookupTablePolyOfResolver vk ch poly p l) (u + 1)))

/-- All separately priced challenges used by the selected lookup endpoint, including the two
row-factor exclusions that eliminate its residual zero-product branch. -/
structure ResolverLookupGoodChallenges
    {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → Polynomial Fp)
    (p : Fin shape.numProofs) (l : Fin shape.numLookups) (u : ℕ) : Prop where
  gamma : ch.gamma ∉ szBadSet
    ((resolverLookupProductDifference vk ch poly p l u).map (evalRingHom ch.beta))
  beta : ∀ j, ch.beta ∉ szBadSet
    ((resolverLookupProductDifference vk ch poly p l u).coeff j)
  inputNonzero : ch.beta ∉ lookupColumnZeroBadSet vk.omega
    (lookupInputPolyOfResolver vk ch poly p l) (u + 1)
  tableNonzero : ch.gamma ∉ lookupColumnZeroBadSet vk.omega
    (lookupTablePolyOfResolver vk ch poly p l) (u + 1)

/-- Resolver-backed full constraint satisfaction enforces scalar membership for every usable row
of a selected compressed lookup.  Tuple recovery is intentionally downstream: it uses the Clean
operation's concrete input/table tuples and the separately priced `θ` collision exclusion. -/
theorem ConstraintSatisfaction.resolverLookupSubset
    {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → Polynomial Fp)
    (sets : Fin shape.numProofs → List (PermSetEval (Polynomial Fp)))
    (chunks : Fin shape.numProofs →
      List (PermSetEval (Polynomial Fp) × List (Polynomial Fp × Polynomial Fp)))
    (l0 lLast lBlind : Polynomial Fp)
    (p : Fin shape.numProofs) (l : Fin shape.numLookups) {n u : ℕ}
    (h : ConstraintSatisfaction
      (constraintModelOfResolver vk ch poly sets chunks l0 lLast lBlind) n)
    (hdom : ResolverLookupDomain vk l0 lLast lBlind n u)
    (hgood : ResolverLookupGoodChallenges vk ch poly p l u) :
    ∀ i : Fin (u + 1), ∃ j : Fin (u + 1),
      lookupColumnRows vk.omega
          (lookupInputPolyOfResolver vk ch poly p l) (u + 1) i =
        lookupColumnRows vk.omega
          (lookupTablePolyOfResolver vk ch poly p l) (u + 1) j := by
  have hdvd := h.lookupConstraintsDvdOfResolver
    vk ch poly sets chunks l0 lLast lBlind p l
  apply deployed_lookup_subset_of_nonzero_challenges
    vk.omega ch.beta ch.gamma
    (poly (.lookupProduct p l))
    (poly (.lookupPermInput p l))
    (poly (.lookupPermTable p l))
    (lookupInputPolyOfResolver vk ch poly p l)
    (lookupTablePolyOfResolver vk ch poly p l)
    l0 lLast lBlind hdvd hdom.omegaNonzero
  · intro i
    rw [← pow_mul, Nat.mul_comm, pow_mul, hdom.root, one_pow]
  · exact hdom.active
  · exact hdom.firstSelector
  · exact hdom.lastSelector
  · simpa [resolverLookupProductDifference] using hgood.gamma
  · simpa [resolverLookupProductDifference] using hgood.beta
  · exact hgood.inputNonzero
  · exact hgood.tableNonzero

end Zcash.Snark
