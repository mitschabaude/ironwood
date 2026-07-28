import Mathlib
import CompElliptic.Fields.Pasta

/-!
# The verifier's scalar field `F_p`

Orchard commitments are Vesta points; challenges and evaluations use Vesta's scalar field `F_p`.
For the Pasta curves, this is `pallas::Base = ZMod PALLAS_BASE_CARD`.

Most proofs remain generic over `[Field F]`. This module fixes the deployed field and proves its
cardinality, which appears in the Schwartz–Zippel bounds. `Soundness.Vesta` proves the Vesta group
order separately.
-/

namespace Zcash.Arithmetic

/-- The Vesta scalar-field order, equal to the Pallas base-field order. -/
@[reducible] def scalarFieldOrder : ℕ := CompElliptic.Fields.Pasta.PALLAS_BASE_CARD

/-- The verifier's scalar field `F_p = ZMod p`. -/
abbrev Fp := ZMod scalarFieldOrder

instance : Fact (Nat.Prime scalarFieldOrder) :=
  inferInstanceAs (Fact (Nat.Prime CompElliptic.Fields.Pasta.PALLAS_BASE_CARD))

instance : NeZero scalarFieldOrder :=
  ⟨(Fact.out : Nat.Prime scalarFieldOrder).pos.ne'⟩

/-- `F_p` is finite of cardinality `p` — the quantity the Schwartz–Zippel soundness bound divides by. -/
theorem card_Fp : Fintype.card Fp = scalarFieldOrder :=
  ZMod.card scalarFieldOrder

end Zcash.Arithmetic
