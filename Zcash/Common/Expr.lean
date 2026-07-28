import Mathlib

/-!
# The verifier's gate-polynomial AST

`Expr` is the gate (or lookup input/table) polynomial exactly as halo2 evaluates it
during verification (`Expression::evaluate`), with queries as indices into the claimed
evaluations. It lives in `Zcash/Common` as a shared leaf: the verifier stack
(`Zcash.Snark.Verifier`) evaluates VK gates with it, and the circuit-side VK-match
projection (`Zcash.Circuits.Fixtures`) produces it — keeping the two subtrees
import-clean of each other. The namespace stays `Zcash.Snark`, where the type
originated and where all existing call sites address it.
-/

namespace Zcash.Snark

/-- A gate (or lookup input/table) polynomial as halo2 evaluates it during verification
(`Expression::evaluate`): a constant, a fixed/advice/instance query (by query index into the claimed
evals), or a negation / sum / product / scaling. Virtual selectors are removed during circuit
optimization, so they never appear here. -/
inductive Expr (F : Type*) where
  | constant : F → Expr F
  | fixed : ℕ → Expr F
  | advice : ℕ → Expr F
  | instance : ℕ → Expr F
  | negated : Expr F → Expr F
  | sum : Expr F → Expr F → Expr F
  | product : Expr F → Expr F → Expr F
  | scaled : Expr F → F → Expr F
deriving DecidableEq, Repr

/-- Carry a gate expression along a ring hom, leaf by leaf. -/
def Expr.map {F G : Type*} (f : F → G) : Expr F → Expr G
  | .constant c => .constant (f c)
  | .fixed i => .fixed i
  | .advice i => .advice i
  | .instance i => .instance i
  | .negated e => .negated (e.map f)
  | .sum a b => .sum (a.map f) (b.map f)
  | .product a b => .product (a.map f) (b.map f)
  | .scaled e c => .scaled (e.map f) (f c)

/-- Mapping an expression twice is mapping once along the composite. -/
theorem Expr.map_map {F G H : Type*} (f : F → G) (g : G → H) (e : Expr F) :
    (e.map f).map g = e.map (fun c => g (f c)) := by
  induction e <;> simp_all [Expr.map]

/-- Mapping an expression along the identity leaves it unchanged. -/
@[simp] theorem Expr.map_id {F : Type*} (e : Expr F) : (e.map fun c => c) = e := by
  induction e <;> simp_all [Expr.map]

/-- Evaluate a gate polynomial at the claimed evaluations (halo2 `Expression::evaluate` with the
verifier's closures): queries resolve to `fixedEvals`/`adviceEvals`/`instanceEvals` at their index. -/
def Expr.eval {F : Type*} [CommRing F] (fixedEvals adviceEvals instanceEvals : ℕ → F) :
    Expr F → F
  | .constant c => c
  | .fixed i => fixedEvals i
  | .advice i => adviceEvals i
  | .instance i => instanceEvals i
  | .negated a => -(a.eval fixedEvals adviceEvals instanceEvals)
  | .sum a b => a.eval fixedEvals adviceEvals instanceEvals + b.eval fixedEvals adviceEvals instanceEvals
  | .product a b =>
      a.eval fixedEvals adviceEvals instanceEvals * b.eval fixedEvals adviceEvals instanceEvals
  | .scaled a c => a.eval fixedEvals adviceEvals instanceEvals * c

end Zcash.Snark
