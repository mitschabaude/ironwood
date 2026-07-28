import Zcash.Common.Expr
import Clean.Halo2.Keygen.RichExpression

/-!
# The verifier `Expr` ↔ pinned `RichExpression` boundary

The verifier keeps its own gate AST `Zcash.Snark.Expr` (`Zcash/Common/Expr.lean`), while
the pinned-constraint-system derivation in Clean core speaks `Halo2.RichExpression`
(`Clean.Halo2.Keygen.RichExpression`). The two types have identical constructor names and
semantics on the shared node set; `RichExpression` merely carries one extra node — a
pre-compression `selector` — that never survives selector compression and therefore never
appears in a verifier gate.

The canonical conversion is `Expr → RichExpression` (`RichExpression.ofExpr`): it is total
and value-preserving with no invented leaves, because every `Expr` constructor is a
`RichExpression` constructor. Evaluation is preserved unconditionally
(`RichExpression.eval_ofExpr`), so verifier-side gate evaluations transport into the pinned
derivation's `RichExpression.eval` semantics (and back) at the VK boundary.
-/

namespace Halo2

/-- Carry a verifier `Expr` into the pinned `RichExpression`, constructor by constructor.
Total: `Expr` has no `selector` node, so no leaf is invented. -/
def RichExpression.ofExpr {F : Type} : Zcash.Snark.Expr F → RichExpression F
  | .constant c => .constant c
  | .fixed i => .fixed i
  | .advice i => .advice i
  | .instance i => .instance i
  | .negated e => .negated (RichExpression.ofExpr e)
  | .sum a b => .sum (RichExpression.ofExpr a) (RichExpression.ofExpr b)
  | .product a b => .product (RichExpression.ofExpr a) (RichExpression.ofExpr b)
  | .scaled e c => .scaled (RichExpression.ofExpr e) c

/-- **Evaluation is preserved.** The pinned expression `RichExpression.ofExpr e` evaluates
exactly as the verifier `Expr` `e` does — no selector-freeness side condition, since
`ofExpr` introduces no `selector` node. -/
@[simp] theorem RichExpression.eval_ofExpr {F : Type} [CommRing F]
    (fE aE iE : ℕ → F) (e : Zcash.Snark.Expr F) :
    (RichExpression.ofExpr e).eval fE aE iE = e.eval fE aE iE := by
  induction e <;>
    simp_all only [RichExpression.ofExpr, RichExpression.eval, Zcash.Snark.Expr.eval]

/-- Carry a pinned `RichExpression` back to the verifier `Expr`, constructor by
constructor. Total in the other direction only up to the extra `selector` node, which
maps to junk (`.constant 0`): post-compression gate/lookup expressions are selector-free
(`compress_selectors` substitutes every simple selector by a fixed-column polynomial), so
the `.selector` arm is never reached on the expressions a derived verifying key carries.
Used to spell a derived VK's gate/lookup fields directly in `Expr` space; the exact
round-trip is `RichExpression.toExpr_ofExpr`. -/
def RichExpression.toExpr {F : Type} [Zero F] : RichExpression F → Zcash.Snark.Expr F
  | .constant c => .constant c
  | .fixed i => .fixed i
  | .advice i => .advice i
  | .instance i => .instance i
  | .selector _ => .constant 0
  | .negated e => .negated (RichExpression.toExpr e)
  | .sum a b => .sum (RichExpression.toExpr a) (RichExpression.toExpr b)
  | .product a b => .product (RichExpression.toExpr a) (RichExpression.toExpr b)
  | .scaled e c => .scaled (RichExpression.toExpr e) c

/-- Converting a pinned expression to the verifier AST preserves evaluation.

The pre-compression `selector` fallback is harmless here: both
`RichExpression.eval` and the converted verifier constant evaluate it as zero.
Post-compression verifying-key expressions do not contain this node in any case. -/
@[simp] theorem RichExpression.eval_toExpr {F : Type} [CommRing F]
    (fE aE iE : ℕ → F) (e : RichExpression F) :
    (RichExpression.toExpr e).eval fE aE iE =
      e.eval fE aE iE := by
  induction e <;>
    simp_all only [RichExpression.toExpr, RichExpression.eval,
      Zcash.Snark.Expr.eval]

/-- **`toExpr` inverts `ofExpr`.** Since `ofExpr` never emits a `selector` node, carrying a
verifier `Expr` into `RichExpression` and back is the identity — the junk `.selector` arm of
`toExpr` is unreachable on `ofExpr` images. This closes the `Expr`/`RichExpression` boundary
for the verifying key's gate and lookup fields. -/
@[simp] theorem RichExpression.toExpr_ofExpr {F : Type} [Zero F] (e : Zcash.Snark.Expr F) :
    RichExpression.toExpr (RichExpression.ofExpr e) = e := by
  induction e <;>
    simp_all only [RichExpression.ofExpr, RichExpression.toExpr]

end Halo2
