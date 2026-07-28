import Mathlib

/-!
# Sequencing a computed break branch

Reductions that follow the breaks-as-computed-data discipline (see
`Zcash.Security.RandomOracle`) conclude `A ⊕' R`: the intended result, *or* the break as data.
Unlike `A ∨ R`, that shape cannot be case-split classically — a `PSum` must be produced, not
merely shown to be inhabited — so composing such reductions needs explicit combinators. Two
suffice for the circuit-integration stack:

* `bindOrRelationWitness` sequences one reduction into a continuation, carrying an explicit
  break through unchanged. It replaces the `by_cases hbad : Bad` idiom, which decided the break
  branch classically and then discharged several results against `¬ Bad`.
* `finForallOrRelationWitness` and `listForallOrRelationWitness` commute a family of reductions
  past `∀`: traversing left to right, they return every result or the *first* break as data. With
  `∨` this commutation was free classically; with data it is a search, and these are the searches.

**Interim file.** `Zcash/Snark/Soundness/AGM/{DeployedPinnedRoots,DeployedConstraintSupply}.lean`
on `main` already define `finForallOrRelationWitness` and `bindOrRelationWitness` under these
names. This file exists so the circuit-integration stack can adopt the discipline before that
work is merged; delete it at the merge. One difference to reconcile there: `main`'s
`finForallOrRelationWitness` fixes `A : Fin n → Type*`, which does not cover the Prop-valued
clean sides in this stack (column encodings, constraint families, evaluation equalities), so the
version below is generalised to `Sort`. Generalising `main`'s in place is the intended
resolution — it subsumes the narrower signature and needs no change at its use sites.
-/

namespace Zcash.Snark

universe u v w

/-- Preserve an explicit break branch while sequencing a successful result. -/
def bindOrRelationWitness {A : Sort u} {B : Sort v} {R : Sort w}
    (outcome : A ⊕' R) (next : A → B) : B ⊕' R :=
  match outcome with
  | PSum.inl value => PSum.inl (next value)
  | PSum.inr relation => PSum.inr relation

/-- Traverse a `Fin`-indexed family of computed outcomes left to right: every left-hand value, or
the first right-hand value as data — no existential search. -/
def finForallOrRelationWitness {n : ℕ} {A : Fin n → Sort v} {R : Sort w}
    (outcome : ∀ i, A i ⊕' R) : (∀ i, A i) ⊕' R := by
  induction n with
  | zero => exact PSum.inl fun i => Fin.elim0 i
  | succ n ih =>
      cases hhead : outcome 0 with
      | inr relation => exact PSum.inr relation
      | inl head =>
          cases htail : ih (fun i => outcome i.succ) with
          | inr relation => exact PSum.inr relation
          | inl tail => exact PSum.inl (Fin.cases head tail)

/-- The bounded-`ℕ` analogue of `finForallOrRelationWitness`. Column and row families in the
compiled constraint system are indexed by a natural number under a bound rather than by `Fin n`,
so this is the shape their folds actually have. -/
def boundedForallOrRelationWitness {n : ℕ} {A : ℕ → Sort v} {R : Sort w}
    (outcome : ∀ i, i < n → A i ⊕' R) : (∀ i, i < n → A i) ⊕' R :=
  bindOrRelationWitness
    (finForallOrRelationWitness (A := fun i : Fin n => A i.val)
      fun i => outcome i.val i.isLt)
    fun h i hi => h ⟨i, hi⟩

/-- The `List` membership analogue of `finForallOrRelationWitness`: the outcomes for every member
of `l`, or the first break as data. Constraint families quantify over membership in a compiled
list — query layouts, declared copies, enabled lookups — rather than over an index range.

The clean side is a `Prop` here, unlike in `finForallOrRelationWitness`. `x ∈ a :: t` unfolds to
the `Prop`-valued `x = a ∨ x ∈ t`, so recovering `A x` from the head and tail results is a
large elimination, available only when `A x` is itself a `Prop`. A `Sort`-valued family
quantified over list membership must reindex through `Fin l.length` and use
`finForallOrRelationWitness`. -/
def listForallOrRelationWitness {α : Type u} {A : α → Prop} {R : Sort w} :
    ∀ l : List α, (∀ x ∈ l, A x ⊕' R) → (∀ x ∈ l, A x) ⊕' R
  | [], _ => PSum.inl fun _ hx => absurd hx (by simp)
  | a :: t, outcome =>
      match outcome a (by simp) with
      | PSum.inr relation => PSum.inr relation
      | PSum.inl head =>
          match listForallOrRelationWitness t
              (fun x hx => outcome x (by simp [hx])) with
          | PSum.inr relation => PSum.inr relation
          | PSum.inl tail =>
              PSum.inl fun x hx =>
                (List.mem_cons.mp hx).elim (fun h => by subst h; exact head) (tail x)

end Zcash.Snark
