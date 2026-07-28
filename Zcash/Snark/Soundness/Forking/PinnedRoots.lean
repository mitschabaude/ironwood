import Zcash.Snark.Soundness.Forking.PinnedSqueeze

/-!
# Additive pricing for pinned root events

A bad root exposed at one squeeze has a direct Schwartz--Zippel bound, and
`xEscTable_measure_le` prices that squeeze at `(Q + 1) * epsilon`.  This file packages a finite
union of such events and sums their budgets — no fourth root.

A squeezed challenge is never re-absorbed, so a transcript prefix does not determine the earlier
answers.  `bad` therefore reads the run output and the whole table; the causal boundary is
`pinned` — invariance under reprogramming the event's own squeeze answer.
-/

namespace Zcash.Snark

open scoped ENNReal
open Classical

variable {T F P : Type*} [Fintype F] [Nonempty F]

/-- One bad-root set for one squeeze of a run.

`point` is the prefix hashed by the squeeze; `bad` may read the run output and the table,
including earlier squeeze answers.  `pinned` bars only the answer being priced: reprogramming it
leaves the set unchanged. -/
structure PinnedRootEvent [DecidableEq T] (A : OracleComp T F P) where
  point : P -> T
  bad : P -> (T -> F) -> Set F
  budget : ENNReal
  measure_le : forall p O,
    (PMF.uniformOfFintype F).toOuterMeasure (bad p O) <= budget
  pinned : forall (O : T -> F) (v : F),
    bad (A.run (Function.update O (point (A.run O)) v))
        (Function.update O (point (A.run O)) v) = bad (A.run O) O

namespace PinnedRootEvent

/-- The run's own squeeze answer lands in this bad-root set. -/
def Landing [DecidableEq T] {A : OracleComp T F P} (event : PinnedRootEvent A)
    (O : T -> F) : Prop :=
  O (event.point (A.run O)) ∈ event.bad (A.run O) O

/-- One pinned root event costs its direct root-set budget, with only the standard query loss. -/
theorem landing_measure_le [Fintype T] [DecidableEq T]
    {A : OracleComp T F P} (event : PinnedRootEvent A) {Q : Nat}
    (hQ : A.QueryBound Q) :
    (PMF.uniformOfFintype (T -> F)).toOuterMeasure {O : T -> F | event.Landing O}
      <= (Q + 1 : Nat) * event.budget := by
  exact xEscTable_measure_le A event.point event.bad event.pinned event.measure_le hQ

end PinnedRootEvent

/-- A finite collection of independently priced root events. -/
structure PinnedRootFamily [DecidableEq T] (A : OracleComp T F P) (n : Nat) where
  event : Fin n -> PinnedRootEvent A

namespace PinnedRootFamily

/-- At least one root event occurs on the run. -/
def Landing [DecidableEq T] {A : OracleComp T F P} {n : Nat}
    (family : PinnedRootFamily A n) (O : T -> F) : Prop :=
  ∃ i : Fin n, (family.event i).Landing O

/-- A finite union of pinned root events is additive: no product threshold and no fourth root. -/
theorem landing_measure_le [Fintype T] [DecidableEq T]
    {A : OracleComp T F P} {n : Nat} (family : PinnedRootFamily A n) {Q : Nat}
    (hQ : A.QueryBound Q) :
    (PMF.uniformOfFintype (T -> F)).toOuterMeasure {O : T -> F | family.Landing O}
      <= (Q + 1 : Nat) * ∑ i : Fin n, (family.event i).budget := by
  have hsub : {O : T -> F | family.Landing O} <=
      ⋃ i : Fin n, {O : T -> F | (family.event i).Landing O} := by
    intro O hO
    obtain ⟨i, hi⟩ := hO
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  refine le_trans (MeasureTheory.measure_mono hsub) ?_
  refine le_trans (MeasureTheory.measure_iUnion_le _) ?_
  rw [tsum_fintype]
  calc
    (∑ i : Fin n, (PMF.uniformOfFintype (T -> F)).toOuterMeasure
        {O : T -> F | (family.event i).Landing O})
        <= ∑ i : Fin n, (Q + 1 : Nat) * (family.event i).budget :=
      Finset.sum_le_sum fun i _ => (family.event i).landing_measure_le hQ
    _ = (Q + 1 : Nat) * ∑ i : Fin n, (family.event i).budget := by
      rw [Finset.mul_sum]

end PinnedRootFamily

/-! ## Instantiability

The event below discharges both conditions for a bad set that reads the table away from its own
point — the capability the deployed root sets need. -/

/-- A table-reading pinned event: the bad set is the answer at `t1`, unchanged by reprogramming
the squeeze point `t0`. -/
noncomputable def tableReadingPinnedRootEvent [DecidableEq T] (p0 : P) {t0 t1 : T}
    (hne : t1 ≠ t0) :
    PinnedRootEvent (OracleComp.pure p0 : OracleComp T F P) where
  point := fun _ => t0
  bad := fun _ O => {v : F | v = O t1}
  budget := 1 / Fintype.card F
  measure_le := by
    intro p O
    have hset : {v : F | v = O t1} = {O t1} := by
      ext v
      simp
    rw [hset, PMF.toOuterMeasure_apply_singleton, PMF.uniformOfFintype_apply, one_div]
  pinned := by
    intro O v
    ext u
    simp [Function.update_of_ne hne]

/-- The demonstration event is priced by the generic bound. -/
theorem tableReadingPinnedRootEvent_landing_measure_le [Fintype T] [DecidableEq T]
    (p0 : P) {t0 t1 : T} (hne : t1 ≠ t0) :
    (PMF.uniformOfFintype (T -> F)).toOuterMeasure
        {O : T -> F | (tableReadingPinnedRootEvent (F := F) p0 hne).Landing O}
      <= (1 : Nat) * (1 / Fintype.card F) :=
  (tableReadingPinnedRootEvent (F := F) p0 hne).landing_measure_le
    (OracleComp.QueryBound.pure p0 0)

end Zcash.Snark
