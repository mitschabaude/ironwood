import Zcash.Snark.Soundness.Forking.Adversary.OracleComp

/-!
# A pinned, table-reading squeeze

The one-level Fiat--Shamir squeeze bound used by the additive root analysis.
-/

namespace Zcash.Snark

open scoped ENNReal

variable {T F P : Type*} [Fintype F] [Nonempty F]

open Classical in
/-- The one-level escape with a table-reading bad set. -/
noncomputable def xEscTable [DecidableEq T] (A : OracleComp T F P) (xpt : P -> T)
    (bad : P -> (T -> F) -> Set F) : T -> (T -> F) -> Set F :=
  fun t O => {v : F | t = xpt (A.run (Function.update O t v)) ∧
    v ∈ bad (A.run (Function.update O t v)) (Function.update O t v)}

open Classical in
/-- A pinned bad set at one adaptive squeeze costs `(Q + 1) * epsilon`. -/
theorem xEscTable_measure_le [Fintype T] [DecidableEq T] (A : OracleComp T F P) (xpt : P -> T)
    (bad : P -> (T -> F) -> Set F)
    (hpin : forall (O : T -> F) (v : F),
      bad (A.run (Function.update O (xpt (A.run O)) v))
          (Function.update O (xpt (A.run O)) v) = bad (A.run O) O)
    {epsilon : ENNReal}
    (hbad : forall p O, (PMF.uniformOfFintype F).toOuterMeasure (bad p O) <= epsilon)
    {Q : Nat} (hQ : A.QueryBound Q) :
    (PMF.uniformOfFintype (T -> F)).toOuterMeasure
      {O : T -> F | O (xpt (A.run O)) ∈ bad (A.run O) O} <= (Q + 1 : Nat) * epsilon := by
  classical
  have hsub : {O : T -> F | O (xpt (A.run O)) ∈ bad (A.run O) O} <=
      {O : T -> F | (A.completing (fun p (_ : Fin 1) => xpt p)).escapesDuringC
        (xEscTable A xpt bad) O} := by
    intro O hO
    refine OracleComp.escapesDuringC_completing _ (fun p (_ : Fin 1) => xpt p) (j := 0) ?_
    show O (xpt (A.run O)) ∈ xEscTable A xpt bad (xpt (A.run O)) O
    constructor
    · rw [Function.update_eq_self]
    · rw [Function.update_eq_self]
      exact hO
  refine le_trans (MeasureTheory.measure_mono hsub) ?_
  have hblind : forall (t : T) (O : T -> F) (v : F),
      xEscTable A xpt bad t (Function.update O t v) = xEscTable A xpt bad t O := by
    intro t O v
    ext u
    simp only [xEscTable, Set.mem_setOf_eq, Function.update_idem]
  have hesc : forall (t : T) (O : T -> F),
      (PMF.uniformOfFintype F).toOuterMeasure (xEscTable A xpt bad t O) <= epsilon := by
    intro t O
    rcases Set.eq_empty_or_nonempty (xEscTable A xpt bad t O) with hemp | ⟨w, hw⟩
    · rw [hemp]
      simp
    obtain ⟨hwt, -⟩ := hw
    refine le_trans ((PMF.uniformOfFintype F).toOuterMeasure.mono ?_)
      (hbad (A.run (Function.update O t w)) (Function.update O t w))
    intro v hv
    obtain ⟨-, hvbad⟩ := hv
    have hupd : Function.update (Function.update O t w) t v = Function.update O t v := by
      rw [Function.update_idem]
    have hpinw := hpin (Function.update O t w) v
    rw [← hwt] at hpinw
    rw [hupd] at hpinw
    rw [← hpinw]
    exact hvbad
  have h := escapesDuringC_measure_le' (xEscTable A xpt bad) hblind hesc
    (OracleComp.queryBound_completing (fun p (_ : Fin 1) => xpt p) hQ)
  exact_mod_cast h

open Classical in
/-- A bad set indexed by the transcript point itself needs no rerun-pinning premise: every
reprogrammed run that still selects `t` is tested against the same `badAt t`. -/
theorem xEscAtPoint_measure_le [Fintype T] [DecidableEq T]
    (A : OracleComp T F P) (xpt : P -> T) (badAt : T -> Set F)
    {epsilon : ENNReal}
    (hbad : forall t, (PMF.uniformOfFintype F).toOuterMeasure (badAt t) <= epsilon)
    {Q : Nat} (hQ : A.QueryBound Q) :
    (PMF.uniformOfFintype (T -> F)).toOuterMeasure
      {O : T -> F | O (xpt (A.run O)) ∈ badAt (xpt (A.run O))}
        <= (Q + 1 : Nat) * epsilon := by
  let esc : T -> (T -> F) -> Set F := fun t O =>
    {v : F | t = xpt (A.run (Function.update O t v)) ∧ v ∈ badAt t}
  have hsub : {O : T -> F | O (xpt (A.run O)) ∈ badAt (xpt (A.run O))} <=
      {O : T -> F | (A.completing (fun p (_ : Fin 1) => xpt p)).escapesDuringC esc O} := by
    intro O hO
    refine OracleComp.escapesDuringC_completing _ (fun p (_ : Fin 1) => xpt p) (j := 0) ?_
    show O (xpt (A.run O)) ∈ esc (xpt (A.run O)) O
    constructor
    · rw [Function.update_eq_self]
    · exact hO
  refine le_trans (MeasureTheory.measure_mono hsub) ?_
  have hblind : forall (t : T) (O : T -> F) (v : F),
      esc t (Function.update O t v) = esc t O := by
    intro t O v
    ext u
    simp only [esc, Set.mem_setOf_eq, Function.update_idem]
  have hesc : forall (t : T) (O : T -> F),
      (PMF.uniformOfFintype F).toOuterMeasure (esc t O) <= epsilon := by
    intro t O
    refine le_trans ((PMF.uniformOfFintype F).toOuterMeasure.mono ?_) (hbad t)
    intro v hv
    exact hv.2
  have h := escapesDuringC_measure_le' esc hblind hesc
    (OracleComp.queryBound_completing (fun p (_ : Fin 1) => xpt p) hQ)
  exact_mod_cast h

end Zcash.Snark
