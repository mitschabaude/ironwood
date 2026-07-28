import Zcash.Snark.Soundness.AGM.AlgebraicUnbatch
import Zcash.Snark.Soundness.Multiopen.Opened

/-!
# Offline decoding of an AGM representation family

Evaluating the adversary's representation function at distinct batching scalars and inverting the
Vandermonde system recovers representations of every batch column — local computations on ghost
AGM data, not accepting rewinds.
-/

namespace Zcash.Snark

open Classical

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- Representations of one fixed power-batched commitment at enough distinct scalar values, with
one slot identified as the aggregate used by the current transcript. -/
structure AlgebraicPowerRepresentationFamily
    (urs : URS G) {numColumns : Nat} (columnCommitments : Fin numColumns -> G)
    (aggregate : Fin (2 ^ urs.k) -> Fp) (aggregateU aggregateW challenge : Fp) where
  points : Fin numColumns -> Fp
  pointsInjective : Function.Injective points
  represented : Fin numColumns -> (Fin (2 ^ urs.k) -> Fp)
  representedU : Fin numColumns -> Fp
  representedW : Fin numColumns -> Fp
  current : Fin numColumns
  currentPoint : points current = challenge
  currentRepresented : represented current = aggregate
  currentU : representedU current = aggregateU
  currentW : representedW current = aggregateW
  commitment : forall r,
    commit urs (represented r) + representedU r • urs.u + representedW r • urs.w =
      ∑ i : Fin numColumns, points r ^ (i : Nat) • columnCommitments i

/-- Vandermonde-decode a representation family into individual represented columns and the exact
current power-batch reconstruction. -/
noncomputable def AlgebraicPowerRepresentationFamily.decode
    {urs : URS G} {numColumns : Nat} {columnCommitments : Fin numColumns -> G}
    {aggregate : Fin (2 ^ urs.k) -> Fp} {aggregateU aggregateW challenge : Fp}
    (family : AlgebraicPowerRepresentationFamily urs columnCommitments
      aggregate aggregateU aggregateW challenge) :
    AlgebraicPowerBatch urs columnCommitments aggregate aggregateU aggregateW challenge := by
  let mu : Matrix (Fin numColumns) (Fin numColumns) Fp :=
    (Matrix.vandermonde family.points)⁻¹
  have hleft : forall i j : Fin numColumns,
      (∑ r : Fin numColumns, mu i r * family.points r ^ (j : Nat)) =
        if i = j then 1 else 0 := by
    intro i j
    exact vandermonde_inv_left family.points family.pointsInjective i j
  have hright : forall r i : Fin numColumns,
      (∑ j : Fin numColumns, family.points r ^ (j : Nat) * mu j i) =
        if r = i then 1 else 0 := by
    intro r i
    exact vandermonde_inv_right family.points family.pointsInjective r i
  let coeffs : Fin numColumns -> (Fin (2 ^ urs.k) -> Fp) :=
    fun i => ∑ r : Fin numColumns, mu i r • family.represented r
  let uComp : Fin numColumns -> Fp :=
    fun i => ∑ r : Fin numColumns, mu i r • family.representedU r
  let wComp : Fin numColumns -> Fp :=
    fun i => ∑ r : Fin numColumns, mu i r • family.representedW r
  refine
    { coeffs := coeffs
      uComp := uComp
      wComp := wComp
      commitment := ?_
      reconstruct := ?_
      reconstructU := ?_
      reconstructW := ?_ }
  · intro i
    have hlin :
        commit urs (coeffs i) + uComp i • urs.u + wComp i • urs.w =
          ∑ r : Fin numColumns, mu i r •
            (commit urs (family.represented r) + family.representedU r • urs.u +
              family.representedW r • urs.w) := by
      change commit urs (∑ r : Fin numColumns, mu i r • family.represented r) +
          (∑ r : Fin numColumns, mu i r • family.representedU r) • urs.u +
          (∑ r : Fin numColumns, mu i r • family.representedW r) • urs.w = _
      rw [commit_eq_commitGen, commitGen_sum, Finset.sum_smul,
        Finset.sum_smul, <- Finset.sum_add_distrib, <- Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [commitGen_smul_left, smul_eq_mul, smul_eq_mul, mul_smul, mul_smul,
        smul_add, smul_add, commit_eq_commitGen]
    rw [hlin]
    exact vandermonde_decode_map mu hleft family.commitment i
  · rw [<- family.currentRepresented]
    change family.represented family.current =
      ∑ i : Fin numColumns, challenge ^ (i : Nat) •
        (∑ r : Fin numColumns, mu i r • family.represented r)
    calc
      family.represented family.current =
          ∑ i : Fin numColumns, family.points family.current ^ (i : Nat) •
            (∑ r : Fin numColumns, mu i r • family.represented r) :=
        (vandermonde_reconstruct_map family.represented mu hright family.current).symm
      _ = _ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [family.currentPoint]
  · rw [<- family.currentU]
    change family.representedU family.current =
      ∑ i : Fin numColumns, challenge ^ (i : Nat) •
        (∑ r : Fin numColumns, mu i r • family.representedU r)
    calc
      family.representedU family.current =
          ∑ i : Fin numColumns, family.points family.current ^ (i : Nat) •
            (∑ r : Fin numColumns, mu i r • family.representedU r) :=
        (vandermonde_reconstruct_map family.representedU mu hright family.current).symm
      _ = _ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [family.currentPoint]
  · rw [<- family.currentW]
    change family.representedW family.current =
      ∑ i : Fin numColumns, challenge ^ (i : Nat) •
        (∑ r : Fin numColumns, mu i r • family.representedW r)
    calc
      family.representedW family.current =
          ∑ i : Fin numColumns, family.points family.current ^ (i : Nat) •
            (∑ r : Fin numColumns, mu i r • family.representedW r) :=
        (vandermonde_reconstruct_map family.representedW mu hright family.current).symm
      _ = _ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [family.currentPoint]

end Zcash.Snark
