/-
Copyright (c) 2026 Ironwood Contributors.
Released under the Apache License, Version 2.0.
-/
import Zcash.Arithmetic.FftSpec
import CompElliptic.Curves.Pasta.Fast.Msm

/-!
# Committing against the derived Lagrange basis is an inverse DFT of the coefficients

`derivedUrsGLagrange urs` is the scaled inverse group-FFT of the monomial URS: by
`bestFftG_dft`, its `j`-th generator is `L_j = ∑ᵢ n⁻¹·ω^(−i·j) • gᵢ`.  Committing a
Lagrange-coefficient column `e` against that basis is therefore, by bilinearity of the
group action,

  `∑ⱼ eⱼ • Lⱼ = ∑ᵢ (∑ⱼ n⁻¹·ω^(−i·j)·eⱼ) • gᵢ`,

i.e. the SAME commitment taken against the **monomial** basis `List.ofFn urs.g`, with the
coefficients replaced by their scaled inverse DFT.  The transform matrix `ω^(−i·j)` is
symmetric, which is what lets the group schedule be reused verbatim on the scalars.

The scalar transform is not a new algorithm: `bestFftG` is stated for an arbitrary
`Fp`-module, and `Fp` is an `Fp`-module, so `scalarInvDft` is literally `bestFftG`
instantiated at `G := Fp` and its semantics come from the same `bestFftG_dft`.

The point of the identity is evaluation cost: the group FFT builds `2 ^ k` **curve** points
(the dominant cost of the concrete certificate), whereas the scalar FFT is `2 ^ k` field
multiplications, and the monomial basis is URS data that needs no derivation at all.
-/

namespace Zcash.Arithmetic
open CompElliptic.Curves.Pasta

variable {G : Type} [AddCommGroup G] [Inhabited G] [Module Fp G]

/-- The scaled inverse DFT of a coefficient list — `derivedUrsGLagrange`'s transform, run on
scalars instead of group elements: the very same `bestFftG` at `G := Fp`. -/
def scalarInvDft (k : ℕ) (evals : List Fp) : List Fp :=
  (bestFftG evals.toArray (omegaInvOf k) k).toList.map
    fun c => (((2 : Fp) ^ k)⁻¹).val • c

omit [Inhabited G] in
/-- The `ZMod.val`-smul the FFT computes is the `Fp`-module action (`FftSpec`'s `val_smul`,
restated here so this module does not depend on that file's private section). -/
private theorem val_smul' (c : Fp) (x : G) : c.val • x = c • x := by
  rw [← Nat.cast_smul_eq_nsmul Fp c.val x, ZMod.natCast_rightInverse c]

theorem scalarInvDft_length (k : ℕ) (evals : List Fp) :
    (scalarInvDft k evals).length = evals.length := by
  simp [scalarInvDft, bestFftG_size]

/-- **The inverse DFT of the scalars, in closed form**: `bestFftG_dft` at `G := Fp`. -/
theorem scalarInvDft_getD (k : ℕ) (hk : k ≤ 32) (evals : List Fp)
    (hlen : evals.length = 2 ^ k) (i : Fin (2 ^ k)) :
    (scalarInvDft k evals).getD (i : ℕ) 0
      = ∑ t : Fin (2 ^ k),
          ((2 : Fp) ^ k)⁻¹ * omegaInvOf k ^ ((i : ℕ) * (t : ℕ)) * evals.getD (t : ℕ) 0 := by
  have hsize : evals.toArray.size = 2 ^ k := by simpa using hlen
  have hdft := bestFftG_dft evals.toArray (omegaInvOf k) k hsize
    (omegaInvOf_isPrimitiveRoot k hk) i
  have hlen' : (bestFftG evals.toArray (omegaInvOf k) k).toList.length = 2 ^ k := by
    simp [bestFftG_size, hsize]
  rw [scalarInvDft]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem (by rw [hlen']; exact i.isLt)]
  simp only [Option.map_some, Option.getD_some, Array.getElem_toList]
  rw [← getElem!_pos _ (i : ℕ) (by rw [bestFftG_size, hsize]; exact i.isLt), hdft]
  rw [val_smul', Finset.smul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [getElem!_pos _ (t : ℕ) (by rw [hsize]; exact t.isLt)]
  rw [smul_eq_mul, smul_eq_mul, mul_assoc]
  congr 1
  rw [List.getD_eq_getElem evals 0 (by rw [hlen]; exact t.isLt)]
  simp

omit [Inhabited G] [Module Fp G] in
/-- `commitLagrangeSpec`'s `range`/`getD` sum, as a `Finset.range` sum. -/
private theorem sum_range_list (n : ℕ) (f : ℕ → G) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := rfl

/-- **The derived Lagrange generators as explicit monomial combinations.** The `j`-th entry of
the derived basis is the monomial URS weighted by the closed Lagrange row `n⁻¹ · ω⁻¹^(j·t)`.
`Keygen/Lagrange.lean` restates this as `derivedUrsGLagrange_generator_eq`, in the verifier's
`commit` vocabulary. -/
theorem derivedUrsGLagrange_getD (urs : URS G) (hk : urs.k ≤ 32) (j : Fin (2 ^ urs.k)) :
    (derivedUrsGLagrange urs).getD (j : ℕ) 0
      = ∑ t : Fin (2 ^ urs.k),
          (((2 : Fp) ^ urs.k)⁻¹ * omegaInvOf urs.k ^ ((j : ℕ) * (t : ℕ))) • urs.g t := by
  have hsize0 : (List.ofFn urs.g).toArray.size = 2 ^ urs.k := by simp
  have hdft := bestFftG_dft (List.ofFn urs.g).toArray (omegaInvOf urs.k) urs.k hsize0
    (omegaInvOf_isPrimitiveRoot urs.k hk) j
  have hlen : (bestFftG (List.ofFn urs.g).toArray (omegaInvOf urs.k) urs.k).toList.length =
      2 ^ urs.k := by
    simp [bestFftG_size]
  rw [derivedUrsGLagrange, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem (by rw [hlen]; exact j.isLt)]
  simp only [Option.map_some, Option.getD_some, Array.getElem_toList]
  rw [← getElem!_pos _ (j : ℕ) (by rw [bestFftG_size, hsize0]; exact j.isLt), hdft, val_smul',
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [getElem!_pos _ (t : ℕ) (by rw [hsize0]; exact t.isLt)]
  simp only [List.getElem_toArray, List.getElem_ofFn]
  rw [smul_smul]

/-- **MSM bilinearity moves the transform off the group and onto the scalars**: committing a
full-domain coefficient column against the derived Lagrange basis is committing its scaled
inverse DFT against the monomial URS.  Both sides carry the same blind.

The hypothesis `hlen` is what makes the two `commitLagrangeSpec` sums range over the whole
domain — the spec pads the basis with zeros to the coefficient count, so a short column would
see only a prefix of the basis on the left while the DFT on the right needs all of it. -/
theorem commitLagrangeSpec_derivedUrsGLagrange (urs : URS G) (hk : urs.k ≤ 32)
    (blind : G) (evals : List Fp) (hlen : evals.length = 2 ^ urs.k) :
    Fast.Msm.commitLagrangeSpec blind (derivedUrsGLagrange urs) evals
      = Fast.Msm.commitLagrangeSpec blind (List.ofFn urs.g) (scalarInvDft urs.k evals) := by
  unfold Fast.Msm.commitLagrangeSpec
  congr 1
  rw [hlen, scalarInvDft_length, hlen, sum_range_list, sum_range_list,
    ← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
  have hL : ∀ j : Fin (2 ^ urs.k),
      (evals.getD (j : ℕ) 0).val • (derivedUrsGLagrange urs).getD (j : ℕ) 0
        = ∑ t : Fin (2 ^ urs.k),
            (((2 : Fp) ^ urs.k)⁻¹ * omegaInvOf urs.k ^ ((j : ℕ) * (t : ℕ))
              * evals.getD (j : ℕ) 0) • urs.g t := by
    intro j
    rw [val_smul', derivedUrsGLagrange_getD urs hk j, Finset.smul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [smul_smul]
    congr 1
    ring
  have hR : ∀ i : Fin (2 ^ urs.k),
      ((scalarInvDft urs.k evals).getD (i : ℕ) 0).val • (List.ofFn urs.g).getD (i : ℕ) 0
        = ∑ t : Fin (2 ^ urs.k),
            (((2 : Fp) ^ urs.k)⁻¹ * omegaInvOf urs.k ^ ((i : ℕ) * (t : ℕ))
              * evals.getD (t : ℕ) 0) • urs.g i := by
    intro i
    rw [val_smul', scalarInvDft_getD urs.k hk evals hlen i, Finset.sum_smul]
    congr 1
    rw [List.getD_eq_getElem _ 0 (by simp)]
    simp
  simp only [hL, hR]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
    (f := fun i t : Fin (2 ^ urs.k) =>
      (((2 : Fp) ^ urs.k)⁻¹ * omegaInvOf urs.k ^ ((i : ℕ) * (t : ℕ))
        * evals.getD (t : ℕ) 0) • urs.g i)]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun t _ => ?_
  congr 2
  rw [Nat.mul_comm]

/-! ## The Lagrange generators as monomial MSMs

The same closed form, read the other way round: an individual derived Lagrange generator is a
single commitment of a closed coefficient row against the monomial URS.  A short **prefix** of
the derived basis therefore costs that many MSMs, instead of the whole `2 ^ k`-point group
FFT. -/

/-- The `j`-th derived Lagrange generator's coefficient row: `n⁻¹ · ω^(−j·t)`, `t < 2 ^ k`.
The scale and the root are bound outside the map: they are loop-invariant, and the scale is a
field inversion. -/
def lagrangeRow (k j : ℕ) : List Fp :=
  let minv : Fp := ((2 : Fp) ^ k)⁻¹
  let w : Fp := omegaInvOf k
  (List.range (2 ^ k)).map fun t => minv * w ^ (j * t)

theorem lagrangeRow_length (k j : ℕ) : (lagrangeRow k j).length = 2 ^ k := by
  simp [lagrangeRow]

/-- Each derived Lagrange generator is the unblinded monomial commitment of its row. -/
theorem commitLagrangeSpec_lagrangeRow (urs : URS G) (hk : urs.k ≤ 32)
    (j : Fin (2 ^ urs.k)) :
    Fast.Msm.commitLagrangeSpec 0 (List.ofFn urs.g) (lagrangeRow urs.k (j : ℕ))
      = (derivedUrsGLagrange urs).getD (j : ℕ) 0 := by
  rw [Fast.Msm.commitLagrangeSpec, derivedUrsGLagrange_getD urs hk j, add_zero,
    lagrangeRow_length, sum_range_list, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [List.getD_eq_getElem _ 0 (by simp [lagrangeRow]), List.getD_eq_getElem _ 0 (by simp),
    val_smul']
  simp [lagrangeRow]

/-- **A prefix of the derived Lagrange basis, without the group FFT**: the first `m`
generators are `m` monomial MSMs of the closed coefficient rows. -/
theorem derivedUrsGLagrange_take (urs : URS G) (hk : urs.k ≤ 32) (m : ℕ)
    (hm : m ≤ 2 ^ urs.k) :
    (derivedUrsGLagrange urs).take m
      = List.ofFn fun j : Fin m =>
          Fast.Msm.commitLagrangeSpec 0 (List.ofFn urs.g) (lagrangeRow urs.k (j : ℕ)) := by
  have hlen := derivedUrsGLagrange_length urs
  refine List.ext_getElem (by simp [hlen]; omega) fun i h1 h2 => ?_
  have hi : i < m := by simp [hlen] at h1; omega
  rw [List.getElem_take, List.getElem_ofFn]
  rw [commitLagrangeSpec_lagrangeRow urs hk ⟨i, lt_of_lt_of_le hi hm⟩]
  exact (List.getD_eq_getElem _ 0 (by rw [hlen]; exact lt_of_lt_of_le hi hm)).symm

end Zcash.Arithmetic
