import Zcash.Arithmetic.Domain

/-!
# The closed form of the Lagrange basis over the evaluation domain

Over the `2^k` root-of-unity domain, the `i`-th Lagrange basis polynomial has the
closed coefficient form `ℓ_i = n⁻¹ · Σ_t ω^{-i·t} Xᵗ`: it has degree below `n` and
evaluates to `δ_{ij}` at `ω^j` (the geometric sum of a nontrivial root vanishes), so it
is the interpolation of `Pi.single i (1 : Fp)`.

This module is the coefficient math alone. Turning it into commitment identities — the
bridge to `LagrangeCommitmentKey.generator_eq` — is `Zcash/Snark/Keygen/Lagrange.lean`,
which is where the verifier-side vocabulary lives.
-/

namespace Zcash.Arithmetic

open Polynomial
open CompElliptic.Curves.Pasta
/-- `ℓ_i` in closed coefficient form: `n⁻¹ · Σ_{t < n} ω^{-i·t} Xᵗ`. -/
noncomputable def lagrangeBasisClosed (k : ℕ) (i : Fin (2 ^ k)) : Polynomial Fp :=
  ((2 ^ k : Fp))⁻¹ • ∑ t : Fin (2 ^ k),
    Polynomial.C ((omegaOf k)⁻¹ ^ ((i : ℕ) * (t : ℕ))) * Polynomial.X ^ (t : ℕ)

theorem lagrangeBasisClosed_coeff (k : ℕ) (i : Fin (2 ^ k)) (t : Fin (2 ^ k)) :
    (lagrangeBasisClosed k i).coeff (t : ℕ) =
      (2 ^ k : Fp)⁻¹ * (omegaOf k)⁻¹ ^ ((i : ℕ) * (t : ℕ)) := by
  classical
  rw [lagrangeBasisClosed, Polynomial.coeff_smul, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single t]
  · simp
  · intro b _ hbt
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    simp only [mul_ite, mul_one, mul_zero, ite_eq_right_iff]
    intro hb
    exact absurd (Fin.ext hb.symm) hbt
  · intro ht
    exact absurd (Finset.mem_univ t) ht

theorem lagrangeBasisClosed_natDegree_lt (k : ℕ) (i : Fin (2 ^ k)) :
    (lagrangeBasisClosed k i).natDegree < 2 ^ k := by
  classical
  have hdeg : (lagrangeBasisClosed k i).degree < (2 ^ k : ℕ) := by
    rw [lagrangeBasisClosed]
    refine lt_of_le_of_lt (Polynomial.degree_smul_le _ _) ?_
    refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
    rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe _)]
    intro t _
    exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _)
      (by exact_mod_cast WithBot.coe_lt_coe.mpr t.isLt)
  by_cases hzero : lagrangeBasisClosed k i = 0
  · rw [hzero, Polynomial.natDegree_zero]
    exact Nat.two_pow_pos k
  · exact (Polynomial.natDegree_lt_iff_degree_lt hzero).mpr hdeg

/-- The closed form evaluates to the Kronecker delta on the domain: at `ω^j` the sum is
geometric in `ω^j·ω^{-i}`, which is `n` at `j = i` and a vanishing nontrivial-root sum
otherwise. -/
theorem lagrangeBasisClosed_eval (k : ℕ) (hk : k ≤ 32) (i j : Fin (2 ^ k)) :
    (lagrangeBasisClosed k i).eval (omegaOf k ^ (j : ℕ)) =
      if j = i then 1 else 0 := by
  classical
  have homega : omegaOf k ≠ 0 :=
    (omegaOf_isPrimitiveRoot k hk).ne_zero (Nat.two_pow_pos k).ne'
  set zeta : Fp := omegaOf k ^ (j : ℕ) * ((omegaOf k)⁻¹) ^ (i : ℕ) with hzeta
  have heval : (lagrangeBasisClosed k i).eval (omegaOf k ^ (j : ℕ)) =
      (2 ^ k : Fp)⁻¹ * ∑ t : Fin (2 ^ k), zeta ^ (t : ℕ) := by
    rw [lagrangeBasisClosed, Polynomial.eval_smul, Polynomial.eval_finsetSum,
      smul_eq_mul]
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      hzeta, mul_pow]
    ring
  rw [heval]
  by_cases hij : j = i
  · subst hij
    have hone : zeta = 1 := by
      rw [hzeta, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ homega)]
    simp only [hone, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
    have hn : (2 ^ k : Fp) ≠ 0 := by
      have hcast := domainSize_cast_ne_zero k hk
      rwa [show ((2 ^ k : ℕ) : Fp) = (2 ^ k : Fp) by push_cast; ring] at hcast
    rw [show ((2 ^ k : ℕ) : Fp) = (2 ^ k : Fp) by push_cast; ring,
      inv_mul_cancel₀ hn]
    simp
  · rw [if_neg hij]
    have hz1 : zeta ≠ 1 := by
      rw [hzeta, inv_pow]
      intro h1
      rw [mul_inv_eq_one₀ (pow_ne_zero _ homega)] at h1
      exact hij (omegaOf_powers_injective k hk h1)
    have hzn : zeta ^ (2 ^ k) = 1 := by
      rw [hzeta, inv_pow, mul_pow, ← inv_pow, ← pow_mul, ← pow_mul,
        Nat.mul_comm (j : ℕ), Nat.mul_comm (i : ℕ), pow_mul, pow_mul]
      simp [(omegaOf_isPrimitiveRoot k hk).pow_eq_one]
    have hsum : ∑ t : Fin (2 ^ k), zeta ^ (t : ℕ) = 0 := by
      rw [Fin.sum_univ_eq_sum_range, geom_sum_eq hz1, hzn]
      simp
    rw [hsum, mul_zero]

end Zcash.Arithmetic
