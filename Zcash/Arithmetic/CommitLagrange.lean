import Zcash.Arithmetic.NatKernelEquiv
import Zcash.Arithmetic.InvDft
import Zcash.Arithmetic.VestaModule

/-!
# The fast Lagrange commitment

`commit_lagrange` — a Pedersen vector commitment against a fixed basis, plus a blind — is the
operation the verifying-key derivation runs 44 times over 2048-term columns, and it dominates
that computation. This module gives the evaluation path for it together with the PROVEN
equalities to the naive spec, so a caller gets the speed without the statement ever mentioning
the fast route.

The evaluation carrier is the dictionary-free `Nat` kernel (`Zcash.Arithmetic.NatKernel`):
projective Vesta points as canonical-`ℕ` triples, whose field steps dispatch to GMP's native
bignum arithmetic under the interpreter. The scalar inverse DFT needs no kernel at all —
`scalarInvDft` is `bestFftG` at `G := Fp`, and `ZMod` multiplication is likewise GMP-backed.

* `msmNatPre` / `commitNatPre` — the kernel MSM against a basis already converted to `ℕ`
  triples, so a nullary sharing site pays the coordinate conversion once for all columns.
* `commitInvDftNatWith` — the per-column committer the certificate runs: the scalar inverse
  DFT of the coefficients, then one MSM against the pre-converted MONOMIAL basis.
* `take_derivedUrsGLagrange_natPre` — a prefix of the derived Lagrange basis as monomial
  MSMs, so no group FFT is evaluated anywhere.
-/

namespace Zcash.Arithmetic

open CompElliptic.Curves.Pasta.Fast
open CompElliptic.Curves.Pasta.Fast.NatKernel (P3)
open CompElliptic.Curves.Pasta.Fast.Projective
open CompElliptic.Curves.Pasta.Fast.Projective.PVes
open CompElliptic.Curves.Pasta.Fast.Msm (Fp)

local instance : Inhabited G := ⟨0⟩

/-- Every `Fp` value's canonical representative is a 256-bit scalar. -/
theorem val_lt_two_pow_256 (a : Fp) : a.val < 2 ^ 256 :=
  lt_of_lt_of_le (ZMod.val_lt a) (by decide)

/-- `PVes → P3`: canonical `ℕ` representatives of the projective coordinates. -/
def ofPVes (P : PVes) : P3 := ⟨P.X.val, P.Y.val, P.Z.val⟩

theorem toPVes_ofPVes (P : PVes) : NatKernel.toPVes (ofPVes P) = P := by
  cases P with
  | mk X Y Z =>
    simp only [NatKernel.toPVes, ofPVes]
    rw [ZMod.natCast_rightInverse X, ZMod.natCast_rightInverse Y,
      ZMod.natCast_rightInverse Z]

theorem toG_ofPVes_ofAffine (g : G) : NatKernel.toG (ofPVes (ofAffine g)) = g := by
  rw [NatKernel.toG_eq, Function.comp_apply, toPVes_ofPVes, toAffine_ofAffine]

theorem valid_toPVes_ofPVes_ofAffine (g : G) :
    Valid (NatKernel.toPVes (ofPVes (ofAffine g))) := by
  rw [toPVes_ofPVes]
  exact valid_ofAffine g

/-! ## The MSM against a pre-converted basis -/

/-- The kernel MSM against a basis **already** held as canonical-`ℕ` projective triples, plus
the blind.  The basis conversion is the caller's, so it can be shared across columns. -/
def msmNatPre (c : ℕ) (blind : G) (basisN : List P3) (scalars : List ℕ) : G :=
  NatKernel.toG (NatKernel.msm c (scalars.zip basisN)) + blind

/-- **The pre-converted MSM is the naive `commit_lagrange` spec**, for a coefficient list as
long as the basis. -/
theorem msmNatPre_eq (c : ℕ) (hc : 0 < c) (blind : G) (basis : List G) (coeffs : List Fp)
    (hlen : coeffs.length = basis.length) :
    msmNatPre c blind (basis.map fun g => ofPVes (ofAffine g)) (coeffs.map ZMod.val)
      = Msm.commitLagrangeSpec blind basis coeffs := by
  unfold msmNatPre
  rw [NatKernel.toG_eq, Function.comp_apply, NatKernel.msm_spec c hc _
    (by intro t ht
        obtain ⟨-, h2⟩ := List.of_mem_zip ht
        rw [List.mem_map] at h2
        obtain ⟨g, -, hg⟩ := h2
        rw [← hg]
        exact valid_toPVes_ofPVes_ofAffine g)
    (by intro t ht
        obtain ⟨h1, -⟩ := List.of_mem_zip ht
        rw [List.mem_map] at h1
        obtain ⟨e, -, he⟩ := h1
        rw [← he]
        exact val_lt_two_pow_256 e)]
  have hterms :
      ((coeffs.map ZMod.val).zip (basis.map fun g => ofPVes (ofAffine g))).map
          (fun t => (t.1, toAffine (NatKernel.toPVes t.2)))
        = (coeffs.zip (basis ++ List.replicate (coeffs.length - basis.length) 0)).map
            fun t => (t.1.val, t.2) := by
    rw [hlen, Nat.sub_self, List.replicate_zero, List.append_nil, List.zip_map, List.map_map]
    refine List.map_congr_left fun t _ => ?_
    simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, toPVes_ofPVes,
      toAffine_ofAffine]
  rw [hterms, Msm.zip_terms_eq, Msm.pippenger_eq_msm c hc, List.map_map]
  rfl

/-- The pre-converted committer at `Fp` coefficients. -/
def commitNatPre (c : ℕ) (blind : G) (basisN : List P3) (coeffs : List Fp) : G :=
  msmNatPre c blind basisN (coeffs.map ZMod.val)

theorem commitNatPre_eq (c : ℕ) (hc : 0 < c) (blind : G) (basis : List G) (coeffs : List Fp)
    (hlen : coeffs.length = basis.length) :
    commitNatPre c blind (basis.map fun g => ofPVes (ofAffine g)) coeffs
      = Msm.commitLagrangeSpec blind basis coeffs :=
  msmNatPre_eq c hc blind basis coeffs hlen

/-! ## The composed per-column committer -/

/-- **The certificate's per-column committer**: the scalar inverse DFT of the coefficients
(`bestFftG` at `G := Fp`, GMP-backed), then one kernel MSM against the pre-converted MONOMIAL
basis.  No group FFT anywhere, no kernel on the scalar half. -/
def commitInvDftNatWith (c : ℕ) (k : ℕ) (blind : G) (basisN : List P3)
    (coeffs : List Fp) : G :=
  msmNatPre c blind basisN ((scalarInvDft k coeffs).map ZMod.val)

/-- **The composed committer IS `commit_lagrange` at the derived Lagrange basis** — the
bilinearity theorem, with the kernel MSM on the group half. -/
theorem commitInvDftNatWith_eq (c : ℕ) (hc : 0 < c)
    (urs : URS G) (hk : urs.k ≤ 32)
    (coeffs : List Fp) (hlen : coeffs.length = 2 ^ urs.k) :
    commitInvDftNatWith c urs.k urs.w
        ((List.ofFn urs.g).map fun g => ofPVes (ofAffine g)) coeffs
      = Msm.commitLagrangeSpec urs.w (derivedUrsGLagrange urs) coeffs := by
  haveI := vestaFpModuleDef
  rw [commitInvDftNatWith,
    msmNatPre_eq c hc urs.w (List.ofFn urs.g) _
      (by rw [scalarInvDft_length, hlen, List.length_ofFn]),
    ← commitLagrangeSpec_derivedUrsGLagrange urs hk urs.w coeffs hlen]

/-! ## The Lagrange prefix without a group FFT -/

/-- **A prefix of the derived Lagrange basis as monomial MSMs**: the `m`-generator prefix
costs `m` MSMs against the same pre-converted monomial basis the columns use, instead of the
full `2 ^ k`-point group FFT. -/
theorem take_derivedUrsGLagrange_natPre (c : ℕ) (hc : 0 < c) (urs : URS G) (hk : urs.k ≤ 32)
    (m : ℕ) (hm : m ≤ 2 ^ urs.k) :
    (derivedUrsGLagrange urs).take m
      = List.ofFn fun j : Fin m =>
          commitNatPre c 0 ((List.ofFn urs.g).map fun g => ofPVes (ofAffine g))
            (lagrangeRow urs.k (j : ℕ)) := by
  haveI := vestaFpModuleDef
  rw [derivedUrsGLagrange_take urs hk m hm]
  refine congrArg List.ofFn (funext fun j => ?_)
  rw [commitNatPre_eq c hc 0 (List.ofFn urs.g) _
    (by rw [lagrangeRow_length, List.length_ofFn])]

end Zcash.Arithmetic
