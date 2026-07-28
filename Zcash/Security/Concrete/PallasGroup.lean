import Zcash.Circuits.Specs.Pallas
import CompElliptic.Curves.PastaOrder
import Mathlib.Algebra.Module.ZMod

namespace Zcash.Security.Concrete

open CompElliptic.CurveForms.ShortWeierstrass
open CompElliptic.Curves.Pasta
open CompElliptic.Fields.Pasta

open Zcash.Circuits

/-- The Pallas group, with its affine `SWPoint` representation kept behind a small
protocol-facing wrapper. -/
structure PallasGroup where
  toSW : SWPoint Pallas.curve
deriving DecidableEq, Repr

namespace PallasGroup

/-- The representation equivalence used to transport the proven Pallas group laws. -/
def equivSW : PallasGroup ≃ SWPoint Pallas.curve where
  toFun := PallasGroup.toSW
  invFun := PallasGroup.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance : AddCommGroup PallasGroup := Equiv.addCommGroup equivSW

@[simp] theorem equivSW_apply (P : PallasGroup) : equivSW P = P.toSW := rfl
@[simp] theorem equivSW_symm_apply (P : SWPoint Pallas.curve) : equivSW.symm P = ⟨P⟩ := rfl

theorem q_nsmul_eq_zero (P : PallasGroup) : PALLAS_SCALAR_CARD • P = 0 := by
  apply equivSW.injective
  change PALLAS_SCALAR_CARD • P.toSW = 0
  rw [← Pallas.card_eq]
  exact card_nsmul_eq_zero'

/-- Scalar multiplication by a Pallas scalar is the executable natural multiplication
by its canonical representative. -/
instance : Module Zcash.Circuits.Fq PallasGroup :=
  AddCommGroup.zmodModule q_nsmul_eq_zero

@[simp] theorem smul_def (s : Zcash.Circuits.Fq) (P : PallasGroup) : s • P = s.val • P := rfl

instance : NoZeroSMulDivisors Zcash.Circuits.Fq PallasGroup :=
  GroupWithZero.toNoZeroSMulDivisors

/-- Turn a valid circuit-coordinate point into its group representation. -/
def ofPoint (P : Point Zcash.Circuits.Fp) (hP : P.Valid) : PallasGroup :=
  equivSW.symm (P.toSW hP)

instance validDecidable (P : Point Zcash.Circuits.Fp) : Decidable P.Valid := by
  unfold Point.Valid Point.OnCurve
  infer_instance

/-- Check whether circuit coordinates represent a Pallas point before converting them. -/
def ofPoint? (P : Point Zcash.Circuits.Fp) : Option PallasGroup :=
  if hP : P.Valid then some (ofPoint P hP) else none

/-- The checked conversion succeeds exactly for valid Pallas coordinates. -/
theorem ofPoint?_isSome_iff (P : Point Zcash.Circuits.Fp) :
    (ofPoint? P).isSome ↔ P.Valid := by
  by_cases hP : P.Valid <;> simp [ofPoint?, hP]

theorem ofPoint?_eq_some (P : Point Zcash.Circuits.Fp) (hP : P.Valid) :
    ofPoint? P = some (ofPoint P hP) := by
  simp [ofPoint?, hP]

/-- Expose the affine coordinate representation of a Pallas group element. -/
def toPoint (P : PallasGroup) : Point Zcash.Circuits.Fp := Point.ofSW P.toSW

theorem toPoint_valid (P : PallasGroup) : (toPoint P).Valid := by
  exact (Point.valid_iff (toPoint P)).mpr P.toSW.onCurve

@[simp] theorem ofPoint_toPoint (P : PallasGroup) :
    ofPoint (toPoint P) (toPoint_valid P) = P := by
  apply equivSW.injective
  apply SWPoint.ext_pair
  rfl

@[simp] theorem toPoint_ofPoint (P : Point Zcash.Circuits.Fp) (hP : P.Valid) :
    toPoint (ofPoint P hP) = P := by
  apply Point.ext_coords
  rfl

theorem toPoint_ofPoint?_eq {P : Point Zcash.Circuits.Fp} {Q : PallasGroup}
    (h : ofPoint? P = some Q) : toPoint Q = P := by
  by_cases hP : P.Valid
  · rw [ofPoint?_eq_some P hP] at h
    injection h with hQ
    subst hQ
    exact toPoint_ofPoint P hP
  · simp [ofPoint?, hP] at h

@[simp] theorem toPoint_zero : toPoint (0 : PallasGroup) = 0 := rfl

@[simp] theorem toPoint_add (P Q : PallasGroup) :
    toPoint (P + Q) = toPoint P + toPoint Q := rfl

@[simp] theorem toPoint_neg (P : PallasGroup) :
    toPoint (-P) = -toPoint P := rfl

@[simp] theorem toPoint_nsmul (n : ℕ) (P : PallasGroup) :
    toPoint (n • P) = n • toPoint P := by
  apply (Point.ext_toSW_iff
    (toPoint_valid (n • P))
    (Point.valid_nsmul (toPoint_valid P) n)).mpr
  rw [Point.toSW_nsmul (toPoint_valid P) n]
  rfl

/-- The module action agrees with the circuit's canonical-representative multiplication. -/
@[simp] theorem toPoint_smul (s : Zcash.Circuits.Fq) (P : PallasGroup) :
    toPoint (s • P) = s.val • toPoint P :=
  toPoint_nsmul s.val P

@[simp] theorem ofPoint_nsmul (n : ℕ) (P : Point Zcash.Circuits.Fp) (hP : P.Valid) :
    ofPoint (n • P) (Point.valid_nsmul hP n) = n • ofPoint P hP := by
  apply equivSW.injective
  exact Point.toSW_nsmul hP n

@[simp] theorem ofPoint_zero : ofPoint 0 Point.valid_zero = 0 := by
  apply equivSW.injective
  exact Point.toSW_zero

/-- `ofPoint` is proof-irrelevant in its validity certificate, so an affine identity
converts to the group identity under any certificate. -/
theorem ofPoint_eq_zero {P : Point Zcash.Circuits.Fp} (hP : P.Valid) (h : P = 0) :
    ofPoint P hP = 0 := by
  subst h
  exact ofPoint_zero

theorem ofPoint_add {P Q : Point Zcash.Circuits.Fp} (hP : P.Valid) (hQ : Q.Valid) :
    ofPoint (P + Q) (Point.valid_add hP hQ) = ofPoint P hP + ofPoint Q hQ := by
  apply equivSW.injective
  exact Point.toSW_add hP hQ

theorem ofPoint_neg {P : Point Zcash.Circuits.Fp} (hP : P.Valid) :
    ofPoint (-P) (Point.valid_neg hP) = -ofPoint P hP := by
  apply equivSW.injective
  exact Point.toSW_neg hP

@[simp] theorem toPoint_x (P : PallasGroup) : (toPoint P).x = P.toSW.x := rfl
@[simp] theorem toPoint_y (P : PallasGroup) : (toPoint P).y = P.toSW.y := rfl

/-- `toPoint` is injective: its affine coordinates determine the group element. -/
private theorem pmfib_toPoint_injective {P Q : PallasGroup}
    (h : toPoint P = toPoint Q) : P = Q := by
  apply equivSW.injective
  apply SWPoint.ext_pair
  exact Prod.ext (congrArg Point.x h) (congrArg Point.y h)

/-- An on-curve affine point has nonzero `x` (the identity encodes as `(0, 0)`). -/
private theorem pmfib_x_ne_zero_of_onCurve {p : Point Zcash.Circuits.Fp}
    (hp : p.OnCurve) : p.x ≠ 0 := by
  intro hx
  rcases p with ⟨x, y⟩
  subst hx
  exact Point.no_onCurve_of_x_zero y hp

/-- The `Extract_ℙ` ±-fibre property: two group elements have equal extracted
`x`-coordinates exactly when they agree up to sign.  The affine encoding of the
identity is `(0, 0)` and no on-curve point has `x = 0`, so the identity is alone in
its fibre. -/
theorem toPoint_x_eq_iff (P Q : PallasGroup) :
    (PallasGroup.toPoint P).x = (PallasGroup.toPoint Q).x ↔ (P = Q ∨ P = -Q) := by
  constructor
  · intro hx
    by_cases hP0 : toPoint P = 0
    · -- `toPoint P` is the identity, so its `x` is `0`, forcing `toPoint Q = 0` too.
      have hQx : (toPoint Q).x = 0 := by
        rw [← hx, hP0]; rfl
      have hQy : (toPoint Q).y = 0 :=
        Point.y_eq_zero_of_valid_of_x_eq_zero (toPoint_valid Q) hQx
      have hQ0 : toPoint Q = 0 := by
        apply Point.ext_coords
        simp only [Point.coords, Point.zero_def, hQx, hQy]
      exact Or.inl (pmfib_toPoint_injective (hP0.trans hQ0.symm))
    · -- `toPoint P` is on-curve; its `x` is nonzero, so `toPoint Q` is on-curve too.
      have hPC : (toPoint P).OnCurve :=
        Point.onCurve_of_valid_of_ne_zero (toPoint_valid P) hP0
      have hPxne : (toPoint P).x ≠ 0 := pmfib_x_ne_zero_of_onCurve hPC
      have hQxne : (toPoint Q).x ≠ 0 := hx ▸ hPxne
      have hQ0 : toPoint Q ≠ 0 := by
        intro h; exact hQxne (by rw [h]; rfl)
      have hQC : (toPoint Q).OnCurve :=
        Point.onCurve_of_valid_of_ne_zero (toPoint_valid Q) hQ0
      rcases Point.eq_or_eq_neg_of_x_eq hPC hQC hx with heq | hneg
      · exact Or.inl (pmfib_toPoint_injective heq)
      · refine Or.inr (pmfib_toPoint_injective ?_)
        rw [toPoint_neg]; exact hneg
  · rintro (rfl | rfl)
    · rfl
    · rw [toPoint_neg, Point.neg_x]

/-- The protocol's canonical embedding of Pallas base-field values into scalars. -/
def embedFp (x : Zcash.Circuits.Fp) : Zcash.Circuits.Fq := (x.val : Zcash.Circuits.Fq)

theorem pallas_base_card_lt_scalar_card : PALLAS_BASE_CARD < PALLAS_SCALAR_CARD := by
  native_decide

@[simp] theorem embedFp_val (x : Zcash.Circuits.Fp) : (embedFp x).val = x.val := by
  exact ZMod.val_natCast_of_lt <|
    lt_trans (ZMod.val_lt x) pallas_base_card_lt_scalar_card

theorem embedFp_injective : Function.Injective embedFp := by
  intro x y hxy
  apply ZMod.val_injective PALLAS_BASE_CARD
  simpa only [embedFp_val] using congrArg ZMod.val hxy

end PallasGroup

end Zcash.Security.Concrete
