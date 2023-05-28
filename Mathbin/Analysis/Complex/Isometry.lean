/-
Copyright (c) 2021 François Sunatori. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François Sunatori

! This file was ported from Lean 3 source module analysis.complex.isometry
! leanprover-community/mathlib commit a87d22575d946e1e156fc1edd1e1269600a8a282
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Complex.Circle
import Mathbin.LinearAlgebra.Determinant
import Mathbin.LinearAlgebra.Matrix.GeneralLinearGroup

/-!
# Isometries of the Complex Plane

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The lemma `linear_isometry_complex` states the classification of isometries in the complex plane.
Specifically, isometries with rotations but without translation.
The proof involves:
1. creating a linear isometry `g` with two fixed points, `g(0) = 0`, `g(1) = 1`
2. applying `linear_isometry_complex_aux` to `g`
The proof of `linear_isometry_complex_aux` is separated in the following parts:
1. show that the real parts match up: `linear_isometry.re_apply_eq_re`
2. show that I maps to either I or -I
3. every z is a linear combination of a + b * I

## References

* [Isometries of the Complex Plane](http://helmut.knaust.info/mediawiki/images/b/b5/Iso.pdf)
-/


noncomputable section

open Complex

open ComplexConjugate

-- mathport name: complex.abs
local notation "|" x "|" => Complex.abs x

/- warning: rotation -> rotation is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align rotation rotationₓ'. -/
/-- An element of the unit circle defines a `linear_isometry_equiv` from `ℂ` to itself, by
rotation. -/
def rotation : circle →* ℂ ≃ₗᵢ[ℝ] ℂ
    where
  toFun a :=
    { DistribMulAction.toLinearEquiv ℝ ℂ a with
      norm_map' := fun x => show |a * x| = |x| by rw [map_mul, abs_coe_circle, one_mul] }
  map_one' := LinearIsometryEquiv.ext <| one_smul _
  map_mul' _ _ := LinearIsometryEquiv.ext <| mul_smul _ _
#align rotation rotation

/- warning: rotation_apply -> rotation_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align rotation_apply rotation_applyₓ'. -/
@[simp]
theorem rotation_apply (a : circle) (z : ℂ) : rotation a z = a * z :=
  rfl
#align rotation_apply rotation_apply

/- warning: rotation_symm -> rotation_symm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align rotation_symm rotation_symmₓ'. -/
@[simp]
theorem rotation_symm (a : circle) : (rotation a).symm = rotation a⁻¹ :=
  LinearIsometryEquiv.ext fun x => rfl
#align rotation_symm rotation_symm

/- warning: rotation_trans -> rotation_trans is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align rotation_trans rotation_transₓ'. -/
@[simp]
theorem rotation_trans (a b : circle) : (rotation a).trans (rotation b) = rotation (b * a) :=
  by
  ext1
  simp
#align rotation_trans rotation_trans

/- warning: rotation_ne_conj_lie -> rotation_ne_conjLie is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align rotation_ne_conj_lie rotation_ne_conjLieₓ'. -/
theorem rotation_ne_conjLie (a : circle) : rotation a ≠ conjLie :=
  by
  intro h
  have h1 : rotation a 1 = conj 1 := LinearIsometryEquiv.congr_fun h 1
  have hI : rotation a I = conj I := LinearIsometryEquiv.congr_fun h I
  rw [rotation_apply, RingHom.map_one, mul_one] at h1
  rw [rotation_apply, conj_I, ← neg_one_mul, mul_left_inj' I_ne_zero, h1, eq_neg_self_iff] at hI
  exact one_ne_zero hI
#align rotation_ne_conj_lie rotation_ne_conjLie

/- warning: rotation_of -> rotationOf is a dubious translation:
lean 3 declaration is
  (LinearIsometryEquiv.{0, 0, 0, 0} Real Real Real.semiring Real.semiring (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) (RingHomInvPair.ids.{0} Real Real.semiring) (RingHomInvPair.ids.{0} Real Real.semiring) Complex Complex (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex (NonUnitalNormedRing.toNonUnitalSeminormedRing.{0} Complex (NormedRing.toNonUnitalNormedRing.{0} Complex (NormedCommRing.toNormedRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField))))) (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex (NonUnitalNormedRing.toNonUnitalSeminormedRing.{0} Complex (NormedRing.toNonUnitalNormedRing.{0} Complex (NormedCommRing.toNormedRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField))))) (Complex.module.{0} Real Real.semiring Real.module) (Complex.module.{0} Real Real.semiring Real.module)) -> (coeSort.{1, 2} (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring))))) Type (SetLike.hasCoeToSort.{0, 0} (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring))))) Complex (Submonoid.setLike.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring)))))) circle)
but is expected to have type
  (LinearIsometryEquiv.{0, 0, 0, 0} Real Real Real.semiring Real.semiring (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) (RingHomInvPair.ids.{0} Real Real.semiring) (RingHomInvPair.ids.{0} Real Real.semiring) Complex Complex (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex (NonUnitalNormedRing.toNonUnitalSeminormedRing.{0} Complex (NormedRing.toNonUnitalNormedRing.{0} Complex (NormedCommRing.toNormedRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex))))) (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex (NonUnitalNormedRing.toNonUnitalSeminormedRing.{0} Complex (NormedRing.toNonUnitalNormedRing.{0} Complex (NormedCommRing.toNormedRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex))))) (Complex.instModuleComplexToAddCommMonoidToNonUnitalNonAssocSemiringToNonUnitalNonAssocRingToNonAssocRingInstRingComplex.{0} Real Real.semiring (NormedSpace.toModule.{0, 0} Real Real Real.normedField (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real (NonUnitalNormedRing.toNonUnitalSeminormedRing.{0} Real (NormedRing.toNonUnitalNormedRing.{0} Real (NormedCommRing.toNormedRing.{0} Real Real.normedCommRing)))) (NormedField.toNormedSpace.{0} Real Real.normedField))) (Complex.instModuleComplexToAddCommMonoidToNonUnitalNonAssocSemiringToNonUnitalNonAssocRingToNonAssocRingInstRingComplex.{0} Real Real.semiring (NormedSpace.toModule.{0, 0} Real Real Real.normedField (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real (NonUnitalNormedRing.toNonUnitalSeminormedRing.{0} Real (NormedRing.toNonUnitalNormedRing.{0} Real (NormedCommRing.toNormedRing.{0} Real Real.normedCommRing)))) (NormedField.toNormedSpace.{0} Real Real.normedField)))) -> (Subtype.{1} Complex (fun (x : Complex) => Membership.mem.{0, 0} Complex (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) (SetLike.instMembership.{0, 0} (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) Complex (Submonoid.instSetLikeSubmonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex))))) x circle))
Case conversion may be inaccurate. Consider using '#align rotation_of rotationOfₓ'. -/
/-- Takes an element of `ℂ ≃ₗᵢ[ℝ] ℂ` and checks if it is a rotation, returns an element of the
unit circle. -/
@[simps]
def rotationOf (e : ℂ ≃ₗᵢ[ℝ] ℂ) : circle :=
  ⟨e 1 / Complex.abs (e 1), by simp⟩
#align rotation_of rotationOf

/- warning: rotation_of_rotation -> rotationOf_rotation is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align rotation_of_rotation rotationOf_rotationₓ'. -/
@[simp]
theorem rotationOf_rotation (a : circle) : rotationOf (rotation a) = a :=
  Subtype.ext <| by simp
#align rotation_of_rotation rotationOf_rotation

/- warning: rotation_injective -> rotation_injective is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align rotation_injective rotation_injectiveₓ'. -/
theorem rotation_injective : Function.Injective rotation :=
  Function.LeftInverse.injective rotationOf_rotation
#align rotation_injective rotation_injective

/- warning: linear_isometry.re_apply_eq_re_of_add_conj_eq -> LinearIsometry.re_apply_eq_re_of_add_conj_eq is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_isometry.re_apply_eq_re_of_add_conj_eq LinearIsometry.re_apply_eq_re_of_add_conj_eqₓ'. -/
theorem LinearIsometry.re_apply_eq_re_of_add_conj_eq (f : ℂ →ₗᵢ[ℝ] ℂ)
    (h₃ : ∀ z, z + conj z = f z + conj (f z)) (z : ℂ) : (f z).re = z.re := by
  simpa [ext_iff, add_re, add_im, conj_re, conj_im, ← two_mul,
    show (2 : ℝ) ≠ 0 by simp [two_ne_zero]] using (h₃ z).symm
#align linear_isometry.re_apply_eq_re_of_add_conj_eq LinearIsometry.re_apply_eq_re_of_add_conj_eq

/- warning: linear_isometry.im_apply_eq_im_or_neg_of_re_apply_eq_re -> LinearIsometry.im_apply_eq_im_or_neg_of_re_apply_eq_re is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_isometry.im_apply_eq_im_or_neg_of_re_apply_eq_re LinearIsometry.im_apply_eq_im_or_neg_of_re_apply_eq_reₓ'. -/
theorem LinearIsometry.im_apply_eq_im_or_neg_of_re_apply_eq_re {f : ℂ →ₗᵢ[ℝ] ℂ}
    (h₂ : ∀ z, (f z).re = z.re) (z : ℂ) : (f z).im = z.im ∨ (f z).im = -z.im :=
  by
  have h₁ := f.norm_map z
  simp only [Complex.abs_def, norm_eq_abs] at h₁
  rwa [Real.sqrt_inj (norm_sq_nonneg _) (norm_sq_nonneg _), norm_sq_apply (f z), norm_sq_apply z,
    h₂, add_left_cancel_iff, mul_self_eq_mul_self_iff] at h₁
#align linear_isometry.im_apply_eq_im_or_neg_of_re_apply_eq_re LinearIsometry.im_apply_eq_im_or_neg_of_re_apply_eq_re

/- warning: linear_isometry.im_apply_eq_im -> LinearIsometry.im_apply_eq_im is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_isometry.im_apply_eq_im LinearIsometry.im_apply_eq_imₓ'. -/
theorem LinearIsometry.im_apply_eq_im {f : ℂ →ₗᵢ[ℝ] ℂ} (h : f 1 = 1) (z : ℂ) :
    z + conj z = f z + conj (f z) :=
  by
  have : ‖f z - 1‖ = ‖z - 1‖ := by rw [← f.norm_map (z - 1), f.map_sub, h]
  apply_fun fun x => x ^ 2  at this
  simp only [norm_eq_abs, ← norm_sq_eq_abs] at this
  rw [← of_real_inj, ← mul_conj, ← mul_conj] at this
  rw [RingHom.map_sub, RingHom.map_sub] at this
  simp only [sub_mul, mul_sub, one_mul, mul_one] at this
  rw [mul_conj, norm_sq_eq_abs, ← norm_eq_abs, LinearIsometry.norm_map] at this
  rw [mul_conj, norm_sq_eq_abs, ← norm_eq_abs] at this
  simp only [sub_sub, sub_right_inj, mul_one, of_real_pow, RingHom.map_one, norm_eq_abs] at this
  simp only [add_sub, sub_left_inj] at this
  rw [add_comm, ← this, add_comm]
#align linear_isometry.im_apply_eq_im LinearIsometry.im_apply_eq_im

/- warning: linear_isometry.re_apply_eq_re -> LinearIsometry.re_apply_eq_re is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_isometry.re_apply_eq_re LinearIsometry.re_apply_eq_reₓ'. -/
theorem LinearIsometry.re_apply_eq_re {f : ℂ →ₗᵢ[ℝ] ℂ} (h : f 1 = 1) (z : ℂ) : (f z).re = z.re :=
  by
  apply LinearIsometry.re_apply_eq_re_of_add_conj_eq
  intro z
  apply LinearIsometry.im_apply_eq_im h
#align linear_isometry.re_apply_eq_re LinearIsometry.re_apply_eq_re

/- warning: linear_isometry_complex_aux -> linear_isometry_complex_aux is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_isometry_complex_aux linear_isometry_complex_auxₓ'. -/
theorem linear_isometry_complex_aux {f : ℂ ≃ₗᵢ[ℝ] ℂ} (h : f 1 = 1) :
    f = LinearIsometryEquiv.refl ℝ ℂ ∨ f = conjLie :=
  by
  have h0 : f I = I ∨ f I = -I :=
    by
    have : |f I| = 1 := by simpa using f.norm_map Complex.I
    simp only [ext_iff, ← and_or_left, neg_re, I_re, neg_im, neg_zero]
    constructor
    · rw [← I_re]
      exact @LinearIsometry.re_apply_eq_re f.to_linear_isometry h I
    · apply @LinearIsometry.im_apply_eq_im_or_neg_of_re_apply_eq_re f.to_linear_isometry
      intro z
      rw [@LinearIsometry.re_apply_eq_re f.to_linear_isometry h]
  refine' h0.imp (fun h' : f I = I => _) fun h' : f I = -I => _ <;>
    · apply LinearIsometryEquiv.toLinearEquiv_injective
      apply complex.basis_one_I.ext'
      intro i
      fin_cases i <;> simp [h, h']
#align linear_isometry_complex_aux linear_isometry_complex_aux

/- warning: linear_isometry_complex -> linear_isometry_complex is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_isometry_complex linear_isometry_complexₓ'. -/
theorem linear_isometry_complex (f : ℂ ≃ₗᵢ[ℝ] ℂ) :
    ∃ a : circle, f = rotation a ∨ f = conjLie.trans (rotation a) :=
  by
  let a : circle := ⟨f 1, by simpa using f.norm_map 1⟩
  use a
  have : (f.trans (rotation a).symm) 1 = 1 := by simpa using rotation_apply a⁻¹ (f 1)
  refine' (linear_isometry_complex_aux this).imp (fun h₁ => _) fun h₂ => _
  · simpa using eq_mul_of_inv_mul_eq h₁
  · exact eq_mul_of_inv_mul_eq h₂
#align linear_isometry_complex linear_isometry_complex

/- warning: to_matrix_rotation -> toMatrix_rotation is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align to_matrix_rotation toMatrix_rotationₓ'. -/
/-- The matrix representation of `rotation a` is equal to the conformal matrix
`!![re a, -im a; im a, re a]`. -/
theorem toMatrix_rotation (a : circle) :
    LinearMap.toMatrix basisOneI basisOneI (rotation a).toLinearEquiv =
      Matrix.planeConformalMatrix (re a) (im a) (by simp [pow_two, ← norm_sq_apply]) :=
  by
  ext (i j)
  simp [LinearMap.toMatrix_apply]
  fin_cases i <;> fin_cases j <;> simp
#align to_matrix_rotation toMatrix_rotation

/- warning: det_rotation -> det_rotation is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align det_rotation det_rotationₓ'. -/
/-- The determinant of `rotation` (as a linear map) is equal to `1`. -/
@[simp]
theorem det_rotation (a : circle) : ((rotation a).toLinearEquiv : ℂ →ₗ[ℝ] ℂ).det = 1 :=
  by
  rw [← LinearMap.det_toMatrix basis_one_I, toMatrix_rotation, Matrix.det_fin_two]
  simp [← norm_sq_apply]
#align det_rotation det_rotation

/- warning: linear_equiv_det_rotation -> linearEquiv_det_rotation is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv_det_rotation linearEquiv_det_rotationₓ'. -/
/-- The determinant of `rotation` (as a linear equiv) is equal to `1`. -/
@[simp]
theorem linearEquiv_det_rotation (a : circle) : (rotation a).toLinearEquiv.det = 1 := by
  rw [← Units.eq_iff, LinearEquiv.coe_det, det_rotation, Units.val_one]
#align linear_equiv_det_rotation linearEquiv_det_rotation

