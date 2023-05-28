/-
Copyright (c) Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

! This file was ported from Lean 3 source module analysis.complex.operator_norm
! leanprover-community/mathlib commit 33c67ae661dd8988516ff7f247b0be3018cdd952
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Complex.Basic
import Mathbin.Analysis.NormedSpace.OperatorNorm
import Mathbin.Data.Complex.Determinant

/-! # The basic continuous linear maps associated to `ℂ`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The continuous linear maps `complex.re_clm` (real part), `complex.im_clm` (imaginary part),
`complex.conj_cle` (conjugation), and `complex.of_real_clm` (inclusion of `ℝ`) were introduced in
`analysis.complex.operator_norm`.  This file contains a few calculations requiring more imports:
the operator norm and (for `complex.conj_cle`) the determinant.
-/


open ContinuousLinearMap

namespace Complex

/- warning: complex.det_conj_lie -> Complex.det_conjLie is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align complex.det_conj_lie Complex.det_conjLieₓ'. -/
/-- The determinant of `conj_lie`, as a linear map. -/
@[simp]
theorem det_conjLie : (conjLie.toLinearEquiv : ℂ →ₗ[ℝ] ℂ).det = -1 :=
  det_conjAe
#align complex.det_conj_lie Complex.det_conjLie

/- warning: complex.linear_equiv_det_conj_lie -> Complex.linearEquiv_det_conjLie is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align complex.linear_equiv_det_conj_lie Complex.linearEquiv_det_conjLieₓ'. -/
/-- The determinant of `conj_lie`, as a linear equiv. -/
@[simp]
theorem linearEquiv_det_conjLie : conjLie.toLinearEquiv.det = -1 :=
  linearEquiv_det_conjAe
#align complex.linear_equiv_det_conj_lie Complex.linearEquiv_det_conjLie

/- warning: complex.re_clm_norm -> Complex.reClm_norm is a dubious translation:
lean 3 declaration is
  Eq.{1} Real (Norm.norm.{0} (ContinuousLinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (AddCommGroup.toAddCommMonoid.{0} Complex Complex.addCommGroup) Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) Real.addCommMonoid (Complex.module.{0} Real Real.semiring Real.module) Real.module) (ContinuousLinearMap.hasOpNorm.{0, 0, 0, 0} Real Real Complex Real (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex (NonUnitalNormedRing.toNonUnitalSeminormedRing.{0} Complex (NormedRing.toNonUnitalNormedRing.{0} Complex (NormedCommRing.toNormedRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField))))) (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real (NonUnitalNormedRing.toNonUnitalSeminormedRing.{0} Real (NormedRing.toNonUnitalNormedRing.{0} Real (NormedCommRing.toNormedRing.{0} Real Real.normedCommRing)))) (DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) (DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) (NormedSpace.complexToReal.{0} Complex Complex.normedAddCommGroup (NormedField.toNormedSpace.{0} Complex Complex.normedField)) (NormedField.toNormedSpace.{0} Real (NontriviallyNormedField.toNormedField.{0} Real (DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))) (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring))) Complex.reClm) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))
but is expected to have type
  Eq.{1} Real (Norm.norm.{0} (ContinuousLinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex (NonAssocRing.toNonUnitalNonAssocRing.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)))) Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) Real.instAddCommMonoidReal (Complex.instModuleComplexToAddCommMonoidToNonUnitalNonAssocSemiringToNonUnitalNonAssocRingToNonAssocRingInstRingComplex.{0} Real Real.semiring (NormedSpace.toModule.{0, 0} Real Real Real.normedField (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real (NonUnitalNormedRing.toNonUnitalSeminormedRing.{0} Real (NormedRing.toNonUnitalNormedRing.{0} Real (NormedCommRing.toNormedRing.{0} Real Real.normedCommRing)))) (NormedField.toNormedSpace.{0} Real Real.normedField))) (NormedSpace.toModule.{0, 0} Real Real Real.normedField (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real (NonUnitalNormedRing.toNonUnitalSeminormedRing.{0} Real (NormedRing.toNonUnitalNormedRing.{0} Real (NormedCommRing.toNormedRing.{0} Real Real.normedCommRing)))) (NormedField.toNormedSpace.{0} Real Real.normedField))) (ContinuousLinearMap.hasOpNorm.{0, 0, 0, 0} Real Real Complex Real (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex (NonUnitalNormedRing.toNonUnitalSeminormedRing.{0} Complex (NormedRing.toNonUnitalNormedRing.{0} Complex (NormedCommRing.toNormedRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex))))) (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real (NonUnitalNormedRing.toNonUnitalSeminormedRing.{0} Real (NormedRing.toNonUnitalNormedRing.{0} Real (NormedCommRing.toNormedRing.{0} Real Real.normedCommRing)))) (DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) (DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) (NormedSpace.complexToReal.{0} Complex Complex.instNormedAddCommGroupComplex (NormedField.toNormedSpace.{0} Complex Complex.instNormedFieldComplex)) (NormedField.toNormedSpace.{0} Real (NontriviallyNormedField.toNormedField.{0} Real (DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))) (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring))) Complex.reClm) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))
Case conversion may be inaccurate. Consider using '#align complex.re_clm_norm Complex.reClm_normₓ'. -/
@[simp]
theorem reClm_norm : ‖reClm‖ = 1 :=
  le_antisymm (LinearMap.mkContinuous_norm_le _ zero_le_one _) <|
    calc
      1 = ‖reClm 1‖ := by simp
      _ ≤ ‖reClm‖ := unit_le_op_norm _ _ (by simp)
      
#align complex.re_clm_norm Complex.reClm_norm

/- warning: complex.re_clm_nnnorm -> Complex.reClm_nnnorm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align complex.re_clm_nnnorm Complex.reClm_nnnormₓ'. -/
@[simp]
theorem reClm_nnnorm : ‖reClm‖₊ = 1 :=
  Subtype.ext reClm_norm
#align complex.re_clm_nnnorm Complex.reClm_nnnorm

/- warning: complex.im_clm_norm -> Complex.imClm_norm is a dubious translation:
lean 3 declaration is
  Eq.{1} Real (Norm.norm.{0} (ContinuousLinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (AddCommGroup.toAddCommMonoid.{0} Complex Complex.addCommGroup) Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) Real.addCommMonoid (Complex.module.{0} Real Real.semiring Real.module) Real.module) (ContinuousLinearMap.hasOpNorm.{0, 0, 0, 0} Real Real Complex Real (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex (NonUnitalNormedRing.toNonUnitalSeminormedRing.{0} Complex (NormedRing.toNonUnitalNormedRing.{0} Complex (NormedCommRing.toNormedRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField))))) (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real (NonUnitalNormedRing.toNonUnitalSeminormedRing.{0} Real (NormedRing.toNonUnitalNormedRing.{0} Real (NormedCommRing.toNormedRing.{0} Real Real.normedCommRing)))) (DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) (DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) (NormedSpace.complexToReal.{0} Complex Complex.normedAddCommGroup (NormedField.toNormedSpace.{0} Complex Complex.normedField)) (NormedField.toNormedSpace.{0} Real (NontriviallyNormedField.toNormedField.{0} Real (DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))) (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring))) Complex.imClm) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))
but is expected to have type
  Eq.{1} Real (Norm.norm.{0} (ContinuousLinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex (NonAssocRing.toNonUnitalNonAssocRing.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)))) Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) Real.instAddCommMonoidReal (Complex.instModuleComplexToAddCommMonoidToNonUnitalNonAssocSemiringToNonUnitalNonAssocRingToNonAssocRingInstRingComplex.{0} Real Real.semiring (NormedSpace.toModule.{0, 0} Real Real Real.normedField (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real (NonUnitalNormedRing.toNonUnitalSeminormedRing.{0} Real (NormedRing.toNonUnitalNormedRing.{0} Real (NormedCommRing.toNormedRing.{0} Real Real.normedCommRing)))) (NormedField.toNormedSpace.{0} Real Real.normedField))) (NormedSpace.toModule.{0, 0} Real Real Real.normedField (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real (NonUnitalNormedRing.toNonUnitalSeminormedRing.{0} Real (NormedRing.toNonUnitalNormedRing.{0} Real (NormedCommRing.toNormedRing.{0} Real Real.normedCommRing)))) (NormedField.toNormedSpace.{0} Real Real.normedField))) (ContinuousLinearMap.hasOpNorm.{0, 0, 0, 0} Real Real Complex Real (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex (NonUnitalNormedRing.toNonUnitalSeminormedRing.{0} Complex (NormedRing.toNonUnitalNormedRing.{0} Complex (NormedCommRing.toNormedRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex))))) (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real (NonUnitalNormedRing.toNonUnitalSeminormedRing.{0} Real (NormedRing.toNonUnitalNormedRing.{0} Real (NormedCommRing.toNormedRing.{0} Real Real.normedCommRing)))) (DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) (DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) (NormedSpace.complexToReal.{0} Complex Complex.instNormedAddCommGroupComplex (NormedField.toNormedSpace.{0} Complex Complex.instNormedFieldComplex)) (NormedField.toNormedSpace.{0} Real (NontriviallyNormedField.toNormedField.{0} Real (DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))) (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring))) Complex.imClm) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))
Case conversion may be inaccurate. Consider using '#align complex.im_clm_norm Complex.imClm_normₓ'. -/
@[simp]
theorem imClm_norm : ‖imClm‖ = 1 :=
  le_antisymm (LinearMap.mkContinuous_norm_le _ zero_le_one _) <|
    calc
      1 = ‖imClm I‖ := by simp
      _ ≤ ‖imClm‖ := unit_le_op_norm _ _ (by simp)
      
#align complex.im_clm_norm Complex.imClm_norm

/- warning: complex.im_clm_nnnorm -> Complex.imClm_nnnorm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align complex.im_clm_nnnorm Complex.imClm_nnnormₓ'. -/
@[simp]
theorem imClm_nnnorm : ‖imClm‖₊ = 1 :=
  Subtype.ext imClm_norm
#align complex.im_clm_nnnorm Complex.imClm_nnnorm

/- warning: complex.conj_cle_norm -> Complex.conjCle_norm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align complex.conj_cle_norm Complex.conjCle_normₓ'. -/
@[simp]
theorem conjCle_norm : ‖(conjCle : ℂ →L[ℝ] ℂ)‖ = 1 :=
  conjLie.toLinearIsometry.norm_toContinuousLinearMap
#align complex.conj_cle_norm Complex.conjCle_norm

/- warning: complex.conj_cle_nnorm -> Complex.conjCle_nnorm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align complex.conj_cle_nnorm Complex.conjCle_nnormₓ'. -/
@[simp]
theorem conjCle_nnorm : ‖(conjCle : ℂ →L[ℝ] ℂ)‖₊ = 1 :=
  Subtype.ext conjCle_norm
#align complex.conj_cle_nnorm Complex.conjCle_nnorm

/- warning: complex.of_real_clm_norm -> Complex.ofRealClm_norm is a dubious translation:
lean 3 declaration is
  Eq.{1} Real (Norm.norm.{0} (ContinuousLinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) Real.addCommMonoid Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (AddCommGroup.toAddCommMonoid.{0} Complex Complex.addCommGroup) Real.module (Complex.module.{0} Real Real.semiring Real.module)) (ContinuousLinearMap.hasOpNorm.{0, 0, 0, 0} Real Real Real Complex (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real (NonUnitalNormedRing.toNonUnitalSeminormedRing.{0} Real (NormedRing.toNonUnitalNormedRing.{0} Real (NormedCommRing.toNormedRing.{0} Real Real.normedCommRing)))) (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex (NonUnitalNormedRing.toNonUnitalSeminormedRing.{0} Complex (NormedRing.toNonUnitalNormedRing.{0} Complex (NormedCommRing.toNormedRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField))))) (DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) (DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) (NormedField.toNormedSpace.{0} Real (NontriviallyNormedField.toNormedField.{0} Real (DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))) (NormedSpace.complexToReal.{0} Complex Complex.normedAddCommGroup (NormedField.toNormedSpace.{0} Complex Complex.normedField)) (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring))) Complex.ofRealClm) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))
but is expected to have type
  Eq.{1} Real (Norm.norm.{0} (ContinuousLinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) Real.instAddCommMonoidReal Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex (NonAssocRing.toNonUnitalNonAssocRing.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)))) (NormedSpace.toModule.{0, 0} Real Real Real.normedField (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real (NonUnitalNormedRing.toNonUnitalSeminormedRing.{0} Real (NormedRing.toNonUnitalNormedRing.{0} Real (NormedCommRing.toNormedRing.{0} Real Real.normedCommRing)))) (NormedField.toNormedSpace.{0} Real Real.normedField)) (Complex.instModuleComplexToAddCommMonoidToNonUnitalNonAssocSemiringToNonUnitalNonAssocRingToNonAssocRingInstRingComplex.{0} Real Real.semiring (NormedSpace.toModule.{0, 0} Real Real Real.normedField (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real (NonUnitalNormedRing.toNonUnitalSeminormedRing.{0} Real (NormedRing.toNonUnitalNormedRing.{0} Real (NormedCommRing.toNormedRing.{0} Real Real.normedCommRing)))) (NormedField.toNormedSpace.{0} Real Real.normedField)))) (ContinuousLinearMap.hasOpNorm.{0, 0, 0, 0} Real Real Real Complex (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real (NonUnitalNormedRing.toNonUnitalSeminormedRing.{0} Real (NormedRing.toNonUnitalNormedRing.{0} Real (NormedCommRing.toNormedRing.{0} Real Real.normedCommRing)))) (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex (NonUnitalNormedRing.toNonUnitalSeminormedRing.{0} Complex (NormedRing.toNonUnitalNormedRing.{0} Complex (NormedCommRing.toNormedRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex))))) (DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) (DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) (NormedField.toNormedSpace.{0} Real (NontriviallyNormedField.toNormedField.{0} Real (DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))) (NormedSpace.complexToReal.{0} Complex Complex.instNormedAddCommGroupComplex (NormedField.toNormedSpace.{0} Complex Complex.instNormedFieldComplex)) (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring))) Complex.ofRealClm) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))
Case conversion may be inaccurate. Consider using '#align complex.of_real_clm_norm Complex.ofRealClm_normₓ'. -/
@[simp]
theorem ofRealClm_norm : ‖ofRealClm‖ = 1 :=
  ofRealLi.norm_toContinuousLinearMap
#align complex.of_real_clm_norm Complex.ofRealClm_norm

/- warning: complex.of_real_clm_nnnorm -> Complex.ofRealClm_nnnorm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align complex.of_real_clm_nnnorm Complex.ofRealClm_nnnormₓ'. -/
@[simp]
theorem ofRealClm_nnnorm : ‖ofRealClm‖₊ = 1 :=
  Subtype.ext <| ofRealClm_norm
#align complex.of_real_clm_nnnorm Complex.ofRealClm_nnnorm

end Complex

