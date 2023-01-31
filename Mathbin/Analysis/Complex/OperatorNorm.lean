/-
Copyright (c) Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

! This file was ported from Lean 3 source module analysis.complex.operator_norm
! leanprover-community/mathlib commit bcfa726826abd57587355b4b5b7e78ad6527b7e4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Complex.Basic
import Mathbin.Analysis.NormedSpace.OperatorNorm
import Mathbin.Data.Complex.Determinant

/-! # The basic continuous linear maps associated to `ℂ`

The continuous linear maps `complex.re_clm` (real part), `complex.im_clm` (imaginary part),
`complex.conj_cle` (conjugation), and `complex.of_real_clm` (inclusion of `ℝ`) were introduced in
`analysis.complex.operator_norm`.  This file contains a few calculations requiring more imports:
the operator norm and (for `complex.conj_cle`) the determinant.
-/


open ContinuousLinearMap

namespace Complex

/-- The determinant of `conj_lie`, as a linear map. -/
@[simp]
theorem det_conjLie : (conjLie.toLinearEquiv : ℂ →ₗ[ℝ] ℂ).det = -1 :=
  det_conj_ae
#align complex.det_conj_lie Complex.det_conjLie

/-- The determinant of `conj_lie`, as a linear equiv. -/
@[simp]
theorem linearEquiv_det_conjLie : conjLie.toLinearEquiv.det = -1 :=
  linear_equiv_det_conj_ae
#align complex.linear_equiv_det_conj_lie Complex.linearEquiv_det_conjLie

@[simp]
theorem reClm_norm : ‖re_clm‖ = 1 :=
  le_antisymm (LinearMap.mkContinuous_norm_le _ zero_le_one _) <|
    calc
      1 = ‖reClm 1‖ := by simp
      _ ≤ ‖re_clm‖ := unit_le_op_norm _ _ (by simp)
      
#align complex.re_clm_norm Complex.reClm_norm

@[simp]
theorem reClm_nnnorm : ‖re_clm‖₊ = 1 :=
  Subtype.ext reClm_norm
#align complex.re_clm_nnnorm Complex.reClm_nnnorm

@[simp]
theorem imClm_norm : ‖im_clm‖ = 1 :=
  le_antisymm (LinearMap.mkContinuous_norm_le _ zero_le_one _) <|
    calc
      1 = ‖imClm i‖ := by simp
      _ ≤ ‖im_clm‖ := unit_le_op_norm _ _ (by simp)
      
#align complex.im_clm_norm Complex.imClm_norm

@[simp]
theorem imClm_nnnorm : ‖im_clm‖₊ = 1 :=
  Subtype.ext imClm_norm
#align complex.im_clm_nnnorm Complex.imClm_nnnorm

@[simp]
theorem conjCle_norm : ‖(conjCle : ℂ →L[ℝ] ℂ)‖ = 1 :=
  conjLie.toLinearIsometry.norm_to_continuous_linear_map
#align complex.conj_cle_norm Complex.conjCle_norm

@[simp]
theorem conjCle_nnorm : ‖(conjCle : ℂ →L[ℝ] ℂ)‖₊ = 1 :=
  Subtype.ext conjCle_norm
#align complex.conj_cle_nnorm Complex.conjCle_nnorm

@[simp]
theorem ofRealClm_norm : ‖of_real_clm‖ = 1 :=
  ofRealLi.norm_to_continuous_linear_map
#align complex.of_real_clm_norm Complex.ofRealClm_norm

@[simp]
theorem ofRealClm_nnnorm : ‖of_real_clm‖₊ = 1 :=
  Subtype.ext <| of_real_clm_norm
#align complex.of_real_clm_nnnorm Complex.ofRealClm_nnnorm

end Complex

