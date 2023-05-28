/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers

! This file was ported from Lean 3 source module data.complex.determinant
! leanprover-community/mathlib commit fe8d0ff42c3c24d789f491dc2622b6cac3d61564
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Complex.Module
import Mathbin.LinearAlgebra.Determinant

/-!
# Determinants of maps in the complex numbers as a vector space over `ℝ`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides results about the determinants of maps in the complex numbers as a vector
space over `ℝ`.

-/


namespace Complex

/- warning: complex.det_conj_ae -> Complex.det_conjAe is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align complex.det_conj_ae Complex.det_conjAeₓ'. -/
/-- The determinant of `conj_ae`, as a linear map. -/
@[simp]
theorem det_conjAe : conjAe.toLinearMap.det = -1 :=
  by
  rw [← LinearMap.det_toMatrix basis_one_I, to_matrix_conj_ae, Matrix.det_fin_two_of]
  simp
#align complex.det_conj_ae Complex.det_conjAe

/- warning: complex.linear_equiv_det_conj_ae -> Complex.linearEquiv_det_conjAe is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align complex.linear_equiv_det_conj_ae Complex.linearEquiv_det_conjAeₓ'. -/
/-- The determinant of `conj_ae`, as a linear equiv. -/
@[simp]
theorem linearEquiv_det_conjAe : conjAe.toLinearEquiv.det = -1 := by
  rw [← Units.eq_iff, LinearEquiv.coe_det, ← LinearEquiv.toLinearMap_eq_coe,
    AlgEquiv.toLinearEquiv_toLinearMap, det_conj_ae, Units.coe_neg_one]
#align complex.linear_equiv_det_conj_ae Complex.linearEquiv_det_conjAe

end Complex

