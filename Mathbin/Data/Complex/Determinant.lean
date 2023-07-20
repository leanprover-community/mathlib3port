/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathbin.Data.Complex.Module
import Mathbin.LinearAlgebra.Determinant

#align_import data.complex.determinant from "leanprover-community/mathlib"@"fe8d0ff42c3c24d789f491dc2622b6cac3d61564"

/-!
# Determinants of maps in the complex numbers as a vector space over `ℝ`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides results about the determinants of maps in the complex numbers as a vector
space over `ℝ`.

-/


namespace Complex

#print Complex.det_conjAe /-
/-- The determinant of `conj_ae`, as a linear map. -/
@[simp]
theorem det_conjAe : conjAe.toLinearMap.det = -1 :=
  by
  rw [← LinearMap.det_toMatrix basis_one_I, to_matrix_conj_ae, Matrix.det_fin_two_of]
  simp
#align complex.det_conj_ae Complex.det_conjAe
-/

#print Complex.linearEquiv_det_conjAe /-
/-- The determinant of `conj_ae`, as a linear equiv. -/
@[simp]
theorem linearEquiv_det_conjAe : conjAe.toLinearEquiv.det = -1 := by
  rw [← Units.eq_iff, LinearEquiv.coe_det, ← LinearEquiv.toLinearMap_eq_coe,
    AlgEquiv.toLinearEquiv_toLinearMap, det_conj_ae, Units.coe_neg_one]
#align complex.linear_equiv_det_conj_ae Complex.linearEquiv_det_conjAe
-/

end Complex

