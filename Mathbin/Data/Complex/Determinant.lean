/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers

! This file was ported from Lean 3 source module data.complex.determinant
! leanprover-community/mathlib commit d3e8e0a0237c10c2627bf52c246b15ff8e7df4c0
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Complex.Module
import Mathbin.LinearAlgebra.Determinant

/-!
# Determinants of maps in the complex numbers as a vector space over `ℝ`

This file provides results about the determinants of maps in the complex numbers as a vector
space over `ℝ`.

-/


namespace Complex

/-- The determinant of `conj_ae`, as a linear map. -/
@[simp]
theorem det_conj_ae : conjAe.toLinearMap.det = -1 :=
  by
  rw [← LinearMap.det_to_matrix basis_one_I, to_matrix_conj_ae, Matrix.det_fin_two_of]
  simp
#align complex.det_conj_ae Complex.det_conj_ae

/-- The determinant of `conj_ae`, as a linear equiv. -/
@[simp]
theorem linear_equiv_det_conj_ae : conjAe.toLinearEquiv.det = -1 := by
  rw [← Units.eq_iff, LinearEquiv.coe_det, ← LinearEquiv.to_linear_map_eq_coe,
    AlgEquiv.to_linear_equiv_to_linear_map, det_conj_ae, Units.coe_neg_one]
#align complex.linear_equiv_det_conj_ae Complex.linear_equiv_det_conj_ae

end Complex

