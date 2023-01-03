/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen

! This file was ported from Lean 3 source module linear_algebra.matrix.dual
! leanprover-community/mathlib commit 9830a300340708eaa85d477c3fb96dd25f9468a5
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.Dual
import Mathbin.LinearAlgebra.Matrix.ToLin

/-!
# Dual space, linear maps and matrices.

This file contains some results on the matrix corresponding to the
transpose of a linear map (in the dual space).

## Tags

matrix, linear_map, transpose, dual
-/


open Matrix

section Transpose

variable {K V₁ V₂ ι₁ ι₂ : Type _} [Field K] [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂]
  [Module K V₂] [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂] {B₁ : Basis ι₁ K V₁}
  {B₂ : Basis ι₂ K V₂}

@[simp]
theorem LinearMap.to_matrix_transpose (u : V₁ →ₗ[K] V₂) :
    LinearMap.toMatrix B₂.dualBasis B₁.dualBasis (Module.Dual.transpose u) =
      (LinearMap.toMatrix B₁ B₂ u)ᵀ :=
  by
  ext (i j)
  simp only [LinearMap.to_matrix_apply, Module.Dual.transpose_apply, B₁.dual_basis_repr,
    B₂.dual_basis_apply, Matrix.transpose_apply, LinearMap.comp_apply]
#align linear_map.to_matrix_transpose LinearMap.to_matrix_transpose

@[simp]
theorem Matrix.to_lin_transpose (M : Matrix ι₁ ι₂ K) :
    Matrix.toLin B₁.dualBasis B₂.dualBasis Mᵀ = Module.Dual.transpose (Matrix.toLin B₂ B₁ M) :=
  by
  apply (LinearMap.toMatrix B₁.dual_basis B₂.dual_basis).Injective
  rw [LinearMap.to_matrix_to_lin, LinearMap.to_matrix_transpose, LinearMap.to_matrix_to_lin]
#align matrix.to_lin_transpose Matrix.to_lin_transpose

end Transpose

