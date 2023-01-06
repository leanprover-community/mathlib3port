/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp

! This file was ported from Lean 3 source module linear_algebra.matrix.pos_def
! leanprover-community/mathlib commit 26f081a2fb920140ed5bc5cc5344e84bcc7cb2b2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.Matrix.Spectrum
import Mathbin.LinearAlgebra.QuadraticForm.Basic

/-! # Positive Definite Matrices
This file defines positive (semi)definite matrices and connects the notion to positive definiteness
of quadratic forms.
## Main definition
 * `matrix.pos_def` : a matrix `M : matrix n n 𝕜` is positive definite if it is hermitian and `xᴴMx`
   is greater than zero for all nonzero `x`.
 * `matrix.pos_semidef` : a matrix `M : matrix n n 𝕜` is positive semidefinite if it is hermitian
   and `xᴴMx` is nonnegative for all `x`.
-/


namespace Matrix

variable {𝕜 : Type _} [IsROrC 𝕜] {m n : Type _} [Fintype m] [Fintype n]

open Matrix

/-- A matrix `M : matrix n n 𝕜` is positive definite if it is hermitian
   and `xᴴMx` is greater than zero for all nonzero `x`. -/
def PosDef (M : Matrix n n 𝕜) :=
  M.IsHermitian ∧ ∀ x : n → 𝕜, x ≠ 0 → 0 < IsROrC.re (dotProduct (star x) (M.mulVec x))
#align matrix.pos_def Matrix.PosDef

theorem PosDef.is_hermitian {M : Matrix n n 𝕜} (hM : M.PosDef) : M.IsHermitian :=
  hM.1
#align matrix.pos_def.is_hermitian Matrix.PosDef.is_hermitian

/-- A matrix `M : matrix n n 𝕜` is positive semidefinite if it is hermitian
   and `xᴴMx` is nonnegative for all `x`. -/
def PosSemidef (M : Matrix n n 𝕜) :=
  M.IsHermitian ∧ ∀ x : n → 𝕜, 0 ≤ IsROrC.re (dotProduct (star x) (M.mulVec x))
#align matrix.pos_semidef Matrix.PosSemidef

theorem PosDef.posSemidef {M : Matrix n n 𝕜} (hM : M.PosDef) : M.PosSemidef :=
  by
  refine' ⟨hM.1, _⟩
  intro x
  by_cases hx : x = 0
  · simp only [hx, zero_dot_product, star_zero, IsROrC.zero_re']
  · exact le_of_lt (hM.2 x hx)
#align matrix.pos_def.pos_semidef Matrix.PosDef.posSemidef

theorem PosSemidef.submatrix {M : Matrix n n 𝕜} (hM : M.PosSemidef) (e : m ≃ n) :
    (M.submatrix e e).PosSemidef :=
  by
  refine' ⟨hM.1.submatrix e, fun x => _⟩
  have : (M.submatrix (⇑e) ⇑e).mulVec x = (M.mul_vec fun i : n => x (e.symm i)) ∘ e :=
    by
    ext i
    dsimp only [(· ∘ ·), mul_vec, dot_product]
    rw [Finset.sum_bij' (fun i _ => e i) _ _ fun i _ => e.symm i] <;>
      simp only [eq_self_iff_true, imp_true_iff, Equiv.symm_apply_apply, Finset.mem_univ,
        submatrix_apply, Equiv.apply_symm_apply]
  rw [this]
  convert hM.2 fun i => x (e.symm i) using 3
  unfold dot_product
  rw [Finset.sum_bij' (fun i _ => e i) _ _ fun i _ => e.symm i] <;>
    simp only [eq_self_iff_true, imp_true_iff, Equiv.symm_apply_apply, Finset.mem_univ,
      submatrix_apply, Equiv.apply_symm_apply, Pi.star_apply]
#align matrix.pos_semidef.submatrix Matrix.PosSemidef.submatrix

@[simp]
theorem pos_semidef_submatrix_equiv {M : Matrix n n 𝕜} (e : m ≃ n) :
    (M.submatrix e e).PosSemidef ↔ M.PosSemidef :=
  ⟨fun h => by simpa using h.submatrix e.symm, fun h => h.submatrix _⟩
#align matrix.pos_semidef_submatrix_equiv Matrix.pos_semidef_submatrix_equiv

theorem PosDef.transpose {M : Matrix n n 𝕜} (hM : M.PosDef) : Mᵀ.PosDef :=
  by
  refine' ⟨is_hermitian.transpose hM.1, fun x hx => _⟩
  convert hM.2 (star x) (star_ne_zero.2 hx) using 2
  rw [mul_vec_transpose, Matrix.dot_product_mul_vec, star_star, dot_product_comm]
#align matrix.pos_def.transpose Matrix.PosDef.transpose

theorem posDefOfToQuadraticForm' [DecidableEq n] {M : Matrix n n ℝ} (hM : M.IsSymm)
    (hMq : M.toQuadraticForm'.PosDef) : M.PosDef :=
  by
  refine' ⟨hM, fun x hx => _⟩
  simp only [to_quadratic_form', QuadraticForm.PosDef, BilinForm.to_quadratic_form_apply,
    Matrix.to_bilin'_apply'] at hMq
  apply hMq x hx
#align matrix.pos_def_of_to_quadratic_form' Matrix.posDefOfToQuadraticForm'

theorem posDefToQuadraticForm' [DecidableEq n] {M : Matrix n n ℝ} (hM : M.PosDef) :
    M.toQuadraticForm'.PosDef := by
  intro x hx
  simp only [to_quadratic_form', BilinForm.to_quadratic_form_apply, Matrix.to_bilin'_apply']
  apply hM.2 x hx
#align matrix.pos_def_to_quadratic_form' Matrix.posDefToQuadraticForm'

namespace PosDef

variable {M : Matrix n n ℝ} (hM : M.PosDef)

include hM

theorem det_pos [DecidableEq n] : 0 < det M :=
  by
  rw [hM.is_hermitian.det_eq_prod_eigenvalues]
  apply Finset.prod_pos
  intro i _
  rw [hM.is_hermitian.eigenvalues_eq]
  apply hM.2 _ fun h => _
  have h_det : hM.is_hermitian.eigenvector_matrixᵀ.det = 0 :=
    Matrix.det_eq_zero_of_row_eq_zero i fun j => congr_fun h j
  simpa only [h_det, not_isUnit_zero] using
    is_unit_det_of_invertible hM.is_hermitian.eigenvector_matrixᵀ
#align matrix.pos_def.det_pos Matrix.PosDef.det_pos

end PosDef

end Matrix

namespace QuadraticForm

variable {n : Type _} [Fintype n]

theorem posDefOfToMatrix' [DecidableEq n] {Q : QuadraticForm ℝ (n → ℝ)} (hQ : Q.toMatrix'.PosDef) :
    Q.PosDef :=
  by
  rw [← to_quadratic_form_associated ℝ Q, ← bilin_form.to_matrix'.left_inv ((associated_hom _) Q)]
  apply Matrix.posDefToQuadraticForm' hQ
#align quadratic_form.pos_def_of_to_matrix' QuadraticForm.posDefOfToMatrix'

theorem posDefToMatrix' [DecidableEq n] {Q : QuadraticForm ℝ (n → ℝ)} (hQ : Q.PosDef) :
    Q.toMatrix'.PosDef :=
  by
  rw [← to_quadratic_form_associated ℝ Q, ←
    bilin_form.to_matrix'.left_inv ((associated_hom _) Q)] at hQ
  apply Matrix.posDefOfToQuadraticForm' (is_symm_to_matrix' Q) hQ
#align quadratic_form.pos_def_to_matrix' QuadraticForm.posDefToMatrix'

end QuadraticForm

namespace Matrix

variable {𝕜 : Type _} [IsROrC 𝕜] {n : Type _} [Fintype n]

/-- A positive definite matrix `M` induces an inner product `⟪x, y⟫ = xᴴMy`. -/
noncomputable def InnerProductSpace.ofMatrix {M : Matrix n n 𝕜} (hM : M.PosDef) :
    InnerProductSpace 𝕜 (n → 𝕜) :=
  InnerProductSpace.ofCore
    { inner := fun x y => dotProduct (star x) (M.mulVec y)
      conj_sym := fun x y => by
        rw [star_dot_product, star_ring_end_apply, star_star, star_mul_vec, dot_product_mul_vec,
          hM.is_hermitian.eq]
      nonneg_re := fun x => by
        by_cases h : x = 0
        · simp [h]
        · exact le_of_lt (hM.2 x h)
      definite := fun x hx => by
        by_contra' h
        simpa [hx, lt_self_iff_false] using hM.2 x h
      add_left := by simp only [star_add, add_dot_product, eq_self_iff_true, forall_const]
      smul_left := fun x y r => by
        rw [← smul_eq_mul, ← smul_dot_product, star_ring_end_apply, ← star_smul] }
#align matrix.inner_product_space.of_matrix Matrix.InnerProductSpace.ofMatrix

end Matrix

