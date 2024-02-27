/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
import LinearAlgebra.Matrix.Spectrum
import LinearAlgebra.QuadraticForm.Basic

#align_import linear_algebra.matrix.pos_def from "leanprover-community/mathlib"@"cff8231f04dfa33fd8f2f45792eebd862ef30cad"

/-! # Positive Definite Matrices

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
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

open scoped Matrix

#print Matrix.PosDef /-
/-- A matrix `M : matrix n n 𝕜` is positive definite if it is hermitian
   and `xᴴMx` is greater than zero for all nonzero `x`. -/
def PosDef (M : Matrix n n 𝕜) :=
  M.IsHermitian ∧ ∀ x : n → 𝕜, x ≠ 0 → 0 < IsROrC.re (dotProduct (star x) (M.mulVec x))
#align matrix.pos_def Matrix.PosDef
-/

#print Matrix.PosDef.isHermitian /-
theorem PosDef.isHermitian {M : Matrix n n 𝕜} (hM : M.PosDef) : M.IsHermitian :=
  hM.1
#align matrix.pos_def.is_hermitian Matrix.PosDef.isHermitian
-/

#print Matrix.PosSemidef /-
/-- A matrix `M : matrix n n 𝕜` is positive semidefinite if it is hermitian
   and `xᴴMx` is nonnegative for all `x`. -/
def PosSemidef (M : Matrix n n 𝕜) :=
  M.IsHermitian ∧ ∀ x : n → 𝕜, 0 ≤ IsROrC.re (dotProduct (star x) (M.mulVec x))
#align matrix.pos_semidef Matrix.PosSemidef
-/

#print Matrix.PosDef.posSemidef /-
theorem PosDef.posSemidef {M : Matrix n n 𝕜} (hM : M.PosDef) : M.PosSemidef :=
  by
  refine' ⟨hM.1, _⟩
  intro x
  by_cases hx : x = 0
  · simp only [hx, zero_dot_product, star_zero, IsROrC.zero_re']
  · exact le_of_lt (hM.2 x hx)
#align matrix.pos_def.pos_semidef Matrix.PosDef.posSemidef
-/

#print Matrix.PosSemidef.submatrix /-
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
-/

#print Matrix.posSemidef_submatrix_equiv /-
@[simp]
theorem posSemidef_submatrix_equiv {M : Matrix n n 𝕜} (e : m ≃ n) :
    (M.submatrix e e).PosSemidef ↔ M.PosSemidef :=
  ⟨fun h => by simpa using h.submatrix e.symm, fun h => h.submatrix _⟩
#align matrix.pos_semidef_submatrix_equiv Matrix.posSemidef_submatrix_equiv
-/

#print Matrix.PosDef.transpose /-
theorem PosDef.transpose {M : Matrix n n 𝕜} (hM : M.PosDef) : Mᵀ.PosDef :=
  by
  refine' ⟨is_hermitian.transpose hM.1, fun x hx => _⟩
  convert hM.2 (star x) (star_ne_zero.2 hx) using 2
  rw [mul_vec_transpose, Matrix.dotProduct_mulVec, star_star, dot_product_comm]
#align matrix.pos_def.transpose Matrix.PosDef.transpose
-/

#print Matrix.PosDef.of_toQuadraticForm' /-
theorem Matrix.PosDef.of_toQuadraticForm' [DecidableEq n] {M : Matrix n n ℝ} (hM : M.IsSymm)
    (hMq : M.toQuadraticForm'.PosDef) : M.PosDef :=
  by
  refine' ⟨hM, fun x hx => _⟩
  simp only [to_quadratic_form', QuadraticForm.PosDef, LinearMap.BilinForm.toQuadraticForm_apply,
    Matrix.toBilin'_apply'] at hMq 
  apply hMq x hx
#align matrix.pos_def_of_to_quadratic_form' Matrix.PosDef.of_toQuadraticForm'
-/

#print Matrix.PosDef.toQuadraticForm' /-
theorem Matrix.PosDef.toQuadraticForm' [DecidableEq n] {M : Matrix n n ℝ} (hM : M.PosDef) :
    M.toQuadraticForm'.PosDef := by
  intro x hx
  simp only [to_quadratic_form', LinearMap.BilinForm.toQuadraticForm_apply, Matrix.toBilin'_apply']
  apply hM.2 x hx
#align matrix.pos_def_to_quadratic_form' Matrix.PosDef.toQuadraticForm'
-/

namespace PosDef

variable {M : Matrix n n ℝ} (hM : M.PosDef)

#print Matrix.PosDef.det_pos /-
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
-/

end PosDef

end Matrix

namespace QuadraticForm

variable {n : Type _} [Fintype n]

#print QuadraticForm.posDef_of_toMatrix' /-
theorem posDef_of_toMatrix' [DecidableEq n] {Q : QuadraticForm ℝ (n → ℝ)}
    (hQ : Q.toMatrix'.PosDef) : Q.PosDef :=
  by
  rw [← to_quadratic_form_associated ℝ Q, ← bilin_form.to_matrix'.left_inv ((associated_hom _) Q)]
  apply Matrix.PosDef.toQuadraticForm' hQ
#align quadratic_form.pos_def_of_to_matrix' QuadraticForm.posDef_of_toMatrix'
-/

#print QuadraticForm.posDef_toMatrix' /-
theorem posDef_toMatrix' [DecidableEq n] {Q : QuadraticForm ℝ (n → ℝ)} (hQ : Q.PosDef) :
    Q.toMatrix'.PosDef :=
  by
  rw [← to_quadratic_form_associated ℝ Q, ←
    bilin_form.to_matrix'.left_inv ((associated_hom _) Q)] at hQ 
  apply Matrix.PosDef.of_toQuadraticForm' (is_symm_to_matrix' Q) hQ
#align quadratic_form.pos_def_to_matrix' QuadraticForm.posDef_toMatrix'
-/

end QuadraticForm

namespace Matrix

variable {𝕜 : Type _} [IsROrC 𝕜] {n : Type _} [Fintype n]

#print Matrix.NormedAddCommGroup.ofMatrix /-
/-- A positive definite matrix `M` induces a norm `‖x‖ = sqrt (re xᴴMx)`. -/
@[reducible]
noncomputable def NormedAddCommGroup.ofMatrix {M : Matrix n n 𝕜} (hM : M.PosDef) :
    NormedAddCommGroup (n → 𝕜) :=
  @InnerProductSpace.Core.toNormedAddCommGroup _ _ _ _ _
    { inner := fun x y => dotProduct (star x) (M.mulVec y)
      conj_symm := fun x y => by
        dsimp only [Inner.inner] <;>
          rw [star_dot_product, starRingEnd_apply, star_star, star_mul_vec, dot_product_mul_vec,
            hM.is_hermitian.eq]
      nonneg_re := fun x => by
        by_cases h : x = 0
        · simp [h]
        · exact le_of_lt (hM.2 x h)
      definite := fun x (hx : dotProduct _ _ = 0) =>
        by
        by_contra! h
        simpa [hx, lt_irrefl] using hM.2 x h
      add_left := by simp only [star_add, add_dot_product, eq_self_iff_true, forall_const]
      smul_left := fun x y r => by
        rw [← smul_eq_mul, ← smul_dot_product, starRingEnd_apply, ← star_smul] }
#align matrix.normed_add_comm_group.of_matrix Matrix.NormedAddCommGroup.ofMatrix
-/

#print Matrix.InnerProductSpace.ofMatrix /-
/-- A positive definite matrix `M` induces an inner product `⟪x, y⟫ = xᴴMy`. -/
def InnerProductSpace.ofMatrix {M : Matrix n n 𝕜} (hM : M.PosDef) :
    @InnerProductSpace 𝕜 (n → 𝕜) _ (NormedAddCommGroup.ofMatrix hM) :=
  InnerProductSpace.ofCore _
#align matrix.inner_product_space.of_matrix Matrix.InnerProductSpace.ofMatrix
-/

end Matrix

