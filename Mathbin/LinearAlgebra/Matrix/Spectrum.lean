/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
import Mathbin.Analysis.InnerProductSpace.Spectrum
import Mathbin.LinearAlgebra.Matrix.Hermitian

/-! # Spectral theory of hermitian matrices

This file proves the spectral theorem for matrices. The proof of the spectral theorem is based on
the spectral theorem for linear maps (`diagonalization_basis_apply_self_apply`).

## Tags

spectral theorem, diagonalization theorem

-/


namespace Matrix

variable {𝕜 : Type _} [IsROrC 𝕜] [DecidableEq 𝕜] {n : Type _} [Fintype n] [DecidableEq n]

variable {A : Matrix n n 𝕜}

open Matrix

open BigOperators

namespace IsHermitian

variable (hA : A.IsHermitian)

/-- The eigenvalues of a hermitian matrix, indexed by `fin (fintype.card n)` where `n` is the index
type of the matrix. -/
noncomputable def eigenvalues₀ : Finₓ (Fintype.card n) → ℝ :=
  (is_hermitian_iff_is_symmetric.1 hA).Eigenvalues finrank_euclidean_space

/-- The eigenvalues of a hermitian matrix, reusing the index `n` of the matrix entries. -/
noncomputable def eigenvalues : n → ℝ := fun i => hA.eigenvalues₀ <| (Fintype.equivOfCardEq (Fintype.card_fin _)).symm i

/-- A choice of an orthonormal basis of eigenvectors of a hermitian matrix. -/
noncomputable def eigenvectorBasis : OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n) :=
  ((is_hermitian_iff_is_symmetric.1 hA).eigenvectorBasis finrank_euclidean_space).reindex
    (Fintype.equivOfCardEq (Fintype.card_fin _))

/-- A matrix whose columns are an orthonormal basis of eigenvectors of a hermitian matrix. -/
noncomputable def eigenvectorMatrix : Matrix n n 𝕜 :=
  (Pi.basisFun 𝕜 n).toMatrix (eigenvectorBasis hA).toBasis

/-- The inverse of `eigenvector_matrix` -/
noncomputable def eigenvectorMatrixInv : Matrix n n 𝕜 :=
  (eigenvectorBasis hA).toBasis.toMatrix (Pi.basisFun 𝕜 n)

theorem eigenvector_matrix_mul_inv : hA.eigenvectorMatrix ⬝ hA.eigenvectorMatrixInv = 1 := by
  apply Basis.to_matrix_mul_to_matrix_flip

noncomputable instance : Invertible hA.eigenvectorMatrixInv :=
  invertibleOfLeftInverse _ _ hA.eigenvector_matrix_mul_inv

noncomputable instance : Invertible hA.eigenvectorMatrix :=
  invertibleOfRightInverse _ _ hA.eigenvector_matrix_mul_inv

theorem eigenvector_matrix_apply (i j : n) : hA.eigenvectorMatrix i j = hA.eigenvectorBasis j i := by
  simp only [eigenvector_matrix, Basis.to_matrix_apply, OrthonormalBasis.coe_to_basis, Pi.basis_fun_repr]

theorem eigenvector_matrix_inv_apply (i j : n) : hA.eigenvectorMatrixInv i j = star (hA.eigenvectorBasis i j) := by
  rw [eigenvector_matrix_inv, Basis.to_matrix_apply, OrthonormalBasis.coe_to_basis_repr_apply, Pi.basis_fun_apply,
    LinearMap.coe_std_basis, OrthonormalBasis.repr_apply_apply]
  change inner (hA.eigenvector_basis i) (EuclideanSpace.single j 1) = _
  rw [EuclideanSpace.inner_single_right]
  simp only [one_mulₓ, conj_transpose_apply, IsROrC.star_def]

theorem conj_transpose_eigenvector_matrix_inv : hA.eigenvectorMatrixInvᴴ = hA.eigenvectorMatrix := by
  ext i j
  rw [conj_transpose_apply, eigenvector_matrix_inv_apply, eigenvector_matrix_apply, star_star]

theorem conj_transpose_eigenvector_matrix : hA.eigenvectorMatrixᴴ = hA.eigenvectorMatrixInv := by
  rw [← conj_transpose_eigenvector_matrix_inv, conj_transpose_conj_transpose]

/-- *Diagonalization theorem*, *spectral theorem* for matrices; A hermitian matrix can be
diagonalized by a change of basis.

For the spectral theorem on linear maps, see `diagonalization_basis_apply_self_apply`. -/
theorem spectral_theorem : hA.eigenvectorMatrixInv ⬝ A = diagonalₓ (coe ∘ hA.Eigenvalues) ⬝ hA.eigenvectorMatrixInv :=
  by
  rw [eigenvector_matrix_inv, basis_to_matrix_basis_fun_mul]
  ext i j
  convert
    @LinearMap.IsSymmetric.diagonalization_basis_apply_self_apply 𝕜 _ _ (PiLp 2 fun _ : n => 𝕜) _ A.to_lin'
      (is_hermitian_iff_is_symmetric.1 hA) _ (Fintype.card n) finrank_euclidean_space (EuclideanSpace.single j 1)
      ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i)
  · rw [eigenvector_basis, to_lin'_apply]
    simp only [Basis.toMatrix, Basis.coe_to_orthonormal_basis_repr, Basis.equiv_fun_apply]
    simp_rw [OrthonormalBasis.coe_to_basis_repr_apply, OrthonormalBasis.reindex_repr, EuclideanSpace.single,
      PiLp.equiv_symm_apply', mul_vec_single, mul_oneₓ]
    rfl
    
  · simp only [diagonal_mul, (· ∘ ·), eigenvalues, eigenvector_basis]
    rw [Basis.to_matrix_apply, OrthonormalBasis.coe_to_basis_repr_apply, OrthonormalBasis.reindex_repr,
      Pi.basis_fun_apply, eigenvalues₀, LinearMap.coe_std_basis, EuclideanSpace.single, PiLp.equiv_symm_apply']
    

theorem eigenvalues_eq (i : n) :
    hA.Eigenvalues i = IsROrC.re (star (hA.eigenvectorMatrixᵀ i) ⬝ᵥ A.mulVec (hA.eigenvectorMatrixᵀ i)) := by
  have := hA.spectral_theorem
  rw [← Matrix.mul_inv_eq_iff_eq_mul_of_invertible] at this
  have := congr_arg IsROrC.re (congr_fun (congr_fun this i) i)
  rw [diagonal_apply_eq, IsROrC.of_real_re, inv_eq_left_inv hA.eigenvector_matrix_mul_inv, ←
    conj_transpose_eigenvector_matrix, mul_mul_apply] at this
  exact this.symm

/-- The determinant of a hermitian matrix is the product of its eigenvalues. -/
theorem det_eq_prod_eigenvalues : det A = ∏ i, hA.Eigenvalues i := by
  apply mul_left_cancel₀ (det_ne_zero_of_left_inverse (eigenvector_matrix_mul_inv hA))
  rw [← det_mul, spectral_theorem, det_mul, mul_comm, det_diagonal]

end IsHermitian

end Matrix

