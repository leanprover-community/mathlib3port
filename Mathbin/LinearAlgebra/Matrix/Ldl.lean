/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp

! This file was ported from Lean 3 source module linear_algebra.matrix.ldl
! leanprover-community/mathlib commit 247a102b14f3cebfee126293341af5f6bed00237
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathbin.LinearAlgebra.Matrix.PosDef

/-! # LDL decomposition

This file proves the LDL-decomposition of matricies: Any positive definite matrix `S` can be
decomposed as `S = LDLᴴ` where `L` is a lower-triangular matrix and `D` is a diagonal matrix.

## Main definitions

 * `LDL.lower` is the lower triangular matrix `L`.
 * `LDL.lower_inv` is the inverse of the lower triangular matrix `L`.
 * `LDL.diag` is the diagonal matrix `D`.

## Main result

* `ldl_decomposition` states that any positive definite matrix can be decomposed as `LDLᴴ`.

## TODO

* Prove that `LDL.lower` is lower triangular from `LDL.lower_inv_triangular`.

-/


variable {𝕜 : Type _} [IsROrC 𝕜]

variable {n : Type _} [LinearOrder n] [IsWellOrder n (· < ·)] [LocallyFiniteOrderBot n]

-- mathport name: «expr⟪ , ⟫»
local notation "⟪" x ", " y "⟫" =>
  @inner 𝕜 (n → 𝕜) (PiLp.innerProductSpace fun _ => 𝕜).toHasInner x y

open Matrix

open Matrix

variable {S : Matrix n n 𝕜} [Fintype n] (hS : S.PosDef)

/-- The inverse of the lower triangular matrix `L` of the LDL-decomposition. It is obtained by
applying Gram-Schmidt-Orthogonalization w.r.t. the inner product induced by `Sᵀ` on the standard
basis vectors `pi.basis_fun`. -/
noncomputable def LDL.lowerInv : Matrix n n 𝕜 :=
  @gramSchmidt 𝕜 (n → 𝕜) _ (InnerProductSpace.ofMatrix hS.transpose) n _ _ _ fun k =>
    Pi.basisFun 𝕜 n k
#align LDL.lower_inv LDL.lowerInv

theorem LDL.lower_inv_eq_gram_schmidt_basis :
    LDL.lowerInv hS =
      ((Pi.basisFun 𝕜 n).toMatrix
          (@gramSchmidtBasis 𝕜 (n → 𝕜) _ (InnerProductSpace.ofMatrix hS.transpose) n _ _ _
            (Pi.basisFun 𝕜 n)))ᵀ :=
  by
  ext (i j)
  rw [LDL.lowerInv, Basis.CoePiBasisFun.to_matrix_eq_transpose, coe_gram_schmidt_basis]
  rfl
#align LDL.lower_inv_eq_gram_schmidt_basis LDL.lower_inv_eq_gram_schmidt_basis

noncomputable instance LDL.invertibleLowerInv : Invertible (LDL.lowerInv hS) :=
  by
  rw [LDL.lower_inv_eq_gram_schmidt_basis]
  haveI :=
    Basis.invertibleToMatrix (Pi.basisFun 𝕜 n)
      (@gramSchmidtBasis 𝕜 (n → 𝕜) _ (inner_product_space.of_matrix hS.transpose) n _ _ _
        (Pi.basisFun 𝕜 n))
  infer_instance
#align LDL.invertible_lower_inv LDL.invertibleLowerInv

theorem LDL.lower_inv_orthogonal {i j : n} (h₀ : i ≠ j) :
    ⟪LDL.lowerInv hS i, Sᵀ.mulVec (LDL.lowerInv hS j)⟫ = 0 :=
  show
    @inner 𝕜 (n → 𝕜) (InnerProductSpace.ofMatrix hS.transpose).toHasInner (LDL.lowerInv hS i)
        (LDL.lowerInv hS j) =
      0
    by apply gram_schmidt_orthogonal _ _ h₀
#align LDL.lower_inv_orthogonal LDL.lower_inv_orthogonal

/-- The entries of the diagonal matrix `D` of the LDL decomposition. -/
noncomputable def LDL.diagEntries : n → 𝕜 := fun i =>
  ⟪star (LDL.lowerInv hS i), S.mulVec (star (LDL.lowerInv hS i))⟫
#align LDL.diag_entries LDL.diagEntries

/-- The diagonal matrix `D` of the LDL decomposition. -/
noncomputable def LDL.diag : Matrix n n 𝕜 :=
  Matrix.diagonal (LDL.diagEntries hS)
#align LDL.diag LDL.diag

theorem LDL.lower_inv_triangular {i j : n} (hij : i < j) : LDL.lowerInv hS i j = 0 := by
  rw [←
    @gram_schmidt_triangular 𝕜 (n → 𝕜) _ (inner_product_space.of_matrix hS.transpose) n _ _ _ i j
      hij (Pi.basisFun 𝕜 n),
    Pi.basis_fun_repr, LDL.lowerInv]
#align LDL.lower_inv_triangular LDL.lower_inv_triangular

/-- Inverse statement of **LDL decomposition**: we can conjugate a positive definite matrix
by some lower triangular matrix and get a diagonal matrix. -/
theorem LDL.diag_eq_lower_inv_conj : LDL.diag hS = LDL.lowerInv hS ⬝ S ⬝ (LDL.lowerInv hS)ᴴ :=
  by
  ext (i j)
  by_cases hij : i = j
  ·
    simpa only [hij, LDL.diag, diagonal_apply_eq, LDL.diagEntries, Matrix.mul_assoc, inner,
      Pi.star_apply, IsROrC.star_def, star_ring_end_self_apply]
  · simp only [LDL.diag, hij, diagonal_apply_ne, Ne.def, not_false_iff, mul_mul_apply]
    rw [conj_transpose, transpose_map, transpose_transpose, dot_product_mul_vec,
      (LDL.lower_inv_orthogonal hS fun h : j = i => hij h.symm).symm, ← inner_conj_sym,
      mul_vec_transpose, EuclideanSpace.inner_eq_star_dot_product, ← IsROrC.star_def, ←
      star_dot_product_star, dot_product_comm, star_star]
    rfl
#align LDL.diag_eq_lower_inv_conj LDL.diag_eq_lower_inv_conj

/-- The lower triangular matrix `L` of the LDL decomposition. -/
noncomputable def LDL.lower :=
  (LDL.lowerInv hS)⁻¹
#align LDL.lower LDL.lower

/-- **LDL decomposition**: any positive definite matrix `S` can be
decomposed as `S = LDLᴴ` where `L` is a lower-triangular matrix and `D` is a diagonal matrix.  -/
theorem LDL.lower_conj_diag : LDL.lower hS ⬝ LDL.diag hS ⬝ (LDL.lower hS)ᴴ = S :=
  by
  rw [LDL.lower, conj_transpose_nonsing_inv, Matrix.mul_assoc,
    Matrix.inv_mul_eq_iff_eq_mul_of_invertible (LDL.lowerInv hS),
    Matrix.mul_inv_eq_iff_eq_mul_of_invertible]
  exact LDL.diag_eq_lower_inv_conj hS
#align LDL.lower_conj_diag LDL.lower_conj_diag

