/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Jeremy Avigad, Johan Commelin

! This file was ported from Lean 3 source module linear_algebra.matrix.schur_complement
! leanprover-community/mathlib commit 0ebfdb71919ac6ca5d7fbc61a082fa2519556818
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.Matrix.NonsingularInverse
import Mathbin.LinearAlgebra.Matrix.PosDef

/-! # Schur complement

This file proves properties of the Schur complement `D - C A⁻¹ B` of a block matrix `[A B; C D]`.

The determinant of a block matrix in terms of the Schur complement is expressed in the lemmas
`matrix.det_from_blocks₁₁` and `matrix.det_from_blocks₂₂` in the file
`linear_algebra.matrix.nonsingular_inverse`.

## Main result

 * `matrix.schur_complement_pos_semidef_iff` : If a matrix `A` is positive definite, then `[A B; Bᴴ
  D]` is postive semidefinite if and only if `D - Bᴴ A⁻¹ B` is postive semidefinite.

-/


namespace Matrix

open Matrix

variable {n : Type _} {m : Type _} {𝕜 : Type _} [IsROrC 𝕜]

-- mathport name: «expr ⊕ᵥ »
scoped infixl:65 " ⊕ᵥ " => Sum.elim

theorem schur_complement_eq₁₁ [Fintype m] [DecidableEq m] [Fintype n] {A : Matrix m m 𝕜}
    (B : Matrix m n 𝕜) (D : Matrix n n 𝕜) (x : m → 𝕜) (y : n → 𝕜) [Invertible A]
    (hA : A.IsHermitian) :
    vecMul (star (x ⊕ᵥ y)) (fromBlocks A B Bᴴ D) ⬝ᵥ (x ⊕ᵥ y) =
      vecMul (star (x + (A⁻¹ ⬝ B).mulVec y)) A ⬝ᵥ (x + (A⁻¹ ⬝ B).mulVec y) +
        vecMul (star y) (D - Bᴴ ⬝ A⁻¹ ⬝ B) ⬝ᵥ y :=
  by
  simp [Function.star_sum_elim, fromBlocks_mulVec, vecMul_fromBlocks, add_vecMul, dotProduct_mulVec,
    vecMul_sub, Matrix.mul_assoc, vecMul_mulVec, hA.eq, conjTranspose_nonsing_inv, star_mulVec]
  abel
#align matrix.schur_complement_eq₁₁ Matrix.schur_complement_eq₁₁

theorem schur_complement_eq₂₂ [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m m 𝕜)
    (B : Matrix m n 𝕜) {D : Matrix n n 𝕜} (x : m → 𝕜) (y : n → 𝕜) [Invertible D]
    (hD : D.IsHermitian) :
    vecMul (star (x ⊕ᵥ y)) (fromBlocks A B Bᴴ D) ⬝ᵥ (x ⊕ᵥ y) =
      vecMul (star ((D⁻¹ ⬝ Bᴴ).mulVec x + y)) D ⬝ᵥ ((D⁻¹ ⬝ Bᴴ).mulVec x + y) +
        vecMul (star x) (A - B ⬝ D⁻¹ ⬝ Bᴴ) ⬝ᵥ x :=
  by
  simp [Function.star_sum_elim, fromBlocks_mulVec, vecMul_fromBlocks, add_vecMul, dotProduct_mulVec,
    vecMul_sub, Matrix.mul_assoc, vecMul_mulVec, hD.eq, conjTranspose_nonsing_inv, star_mulVec]
  abel
#align matrix.schur_complement_eq₂₂ Matrix.schur_complement_eq₂₂

end Matrix

namespace Matrix

open Matrix

variable {n : Type _} {m : Type _} {𝕜 : Type _} [IsROrC 𝕜]

theorem IsHermitian.from_blocks₁₁ [Fintype m] [DecidableEq m] {A : Matrix m m 𝕜} (B : Matrix m n 𝕜)
    (D : Matrix n n 𝕜) (hA : A.IsHermitian) :
    (fromBlocks A B Bᴴ D).IsHermitian ↔ (D - Bᴴ ⬝ A⁻¹ ⬝ B).IsHermitian :=
  by
  have hBAB : (Bᴴ ⬝ A⁻¹ ⬝ B).IsHermitian :=
    by
    apply isHermitian_conjTranspose_mul_mul
    apply hA.inv
  rw [isHermitian_fromBlocks_iff]
  constructor
  · intro h
    apply IsHermitian.sub h.2.2.2 hBAB
  · intro h
    refine' ⟨hA, rfl, conjTranspose_conjTranspose B, _⟩
    rw [← sub_add_cancel D]
    apply IsHermitian.add h hBAB
#align matrix.is_hermitian.from_blocks₁₁ Matrix.IsHermitian.from_blocks₁₁

theorem IsHermitian.from_blocks₂₂ [Fintype n] [DecidableEq n] (A : Matrix m m 𝕜) (B : Matrix m n 𝕜)
    {D : Matrix n n 𝕜} (hD : D.IsHermitian) :
    (fromBlocks A B Bᴴ D).IsHermitian ↔ (A - B ⬝ D⁻¹ ⬝ Bᴴ).IsHermitian :=
  by
  rw [← isHermitian_submatrix_equiv (Equiv.sumComm n m), Equiv.sumComm_apply,
    fromBlocks_submatrix_sum_swap_sum_swap]
  convert IsHermitian.from_blocks₁₁ _ _ hD <;> simp
#align matrix.is_hermitian.from_blocks₂₂ Matrix.IsHermitian.from_blocks₂₂

theorem PosSemidef.from_blocks₁₁ [Fintype m] [DecidableEq m] [Fintype n] {A : Matrix m m 𝕜}
    (B : Matrix m n 𝕜) (D : Matrix n n 𝕜) (hA : A.PosDef) [Invertible A] :
    (fromBlocks A B Bᴴ D).PosSemidef ↔ (D - Bᴴ ⬝ A⁻¹ ⬝ B).PosSemidef :=
  by
  rw [PosSemidef, IsHermitian.from_blocks₁₁ _ _ hA.1]
  constructor
  · refine' fun h => ⟨h.1, fun x => _⟩
    have := h.2 (-(A⁻¹ ⬝ B).mulVec x ⊕ᵥ x)
    rw [dotProduct_mulVec, schur_complement_eq₁₁ B D _ _ hA.1, neg_add_self, dotProduct_zero,
      zero_add] at this
    rw [dotProduct_mulVec]
    exact this
  · refine' fun h => ⟨h.1, fun x => _⟩
    rw [dotProduct_mulVec, ← Sum.elim_comp_inl_inr x, schur_complement_eq₁₁ B D _ _ hA.1, map_add]
    apply le_add_of_nonneg_of_le
    · rw [← dotProduct_mulVec]
      apply hA.pos_semidef.2
    · rw [← dotProduct_mulVec]
      apply h.2
#align matrix.pos_semidef.from_blocks₁₁ Matrix.PosSemidef.from_blocks₁₁

theorem PosSemidef.from_blocks₂₂ [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m m 𝕜)
    (B : Matrix m n 𝕜) {D : Matrix n n 𝕜} (hD : D.PosDef) [Invertible D] :
    (fromBlocks A B Bᴴ D).PosSemidef ↔ (A - B ⬝ D⁻¹ ⬝ Bᴴ).PosSemidef :=
  by
  rw [← posSemidef_submatrix_equiv (Equiv.sumComm n m), Equiv.sumComm_apply,
    fromBlocks_submatrix_sum_swap_sum_swap]
  convert PosSemidef.from_blocks₁₁ _ _ hD <;> first |infer_instance|simp
#align matrix.pos_semidef.from_blocks₂₂ Matrix.PosSemidef.from_blocks₂₂

end Matrix

