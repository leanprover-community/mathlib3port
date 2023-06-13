/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Eric Wieser, Jeremy Avigad, Johan Commelin

! This file was ported from Lean 3 source module linear_algebra.matrix.schur_complement
! leanprover-community/mathlib commit 96aa788f3e443efb3dace8a634258a9259364f43
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.Matrix.NonsingularInverse
import Mathbin.LinearAlgebra.Matrix.PosDef

/-! # 2×2 block matrices and the Schur complement

This file proves properties of 2×2 block matrices `[A B; C D]` that relate to the Schur complement
`D - C⬝A⁻¹⬝B`.

## Main results

 * `matrix.det_from_blocks₁₁`, `matrix.det_from_blocks₂₂`: determinant of a block matrix in terms of
   the Schur complement.
 * `matrix.inv_of_from_blocks_zero₂₁_eq`, `matrix.inv_of_from_blocks_zero₁₂_eq`: the inverse of a
   block triangular matrix.
 * `matrix.is_unit_from_blocks_zero₂₁`, `matrix.is_unit_from_blocks_zero₁₂`: invertibility of a
   block triangular matrix.
 * `matrix.det_one_add_mul_comm`: the **Weinstein–Aronszajn identity**.
 * `matrix.schur_complement_pos_semidef_iff` : If a matrix `A` is positive definite, then
  `[A B; Bᴴ D]` is postive semidefinite if and only if `D - Bᴴ A⁻¹ B` is postive semidefinite.

-/


variable {l m n α : Type _}

namespace Matrix

open scoped Matrix

section CommRing

variable [Fintype l] [Fintype m] [Fintype n]

variable [DecidableEq l] [DecidableEq m] [DecidableEq n]

variable [CommRing α]

/-- LDU decomposition of a block matrix with an invertible top-left corner, using the
Schur complement. -/
theorem fromBlocks_eq_of_invertible₁₁ (A : Matrix m m α) (B : Matrix m n α) (C : Matrix l m α)
    (D : Matrix l n α) [Invertible A] :
    fromBlocks A B C D =
      fromBlocks 1 0 (C ⬝ ⅟ A) 1 ⬝ fromBlocks A 0 0 (D - C ⬝ ⅟ A ⬝ B) ⬝
        fromBlocks 1 (⅟ A ⬝ B) 0 1 :=
  by
  simp only [from_blocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.one_mul, Matrix.mul_one, Matrix.invOf_mul_self, Matrix.mul_invOf_self_assoc,
    Matrix.mul_invOf_mul_self_cancel, Matrix.mul_assoc, add_sub_cancel'_right]
#align matrix.from_blocks_eq_of_invertible₁₁ Matrix.fromBlocks_eq_of_invertible₁₁

/-- LDU decomposition of a block matrix with an invertible bottom-right corner, using the
Schur complement. -/
theorem fromBlocks_eq_of_invertible₂₂ (A : Matrix l m α) (B : Matrix l n α) (C : Matrix n m α)
    (D : Matrix n n α) [Invertible D] :
    fromBlocks A B C D =
      fromBlocks 1 (B ⬝ ⅟ D) 0 1 ⬝ fromBlocks (A - B ⬝ ⅟ D ⬝ C) 0 0 D ⬝
        fromBlocks 1 0 (⅟ D ⬝ C) 1 :=
  (Matrix.reindex (Equiv.sumComm _ _) (Equiv.sumComm _ _)).Injective <| by
    simpa [reindex_apply, Equiv.sumComm_symm, ← submatrix_mul_equiv _ _ _ (Equiv.sumComm n m), ←
      submatrix_mul_equiv _ _ _ (Equiv.sumComm n l), Equiv.sumComm_apply,
      from_blocks_submatrix_sum_swap_sum_swap] using from_blocks_eq_of_invertible₁₁ D C B A
#align matrix.from_blocks_eq_of_invertible₂₂ Matrix.fromBlocks_eq_of_invertible₂₂

section Triangular

/-! #### Block triangular matrices -/


/-- An upper-block-triangular matrix is invertible if its diagonal is. -/
def fromBlocksZero₂₁Invertible (A : Matrix m m α) (B : Matrix m n α) (D : Matrix n n α)
    [Invertible A] [Invertible D] : Invertible (fromBlocks A B 0 D) :=
  invertibleOfLeftInverse _ (fromBlocks (⅟ A) (-⅟ A ⬝ B ⬝ ⅟ D) 0 (⅟ D)) <| by
    simp_rw [from_blocks_multiply, Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero,
      Matrix.neg_mul, Matrix.invOf_mul_self, Matrix.mul_invOf_mul_self_cancel, add_right_neg,
      from_blocks_one]
#align matrix.from_blocks_zero₂₁_invertible Matrix.fromBlocksZero₂₁Invertible

/-- A lower-block-triangular matrix is invertible if its diagonal is. -/
def fromBlocksZero₁₂Invertible (A : Matrix m m α) (C : Matrix n m α) (D : Matrix n n α)
    [Invertible A] [Invertible D] : Invertible (fromBlocks A 0 C D) :=
  invertibleOfLeftInverse _
      (fromBlocks (⅟ A) 0 (-⅟ D ⬝ C ⬝ ⅟ A)
        (⅟ D)) <|-- a symmetry argument is more work than just copying the proof
  by
    simp_rw [from_blocks_multiply, Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero,
      Matrix.neg_mul, Matrix.invOf_mul_self, Matrix.mul_invOf_mul_self_cancel, add_left_neg,
      from_blocks_one]
#align matrix.from_blocks_zero₁₂_invertible Matrix.fromBlocksZero₁₂Invertible

theorem invOf_fromBlocks_zero₂₁_eq (A : Matrix m m α) (B : Matrix m n α) (D : Matrix n n α)
    [Invertible A] [Invertible D] [Invertible (fromBlocks A B 0 D)] :
    ⅟ (fromBlocks A B 0 D) = fromBlocks (⅟ A) (-⅟ A ⬝ B ⬝ ⅟ D) 0 (⅟ D) :=
  by
  letI := from_blocks_zero₂₁_invertible A B D
  convert (rfl : ⅟ (from_blocks A B 0 D) = _)
#align matrix.inv_of_from_blocks_zero₂₁_eq Matrix.invOf_fromBlocks_zero₂₁_eq

theorem invOf_fromBlocks_zero₁₂_eq (A : Matrix m m α) (C : Matrix n m α) (D : Matrix n n α)
    [Invertible A] [Invertible D] [Invertible (fromBlocks A 0 C D)] :
    ⅟ (fromBlocks A 0 C D) = fromBlocks (⅟ A) 0 (-⅟ D ⬝ C ⬝ ⅟ A) (⅟ D) :=
  by
  letI := from_blocks_zero₁₂_invertible A C D
  convert (rfl : ⅟ (from_blocks A 0 C D) = _)
#align matrix.inv_of_from_blocks_zero₁₂_eq Matrix.invOf_fromBlocks_zero₁₂_eq

/-- Both diagonal entries of an invertible upper-block-triangular matrix are invertible (by reading
off the diagonal entries of the inverse). -/
def invertibleOfFromBlocksZero₂₁Invertible (A : Matrix m m α) (B : Matrix m n α) (D : Matrix n n α)
    [Invertible (fromBlocks A B 0 D)] : Invertible A × Invertible D
    where
  fst :=
    invertibleOfLeftInverse _ (⅟ (fromBlocks A B 0 D)).toBlocks₁₁ <|
      by
      have := Matrix.invOf_mul_self (from_blocks A B 0 D)
      rw [← from_blocks_to_blocks (⅟ (from_blocks A B 0 D)), from_blocks_multiply] at this 
      replace := congr_arg Matrix.toBlocks₁₁ this
      simpa only [Matrix.toBlocks_fromBlocks₁₁, Matrix.mul_zero, add_zero, ← from_blocks_one] using
        this
  snd :=
    invertibleOfRightInverse _ (⅟ (fromBlocks A B 0 D)).toBlocks₂₂ <|
      by
      have := Matrix.mul_invOf_self (from_blocks A B 0 D)
      rw [← from_blocks_to_blocks (⅟ (from_blocks A B 0 D)), from_blocks_multiply] at this 
      replace := congr_arg Matrix.toBlocks₂₂ this
      simpa only [Matrix.toBlocks_fromBlocks₂₂, Matrix.zero_mul, zero_add, ← from_blocks_one] using
        this
#align matrix.invertible_of_from_blocks_zero₂₁_invertible Matrix.invertibleOfFromBlocksZero₂₁Invertible

/-- Both diagonal entries of an invertible lower-block-triangular matrix are invertible (by reading
off the diagonal entries of the inverse). -/
def invertibleOfFromBlocksZero₁₂Invertible (A : Matrix m m α) (C : Matrix n m α) (D : Matrix n n α)
    [Invertible (fromBlocks A 0 C D)] : Invertible A × Invertible D
    where
  fst :=
    invertibleOfRightInverse _ (⅟ (fromBlocks A 0 C D)).toBlocks₁₁ <|
      by
      have := Matrix.mul_invOf_self (from_blocks A 0 C D)
      rw [← from_blocks_to_blocks (⅟ (from_blocks A 0 C D)), from_blocks_multiply] at this 
      replace := congr_arg Matrix.toBlocks₁₁ this
      simpa only [Matrix.toBlocks_fromBlocks₁₁, Matrix.zero_mul, add_zero, ← from_blocks_one] using
        this
  snd :=
    invertibleOfLeftInverse _ (⅟ (fromBlocks A 0 C D)).toBlocks₂₂ <|
      by
      have := Matrix.invOf_mul_self (from_blocks A 0 C D)
      rw [← from_blocks_to_blocks (⅟ (from_blocks A 0 C D)), from_blocks_multiply] at this 
      replace := congr_arg Matrix.toBlocks₂₂ this
      simpa only [Matrix.toBlocks_fromBlocks₂₂, Matrix.mul_zero, zero_add, ← from_blocks_one] using
        this
#align matrix.invertible_of_from_blocks_zero₁₂_invertible Matrix.invertibleOfFromBlocksZero₁₂Invertible

/-- `invertible_of_from_blocks_zero₂₁_invertible` and `from_blocks_zero₂₁_invertible` form
an equivalence. -/
def fromBlocksZero₂₁InvertibleEquiv (A : Matrix m m α) (B : Matrix m n α) (D : Matrix n n α) :
    Invertible (fromBlocks A B 0 D) ≃ Invertible A × Invertible D
    where
  toFun _ := invertible_of_from_blocks_zero₂₁_invertible A B D
  invFun i := by letI := i.1 <;> letI := i.2 <;> exact from_blocks_zero₂₁_invertible A B D
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
#align matrix.from_blocks_zero₂₁_invertible_equiv Matrix.fromBlocksZero₂₁InvertibleEquiv

/-- `invertible_of_from_blocks_zero₁₂_invertible` and `from_blocks_zero₁₂_invertible` form
an equivalence. -/
def fromBlocksZero₁₂InvertibleEquiv (A : Matrix m m α) (C : Matrix n m α) (D : Matrix n n α) :
    Invertible (fromBlocks A 0 C D) ≃ Invertible A × Invertible D
    where
  toFun _ := invertible_of_from_blocks_zero₁₂_invertible A C D
  invFun i := by letI := i.1 <;> letI := i.2 <;> exact from_blocks_zero₁₂_invertible A C D
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
#align matrix.from_blocks_zero₁₂_invertible_equiv Matrix.fromBlocksZero₁₂InvertibleEquiv

/-- An upper block-triangular matrix is invertible iff both elements of its diagonal are.

This is a propositional form of `matrix.from_blocks_zero₂₁_invertible_equiv`. -/
@[simp]
theorem isUnit_fromBlocks_zero₂₁ {A : Matrix m m α} {B : Matrix m n α} {D : Matrix n n α} :
    IsUnit (fromBlocks A B 0 D) ↔ IsUnit A ∧ IsUnit D := by
  simp only [← nonempty_invertible_iff_isUnit, ← nonempty_prod,
    (from_blocks_zero₂₁_invertible_equiv _ _ _).nonempty_congr]
#align matrix.is_unit_from_blocks_zero₂₁ Matrix.isUnit_fromBlocks_zero₂₁

/-- A lower block-triangular matrix is invertible iff both elements of its diagonal are.

This is a propositional form of  `matrix.from_blocks_zero₁₂_invertible_equiv` forms an `iff`. -/
@[simp]
theorem isUnit_fromBlocks_zero₁₂ {A : Matrix m m α} {C : Matrix n m α} {D : Matrix n n α} :
    IsUnit (fromBlocks A 0 C D) ↔ IsUnit A ∧ IsUnit D := by
  simp only [← nonempty_invertible_iff_isUnit, ← nonempty_prod,
    (from_blocks_zero₁₂_invertible_equiv _ _ _).nonempty_congr]
#align matrix.is_unit_from_blocks_zero₁₂ Matrix.isUnit_fromBlocks_zero₁₂

/-- An expression for the inverse of an upper block-triangular matrix, when either both elements of
diagonal are invertible, or both are not. -/
theorem inv_fromBlocks_zero₂₁_of_isUnit_iff (A : Matrix m m α) (B : Matrix m n α) (D : Matrix n n α)
    (hAD : IsUnit A ↔ IsUnit D) : (fromBlocks A B 0 D)⁻¹ = fromBlocks A⁻¹ (-A⁻¹ ⬝ B ⬝ D⁻¹) 0 D⁻¹ :=
  by
  by_cases hA : IsUnit A
  · have hD := hAD.mp hA
    cases hA.nonempty_invertible
    cases hD.nonempty_invertible
    letI := from_blocks_zero₂₁_invertible A B D
    simp_rw [← inv_of_eq_nonsing_inv, inv_of_from_blocks_zero₂₁_eq]
  · have hD := hAD.not.mp hA
    have : ¬IsUnit (from_blocks A B 0 D) :=
      is_unit_from_blocks_zero₂₁.not.mpr (not_and'.mpr fun _ => hA)
    simp_rw [nonsing_inv_eq_ring_inverse, Ring.inverse_non_unit _ hA, Ring.inverse_non_unit _ hD,
      Ring.inverse_non_unit _ this, Matrix.zero_mul, neg_zero, from_blocks_zero]
#align matrix.inv_from_blocks_zero₂₁_of_is_unit_iff Matrix.inv_fromBlocks_zero₂₁_of_isUnit_iff

/-- An expression for the inverse of a lower block-triangular matrix, when either both elements of
diagonal are invertible, or both are not. -/
theorem inv_fromBlocks_zero₁₂_of_isUnit_iff (A : Matrix m m α) (C : Matrix n m α) (D : Matrix n n α)
    (hAD : IsUnit A ↔ IsUnit D) : (fromBlocks A 0 C D)⁻¹ = fromBlocks A⁻¹ 0 (-D⁻¹ ⬝ C ⬝ A⁻¹) D⁻¹ :=
  by
  by_cases hA : IsUnit A
  · have hD := hAD.mp hA
    cases hA.nonempty_invertible
    cases hD.nonempty_invertible
    letI := from_blocks_zero₁₂_invertible A C D
    simp_rw [← inv_of_eq_nonsing_inv, inv_of_from_blocks_zero₁₂_eq]
  · have hD := hAD.not.mp hA
    have : ¬IsUnit (from_blocks A 0 C D) :=
      is_unit_from_blocks_zero₁₂.not.mpr (not_and'.mpr fun _ => hA)
    simp_rw [nonsing_inv_eq_ring_inverse, Ring.inverse_non_unit _ hA, Ring.inverse_non_unit _ hD,
      Ring.inverse_non_unit _ this, Matrix.zero_mul, neg_zero, from_blocks_zero]
#align matrix.inv_from_blocks_zero₁₂_of_is_unit_iff Matrix.inv_fromBlocks_zero₁₂_of_isUnit_iff

end Triangular

/-! ### Lemmas about `matrix.det` -/


section Det

/-- Determinant of a 2×2 block matrix, expanded around an invertible top left element in terms of
the Schur complement. -/
theorem det_from_blocks₁₁ (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α)
    (D : Matrix n n α) [Invertible A] :
    (Matrix.fromBlocks A B C D).det = det A * det (D - C ⬝ ⅟ A ⬝ B) := by
  rw [from_blocks_eq_of_invertible₁₁, det_mul, det_mul, det_from_blocks_zero₂₁,
    det_from_blocks_zero₂₁, det_from_blocks_zero₁₂, det_one, det_one, one_mul, one_mul, mul_one]
#align matrix.det_from_blocks₁₁ Matrix.det_from_blocks₁₁

@[simp]
theorem det_fromBlocks_one₁₁ (B : Matrix m n α) (C : Matrix n m α) (D : Matrix n n α) :
    (Matrix.fromBlocks 1 B C D).det = det (D - C ⬝ B) :=
  by
  haveI : Invertible (1 : Matrix m m α) := invertibleOne
  rw [det_from_blocks₁₁, invOf_one, Matrix.mul_one, det_one, one_mul]
#align matrix.det_from_blocks_one₁₁ Matrix.det_fromBlocks_one₁₁

/-- Determinant of a 2×2 block matrix, expanded around an invertible bottom right element in terms
of the Schur complement. -/
theorem det_from_blocks₂₂ (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α)
    (D : Matrix n n α) [Invertible D] :
    (Matrix.fromBlocks A B C D).det = det D * det (A - B ⬝ ⅟ D ⬝ C) :=
  by
  have :
    from_blocks A B C D = (from_blocks D C B A).submatrix (Equiv.sumComm _ _) (Equiv.sumComm _ _) :=
    by
    ext (i j)
    cases i <;> cases j <;> rfl
  rw [this, det_submatrix_equiv_self, det_from_blocks₁₁]
#align matrix.det_from_blocks₂₂ Matrix.det_from_blocks₂₂

@[simp]
theorem det_fromBlocks_one₂₂ (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α) :
    (Matrix.fromBlocks A B C 1).det = det (A - B ⬝ C) :=
  by
  haveI : Invertible (1 : Matrix n n α) := invertibleOne
  rw [det_from_blocks₂₂, invOf_one, Matrix.mul_one, det_one, one_mul]
#align matrix.det_from_blocks_one₂₂ Matrix.det_fromBlocks_one₂₂

/-- The **Weinstein–Aronszajn identity**. Note the `1` on the LHS is of shape m×m, while the `1` on
the RHS is of shape n×n. -/
theorem det_one_add_mul_comm (A : Matrix m n α) (B : Matrix n m α) :
    det (1 + A ⬝ B) = det (1 + B ⬝ A) :=
  calc
    det (1 + A ⬝ B) = det (fromBlocks 1 (-A) B 1) := by
      rw [det_from_blocks_one₂₂, Matrix.neg_mul, sub_neg_eq_add]
    _ = det (1 + B ⬝ A) := by rw [det_from_blocks_one₁₁, Matrix.mul_neg, sub_neg_eq_add]
#align matrix.det_one_add_mul_comm Matrix.det_one_add_mul_comm

/-- Alternate statement of the **Weinstein–Aronszajn identity** -/
theorem det_mul_add_one_comm (A : Matrix m n α) (B : Matrix n m α) :
    det (A ⬝ B + 1) = det (B ⬝ A + 1) := by rw [add_comm, det_one_add_mul_comm, add_comm]
#align matrix.det_mul_add_one_comm Matrix.det_mul_add_one_comm

theorem det_one_sub_mul_comm (A : Matrix m n α) (B : Matrix n m α) :
    det (1 - A ⬝ B) = det (1 - B ⬝ A) := by
  rw [sub_eq_add_neg, ← Matrix.neg_mul, det_one_add_mul_comm, Matrix.mul_neg, ← sub_eq_add_neg]
#align matrix.det_one_sub_mul_comm Matrix.det_one_sub_mul_comm

/-- A special case of the **Matrix determinant lemma** for when `A = I`.

TODO: show this more generally. -/
theorem det_one_add_col_mul_row (u v : m → α) : det (1 + col u ⬝ row v) = 1 + v ⬝ᵥ u := by
  rw [det_one_add_mul_comm, det_unique, Pi.add_apply, Pi.add_apply, Matrix.one_apply_eq,
    Matrix.row_mul_col_apply]
#align matrix.det_one_add_col_mul_row Matrix.det_one_add_col_mul_row

end Det

end CommRing

/-! ### Lemmas about `ℝ` and `ℂ`-/


section IsROrC

open scoped Matrix

variable {𝕜 : Type _} [IsROrC 𝕜]

scoped infixl:65 " ⊕ᵥ " => Sum.elim

theorem schur_complement_eq₁₁ [Fintype m] [DecidableEq m] [Fintype n] {A : Matrix m m 𝕜}
    (B : Matrix m n 𝕜) (D : Matrix n n 𝕜) (x : m → 𝕜) (y : n → 𝕜) [Invertible A]
    (hA : A.IsHermitian) :
    vecMul (star (x ⊕ᵥ y)) (fromBlocks A B Bᴴ D) ⬝ᵥ (x ⊕ᵥ y) =
      vecMul (star (x + (A⁻¹ ⬝ B).mulVec y)) A ⬝ᵥ (x + (A⁻¹ ⬝ B).mulVec y) +
        vecMul (star y) (D - Bᴴ ⬝ A⁻¹ ⬝ B) ⬝ᵥ y :=
  by
  simp [Function.star_sum_elim, from_blocks_mul_vec, vec_mul_from_blocks, add_vec_mul,
    dot_product_mul_vec, vec_mul_sub, Matrix.mul_assoc, vec_mul_mul_vec, hA.eq,
    conj_transpose_nonsing_inv, star_mul_vec]
  abel
#align matrix.schur_complement_eq₁₁ Matrix.schur_complement_eq₁₁

theorem schur_complement_eq₂₂ [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m m 𝕜)
    (B : Matrix m n 𝕜) {D : Matrix n n 𝕜} (x : m → 𝕜) (y : n → 𝕜) [Invertible D]
    (hD : D.IsHermitian) :
    vecMul (star (x ⊕ᵥ y)) (fromBlocks A B Bᴴ D) ⬝ᵥ (x ⊕ᵥ y) =
      vecMul (star ((D⁻¹ ⬝ Bᴴ).mulVec x + y)) D ⬝ᵥ ((D⁻¹ ⬝ Bᴴ).mulVec x + y) +
        vecMul (star x) (A - B ⬝ D⁻¹ ⬝ Bᴴ) ⬝ᵥ x :=
  by
  simp [Function.star_sum_elim, from_blocks_mul_vec, vec_mul_from_blocks, add_vec_mul,
    dot_product_mul_vec, vec_mul_sub, Matrix.mul_assoc, vec_mul_mul_vec, hD.eq,
    conj_transpose_nonsing_inv, star_mul_vec]
  abel
#align matrix.schur_complement_eq₂₂ Matrix.schur_complement_eq₂₂

theorem IsHermitian.from_blocks₁₁ [Fintype m] [DecidableEq m] {A : Matrix m m 𝕜} (B : Matrix m n 𝕜)
    (D : Matrix n n 𝕜) (hA : A.IsHermitian) :
    (fromBlocks A B Bᴴ D).IsHermitian ↔ (D - Bᴴ ⬝ A⁻¹ ⬝ B).IsHermitian :=
  by
  have hBAB : (Bᴴ ⬝ A⁻¹ ⬝ B).IsHermitian :=
    by
    apply is_hermitian_conj_transpose_mul_mul
    apply hA.inv
  rw [is_hermitian_from_blocks_iff]
  constructor
  · intro h
    apply is_hermitian.sub h.2.2.2 hBAB
  · intro h
    refine' ⟨hA, rfl, conj_transpose_conj_transpose B, _⟩
    rw [← sub_add_cancel D]
    apply is_hermitian.add h hBAB
#align matrix.is_hermitian.from_blocks₁₁ Matrix.IsHermitian.from_blocks₁₁

theorem IsHermitian.from_blocks₂₂ [Fintype n] [DecidableEq n] (A : Matrix m m 𝕜) (B : Matrix m n 𝕜)
    {D : Matrix n n 𝕜} (hD : D.IsHermitian) :
    (fromBlocks A B Bᴴ D).IsHermitian ↔ (A - B ⬝ D⁻¹ ⬝ Bᴴ).IsHermitian :=
  by
  rw [← is_hermitian_submatrix_equiv (Equiv.sumComm n m), Equiv.sumComm_apply,
    from_blocks_submatrix_sum_swap_sum_swap]
  convert is_hermitian.from_blocks₁₁ _ _ hD <;> simp
#align matrix.is_hermitian.from_blocks₂₂ Matrix.IsHermitian.from_blocks₂₂

theorem PosSemidef.from_blocks₁₁ [Fintype m] [DecidableEq m] [Fintype n] {A : Matrix m m 𝕜}
    (B : Matrix m n 𝕜) (D : Matrix n n 𝕜) (hA : A.PosDef) [Invertible A] :
    (fromBlocks A B Bᴴ D).PosSemidef ↔ (D - Bᴴ ⬝ A⁻¹ ⬝ B).PosSemidef :=
  by
  rw [pos_semidef, is_hermitian.from_blocks₁₁ _ _ hA.1]
  constructor
  · refine' fun h => ⟨h.1, fun x => _⟩
    have := h.2 (-(A⁻¹ ⬝ B).mulVec x ⊕ᵥ x)
    rw [dot_product_mul_vec, schur_complement_eq₁₁ B D _ _ hA.1, neg_add_self, dot_product_zero,
      zero_add] at this 
    rw [dot_product_mul_vec]; exact this
  · refine' fun h => ⟨h.1, fun x => _⟩
    rw [dot_product_mul_vec, ← Sum.elim_comp_inl_inr x, schur_complement_eq₁₁ B D _ _ hA.1, map_add]
    apply le_add_of_nonneg_of_le
    · rw [← dot_product_mul_vec]
      apply hA.pos_semidef.2
    · rw [← dot_product_mul_vec]; apply h.2
#align matrix.pos_semidef.from_blocks₁₁ Matrix.PosSemidef.from_blocks₁₁

theorem PosSemidef.from_blocks₂₂ [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m m 𝕜)
    (B : Matrix m n 𝕜) {D : Matrix n n 𝕜} (hD : D.PosDef) [Invertible D] :
    (fromBlocks A B Bᴴ D).PosSemidef ↔ (A - B ⬝ D⁻¹ ⬝ Bᴴ).PosSemidef :=
  by
  rw [← pos_semidef_submatrix_equiv (Equiv.sumComm n m), Equiv.sumComm_apply,
    from_blocks_submatrix_sum_swap_sum_swap]
  convert pos_semidef.from_blocks₁₁ _ _ hD <;>
    first
    | infer_instance
    | simp
#align matrix.pos_semidef.from_blocks₂₂ Matrix.PosSemidef.from_blocks₂₂

end IsROrC

end Matrix

