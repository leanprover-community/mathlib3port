import Mathbin.Data.Matrix.Block

/-!
# Symmetric matrices

This file contains the definition and basic results about symmetric matrices.

## Main definition

 * `matrix.is_symm `: a matrix `A : matrix n n α` is "symmetric" if `Aᵀ = A`.

## Tags

symm, symmetric, matrix
-/


variable {α β n m R : Type _}

namespace Matrix

open_locale Matrix

/-- A matrix `A : matrix n n α` is "symmetric" if `Aᵀ = A`. -/
def IsSymm (A : Matrix n n α) : Prop :=
  (A)ᵀ = A

theorem is_symm.eq {A : Matrix n n α} (h : A.is_symm) : (A)ᵀ = A :=
  h

/-- A version of `matrix.ext_iff` that unfolds the `matrix.transpose`. -/
theorem is_symm.ext_iff {A : Matrix n n α} : A.is_symm ↔ ∀ i j, A j i = A i j :=
  Matrix.ext_iff.symm

/-- A version of `matrix.ext` that unfolds the `matrix.transpose`. -/
@[ext]
theorem is_symm.ext {A : Matrix n n α} : (∀ i j, A j i = A i j) → A.is_symm :=
  Matrix.ext

theorem is_symm.apply {A : Matrix n n α} (h : A.is_symm) (i j : n) : A j i = A i j :=
  is_symm.ext_iff.1 h i j

theorem is_symm_mul_transpose_self [Fintype n] [CommSemiringₓ α] (A : Matrix n n α) : (A ⬝ (A)ᵀ).IsSymm :=
  transpose_mul _ _

theorem is_symm_transpose_mul_self [Fintype n] [CommSemiringₓ α] (A : Matrix n n α) : ((A)ᵀ ⬝ A).IsSymm :=
  transpose_mul _ _

theorem is_symm_add_transpose_self [AddCommSemigroupₓ α] (A : Matrix n n α) : (A+(A)ᵀ).IsSymm :=
  add_commₓ _ _

theorem is_symm_transpose_add_self [AddCommSemigroupₓ α] (A : Matrix n n α) : ((A)ᵀ+A).IsSymm :=
  add_commₓ _ _

@[simp]
theorem is_symm_zero [HasZero α] : (0 : Matrix n n α).IsSymm :=
  transpose_zero

@[simp]
theorem is_symm_one [DecidableEq n] [HasZero α] [HasOne α] : (1 : Matrix n n α).IsSymm :=
  transpose_one

@[simp]
theorem is_symm.map {A : Matrix n n α} (h : A.is_symm) (f : α → β) : (A.map f).IsSymm :=
  transpose_map.symm.trans (h.symm ▸ rfl)

@[simp]
theorem is_symm.transpose {A : Matrix n n α} (h : A.is_symm) : (A)ᵀ.IsSymm :=
  congr_argₓ _ h

@[simp]
theorem is_symm.conj_transpose [HasStar α] {A : Matrix n n α} (h : A.is_symm) : (A)ᴴ.IsSymm :=
  h.transpose.map _

@[simp]
theorem is_symm.neg [Neg α] {A : Matrix n n α} (h : A.is_symm) : (-A).IsSymm :=
  (transpose_neg _).trans (congr_argₓ _ h)

@[simp]
theorem is_symm.add {A B : Matrix n n α} [Add α] (hA : A.is_symm) (hB : B.is_symm) : (A+B).IsSymm :=
  (transpose_add _ _).trans (hA.symm ▸ hB.symm ▸ rfl)

@[simp]
theorem is_symm.sub {A B : Matrix n n α} [Sub α] (hA : A.is_symm) (hB : B.is_symm) : (A - B).IsSymm :=
  (transpose_sub _ _).trans (hA.symm ▸ hB.symm ▸ rfl)

@[simp]
theorem is_symm.smul [HasScalar R α] {A : Matrix n n α} (h : A.is_symm) (k : R) : (k • A).IsSymm :=
  (transpose_smul _ _).trans (congr_argₓ _ h)

@[simp]
theorem is_symm.minor {A : Matrix n n α} (h : A.is_symm) (f : m → n) : (A.minor f f).IsSymm :=
  (transpose_minor _ _ _).trans (h.symm ▸ rfl)

/-- The diagonal matrix `diagonal v` is symmetric. -/
@[simp]
theorem is_symm_diagonal [DecidableEq n] [HasZero α] (v : n → α) : (diagonal v).IsSymm :=
  diagonal_transpose _

/-- A block matrix `A.from_blocks B C D` is symmetric,
    if `A` and `D` are symmetric and `Bᵀ = C`. -/
theorem is_symm.from_blocks {A : Matrix m m α} {B : Matrix m n α} {C : Matrix n m α} {D : Matrix n n α} (hA : A.is_symm)
  (hBC : (B)ᵀ = C) (hD : D.is_symm) : (A.from_blocks B C D).IsSymm :=
  by 
    have hCB : (C)ᵀ = B
    ·
      rw [←hBC]
      simp 
    unfold Matrix.IsSymm 
    rw [from_blocks_transpose]
    congr <;> assumption

/-- This is the `iff` version of `matrix.is_symm.from_blocks`. -/
theorem is_symm_from_blocks_iff {A : Matrix m m α} {B : Matrix m n α} {C : Matrix n m α} {D : Matrix n n α} :
  (A.from_blocks B C D).IsSymm ↔ A.is_symm ∧ (B)ᵀ = C ∧ (C)ᵀ = B ∧ D.is_symm :=
  ⟨fun h => ⟨congr_argₓ to_blocks₁₁ h, congr_argₓ to_blocks₂₁ h, congr_argₓ to_blocks₁₂ h, congr_argₓ to_blocks₂₂ h⟩,
    fun ⟨hA, hBC, hCB, hD⟩ => is_symm.from_blocks hA hBC hD⟩

end Matrix

