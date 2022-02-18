import Mathbin.Data.Matrix.Basic

/-!
# Orthogonal

This file contains definitions and properties concerning orthogonality of rows and columns.

## Main results

- `matrix.has_orthogonal_rows`:
  `A.has_orthogonal_rows` means `A` has orthogonal (with respect to `dot_product`) rows.
- `matrix.has_orthogonal_cols`:
  `A.has_orthogonal_cols` means `A` has orthogonal (with respect to `dot_product`) columns.

## Tags

orthogonal
-/


namespace Matrix

variable {α n m : Type _}

variable [Mul α] [AddCommMonoidₓ α]

variable (A : Matrix m n α)

open_locale Matrix

/-- `A.has_orthogonal_rows` means matrix `A` has orthogonal rows (with respect to
`matrix.dot_product`). -/
def has_orthogonal_rows [Fintype n] : Prop :=
  ∀ ⦃i₁ i₂⦄, i₁ ≠ i₂ → dotProduct (A i₁) (A i₂) = 0

/-- `A.has_orthogonal_rows` means matrix `A` has orthogonal columns (with respect to
`matrix.dot_product`). -/
def has_orthogonal_cols [Fintype m] : Prop :=
  HasOrthogonalRows (A)ᵀ

/-- `Aᵀ` has orthogonal rows iff `A` has orthogonal columns. -/
@[simp]
theorem transpose_has_orthogonal_rows_iff_has_orthogonal_cols [Fintype m] :
    (A)ᵀ.HasOrthogonalRows ↔ A.HasOrthogonalCols :=
  Iff.rfl

/-- `Aᵀ` has orthogonal columns iff `A` has orthogonal rows. -/
@[simp]
theorem transpose_has_orthogonal_cols_iff_has_orthogonal_rows [Fintype n] :
    (A)ᵀ.HasOrthogonalCols ↔ A.HasOrthogonalRows :=
  Iff.rfl

variable {A}

theorem has_orthogonal_rows.has_orthogonal_cols [Fintype m] (h : (A)ᵀ.HasOrthogonalRows) : A.HasOrthogonalCols :=
  h

theorem has_orthogonal_cols.transpose_has_orthogonal_rows [Fintype m] (h : A.HasOrthogonalCols) :
    (A)ᵀ.HasOrthogonalRows :=
  h

theorem has_orthogonal_cols.has_orthogonal_rows [Fintype n] (h : (A)ᵀ.HasOrthogonalCols) : A.HasOrthogonalRows :=
  h

theorem has_orthogonal_rows.transpose_has_orthogonal_cols [Fintype n] (h : A.HasOrthogonalRows) :
    (A)ᵀ.HasOrthogonalCols :=
  h

end Matrix

