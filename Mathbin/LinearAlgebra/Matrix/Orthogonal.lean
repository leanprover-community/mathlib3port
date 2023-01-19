/-
Copyright (c) 2021 Lu-Ming Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lu-Ming Zhang

! This file was ported from Lean 3 source module linear_algebra.matrix.orthogonal
! leanprover-community/mathlib commit 509de852e1de55e1efa8eacfa11df0823f26f226
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
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

variable [Mul α] [AddCommMonoid α]

variable (A : Matrix m n α)

open Matrix

/-- `A.has_orthogonal_rows` means matrix `A` has orthogonal rows (with respect to
`matrix.dot_product`). -/
def HasOrthogonalRows [Fintype n] : Prop :=
  ∀ ⦃i₁ i₂⦄, i₁ ≠ i₂ → dotProduct (A i₁) (A i₂) = 0
#align matrix.has_orthogonal_rows Matrix.HasOrthogonalRows

/-- `A.has_orthogonal_rows` means matrix `A` has orthogonal columns (with respect to
`matrix.dot_product`). -/
def HasOrthogonalCols [Fintype m] : Prop :=
  HasOrthogonalRows Aᵀ
#align matrix.has_orthogonal_cols Matrix.HasOrthogonalCols

/-- `Aᵀ` has orthogonal rows iff `A` has orthogonal columns. -/
@[simp]
theorem transpose_has_orthogonal_rows_iff_has_orthogonal_cols [Fintype m] :
    Aᵀ.HasOrthogonalRows ↔ A.HasOrthogonalCols :=
  Iff.rfl
#align matrix.transpose_has_orthogonal_rows_iff_has_orthogonal_cols Matrix.transpose_has_orthogonal_rows_iff_has_orthogonal_cols

/-- `Aᵀ` has orthogonal columns iff `A` has orthogonal rows. -/
@[simp]
theorem transpose_has_orthogonal_cols_iff_has_orthogonal_rows [Fintype n] :
    Aᵀ.HasOrthogonalCols ↔ A.HasOrthogonalRows :=
  Iff.rfl
#align matrix.transpose_has_orthogonal_cols_iff_has_orthogonal_rows Matrix.transpose_has_orthogonal_cols_iff_has_orthogonal_rows

variable {A}

theorem HasOrthogonalRows.has_orthogonal_cols [Fintype m] (h : Aᵀ.HasOrthogonalRows) :
    A.HasOrthogonalCols :=
  h
#align matrix.has_orthogonal_rows.has_orthogonal_cols Matrix.HasOrthogonalRows.has_orthogonal_cols

theorem HasOrthogonalCols.transpose_has_orthogonal_rows [Fintype m] (h : A.HasOrthogonalCols) :
    Aᵀ.HasOrthogonalRows :=
  h
#align matrix.has_orthogonal_cols.transpose_has_orthogonal_rows Matrix.HasOrthogonalCols.transpose_has_orthogonal_rows

theorem HasOrthogonalCols.has_orthogonal_rows [Fintype n] (h : Aᵀ.HasOrthogonalCols) :
    A.HasOrthogonalRows :=
  h
#align matrix.has_orthogonal_cols.has_orthogonal_rows Matrix.HasOrthogonalCols.has_orthogonal_rows

theorem HasOrthogonalRows.transpose_has_orthogonal_cols [Fintype n] (h : A.HasOrthogonalRows) :
    Aᵀ.HasOrthogonalCols :=
  h
#align matrix.has_orthogonal_rows.transpose_has_orthogonal_cols Matrix.HasOrthogonalRows.transpose_has_orthogonal_cols

end Matrix

