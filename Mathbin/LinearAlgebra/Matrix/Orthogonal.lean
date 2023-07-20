/-
Copyright (c) 2021 Lu-Ming Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lu-Ming Zhang
-/
import Mathbin.Data.Matrix.Basic

#align_import linear_algebra.matrix.orthogonal from "leanprover-community/mathlib"@"d64d67d000b974f0d86a2be7918cf800be6271c8"

/-!
# Orthogonal

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

open scoped Matrix

#print Matrix.HasOrthogonalRows /-
/-- `A.has_orthogonal_rows` means matrix `A` has orthogonal rows (with respect to
`matrix.dot_product`). -/
def HasOrthogonalRows [Fintype n] : Prop :=
  ∀ ⦃i₁ i₂⦄, i₁ ≠ i₂ → dotProduct (A i₁) (A i₂) = 0
#align matrix.has_orthogonal_rows Matrix.HasOrthogonalRows
-/

#print Matrix.HasOrthogonalCols /-
/-- `A.has_orthogonal_rows` means matrix `A` has orthogonal columns (with respect to
`matrix.dot_product`). -/
def HasOrthogonalCols [Fintype m] : Prop :=
  HasOrthogonalRows Aᵀ
#align matrix.has_orthogonal_cols Matrix.HasOrthogonalCols
-/

#print Matrix.transpose_hasOrthogonalRows_iff_hasOrthogonalCols /-
/-- `Aᵀ` has orthogonal rows iff `A` has orthogonal columns. -/
@[simp]
theorem transpose_hasOrthogonalRows_iff_hasOrthogonalCols [Fintype m] :
    Aᵀ.HasOrthogonalRows ↔ A.HasOrthogonalCols :=
  Iff.rfl
#align matrix.transpose_has_orthogonal_rows_iff_has_orthogonal_cols Matrix.transpose_hasOrthogonalRows_iff_hasOrthogonalCols
-/

#print Matrix.transpose_hasOrthogonalCols_iff_hasOrthogonalRows /-
/-- `Aᵀ` has orthogonal columns iff `A` has orthogonal rows. -/
@[simp]
theorem transpose_hasOrthogonalCols_iff_hasOrthogonalRows [Fintype n] :
    Aᵀ.HasOrthogonalCols ↔ A.HasOrthogonalRows :=
  Iff.rfl
#align matrix.transpose_has_orthogonal_cols_iff_has_orthogonal_rows Matrix.transpose_hasOrthogonalCols_iff_hasOrthogonalRows
-/

variable {A}

#print Matrix.HasOrthogonalRows.hasOrthogonalCols /-
theorem HasOrthogonalRows.hasOrthogonalCols [Fintype m] (h : Aᵀ.HasOrthogonalRows) :
    A.HasOrthogonalCols :=
  h
#align matrix.has_orthogonal_rows.has_orthogonal_cols Matrix.HasOrthogonalRows.hasOrthogonalCols
-/

#print Matrix.HasOrthogonalCols.transpose_hasOrthogonalRows /-
theorem HasOrthogonalCols.transpose_hasOrthogonalRows [Fintype m] (h : A.HasOrthogonalCols) :
    Aᵀ.HasOrthogonalRows :=
  h
#align matrix.has_orthogonal_cols.transpose_has_orthogonal_rows Matrix.HasOrthogonalCols.transpose_hasOrthogonalRows
-/

#print Matrix.HasOrthogonalCols.hasOrthogonalRows /-
theorem HasOrthogonalCols.hasOrthogonalRows [Fintype n] (h : Aᵀ.HasOrthogonalCols) :
    A.HasOrthogonalRows :=
  h
#align matrix.has_orthogonal_cols.has_orthogonal_rows Matrix.HasOrthogonalCols.hasOrthogonalRows
-/

#print Matrix.HasOrthogonalRows.transpose_hasOrthogonalCols /-
theorem HasOrthogonalRows.transpose_hasOrthogonalCols [Fintype n] (h : A.HasOrthogonalRows) :
    Aᵀ.HasOrthogonalCols :=
  h
#align matrix.has_orthogonal_rows.transpose_has_orthogonal_cols Matrix.HasOrthogonalRows.transpose_hasOrthogonalCols
-/

end Matrix

