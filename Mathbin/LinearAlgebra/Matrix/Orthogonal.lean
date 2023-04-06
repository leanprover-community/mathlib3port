/-
Copyright (c) 2021 Lu-Ming Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lu-Ming Zhang

! This file was ported from Lean 3 source module linear_algebra.matrix.orthogonal
! leanprover-community/mathlib commit d64d67d000b974f0d86a2be7918cf800be6271c8
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Matrix.Basic

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

open Matrix

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

/- warning: matrix.transpose_has_orthogonal_rows_iff_has_orthogonal_cols -> Matrix.transpose_hasOrthogonalRows_iff_hasOrthogonalCols is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {n : Type.{u2}} {m : Type.{u3}} [_inst_1 : Mul.{u1} α] [_inst_2 : AddCommMonoid.{u1} α] (A : Matrix.{u3, u2, u1} m n α) [_inst_3 : Fintype.{u3} m], Iff (Matrix.HasOrthogonalRows.{u1, u3, u2} α m n _inst_1 _inst_2 (Matrix.transpose.{u1, u3, u2} m n α A) _inst_3) (Matrix.HasOrthogonalCols.{u1, u2, u3} α n m _inst_1 _inst_2 A _inst_3)
but is expected to have type
  forall {α : Type.{u2}} {n : Type.{u1}} {m : Type.{u3}} [_inst_1 : Mul.{u2} α] [_inst_2 : AddCommMonoid.{u2} α] (A : Matrix.{u3, u1, u2} m n α) [_inst_3 : Fintype.{u3} m], Iff (Matrix.HasOrthogonalRows.{u2, u3, u1} α m n _inst_1 _inst_2 (Matrix.transpose.{u2, u3, u1} m n α A) _inst_3) (Matrix.HasOrthogonalCols.{u2, u1, u3} α n m _inst_1 _inst_2 A _inst_3)
Case conversion may be inaccurate. Consider using '#align matrix.transpose_has_orthogonal_rows_iff_has_orthogonal_cols Matrix.transpose_hasOrthogonalRows_iff_hasOrthogonalColsₓ'. -/
/-- `Aᵀ` has orthogonal rows iff `A` has orthogonal columns. -/
@[simp]
theorem transpose_hasOrthogonalRows_iff_hasOrthogonalCols [Fintype m] :
    Aᵀ.HasOrthogonalRows ↔ A.HasOrthogonalCols :=
  Iff.rfl
#align matrix.transpose_has_orthogonal_rows_iff_has_orthogonal_cols Matrix.transpose_hasOrthogonalRows_iff_hasOrthogonalCols

/- warning: matrix.transpose_has_orthogonal_cols_iff_has_orthogonal_rows -> Matrix.transpose_hasOrthogonalCols_iff_hasOrthogonalRows is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {n : Type.{u2}} {m : Type.{u3}} [_inst_1 : Mul.{u1} α] [_inst_2 : AddCommMonoid.{u1} α] (A : Matrix.{u3, u2, u1} m n α) [_inst_3 : Fintype.{u2} n], Iff (Matrix.HasOrthogonalCols.{u1, u3, u2} α m n _inst_1 _inst_2 (Matrix.transpose.{u1, u3, u2} m n α A) _inst_3) (Matrix.HasOrthogonalRows.{u1, u2, u3} α n m _inst_1 _inst_2 A _inst_3)
but is expected to have type
  forall {α : Type.{u2}} {n : Type.{u3}} {m : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : AddCommMonoid.{u2} α] (A : Matrix.{u1, u3, u2} m n α) [_inst_3 : Fintype.{u3} n], Iff (Matrix.HasOrthogonalCols.{u2, u1, u3} α m n _inst_1 _inst_2 (Matrix.transpose.{u2, u1, u3} m n α A) _inst_3) (Matrix.HasOrthogonalRows.{u2, u3, u1} α n m _inst_1 _inst_2 A _inst_3)
Case conversion may be inaccurate. Consider using '#align matrix.transpose_has_orthogonal_cols_iff_has_orthogonal_rows Matrix.transpose_hasOrthogonalCols_iff_hasOrthogonalRowsₓ'. -/
/-- `Aᵀ` has orthogonal columns iff `A` has orthogonal rows. -/
@[simp]
theorem transpose_hasOrthogonalCols_iff_hasOrthogonalRows [Fintype n] :
    Aᵀ.HasOrthogonalCols ↔ A.HasOrthogonalRows :=
  Iff.rfl
#align matrix.transpose_has_orthogonal_cols_iff_has_orthogonal_rows Matrix.transpose_hasOrthogonalCols_iff_hasOrthogonalRows

variable {A}

/- warning: matrix.has_orthogonal_rows.has_orthogonal_cols -> Matrix.HasOrthogonalRows.hasOrthogonalCols is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {n : Type.{u2}} {m : Type.{u3}} [_inst_1 : Mul.{u1} α] [_inst_2 : AddCommMonoid.{u1} α] {A : Matrix.{u3, u2, u1} m n α} [_inst_3 : Fintype.{u3} m], (Matrix.HasOrthogonalRows.{u1, u3, u2} α m n _inst_1 _inst_2 (Matrix.transpose.{u1, u3, u2} m n α A) _inst_3) -> (Matrix.HasOrthogonalCols.{u1, u2, u3} α n m _inst_1 _inst_2 A _inst_3)
but is expected to have type
  forall {α : Type.{u2}} {n : Type.{u1}} {m : Type.{u3}} [_inst_1 : Mul.{u2} α] [_inst_2 : AddCommMonoid.{u2} α] {A : Matrix.{u3, u1, u2} m n α} [_inst_3 : Fintype.{u3} m], (Matrix.HasOrthogonalRows.{u2, u3, u1} α m n _inst_1 _inst_2 (Matrix.transpose.{u2, u3, u1} m n α A) _inst_3) -> (Matrix.HasOrthogonalCols.{u2, u1, u3} α n m _inst_1 _inst_2 A _inst_3)
Case conversion may be inaccurate. Consider using '#align matrix.has_orthogonal_rows.has_orthogonal_cols Matrix.HasOrthogonalRows.hasOrthogonalColsₓ'. -/
theorem HasOrthogonalRows.hasOrthogonalCols [Fintype m] (h : Aᵀ.HasOrthogonalRows) :
    A.HasOrthogonalCols :=
  h
#align matrix.has_orthogonal_rows.has_orthogonal_cols Matrix.HasOrthogonalRows.hasOrthogonalCols

/- warning: matrix.has_orthogonal_cols.transpose_has_orthogonal_rows -> Matrix.HasOrthogonalCols.transpose_hasOrthogonalRows is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {n : Type.{u2}} {m : Type.{u3}} [_inst_1 : Mul.{u1} α] [_inst_2 : AddCommMonoid.{u1} α] {A : Matrix.{u3, u2, u1} m n α} [_inst_3 : Fintype.{u3} m], (Matrix.HasOrthogonalCols.{u1, u2, u3} α n m _inst_1 _inst_2 A _inst_3) -> (Matrix.HasOrthogonalRows.{u1, u3, u2} α m n _inst_1 _inst_2 (Matrix.transpose.{u1, u3, u2} m n α A) _inst_3)
but is expected to have type
  forall {α : Type.{u2}} {n : Type.{u1}} {m : Type.{u3}} [_inst_1 : Mul.{u2} α] [_inst_2 : AddCommMonoid.{u2} α] {A : Matrix.{u3, u1, u2} m n α} [_inst_3 : Fintype.{u3} m], (Matrix.HasOrthogonalCols.{u2, u1, u3} α n m _inst_1 _inst_2 A _inst_3) -> (Matrix.HasOrthogonalRows.{u2, u3, u1} α m n _inst_1 _inst_2 (Matrix.transpose.{u2, u3, u1} m n α A) _inst_3)
Case conversion may be inaccurate. Consider using '#align matrix.has_orthogonal_cols.transpose_has_orthogonal_rows Matrix.HasOrthogonalCols.transpose_hasOrthogonalRowsₓ'. -/
theorem HasOrthogonalCols.transpose_hasOrthogonalRows [Fintype m] (h : A.HasOrthogonalCols) :
    Aᵀ.HasOrthogonalRows :=
  h
#align matrix.has_orthogonal_cols.transpose_has_orthogonal_rows Matrix.HasOrthogonalCols.transpose_hasOrthogonalRows

/- warning: matrix.has_orthogonal_cols.has_orthogonal_rows -> Matrix.HasOrthogonalCols.hasOrthogonalRows is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {n : Type.{u2}} {m : Type.{u3}} [_inst_1 : Mul.{u1} α] [_inst_2 : AddCommMonoid.{u1} α] {A : Matrix.{u3, u2, u1} m n α} [_inst_3 : Fintype.{u2} n], (Matrix.HasOrthogonalCols.{u1, u3, u2} α m n _inst_1 _inst_2 (Matrix.transpose.{u1, u3, u2} m n α A) _inst_3) -> (Matrix.HasOrthogonalRows.{u1, u2, u3} α n m _inst_1 _inst_2 A _inst_3)
but is expected to have type
  forall {α : Type.{u2}} {n : Type.{u3}} {m : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : AddCommMonoid.{u2} α] {A : Matrix.{u1, u3, u2} m n α} [_inst_3 : Fintype.{u3} n], (Matrix.HasOrthogonalCols.{u2, u1, u3} α m n _inst_1 _inst_2 (Matrix.transpose.{u2, u1, u3} m n α A) _inst_3) -> (Matrix.HasOrthogonalRows.{u2, u3, u1} α n m _inst_1 _inst_2 A _inst_3)
Case conversion may be inaccurate. Consider using '#align matrix.has_orthogonal_cols.has_orthogonal_rows Matrix.HasOrthogonalCols.hasOrthogonalRowsₓ'. -/
theorem HasOrthogonalCols.hasOrthogonalRows [Fintype n] (h : Aᵀ.HasOrthogonalCols) :
    A.HasOrthogonalRows :=
  h
#align matrix.has_orthogonal_cols.has_orthogonal_rows Matrix.HasOrthogonalCols.hasOrthogonalRows

/- warning: matrix.has_orthogonal_rows.transpose_has_orthogonal_cols -> Matrix.HasOrthogonalRows.transpose_hasOrthogonalCols is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {n : Type.{u2}} {m : Type.{u3}} [_inst_1 : Mul.{u1} α] [_inst_2 : AddCommMonoid.{u1} α] {A : Matrix.{u3, u2, u1} m n α} [_inst_3 : Fintype.{u2} n], (Matrix.HasOrthogonalRows.{u1, u2, u3} α n m _inst_1 _inst_2 A _inst_3) -> (Matrix.HasOrthogonalCols.{u1, u3, u2} α m n _inst_1 _inst_2 (Matrix.transpose.{u1, u3, u2} m n α A) _inst_3)
but is expected to have type
  forall {α : Type.{u2}} {n : Type.{u3}} {m : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : AddCommMonoid.{u2} α] {A : Matrix.{u1, u3, u2} m n α} [_inst_3 : Fintype.{u3} n], (Matrix.HasOrthogonalRows.{u2, u3, u1} α n m _inst_1 _inst_2 A _inst_3) -> (Matrix.HasOrthogonalCols.{u2, u1, u3} α m n _inst_1 _inst_2 (Matrix.transpose.{u2, u1, u3} m n α A) _inst_3)
Case conversion may be inaccurate. Consider using '#align matrix.has_orthogonal_rows.transpose_has_orthogonal_cols Matrix.HasOrthogonalRows.transpose_hasOrthogonalColsₓ'. -/
theorem HasOrthogonalRows.transpose_hasOrthogonalCols [Fintype n] (h : A.HasOrthogonalRows) :
    Aᵀ.HasOrthogonalCols :=
  h
#align matrix.has_orthogonal_rows.transpose_has_orthogonal_cols Matrix.HasOrthogonalRows.transpose_hasOrthogonalCols

end Matrix

