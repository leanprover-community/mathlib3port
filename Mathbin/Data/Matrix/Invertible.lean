/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Algebra.Group.Invertible.Defs
import Data.Matrix.Basic

#align_import data.matrix.invertible from "leanprover-community/mathlib"@"5d0c76894ada7940957143163d7b921345474cbc"

/-! # Extra lemmas about invertible matrices

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Many of the `invertible` lemmas are about `*`; this restates them to be about `⬝`.

For lemmas about the matrix inverse in terms of the determinant and adjugate, see `matrix.has_inv`
in `linear_algebra/matrix/nonsingular_inverse.lean`.
-/


open scoped Matrix

variable {m n : Type _} {α : Type _}

variable [Fintype n] [DecidableEq n] [Semiring α]

namespace Matrix

/- warning: matrix.inv_of_mul_self clashes with inv_of_mul_self -> invOf_mul_self
Case conversion may be inaccurate. Consider using '#align matrix.inv_of_mul_self invOf_mul_selfₓ'. -/
#print invOf_mul_self /-
/-- A copy of `inv_of_mul_self` using `⬝` not `*`. -/
protected theorem invOf_mul_self (A : Matrix n n α) [Invertible A] : ⅟ A ⬝ A = 1 :=
  invOf_mul_self A
#align matrix.inv_of_mul_self invOf_mul_self
-/

/- warning: matrix.mul_inv_of_self clashes with mul_inv_of_self -> mul_invOf_self
Case conversion may be inaccurate. Consider using '#align matrix.mul_inv_of_self mul_invOf_selfₓ'. -/
#print mul_invOf_self /-
/-- A copy of `mul_inv_of_self` using `⬝` not `*`. -/
protected theorem mul_invOf_self (A : Matrix n n α) [Invertible A] : A ⬝ ⅟ A = 1 :=
  mul_invOf_self A
#align matrix.mul_inv_of_self mul_invOf_self
-/

#print Matrix.invOf_mul_self_assoc /-
/-- A copy of `inv_of_mul_self_assoc` using `⬝` not `*`. -/
protected theorem invOf_mul_self_assoc (A : Matrix n n α) (B : Matrix n m α) [Invertible A] :
    ⅟ A ⬝ (A ⬝ B) = B := by rw [← Matrix.mul_assoc, invOf_mul_self, Matrix.one_mul]
#align matrix.inv_of_mul_self_assoc Matrix.invOf_mul_self_assoc
-/

#print Matrix.mul_invOf_self_assoc /-
/-- A copy of `mul_inv_of_self_assoc` using `⬝` not `*`. -/
protected theorem mul_invOf_self_assoc (A : Matrix n n α) (B : Matrix n m α) [Invertible A] :
    A ⬝ (⅟ A ⬝ B) = B := by rw [← Matrix.mul_assoc, mul_invOf_self, Matrix.one_mul]
#align matrix.mul_inv_of_self_assoc Matrix.mul_invOf_self_assoc
-/

#print Matrix.mul_invOf_mul_self_cancel /-
/-- A copy of `mul_inv_of_mul_self_cancel` using `⬝` not `*`. -/
protected theorem mul_invOf_mul_self_cancel (A : Matrix m n α) (B : Matrix n n α) [Invertible B] :
    A ⬝ ⅟ B ⬝ B = A := by rw [Matrix.mul_assoc, invOf_mul_self, Matrix.mul_one]
#align matrix.mul_inv_of_mul_self_cancel Matrix.mul_invOf_mul_self_cancel
-/

#print Matrix.mul_mul_invOf_self_cancel /-
/-- A copy of `mul_mul_inv_of_self_cancel` using `⬝` not `*`. -/
protected theorem mul_mul_invOf_self_cancel (A : Matrix m n α) (B : Matrix n n α) [Invertible B] :
    A ⬝ B ⬝ ⅟ B = A := by rw [Matrix.mul_assoc, mul_invOf_self, Matrix.mul_one]
#align matrix.mul_mul_inv_of_self_cancel Matrix.mul_mul_invOf_self_cancel
-/

/- warning: matrix.invertible_mul clashes with invertible_mul -> invertibleMul
Case conversion may be inaccurate. Consider using '#align matrix.invertible_mul invertibleMulₓ'. -/
#print invertibleMul /-
/-- A copy of `invertible_mul` using `⬝` not `*`. -/
@[reducible]
protected def invertibleMul (A B : Matrix n n α) [Invertible A] [Invertible B] :
    Invertible (A ⬝ B) :=
  { invertibleMul _ _ with invOf := ⅟ B ⬝ ⅟ A }
#align matrix.invertible_mul invertibleMul
-/

/-- A copy of `invertible.mul` using `⬝` not `*`.-/
@[reducible]
def Invertible.matrixMul {A B : Matrix n n α} (ha : Invertible A) (hb : Invertible B) :
    Invertible (A ⬝ B) :=
  invertibleMul _ _
#align invertible.matrix_mul Invertible.matrixMul

/- warning: matrix.inv_of_mul clashes with inv_of_mul -> invOf_mul
Case conversion may be inaccurate. Consider using '#align matrix.inv_of_mul invOf_mulₓ'. -/
#print invOf_mul /-
protected theorem invOf_mul {A B : Matrix n n α} [Invertible A] [Invertible B]
    [Invertible (A ⬝ B)] : ⅟ (A ⬝ B) = ⅟ B ⬝ ⅟ A :=
  invOf_mul _ _
#align matrix.inv_of_mul invOf_mul
-/

/- warning: matrix.invertible_of_invertible_mul clashes with invertible_of_invertible_mul -> invertibleOfInvertibleMul
Case conversion may be inaccurate. Consider using '#align matrix.invertible_of_invertible_mul invertibleOfInvertibleMulₓ'. -/
#print invertibleOfInvertibleMul /-
/-- A copy of `invertible_of_invertible_mul` using `⬝` not `*`. -/
@[reducible]
protected def invertibleOfInvertibleMul (a b : Matrix n n α) [Invertible a] [Invertible (a ⬝ b)] :
    Invertible b :=
  { invertibleOfInvertibleMul a b with invOf := ⅟ (a ⬝ b) ⬝ a }
#align matrix.invertible_of_invertible_mul invertibleOfInvertibleMul
-/

/- warning: matrix.invertible_of_mul_invertible clashes with invertible_of_mul_invertible -> invertibleOfMulInvertible
Case conversion may be inaccurate. Consider using '#align matrix.invertible_of_mul_invertible invertibleOfMulInvertibleₓ'. -/
#print invertibleOfMulInvertible /-
/-- A copy of `invertible_of_mul_invertible` using `⬝` not `*`. -/
@[reducible]
protected def invertibleOfMulInvertible (a b : Matrix n n α) [Invertible (a ⬝ b)] [Invertible b] :
    Invertible a :=
  { invertibleOfMulInvertible a b with invOf := b ⬝ ⅟ (a ⬝ b) }
#align matrix.invertible_of_mul_invertible invertibleOfMulInvertible
-/

end Matrix

/- warning: invertible.matrix_mul_left clashes with invertible.mul_left -> Invertible.mulLeft
Case conversion may be inaccurate. Consider using '#align invertible.matrix_mul_left Invertible.mulLeftₓ'. -/
#print Invertible.mulLeft /-
/-- A copy of `invertible.mul_left` using `⬝` not `*`. -/
@[reducible]
def Invertible.mulLeft {a : Matrix n n α} (ha : Invertible a) (b : Matrix n n α) :
    Invertible b ≃ Invertible (a ⬝ b)
    where
  toFun hb := invertibleMul a b
  invFun hab := invertibleOfInvertibleMul a _
  left_inv hb := Subsingleton.elim _ _
  right_inv hab := Subsingleton.elim _ _
#align invertible.matrix_mul_left Invertible.mulLeft
-/

/- warning: invertible.matrix_mul_right clashes with invertible.mul_right -> Invertible.mulRight
Case conversion may be inaccurate. Consider using '#align invertible.matrix_mul_right Invertible.mulRightₓ'. -/
#print Invertible.mulRight /-
/-- A copy of `invertible.mul_right` using `⬝` not `*`. -/
@[reducible]
def Invertible.mulRight (a : Matrix n n α) {b : Matrix n n α} (ha : Invertible b) :
    Invertible a ≃ Invertible (a ⬝ b)
    where
  toFun hb := invertibleMul a b
  invFun hab := invertibleOfMulInvertible _ b
  left_inv hb := Subsingleton.elim _ _
  right_inv hab := Subsingleton.elim _ _
#align invertible.matrix_mul_right Invertible.mulRight
-/

