/-
Copyright (c) 2021 Lu-Ming Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lu-Ming Zhang
-/
import LinearAlgebra.Matrix.Trace

#align_import data.matrix.hadamard from "leanprover-community/mathlib"@"d64d67d000b974f0d86a2be7918cf800be6271c8"

/-!
# Hadamard product of matrices

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the Hadamard product `matrix.hadamard`
and contains basic properties about them.

## Main definition

- `matrix.hadamard`: defines the Hadamard product,
  which is the pointwise product of two matrices of the same size.

## Notation

* `⊙`: the Hadamard product `matrix.hadamard`;

## References

*  <https://en.wikipedia.org/wiki/hadamard_product_(matrices)>

## Tags

hadamard product, hadamard
-/


variable {α β γ m n : Type _}

variable {R : Type _}

namespace Matrix

open scoped Matrix BigOperators

#print Matrix.hadamard /-
/-- `matrix.hadamard` defines the Hadamard product,
    which is the pointwise product of two matrices of the same size.-/
def hadamard [Mul α] (A : Matrix m n α) (B : Matrix m n α) : Matrix m n α :=
  of fun i j => A i j * B i j
#align matrix.hadamard Matrix.hadamard
-/

#print Matrix.hadamard_apply /-
-- TODO: set as an equation lemma for `hadamard`, see mathlib4#3024
@[simp]
theorem hadamard_apply [Mul α] (A : Matrix m n α) (B : Matrix m n α) (i j) :
    hadamard A B i j = A i j * B i j :=
  rfl
#align matrix.hadamard_apply Matrix.hadamard_apply
-/

scoped infixl:100 " ⊙ " => Matrix.hadamard

section BasicProperties

variable (A : Matrix m n α) (B : Matrix m n α) (C : Matrix m n α)

#print Matrix.hadamard_comm /-
-- commutativity
theorem hadamard_comm [CommSemigroup α] : A ⊙ B = B ⊙ A :=
  ext fun _ _ => mul_comm _ _
#align matrix.hadamard_comm Matrix.hadamard_comm
-/

#print Matrix.hadamard_assoc /-
-- associativity
theorem hadamard_assoc [Semigroup α] : A ⊙ B ⊙ C = A ⊙ (B ⊙ C) :=
  ext fun _ _ => mul_assoc _ _ _
#align matrix.hadamard_assoc Matrix.hadamard_assoc
-/

#print Matrix.hadamard_add /-
-- distributivity
theorem hadamard_add [Distrib α] : A ⊙ (B + C) = A ⊙ B + A ⊙ C :=
  ext fun _ _ => left_distrib _ _ _
#align matrix.hadamard_add Matrix.hadamard_add
-/

#print Matrix.add_hadamard /-
theorem add_hadamard [Distrib α] : (B + C) ⊙ A = B ⊙ A + C ⊙ A :=
  ext fun _ _ => right_distrib _ _ _
#align matrix.add_hadamard Matrix.add_hadamard
-/

-- scalar multiplication
section Scalar

#print Matrix.smul_hadamard /-
@[simp]
theorem smul_hadamard [Mul α] [SMul R α] [IsScalarTower R α α] (k : R) : (k • A) ⊙ B = k • A ⊙ B :=
  ext fun _ _ => smul_mul_assoc _ _ _
#align matrix.smul_hadamard Matrix.smul_hadamard
-/

#print Matrix.hadamard_smul /-
@[simp]
theorem hadamard_smul [Mul α] [SMul R α] [SMulCommClass R α α] (k : R) : A ⊙ (k • B) = k • A ⊙ B :=
  ext fun _ _ => mul_smul_comm _ _ _
#align matrix.hadamard_smul Matrix.hadamard_smul
-/

end Scalar

section Zero

variable [MulZeroClass α]

#print Matrix.hadamard_zero /-
@[simp]
theorem hadamard_zero : A ⊙ (0 : Matrix m n α) = 0 :=
  ext fun _ _ => MulZeroClass.mul_zero _
#align matrix.hadamard_zero Matrix.hadamard_zero
-/

#print Matrix.zero_hadamard /-
@[simp]
theorem zero_hadamard : (0 : Matrix m n α) ⊙ A = 0 :=
  ext fun _ _ => MulZeroClass.zero_mul _
#align matrix.zero_hadamard Matrix.zero_hadamard
-/

end Zero

section One

variable [DecidableEq n] [MulZeroOneClass α]

variable (M : Matrix n n α)

#print Matrix.hadamard_one /-
theorem hadamard_one : M ⊙ (1 : Matrix n n α) = diagonal fun i => M i i := by ext;
  by_cases h : i = j <;> simp [h]
#align matrix.hadamard_one Matrix.hadamard_one
-/

#print Matrix.one_hadamard /-
theorem one_hadamard : (1 : Matrix n n α) ⊙ M = diagonal fun i => M i i := by ext;
  by_cases h : i = j <;> simp [h]
#align matrix.one_hadamard Matrix.one_hadamard
-/

end One

section Diagonal

variable [DecidableEq n] [MulZeroClass α]

#print Matrix.diagonal_hadamard_diagonal /-
theorem diagonal_hadamard_diagonal (v : n → α) (w : n → α) :
    diagonal v ⊙ diagonal w = diagonal (v * w) :=
  ext fun _ _ => (apply_ite₂ _ _ _ _ _ _).trans (congr_arg _ <| MulZeroClass.zero_mul 0)
#align matrix.diagonal_hadamard_diagonal Matrix.diagonal_hadamard_diagonal
-/

end Diagonal

section trace

variable [Fintype m] [Fintype n]

variable (R) [Semiring α] [Semiring R] [Module R α]

#print Matrix.sum_hadamard_eq /-
theorem sum_hadamard_eq : ∑ (i : m) (j : n), (A ⊙ B) i j = trace (A ⬝ Bᵀ) :=
  rfl
#align matrix.sum_hadamard_eq Matrix.sum_hadamard_eq
-/

#print Matrix.dotProduct_vecMul_hadamard /-
theorem dotProduct_vecMul_hadamard [DecidableEq m] [DecidableEq n] (v : m → α) (w : n → α) :
    dotProduct (vecMul v (A ⊙ B)) w = trace (diagonal v ⬝ A ⬝ (B ⬝ diagonal w)ᵀ) :=
  by
  rw [← sum_hadamard_eq, Finset.sum_comm]
  simp [dot_product, vec_mul, Finset.sum_mul, mul_assoc]
#align matrix.dot_product_vec_mul_hadamard Matrix.dotProduct_vecMul_hadamard
-/

end trace

end BasicProperties

end Matrix

