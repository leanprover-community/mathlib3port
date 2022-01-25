import Mathbin.LinearAlgebra.Matrix.Trace

/-!
# Hadamard product of matrices

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

open_locale Matrix BigOperators

/-- `matrix.hadamard` defines the Hadamard product,
    which is the pointwise product of two matrices of the same size.-/
@[simp]
def hadamard [Mul α] (A : Matrix m n α) (B : Matrix m n α) : Matrix m n α
  | i, j => A i j * B i j

localized [Matrix] infixl:100 " ⊙ " => Matrix.hadamard

section BasicProperties

variable (A : Matrix m n α) (B : Matrix m n α) (C : Matrix m n α)

theorem hadamard_comm [CommSemigroupₓ α] : A ⊙ B = B ⊙ A :=
  ext $ fun _ _ => mul_comm _ _

theorem hadamard_assoc [Semigroupₓ α] : A ⊙ B ⊙ C = A ⊙ (B ⊙ C) :=
  ext $ fun _ _ => mul_assoc _ _ _

theorem hadamard_add [Distrib α] : A ⊙ (B + C) = A ⊙ B + A ⊙ C :=
  ext $ fun _ _ => left_distrib _ _ _

theorem add_hadamard [Distrib α] : (B + C) ⊙ A = B ⊙ A + C ⊙ A :=
  ext $ fun _ _ => right_distrib _ _ _

section Scalar

@[simp]
theorem smul_hadamard [Mul α] [HasScalar R α] [IsScalarTower R α α] (k : R) : (k • A) ⊙ B = k • A ⊙ B :=
  ext $ fun _ _ => smul_mul_assoc _ _ _

@[simp]
theorem hadamard_smul [Mul α] [HasScalar R α] [SmulCommClass R α α] (k : R) : A ⊙ (k • B) = k • A ⊙ B :=
  ext $ fun _ _ => mul_smul_comm _ _ _

end Scalar

section Zero

variable [MulZeroClass α]

@[simp]
theorem hadamard_zero : A ⊙ (0 : Matrix m n α) = 0 :=
  ext $ fun _ _ => mul_zero _

@[simp]
theorem zero_hadamard : (0 : Matrix m n α) ⊙ A = 0 :=
  ext $ fun _ _ => zero_mul _

end Zero

section One

variable [DecidableEq n] [MulZeroOneClass α]

variable (M : Matrix n n α)

theorem hadamard_one : M ⊙ (1 : Matrix n n α) = diagonal fun i => M i i := by
  ext
  by_cases' h : i = j <;> simp [h]

theorem one_hadamard : (1 : Matrix n n α) ⊙ M = diagonal fun i => M i i := by
  ext
  by_cases' h : i = j <;> simp [h]

end One

section Diagonal

variable [DecidableEq n] [MulZeroClass α]

theorem diagonal_hadamard_diagonal (v : n → α) (w : n → α) : diagonal v ⊙ diagonal w = diagonal (v * w) :=
  ext $ fun _ _ => (apply_ite2 _ _ _ _ _ _).trans (congr_argₓ _ $ zero_mul 0)

end Diagonal

section trace

variable [Fintype m] [Fintype n]

variable (R) [Semiringₓ α] [Semiringₓ R] [Module R α]

theorem sum_hadamard_eq : (∑ (i : m) (j : n), (A ⊙ B) i j) = trace m R α (A ⬝ (B)ᵀ) :=
  rfl

theorem dot_product_vec_mul_hadamard [DecidableEq m] [DecidableEq n] (v : m → α) (w : n → α) :
    dot_product (vec_mul v (A ⊙ B)) w = trace m R α (diagonal v ⬝ A ⬝ (B ⬝ diagonal w)ᵀ) := by
  rw [← sum_hadamard_eq, Finset.sum_comm]
  simp [dot_product, vec_mul, Finset.sum_mul, mul_assoc]

end trace

end BasicProperties

end Matrix

