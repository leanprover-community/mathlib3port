import Mathbin.LinearAlgebra.Matrix.ToLin
import Mathbin.LinearAlgebra.Matrix.NonsingularInverse
import Mathbin.Algebra.Star.Unitary

/-!
# The Unitary Group

This file defines elements of the unitary group `unitary_group n α`, where `α` is a `star_ring`.
This consists of all `n` by `n` matrices with entries in `α` such that the star-transpose is its
inverse. In addition, we define the group structure on `unitary_group n α`, and the embedding into
the general linear group `general_linear_group α (n → α)`.

We also define the orthogonal group `orthogonal_group n β`, where `β` is a `comm_ring`.

## Main Definitions

 * `matrix.unitary_group` is the type of matrices where the star-transpose is the inverse
 * `matrix.unitary_group.group` is the group structure (under multiplication)
 * `matrix.unitary_group.embedding_GL` is the embedding `unitary_group n α → GLₙ(α)`
 * `matrix.orthogonal_group` is the type of matrices where the transpose is the inverse

## References

 * https://en.wikipedia.org/wiki/Unitary_group

## Tags

matrix group, group, unitary group, orthogonal group

-/


universe u v

namespace Matrix

open LinearMap

open_locale Matrix

section

variable (n : Type u) [DecidableEq n] [Fintype n]

variable (α : Type v) [CommRingₓ α] [StarRing α]

/-- `unitary_group n` is the group of `n` by `n` matrices where the star-transpose is the inverse.
-/
abbrev unitary_group :=
  unitary (Matrix n n α)

end

variable {n : Type u} [DecidableEq n] [Fintype n]

variable {α : Type v} [CommRingₓ α] [StarRing α]

namespace UnitaryGroup

instance coe_matrix : Coe (unitary_group n α) (Matrix n n α) :=
  ⟨Subtype.val⟩

instance coe_fun : CoeFun (unitary_group n α) fun _ => n → n → α where
  coe := fun A => A.val

/-- `to_lin' A` is matrix multiplication of vectors by `A`, as a linear map.

After the group structure on `unitary_group n` is defined,
we show in `to_linear_equiv` that this gives a linear equivalence.
-/
def to_lin' (A : unitary_group n α) :=
  Matrix.toLin' A

theorem ext_iff (A B : unitary_group n α) : A = B ↔ ∀ i j, A i j = B i j :=
  Subtype.ext_iff_val.trans ⟨fun h i j => congr_funₓ (congr_funₓ h i) j, Matrix.ext⟩

@[ext]
theorem ext (A B : unitary_group n α) : (∀ i j, A i j = B i j) → A = B :=
  (unitary_group.ext_iff A B).mpr

@[simp]
theorem star_mul_self (A : unitary_group n α) : star A ⬝ A = 1 :=
  A.2.1

section CoeLemmas

variable (A B : unitary_group n α)

@[simp]
theorem inv_val : ↑A⁻¹ = (star A : Matrix n n α) :=
  rfl

@[simp]
theorem inv_apply : ⇑A⁻¹ = (star A : Matrix n n α) :=
  rfl

@[simp]
theorem mul_val : ↑(A * B) = A ⬝ B :=
  rfl

@[simp]
theorem mul_apply : ⇑(A * B) = A ⬝ B :=
  rfl

@[simp]
theorem one_val : ↑(1 : unitary_group n α) = (1 : Matrix n n α) :=
  rfl

@[simp]
theorem one_apply : ⇑(1 : unitary_group n α) = (1 : Matrix n n α) :=
  rfl

@[simp]
theorem to_lin'_mul : to_lin' (A * B) = (to_lin' A).comp (to_lin' B) :=
  Matrix.to_lin'_mul A B

@[simp]
theorem to_lin'_one : to_lin' (1 : unitary_group n α) = LinearMap.id :=
  Matrix.to_lin'_one

end CoeLemmas

/-- `to_linear_equiv A` is matrix multiplication of vectors by `A`, as a linear equivalence. -/
def to_linear_equiv (A : unitary_group n α) : (n → α) ≃ₗ[α] n → α :=
  { Matrix.toLin' A with invFun := to_lin' (A⁻¹),
    left_inv := fun x =>
      calc
        (to_lin' (A⁻¹)).comp (to_lin' A) x = (to_lin' (A⁻¹ * A)) x := by
          rw [← to_lin'_mul]
        _ = x := by
          rw [mul_left_invₓ, to_lin'_one, id_apply]
        ,
    right_inv := fun x =>
      calc
        (to_lin' A).comp (to_lin' (A⁻¹)) x = to_lin' (A * A⁻¹) x := by
          rw [← to_lin'_mul]
        _ = x := by
          rw [mul_right_invₓ, to_lin'_one, id_apply]
         }

/-- `to_GL` is the map from the unitary group to the general linear group -/
def to_GL (A : unitary_group n α) : general_linear_group α (n → α) :=
  general_linear_group.of_linear_equiv (to_linear_equiv A)

theorem coe_to_GL (A : unitary_group n α) : ↑to_GL A = to_lin' A :=
  rfl

@[simp]
theorem to_GL_one : to_GL (1 : unitary_group n α) = 1 := by
  ext1 v i
  rw [coe_to_GL, to_lin'_one]
  rfl

@[simp]
theorem to_GL_mul (A B : unitary_group n α) : to_GL (A * B) = to_GL A * to_GL B := by
  ext1 v i
  rw [coe_to_GL, to_lin'_mul]
  rfl

/-- `unitary_group.embedding_GL` is the embedding from `unitary_group n α`
to `general_linear_group n α`. -/
def embedding_GL : unitary_group n α →* general_linear_group α (n → α) :=
  ⟨fun A => to_GL A, by
    simp , by
    simp ⟩

end UnitaryGroup

section OrthogonalGroup

variable (β : Type v) [CommRingₓ β]

attribute [local instance] starRingOfComm

/-- `orthogonal_group n` is the group of `n` by `n` matrices where the transpose is the inverse.
-/
abbrev orthogonal_group :=
  unitary_group n β

end OrthogonalGroup

end Matrix

