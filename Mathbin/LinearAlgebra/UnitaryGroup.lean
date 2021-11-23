import Mathbin.LinearAlgebra.Matrix.ToLin 
import Mathbin.LinearAlgebra.Matrix.NonsingularInverse

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

section 

variable(M : Type v)[Monoidₓ M][StarMonoid M]

/--
In a `star_monoid M`, `unitary_submonoid M` is the submonoid consisting of all the elements of
`M` such that `star A * A = 1`.
-/
def unitarySubmonoid : Submonoid M :=
  { Carrier := { A | (star A*A) = 1 },
    one_mem' :=
      by 
        simp ,
    mul_mem' :=
      fun A B hA : (star A*A) = 1 hB : (star B*B) = 1 =>
        show (star (A*B)*A*B) = 1by 
          rwa [star_mul, ←mul_assocₓ, mul_assocₓ _ _ A, hA, mul_oneₓ] }

end 

namespace Matrix

open LinearMap

open_locale Matrix

section 

variable(n : Type u)[DecidableEq n][Fintype n]

variable(α : Type v)[CommRingₓ α][StarRing α]

-- error in LinearAlgebra.UnitaryGroup: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler monoid
/--
`unitary_group n` is the group of `n` by `n` matrices where the star-transpose is the inverse.
-/ @[derive #[expr monoid]] def unitary_group : Type* :=
unitary_submonoid (matrix n n α)

end 

variable{n : Type u}[DecidableEq n][Fintype n]

variable{α : Type v}[CommRingₓ α][StarRing α]

namespace unitarySubmonoid

theorem star_mem {A : Matrix n n α} (h : A ∈ unitarySubmonoid (Matrix n n α)) :
  star A ∈ unitarySubmonoid (Matrix n n α) :=
  mul_eq_one_comm.mp$ (star_star A).symm ▸ h

@[simp]
theorem star_mem_iff {A : Matrix n n α} :
  star A ∈ unitarySubmonoid (Matrix n n α) ↔ A ∈ unitarySubmonoid (Matrix n n α) :=
  ⟨fun ha => star_star A ▸ star_mem ha, star_mem⟩

end unitarySubmonoid

namespace UnitaryGroup

instance coe_matrix : Coe (unitary_group n α) (Matrix n n α) :=
  ⟨Subtype.val⟩

instance coe_fun : CoeFun (unitary_group n α) fun _ => n → n → α :=
  { coe := fun A => A.val }

/--
`to_lin' A` is matrix multiplication of vectors by `A`, as a linear map.

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

instance  : HasInv (unitary_group n α) :=
  ⟨fun A => ⟨star A.1, unitary_submonoid.star_mem_iff.mpr A.2⟩⟩

instance  : StarMonoid (unitary_group n α) :=
  { star := fun A => ⟨star A.1, unitary_submonoid.star_mem A.2⟩, star_involutive := fun A => Subtype.ext$ star_star A.1,
    star_mul := fun A B => Subtype.ext$ star_mul A.1 B.1 }

@[simp]
theorem star_mul_self (A : unitary_group n α) : star A ⬝ A = 1 :=
  A.2

instance  : Inhabited (unitary_group n α) :=
  ⟨1⟩

section CoeLemmas

variable(A B : unitary_group n α)

@[simp]
theorem inv_val : «expr↑ » (A⁻¹) = (star A : Matrix n n α) :=
  rfl

@[simp]
theorem inv_apply : «expr⇑ » (A⁻¹) = (star A : Matrix n n α) :=
  rfl

@[simp]
theorem mul_val : «expr↑ » (A*B) = A ⬝ B :=
  rfl

@[simp]
theorem mul_apply : «expr⇑ » (A*B) = A ⬝ B :=
  rfl

@[simp]
theorem one_val : «expr↑ » (1 : unitary_group n α) = (1 : Matrix n n α) :=
  rfl

@[simp]
theorem one_apply : «expr⇑ » (1 : unitary_group n α) = (1 : Matrix n n α) :=
  rfl

@[simp]
theorem to_lin'_mul : to_lin' (A*B) = (to_lin' A).comp (to_lin' B) :=
  Matrix.to_lin'_mul A B

@[simp]
theorem to_lin'_one : to_lin' (1 : unitary_group n α) = LinearMap.id :=
  Matrix.to_lin'_one

end CoeLemmas

instance  : Groupₓ (unitary_group n α) :=
  { unitary_group.has_inv, unitary_group.monoid n α with mul_left_inv := fun A => Subtype.eq A.2 }

/-- `to_linear_equiv A` is matrix multiplication of vectors by `A`, as a linear equivalence. -/
def to_linear_equiv (A : unitary_group n α) : (n → α) ≃ₗ[α] n → α :=
  { Matrix.toLin' A with invFun := A⁻¹.toLin',
    left_inv :=
      fun x =>
        calc A⁻¹.toLin'.comp A.to_lin' x = (A⁻¹*A).toLin' x :=
          by 
            rw [←to_lin'_mul]
          _ = x :=
          by 
            rw [mul_left_invₓ, to_lin'_one, id_apply]
          ,
    right_inv :=
      fun x =>
        calc A.to_lin'.comp A⁻¹.toLin' x = (A*A⁻¹).toLin' x :=
          by 
            rw [←to_lin'_mul]
          _ = x :=
          by 
            rw [mul_right_invₓ, to_lin'_one, id_apply]
           }

/-- `to_GL` is the map from the unitary group to the general linear group -/
def to_GL (A : unitary_group n α) : general_linear_group α (n → α) :=
  general_linear_group.of_linear_equiv (to_linear_equiv A)

theorem coe_to_GL (A : unitary_group n α) : «expr↑ » (to_GL A) = A.to_lin' :=
  rfl

@[simp]
theorem to_GL_one : to_GL (1 : unitary_group n α) = 1 :=
  by 
    ext1 v i 
    rw [coe_to_GL, to_lin'_one]
    rfl

@[simp]
theorem to_GL_mul (A B : unitary_group n α) : to_GL (A*B) = to_GL A*to_GL B :=
  by 
    ext1 v i 
    rw [coe_to_GL, to_lin'_mul]
    rfl

/-- `unitary_group.embedding_GL` is the embedding from `unitary_group n α`
to `general_linear_group n α`. -/
def embedding_GL : unitary_group n α →* general_linear_group α (n → α) :=
  ⟨fun A => to_GL A,
    by 
      simp ,
    by 
      simp ⟩

end UnitaryGroup

section OrthogonalGroup

variable(β : Type v)[CommRingₓ β]

attribute [local instance] starRingOfComm

/--
`orthogonal_group n` is the group of `n` by `n` matrices where the transpose is the inverse.
-/
abbrev orthogonal_group :=
  unitary_group n β

end OrthogonalGroup

end Matrix

