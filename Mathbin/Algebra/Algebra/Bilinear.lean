/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
import Mathbin.Algebra.Algebra.Basic
import Mathbin.Algebra.Hom.Iterate
import Mathbin.Algebra.Hom.NonUnitalAlg
import Mathbin.LinearAlgebra.TensorProduct

/-!
# Facts about algebras involving bilinear maps and tensor products

We move a few basic statements about algebras out of `algebra.algebra.basic`,
in order to avoid importing `linear_algebra.bilinear_map` and
`linear_algebra.tensor_product` unnecessarily.
-/


open TensorProduct

open Module

namespace LinearMap

section NonUnitalNonAssoc

variable (R A : Type _) [CommSemiringₓ R] [NonUnitalNonAssocSemiringₓ A] [Module R A] [SmulCommClass R A A]
  [IsScalarTower R A A]

/-- The multiplication in a non-unital non-associative algebra is a bilinear map.

A weaker version of this for semirings exists as `add_monoid_hom.mul`. -/
def mul : A →ₗ[R] A →ₗ[R] A :=
  LinearMap.mk₂ R (· * ·) add_mulₓ smul_mul_assoc mul_addₓ mul_smul_comm

/-- The multiplication map on a non-unital algebra, as an `R`-linear map from `A ⊗[R] A` to `A`. -/
def mul' : A ⊗[R] A →ₗ[R] A :=
  TensorProduct.lift (mul R A)

variable {A}

/-- The multiplication on the left in a non-unital algebra is a linear map. -/
def mulLeft (a : A) : A →ₗ[R] A :=
  mul R A a

/-- The multiplication on the right in an algebra is a linear map. -/
def mulRight (a : A) : A →ₗ[R] A :=
  (mul R A).flip a

/-- Simultaneous multiplication on the left and right is a linear map. -/
def mulLeftRight (ab : A × A) : A →ₗ[R] A :=
  (mulRight R ab.snd).comp (mulLeft R ab.fst)

@[simp]
theorem mul_left_to_add_monoid_hom (a : A) : (mulLeft R a : A →+ A) = AddMonoidHom.mulLeft a :=
  rfl

@[simp]
theorem mul_right_to_add_monoid_hom (a : A) : (mulRight R a : A →+ A) = AddMonoidHom.mulRight a :=
  rfl

variable {R}

@[simp]
theorem mul_apply' (a b : A) : mul R A a b = a * b :=
  rfl

@[simp]
theorem mul_left_apply (a b : A) : mulLeft R a b = a * b :=
  rfl

@[simp]
theorem mul_right_apply (a b : A) : mulRight R a b = b * a :=
  rfl

@[simp]
theorem mul_left_right_apply (a b x : A) : mulLeftRight R (a, b) x = a * x * b :=
  rfl

@[simp]
theorem mul'_apply {a b : A} : mul' R A (a ⊗ₜ b) = a * b := by
  simp only [← LinearMap.mul', ← TensorProduct.lift.tmul, ← mul_apply']

@[simp]
theorem mul_left_zero_eq_zero : mulLeft R (0 : A) = 0 :=
  (mul R A).map_zero

@[simp]
theorem mul_right_zero_eq_zero : mulRight R (0 : A) = 0 :=
  (mul R A).flip.map_zero

end NonUnitalNonAssoc

section NonUnital

variable (R A : Type _) [CommSemiringₓ R] [NonUnitalSemiringₓ A] [Module R A] [SmulCommClass R A A]
  [IsScalarTower R A A]

/-- The multiplication in a non-unital algebra is a bilinear map.

A weaker version of this for non-unital non-associative algebras exists as `linear_map.mul`. -/
def _root_.non_unital_alg_hom.lmul : A →ₙₐ[R] End R A :=
  { mul R A with
    map_mul' := by
      intro a b
      ext c
      exact mul_assoc a b c,
    map_zero' := by
      ext a
      exact zero_mul a }

variable {R A}

@[simp]
theorem _root_.non_unital_alg_hom.coe_lmul_eq_mul : ⇑(NonUnitalAlgHom.lmul R A) = mul R A :=
  rfl

theorem commute_mul_left_right (a b : A) : Commute (mulLeft R a) (mulRight R b) := by
  ext c
  exact (mul_assoc a c b).symm

@[simp]
theorem mul_left_mul (a b : A) : mulLeft R (a * b) = (mulLeft R a).comp (mulLeft R b) := by
  ext
  simp only [← mul_left_apply, ← comp_apply, ← mul_assoc]

@[simp]
theorem mul_right_mul (a b : A) : mulRight R (a * b) = (mulRight R b).comp (mulRight R a) := by
  ext
  simp only [← mul_right_apply, ← comp_apply, ← mul_assoc]

end NonUnital

section Semiringₓ

variable (R A : Type _) [CommSemiringₓ R] [Semiringₓ A] [Algebra R A]

/-- The multiplication in an algebra is an algebra homomorphism into the endomorphisms on
the algebra.

A weaker version of this for non-unital algebras exists as `non_unital_alg_hom.mul`. -/
def _root_.algebra.lmul : A →ₐ[R] End R A :=
  { LinearMap.mul R A with
    map_one' := by
      ext a
      exact one_mulₓ a,
    map_mul' := by
      intro a b
      ext c
      exact mul_assoc a b c,
    map_zero' := by
      ext a
      exact zero_mul a,
    commutes' := by
      intro r
      ext a
      exact (Algebra.smul_def r a).symm }

variable {R A}

@[simp]
theorem _root_.algebra.coe_lmul_eq_mul : ⇑(Algebra.lmul R A) = mul R A :=
  rfl

@[simp]
theorem mul_left_eq_zero_iff (a : A) : mulLeft R a = 0 ↔ a = 0 := by
  constructor <;> intro h
  · rw [← mul_oneₓ a, ← mul_left_apply a 1, h, LinearMap.zero_apply]
    
  · rw [h]
    exact mul_left_zero_eq_zero
    

@[simp]
theorem mul_right_eq_zero_iff (a : A) : mulRight R a = 0 ↔ a = 0 := by
  constructor <;> intro h
  · rw [← one_mulₓ a, ← mul_right_apply a 1, h, LinearMap.zero_apply]
    
  · rw [h]
    exact mul_right_zero_eq_zero
    

@[simp]
theorem mul_left_one : mulLeft R (1 : A) = LinearMap.id := by
  ext
  simp only [← LinearMap.id_coe, ← one_mulₓ, ← id.def, ← mul_left_apply]

@[simp]
theorem mul_right_one : mulRight R (1 : A) = LinearMap.id := by
  ext
  simp only [← LinearMap.id_coe, ← mul_oneₓ, ← id.def, ← mul_right_apply]

@[simp]
theorem pow_mul_left (a : A) (n : ℕ) : mulLeft R a ^ n = mulLeft R (a ^ n) := by
  simpa only [← mul_left, Algebra.coe_lmul_eq_mul] using ((Algebra.lmul R A).map_pow a n).symm

@[simp]
theorem pow_mul_right (a : A) (n : ℕ) : mulRight R a ^ n = mulRight R (a ^ n) := by
  simp only [← mul_right, Algebra.coe_lmul_eq_mul]
  exact LinearMap.coe_injective (((mul_right R a).coe_pow n).symm ▸ mul_right_iterate a n)

end Semiringₓ

section Ringₓ

variable {R A : Type _} [CommSemiringₓ R] [Ringₓ A] [Algebra R A]

theorem mul_left_injective [NoZeroDivisors A] {x : A} (hx : x ≠ 0) : Function.Injective (mulLeft R x) := by
  letI : IsDomain A := { ‹Ringₓ A›, ‹NoZeroDivisors A› with exists_pair_ne := ⟨x, 0, hx⟩ }
  exact mul_right_injective₀ hx

theorem mul_right_injective [NoZeroDivisors A] {x : A} (hx : x ≠ 0) : Function.Injective (mulRight R x) := by
  letI : IsDomain A := { ‹Ringₓ A›, ‹NoZeroDivisors A› with exists_pair_ne := ⟨x, 0, hx⟩ }
  exact mul_left_injective₀ hx

theorem mul_injective [NoZeroDivisors A] {x : A} (hx : x ≠ 0) : Function.Injective (mul R A x) := by
  letI : IsDomain A := { ‹Ringₓ A›, ‹NoZeroDivisors A› with exists_pair_ne := ⟨x, 0, hx⟩ }
  exact mul_right_injective₀ hx

end Ringₓ

end LinearMap

