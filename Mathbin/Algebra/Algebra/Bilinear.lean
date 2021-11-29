import Mathbin.Algebra.Algebra.Basic 
import Mathbin.LinearAlgebra.TensorProduct 
import Mathbin.Algebra.IterateHom

/-!
# Facts about algebras involving bilinear maps and tensor products

We move a few basic statements about algebras out of `algebra.algebra.basic`,
in order to avoid importing `linear_algebra.bilinear_map` and
`linear_algebra.tensor_product` unnecessarily.
-/


universe u v w

namespace Algebra

open_locale TensorProduct

open Module

section 

variable (R A : Type _) [CommSemiringₓ R] [Semiringₓ A] [Algebra R A]

/-- The multiplication in an algebra is a bilinear map.

A weaker version of this for semirings exists as `add_monoid_hom.mul`. -/
def lmul : A →ₐ[R] End R A :=
  { show A →ₗ[R] A →ₗ[R] A from
      LinearMap.mk₂ R (·*·) (fun x y z => add_mulₓ x y z)
        (fun c x y =>
          by 
            rw [smul_def, smul_def, mul_assocₓ _ x y])
        (fun x y z => mul_addₓ x y z)
        fun c x y =>
          by 
            rw [smul_def, smul_def, left_comm] with
    map_one' :=
      by 
        ext a 
        exact one_mulₓ a,
    map_mul' :=
      by 
        intro a b 
        ext c 
        exact mul_assocₓ a b c,
    map_zero' :=
      by 
        ext a 
        exact zero_mul a,
    commutes' :=
      by 
        intro r 
        ext a 
        dsimp 
        rw [smul_def] }

variable {R A}

@[simp]
theorem lmul_apply (p q : A) : lmul R A p q = p*q :=
  rfl

variable (R)

/-- The multiplication on the left in an algebra is a linear map. -/
def lmul_left (r : A) : A →ₗ[R] A :=
  lmul R A r

/-- The multiplication on the right in an algebra is a linear map. -/
def lmul_right (r : A) : A →ₗ[R] A :=
  (lmul R A).toLinearMap.flip r

/-- Simultaneous multiplication on the left and right is a linear map. -/
def lmul_left_right (vw : A × A) : A →ₗ[R] A :=
  (lmul_right R vw.2).comp (lmul_left R vw.1)

theorem commute_lmul_left_right (a b : A) : Commute (lmul_left R a) (lmul_right R b) :=
  by 
    ext c 
    exact (mul_assocₓ a c b).symm

/-- The multiplication map on an algebra, as an `R`-linear map from `A ⊗[R] A` to `A`. -/
def lmul' : A ⊗[R] A →ₗ[R] A :=
  TensorProduct.lift (lmul R A).toLinearMap

variable {R A}

@[simp]
theorem lmul'_apply {x y : A} : lmul' R (x ⊗ₜ y) = x*y :=
  by 
    simp only [Algebra.lmul', TensorProduct.lift.tmul, AlgHom.to_linear_map_apply, lmul_apply]

@[simp]
theorem lmul_left_apply (p q : A) : lmul_left R p q = p*q :=
  rfl

@[simp]
theorem lmul_right_apply (p q : A) : lmul_right R p q = q*p :=
  rfl

@[simp]
theorem lmul_left_right_apply (vw : A × A) (p : A) : lmul_left_right R vw p = (vw.1*p)*vw.2 :=
  rfl

@[simp]
theorem lmul_left_one : lmul_left R (1 : A) = LinearMap.id :=
  by 
    ext 
    simp only [LinearMap.id_coe, one_mulₓ, id.def, lmul_left_apply]

@[simp]
theorem lmul_left_mul (a b : A) : lmul_left R (a*b) = (lmul_left R a).comp (lmul_left R b) :=
  by 
    ext 
    simp only [lmul_left_apply, LinearMap.comp_apply, mul_assocₓ]

@[simp]
theorem lmul_right_one : lmul_right R (1 : A) = LinearMap.id :=
  by 
    ext 
    simp only [LinearMap.id_coe, mul_oneₓ, id.def, lmul_right_apply]

@[simp]
theorem lmul_right_mul (a b : A) : lmul_right R (a*b) = (lmul_right R b).comp (lmul_right R a) :=
  by 
    ext 
    simp only [lmul_right_apply, LinearMap.comp_apply, mul_assocₓ]

@[simp]
theorem lmul_left_zero_eq_zero : lmul_left R (0 : A) = 0 :=
  (lmul R A).map_zero

@[simp]
theorem lmul_right_zero_eq_zero : lmul_right R (0 : A) = 0 :=
  (lmul R A).toLinearMap.flip.map_zero

@[simp]
theorem lmul_left_eq_zero_iff (a : A) : lmul_left R a = 0 ↔ a = 0 :=
  by 
    split  <;> intro h
    ·
      rw [←mul_oneₓ a, ←lmul_left_apply a 1, h, LinearMap.zero_apply]
    ·
      rw [h]
      exact lmul_left_zero_eq_zero

@[simp]
theorem lmul_right_eq_zero_iff (a : A) : lmul_right R a = 0 ↔ a = 0 :=
  by 
    split  <;> intro h
    ·
      rw [←one_mulₓ a, ←lmul_right_apply a 1, h, LinearMap.zero_apply]
    ·
      rw [h]
      exact lmul_right_zero_eq_zero

@[simp]
theorem pow_lmul_left (a : A) (n : ℕ) : lmul_left R a ^ n = lmul_left R (a ^ n) :=
  ((lmul R A).map_pow a n).symm

@[simp]
theorem pow_lmul_right (a : A) (n : ℕ) : lmul_right R a ^ n = lmul_right R (a ^ n) :=
  LinearMap.coe_injective$ ((lmul_right R a).coe_pow n).symm ▸ mul_right_iterate a n

end 

section 

variable {R A : Type _} [CommSemiringₓ R] [Ringₓ A] [Algebra R A]

-- error in Algebra.Algebra.Bilinear: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem lmul_left_injective [no_zero_divisors A] {x : A} (hx : «expr ≠ »(x, 0)) : function.injective (lmul_left R x) :=
by { letI [] [":", expr is_domain A] [":=", expr { exists_pair_ne := ⟨x, 0, hx⟩,
     ..«expr‹ ›»(ring A),
     ..«expr‹ ›»(no_zero_divisors A) }],
  exact [expr mul_right_injective₀ hx] }

-- error in Algebra.Algebra.Bilinear: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem lmul_right_injective
[no_zero_divisors A]
{x : A}
(hx : «expr ≠ »(x, 0)) : function.injective (lmul_right R x) :=
by { letI [] [":", expr is_domain A] [":=", expr { exists_pair_ne := ⟨x, 0, hx⟩,
     ..«expr‹ ›»(ring A),
     ..«expr‹ ›»(no_zero_divisors A) }],
  exact [expr mul_left_injective₀ hx] }

-- error in Algebra.Algebra.Bilinear: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem lmul_injective [no_zero_divisors A] {x : A} (hx : «expr ≠ »(x, 0)) : function.injective (lmul R A x) :=
by { letI [] [":", expr is_domain A] [":=", expr { exists_pair_ne := ⟨x, 0, hx⟩,
     ..«expr‹ ›»(ring A),
     ..«expr‹ ›»(no_zero_divisors A) }],
  exact [expr mul_right_injective₀ hx] }

end 

end Algebra

