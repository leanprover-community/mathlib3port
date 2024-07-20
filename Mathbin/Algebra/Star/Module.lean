/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Frédéric Dupuis
-/
import Algebra.Star.SelfAdjoint
import Algebra.Module.Equiv.Defs
import LinearAlgebra.Prod

#align_import algebra.star.module from "leanprover-community/mathlib"@"aa6669832974f87406a3d9d70fc5707a60546207"

/-!
# The star operation, bundled as a star-linear equiv

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define `star_linear_equiv`, which is the star operation bundled as a star-linear map.
It is defined on a star algebra `A` over the base ring `R`.

This file also provides some lemmas that need `algebra.module.basic` imported to prove.

## TODO

- Define `star_linear_equiv` for noncommutative `R`. We only the commutative case for now since,
  in the noncommutative case, the ring hom needs to reverse the order of multiplication. This
  requires a ring hom of type `R →+* Rᵐᵒᵖ`, which is very undesirable in the commutative case.
  One way out would be to define a new typeclass `is_op R S` and have an instance `is_op R R`
  for commutative `R`.
- Also note that such a definition involving `Rᵐᵒᵖ` or `is_op R S` would require adding
  the appropriate `ring_hom_inv_pair` instances to be able to define the semilinear
  equivalence.
-/


section SmulLemmas

variable {R M : Type _}

#print star_natCast_smul /-
@[simp]
theorem star_natCast_smul [Semiring R] [AddCommMonoid M] [Module R M] [StarAddMonoid M] (n : ℕ)
    (x : M) : star ((n : R) • x) = (n : R) • star x :=
  map_natCast_smul (starAddEquiv : M ≃+ M) R R n x
#align star_nat_cast_smul star_natCast_smul
-/

#print star_intCast_smul /-
@[simp]
theorem star_intCast_smul [Ring R] [AddCommGroup M] [Module R M] [StarAddMonoid M] (n : ℤ) (x : M) :
    star ((n : R) • x) = (n : R) • star x :=
  map_intCast_smul (starAddEquiv : M ≃+ M) R R n x
#align star_int_cast_smul star_intCast_smul
-/

#print star_inv_natCast_smul /-
@[simp]
theorem star_inv_natCast_smul [DivisionSemiring R] [AddCommMonoid M] [Module R M] [StarAddMonoid M]
    (n : ℕ) (x : M) : star ((n⁻¹ : R) • x) = (n⁻¹ : R) • star x :=
  map_inv_natCast_smul (starAddEquiv : M ≃+ M) R R n x
#align star_inv_nat_cast_smul star_inv_natCast_smul
-/

#print star_inv_intCast_smul /-
@[simp]
theorem star_inv_intCast_smul [DivisionRing R] [AddCommGroup M] [Module R M] [StarAddMonoid M]
    (n : ℤ) (x : M) : star ((n⁻¹ : R) • x) = (n⁻¹ : R) • star x :=
  map_inv_intCast_smul (starAddEquiv : M ≃+ M) R R n x
#align star_inv_int_cast_smul star_inv_intCast_smul
-/

#print star_ratCast_smul /-
@[simp]
theorem star_ratCast_smul [DivisionRing R] [AddCommGroup M] [Module R M] [StarAddMonoid M] (n : ℚ)
    (x : M) : star ((n : R) • x) = (n : R) • star x :=
  map_ratCast_smul (starAddEquiv : M ≃+ M) _ _ _ x
#align star_rat_cast_smul star_ratCast_smul
-/

#print star_rat_smul /-
@[simp]
theorem star_rat_smul {R : Type _} [AddCommGroup R] [StarAddMonoid R] [Module ℚ R] (x : R) (n : ℚ) :
    star (n • x) = n • star x :=
  map_rat_smul (starAddEquiv : R ≃+ R) _ _
#align star_rat_smul star_rat_smul
-/

end SmulLemmas

#print starLinearEquiv /-
/-- If `A` is a module over a commutative `R` with compatible actions,
then `star` is a semilinear equivalence. -/
@[simps]
def starLinearEquiv (R : Type _) {A : Type _} [CommSemiring R] [StarRing R] [AddCommMonoid A]
    [StarAddMonoid A] [Module R A] [StarModule R A] : A ≃ₗ⋆[R] A :=
  { starAddEquiv with
    toFun := star
    map_smul' := star_smul }
#align star_linear_equiv starLinearEquiv
-/

variable (R : Type _) (A : Type _) [Semiring R] [StarMul R] [TrivialStar R] [AddCommGroup A]
  [Module R A] [StarAddMonoid A] [StarModule R A]

#print selfAdjoint.submodule /-
/-- The self-adjoint elements of a star module, as a submodule. -/
def selfAdjoint.submodule : Submodule R A :=
  { selfAdjoint A with smul_mem' := fun r x => (IsSelfAdjoint.all _).smul }
#align self_adjoint.submodule selfAdjoint.submodule
-/

#print skewAdjoint.submodule /-
/-- The skew-adjoint elements of a star module, as a submodule. -/
def skewAdjoint.submodule : Submodule R A :=
  { skewAdjoint A with smul_mem' := skewAdjoint.smul_mem }
#align skew_adjoint.submodule skewAdjoint.submodule
-/

variable {A} [Invertible (2 : R)]

#print selfAdjointPart /-
/-- The self-adjoint part of an element of a star module, as a linear map. -/
@[simps]
def selfAdjointPart : A →ₗ[R] selfAdjoint A
    where
  toFun x :=
    ⟨(⅟ 2 : R) • (x + star x), by
      simp only [selfAdjoint.mem_iff, star_smul, add_comm, StarAddMonoid.star_add, star_inv',
        star_bit0, star_one, star_star, star_invOf (2 : R), star_trivial]⟩
  map_add' x y := by ext; simp [add_add_add_comm]
  map_smul' r x := by ext;
    simp [← mul_smul, show ⅟ 2 * r = r * ⅟ 2 from Commute.invOf_left (Commute.one_left r).bit0_left]
#align self_adjoint_part selfAdjointPart
-/

#print skewAdjointPart /-
/-- The skew-adjoint part of an element of a star module, as a linear map. -/
@[simps]
def skewAdjointPart : A →ₗ[R] skewAdjoint A
    where
  toFun x :=
    ⟨(⅟ 2 : R) • (x - star x), by
      simp only [skewAdjoint.mem_iff, star_smul, star_sub, star_star, star_trivial, ← smul_neg,
        neg_sub]⟩
  map_add' x y := by ext;
    simp only [sub_add, ← smul_add, sub_sub_eq_add_sub, star_add, AddSubgroup.coe_mk,
      AddSubgroup.coe_add]
  map_smul' r x := by ext;
    simp [← mul_smul, ← smul_sub,
      show r * ⅟ 2 = ⅟ 2 * r from Commute.invOf_right (Commute.one_right r).bit0_right]
#align skew_adjoint_part skewAdjointPart
-/

#print StarModule.selfAdjointPart_add_skewAdjointPart /-
theorem StarModule.selfAdjointPart_add_skewAdjointPart (x : A) :
    (selfAdjointPart R x : A) + skewAdjointPart R x = x := by
  simp only [smul_sub, selfAdjointPart_apply_coe, smul_add, skewAdjointPart_apply_coe,
    add_add_sub_cancel, invOf_two_smul_add_invOf_two_smul]
#align star_module.self_adjoint_part_add_skew_adjoint_part StarModule.selfAdjointPart_add_skewAdjointPart
-/

variable (A)

#print StarModule.decomposeProdAdjoint /-
/-- The decomposition of elements of a star module into their self- and skew-adjoint parts,
as a linear equivalence. -/
@[simps]
def StarModule.decomposeProdAdjoint : A ≃ₗ[R] selfAdjoint A × skewAdjoint A :=
  LinearEquiv.ofLinear ((selfAdjointPart R).Prod (skewAdjointPart R))
    ((selfAdjoint.submodule R A).Subtype.coprod (skewAdjoint.submodule R A).Subtype)
    (by ext <;> simp) (LinearMap.ext <| StarModule.selfAdjointPart_add_skewAdjointPart R)
#align star_module.decompose_prod_adjoint StarModule.decomposeProdAdjoint
-/

#print algebraMap_star_comm /-
@[simp]
theorem algebraMap_star_comm {R A : Type _} [CommSemiring R] [StarRing R] [Semiring A] [StarMul A]
    [Algebra R A] [StarModule R A] (r : R) : algebraMap R A (star r) = star (algebraMap R A r) := by
  simp only [Algebra.algebraMap_eq_smul_one, star_smul, star_one]
#align algebra_map_star_comm algebraMap_star_comm
-/

