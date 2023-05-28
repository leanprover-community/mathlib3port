/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Anne Baanen

! This file was ported from Lean 3 source module algebra.algebra.tower
! leanprover-community/mathlib commit 832f7b9162039c28b9361289c8681f155cae758f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Algebra.Equiv
import Mathbin.LinearAlgebra.Span

/-!
# Towers of algebras

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove basic facts about towers of algebra.

An algebra tower A/S/R is expressed by having instances of `algebra A S`,
`algebra R S`, `algebra R A` and `is_scalar_tower R S A`, the later asserting the
compatibility condition `(r • s) • a = r • (s • a)`.

An important definition is `to_alg_hom R S A`, the canonical `R`-algebra homomorphism `S →ₐ[R] A`.

-/


open Pointwise

universe u v w u₁ v₁

variable (R : Type u) (S : Type v) (A : Type w) (B : Type u₁) (M : Type v₁)

namespace Algebra

variable [CommSemiring R] [Semiring A] [Algebra R A]

variable [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

variable {A}

/- warning: algebra.lsmul -> Algebra.lsmul is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) {A : Type.{u2}} (M : Type.{u3}) [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_3 : Algebra.{u1, u2} R A _inst_1 _inst_2] [_inst_4 : AddCommMonoid.{u3} M] [_inst_5 : Module.{u1, u3} R M (CommSemiring.toSemiring.{u1} R _inst_1) _inst_4] [_inst_6 : Module.{u2, u3} A M _inst_2 _inst_4] [_inst_7 : IsScalarTower.{u1, u2, u3} R A M (SMulZeroClass.toHasSmul.{u1, u2} R A (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2)))))) (SMulWithZero.toSmulZeroClass.{u1, u2} R A (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2)))))) (MulActionWithZero.toSMulWithZero.{u1, u2} R A (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2)))))) (Module.toMulActionWithZero.{u1, u2} R A (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3))))) (SMulZeroClass.toHasSmul.{u2, u3} A M (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4))) (SMulWithZero.toSmulZeroClass.{u2, u3} A M (MulZeroClass.toHasZero.{u2} A (MulZeroOneClass.toMulZeroClass.{u2} A (MonoidWithZero.toMulZeroOneClass.{u2} A (Semiring.toMonoidWithZero.{u2} A _inst_2)))) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4))) (MulActionWithZero.toSMulWithZero.{u2, u3} A M (Semiring.toMonoidWithZero.{u2} A _inst_2) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4))) (Module.toMulActionWithZero.{u2, u3} A M _inst_2 _inst_4 _inst_6)))) (SMulZeroClass.toHasSmul.{u1, u3} R M (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4))) (SMulWithZero.toSmulZeroClass.{u1, u3} R M (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4))) (MulActionWithZero.toSMulWithZero.{u1, u3} R M (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4))) (Module.toMulActionWithZero.{u1, u3} R M (CommSemiring.toSemiring.{u1} R _inst_1) _inst_4 _inst_5))))], AlgHom.{u1, u2, u3} R A (Module.End.{u1, u3} R M (CommSemiring.toSemiring.{u1} R _inst_1) _inst_4 _inst_5) _inst_1 _inst_2 (Module.End.semiring.{u1, u3} R M (CommSemiring.toSemiring.{u1} R _inst_1) _inst_4 _inst_5) _inst_3 (Module.End.algebra.{u1, u3} R M _inst_1 _inst_4 _inst_5)
but is expected to have type
  forall (R : Type.{u1}) {A : Type.{u2}} (M : Type.{u3}) [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_3 : Algebra.{u1, u2} R A _inst_1 _inst_2] [_inst_4 : AddCommMonoid.{u3} M] [_inst_5 : Module.{u1, u3} R M (CommSemiring.toSemiring.{u1} R _inst_1) _inst_4] [_inst_6 : Module.{u2, u3} A M _inst_2 _inst_4] [_inst_7 : IsScalarTower.{u1, u2, u3} R A M (Algebra.toSMul.{u1, u2} R A _inst_1 _inst_2 _inst_3) (SMulZeroClass.toSMul.{u2, u3} A M (AddMonoid.toZero.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4)) (SMulWithZero.toSMulZeroClass.{u2, u3} A M (MonoidWithZero.toZero.{u2} A (Semiring.toMonoidWithZero.{u2} A _inst_2)) (AddMonoid.toZero.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4)) (MulActionWithZero.toSMulWithZero.{u2, u3} A M (Semiring.toMonoidWithZero.{u2} A _inst_2) (AddMonoid.toZero.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4)) (Module.toMulActionWithZero.{u2, u3} A M _inst_2 _inst_4 _inst_6)))) (SMulZeroClass.toSMul.{u1, u3} R M (AddMonoid.toZero.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4)) (SMulWithZero.toSMulZeroClass.{u1, u3} R M (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R _inst_1)) (AddMonoid.toZero.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4)) (MulActionWithZero.toSMulWithZero.{u1, u3} R M (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (AddMonoid.toZero.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4)) (Module.toMulActionWithZero.{u1, u3} R M (CommSemiring.toSemiring.{u1} R _inst_1) _inst_4 _inst_5))))], AlgHom.{u1, u2, u3} R A (Module.End.{u1, u3} R M (CommSemiring.toSemiring.{u1} R _inst_1) _inst_4 _inst_5) _inst_1 _inst_2 (Module.End.semiring.{u1, u3} R M (CommSemiring.toSemiring.{u1} R _inst_1) _inst_4 _inst_5) _inst_3 (Module.instAlgebraEndToSemiringSemiring.{u1, u3} R M _inst_1 _inst_4 _inst_5)
Case conversion may be inaccurate. Consider using '#align algebra.lsmul Algebra.lsmulₓ'. -/
/-- The `R`-algebra morphism `A → End (M)` corresponding to the representation of the algebra `A`
on the `R`-module `M`.

This is a stronger version of `distrib_mul_action.to_linear_map`, and could also have been
called `algebra.to_module_End`. -/
def lsmul : A →ₐ[R] Module.End R M
    where
  toFun := DistribMulAction.toLinearMap R M
  map_one' := LinearMap.ext fun _ => one_smul A _
  map_mul' a b := LinearMap.ext <| smul_assoc a b
  map_zero' := LinearMap.ext fun _ => zero_smul A _
  map_add' a b := LinearMap.ext fun _ => add_smul _ _ _
  commutes' r := LinearMap.ext <| algebraMap_smul A r
#align algebra.lsmul Algebra.lsmul

/- warning: algebra.lsmul_coe -> Algebra.lsmul_coe is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebra.lsmul_coe Algebra.lsmul_coeₓ'. -/
@[simp]
theorem lsmul_coe (a : A) : (lsmul R M a : M → M) = (· • ·) a :=
  rfl
#align algebra.lsmul_coe Algebra.lsmul_coe

end Algebra

namespace IsScalarTower

section Module

variable [CommSemiring R] [Semiring A] [Algebra R A]

variable [SMul R M] [MulAction A M] [IsScalarTower R A M]

variable {R} (A) {M}

/- warning: is_scalar_tower.algebra_map_smul -> IsScalarTower.algebraMap_smul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_scalar_tower.algebra_map_smul IsScalarTower.algebraMap_smulₓ'. -/
theorem algebraMap_smul (r : R) (x : M) : algebraMap R A r • x = r • x := by
  rw [Algebra.algebraMap_eq_smul_one, smul_assoc, one_smul]
#align is_scalar_tower.algebra_map_smul IsScalarTower.algebraMap_smul

end Module

section Semiring

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra S A] [Algebra S B]

variable {R S A}

/- warning: is_scalar_tower.of_algebra_map_eq -> IsScalarTower.of_algebraMap_eq is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_scalar_tower.of_algebra_map_eq IsScalarTower.of_algebraMap_eqₓ'. -/
theorem of_algebraMap_eq [Algebra R A]
    (h : ∀ x, algebraMap R A x = algebraMap S A (algebraMap R S x)) : IsScalarTower R S A :=
  ⟨fun x y z => by simp_rw [Algebra.smul_def, RingHom.map_mul, mul_assoc, h]⟩
#align is_scalar_tower.of_algebra_map_eq IsScalarTower.of_algebraMap_eq

#print IsScalarTower.of_algebraMap_eq' /-
/-- See note [partially-applied ext lemmas]. -/
theorem of_algebraMap_eq' [Algebra R A]
    (h : algebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A :=
  of_algebraMap_eq <| RingHom.ext_iff.1 h
#align is_scalar_tower.of_algebra_map_eq' IsScalarTower.of_algebraMap_eq'
-/

variable (R S A)

variable [Algebra R A] [Algebra R B]

variable [IsScalarTower R S A] [IsScalarTower R S B]

#print IsScalarTower.algebraMap_eq /-
theorem algebraMap_eq : algebraMap R A = (algebraMap S A).comp (algebraMap R S) :=
  RingHom.ext fun x => by
    simp_rw [RingHom.comp_apply, Algebra.algebraMap_eq_smul_one, smul_assoc, one_smul]
#align is_scalar_tower.algebra_map_eq IsScalarTower.algebraMap_eq
-/

/- warning: is_scalar_tower.algebra_map_apply -> IsScalarTower.algebraMap_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_scalar_tower.algebra_map_apply IsScalarTower.algebraMap_applyₓ'. -/
theorem algebraMap_apply (x : R) : algebraMap R A x = algebraMap S A (algebraMap R S x) := by
  rw [algebra_map_eq R S A, RingHom.comp_apply]
#align is_scalar_tower.algebra_map_apply IsScalarTower.algebraMap_apply

#print IsScalarTower.Algebra.ext /-
@[ext]
theorem Algebra.ext {S : Type u} {A : Type v} [CommSemiring S] [Semiring A] (h1 h2 : Algebra S A)
    (h :
      ∀ (r : S) (x : A),
        (haveI := h1
          r • x) =
          r • x) :
    h1 = h2 :=
  Algebra.algebra_ext _ _ fun r => by
    simpa only [@Algebra.smul_def _ _ _ _ h1, @Algebra.smul_def _ _ _ _ h2, mul_one] using h r 1
#align is_scalar_tower.algebra.ext IsScalarTower.Algebra.ext
-/

#print IsScalarTower.toAlgHom /-
/-- In a tower, the canonical map from the middle element to the top element is an
algebra homomorphism over the bottom element. -/
def toAlgHom : S →ₐ[R] A :=
  { algebraMap S A with commutes' := fun _ => (algebraMap_apply _ _ _ _).symm }
#align is_scalar_tower.to_alg_hom IsScalarTower.toAlgHom
-/

#print IsScalarTower.toAlgHom_apply /-
theorem toAlgHom_apply (y : S) : toAlgHom R S A y = algebraMap S A y :=
  rfl
#align is_scalar_tower.to_alg_hom_apply IsScalarTower.toAlgHom_apply
-/

/- warning: is_scalar_tower.coe_to_alg_hom -> IsScalarTower.coe_toAlgHom is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_scalar_tower.coe_to_alg_hom IsScalarTower.coe_toAlgHomₓ'. -/
@[simp]
theorem coe_toAlgHom : ↑(toAlgHom R S A) = algebraMap S A :=
  RingHom.ext fun _ => rfl
#align is_scalar_tower.coe_to_alg_hom IsScalarTower.coe_toAlgHom

#print IsScalarTower.coe_toAlgHom' /-
@[simp]
theorem coe_toAlgHom' : (toAlgHom R S A : S → A) = algebraMap S A :=
  rfl
#align is_scalar_tower.coe_to_alg_hom' IsScalarTower.coe_toAlgHom'
-/

variable {R S A B}

#print AlgHom.map_algebraMap /-
@[simp]
theorem AlgHom.map_algebraMap (f : A →ₐ[S] B) (r : R) : f (algebraMap R A r) = algebraMap R B r :=
  by rw [algebraMap_apply R S A r, f.commutes, ← algebraMap_apply R S B]
#align alg_hom.map_algebra_map AlgHom.map_algebraMap
-/

variable (R)

/- warning: alg_hom.comp_algebra_map_of_tower -> AlgHom.comp_algebraMap_of_tower is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_hom.comp_algebra_map_of_tower AlgHom.comp_algebraMap_of_towerₓ'. -/
@[simp]
theorem AlgHom.comp_algebraMap_of_tower (f : A →ₐ[S] B) :
    (f : A →+* B).comp (algebraMap R A) = algebraMap R B :=
  RingHom.ext f.map_algebraMap
#align alg_hom.comp_algebra_map_of_tower AlgHom.comp_algebraMap_of_tower

variable (R) {S A B}

/- warning: is_scalar_tower.subsemiring -> IsScalarTower.subsemiring is a dubious translation:
lean 3 declaration is
  forall {S : Type.{u1}} {A : Type.{u2}} [_inst_2 : CommSemiring.{u1} S] [_inst_3 : Semiring.{u2} A] [_inst_6 : Algebra.{u1, u2} S A _inst_2 _inst_3] (U : Subsemiring.{u1} S (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2))), IsScalarTower.{u1, u1, u2} (coeSort.{succ u1, succ (succ u1)} (Subsemiring.{u1} S (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subsemiring.{u1} S (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2))) S (Subsemiring.setLike.{u1} S (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)))) U) S A (Subsemiring.hasSmul.{u1, u1} S S (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)) (Mul.toSMul.{u1} S (Distrib.toHasMul.{u1} S (NonUnitalNonAssocSemiring.toDistrib.{u1} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} S (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)))))) U) (SMulZeroClass.toHasSmul.{u1, u2} S A (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_3)))))) (SMulWithZero.toSmulZeroClass.{u1, u2} S A (MulZeroClass.toHasZero.{u1} S (MulZeroOneClass.toMulZeroClass.{u1} S (MonoidWithZero.toMulZeroOneClass.{u1} S (Semiring.toMonoidWithZero.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2))))) (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_3)))))) (MulActionWithZero.toSMulWithZero.{u1, u2} S A (Semiring.toMonoidWithZero.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)) (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_3)))))) (Module.toMulActionWithZero.{u1, u2} S A (CommSemiring.toSemiring.{u1} S _inst_2) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_3))) (Algebra.toModule.{u1, u2} S A _inst_2 _inst_3 _inst_6))))) (Subsemiring.hasSmul.{u1, u2} S A (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)) (SMulZeroClass.toHasSmul.{u1, u2} S A (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_3)))))) (SMulWithZero.toSmulZeroClass.{u1, u2} S A (MulZeroClass.toHasZero.{u1} S (MulZeroOneClass.toMulZeroClass.{u1} S (MonoidWithZero.toMulZeroOneClass.{u1} S (Semiring.toMonoidWithZero.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2))))) (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_3)))))) (MulActionWithZero.toSMulWithZero.{u1, u2} S A (Semiring.toMonoidWithZero.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)) (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_3)))))) (Module.toMulActionWithZero.{u1, u2} S A (CommSemiring.toSemiring.{u1} S _inst_2) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_3))) (Algebra.toModule.{u1, u2} S A _inst_2 _inst_3 _inst_6))))) U)
but is expected to have type
  forall {S : Type.{u1}} {A : Type.{u2}} [_inst_2 : CommSemiring.{u1} S] [_inst_3 : Semiring.{u2} A] [_inst_6 : Algebra.{u1, u2} S A _inst_2 _inst_3] (U : Subsemiring.{u1} S (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2))), IsScalarTower.{u1, u1, u2} (Subtype.{succ u1} S (fun (x : S) => Membership.mem.{u1, u1} S (Subsemiring.{u1} S (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2))) (SetLike.instMembership.{u1, u1} (Subsemiring.{u1} S (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2))) S (Subsemiring.instSetLikeSubsemiring.{u1} S (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)))) x U)) S A (Subsemiring.smul.{u1, u1} S S (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)) (Algebra.toSMul.{u1, u1} S S _inst_2 (CommSemiring.toSemiring.{u1} S _inst_2) (Algebra.id.{u1} S _inst_2)) U) (Algebra.toSMul.{u1, u2} S A _inst_2 _inst_3 _inst_6) (Subsemiring.smul.{u1, u2} S A (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)) (Algebra.toSMul.{u1, u2} S A _inst_2 _inst_3 _inst_6) U)
Case conversion may be inaccurate. Consider using '#align is_scalar_tower.subsemiring IsScalarTower.subsemiringₓ'. -/
-- conflicts with is_scalar_tower.subalgebra
instance (priority := 999) subsemiring (U : Subsemiring S) : IsScalarTower U S A :=
  of_algebraMap_eq fun x => rfl
#align is_scalar_tower.subsemiring IsScalarTower.subsemiring

#print IsScalarTower.of_ring_hom /-
@[nolint instance_priority]
instance of_ring_hom {R A B : Type _} [CommSemiring R] [CommSemiring A] [CommSemiring B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) :
    @IsScalarTower R A B _ f.toRingHom.toAlgebra.toSMul _ :=
  letI := (f : A →+* B).toAlgebra
  of_algebra_map_eq fun x => (f.commutes x).symm
#align is_scalar_tower.of_ring_hom IsScalarTower.of_ring_hom
-/

end Semiring

end IsScalarTower

section Homs

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra S A] [Algebra S B]

variable [Algebra R A] [Algebra R B]

variable [IsScalarTower R S A] [IsScalarTower R S B]

variable (R) {A S B}

open IsScalarTower

namespace AlgHom

#print AlgHom.restrictScalars /-
/-- R ⟶ S induces S-Alg ⥤ R-Alg -/
def restrictScalars (f : A →ₐ[S] B) : A →ₐ[R] B :=
  { (f : A →+* B) with
    commutes' := fun r => by
      rw [algebraMap_apply R S A, algebraMap_apply R S B]
      exact f.commutes (algebraMap R S r) }
#align alg_hom.restrict_scalars AlgHom.restrictScalars
-/

#print AlgHom.restrictScalars_apply /-
theorem restrictScalars_apply (f : A →ₐ[S] B) (x : A) : f.restrictScalars R x = f x :=
  rfl
#align alg_hom.restrict_scalars_apply AlgHom.restrictScalars_apply
-/

/- warning: alg_hom.coe_restrict_scalars -> AlgHom.coe_restrictScalars is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_hom.coe_restrict_scalars AlgHom.coe_restrictScalarsₓ'. -/
@[simp]
theorem coe_restrictScalars (f : A →ₐ[S] B) : (f.restrictScalars R : A →+* B) = f :=
  rfl
#align alg_hom.coe_restrict_scalars AlgHom.coe_restrictScalars

#print AlgHom.coe_restrictScalars' /-
@[simp]
theorem coe_restrictScalars' (f : A →ₐ[S] B) : (restrictScalars R f : A → B) = f :=
  rfl
#align alg_hom.coe_restrict_scalars' AlgHom.coe_restrictScalars'
-/

#print AlgHom.restrictScalars_injective /-
theorem restrictScalars_injective :
    Function.Injective (restrictScalars R : (A →ₐ[S] B) → A →ₐ[R] B) := fun f g h =>
  AlgHom.ext (AlgHom.congr_fun h : _)
#align alg_hom.restrict_scalars_injective AlgHom.restrictScalars_injective
-/

end AlgHom

namespace AlgEquiv

#print AlgEquiv.restrictScalars /-
/-- R ⟶ S induces S-Alg ⥤ R-Alg -/
def restrictScalars (f : A ≃ₐ[S] B) : A ≃ₐ[R] B :=
  { (f : A ≃+* B) with
    commutes' := fun r => by
      rw [algebraMap_apply R S A, algebraMap_apply R S B]
      exact f.commutes (algebraMap R S r) }
#align alg_equiv.restrict_scalars AlgEquiv.restrictScalars
-/

/- warning: alg_equiv.restrict_scalars_apply -> AlgEquiv.restrictScalars_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.restrict_scalars_apply AlgEquiv.restrictScalars_applyₓ'. -/
theorem restrictScalars_apply (f : A ≃ₐ[S] B) (x : A) : f.restrictScalars R x = f x :=
  rfl
#align alg_equiv.restrict_scalars_apply AlgEquiv.restrictScalars_apply

/- warning: alg_equiv.coe_restrict_scalars -> AlgEquiv.coe_restrictScalars is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.coe_restrict_scalars AlgEquiv.coe_restrictScalarsₓ'. -/
@[simp]
theorem coe_restrictScalars (f : A ≃ₐ[S] B) : (f.restrictScalars R : A ≃+* B) = f :=
  rfl
#align alg_equiv.coe_restrict_scalars AlgEquiv.coe_restrictScalars

/- warning: alg_equiv.coe_restrict_scalars' -> AlgEquiv.coe_restrictScalars' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.coe_restrict_scalars' AlgEquiv.coe_restrictScalars'ₓ'. -/
@[simp]
theorem coe_restrictScalars' (f : A ≃ₐ[S] B) : (restrictScalars R f : A → B) = f :=
  rfl
#align alg_equiv.coe_restrict_scalars' AlgEquiv.coe_restrictScalars'

#print AlgEquiv.restrictScalars_injective /-
theorem restrictScalars_injective :
    Function.Injective (restrictScalars R : (A ≃ₐ[S] B) → A ≃ₐ[R] B) := fun f g h =>
  AlgEquiv.ext (AlgEquiv.congr_fun h : _)
#align alg_equiv.restrict_scalars_injective AlgEquiv.restrictScalars_injective
-/

end AlgEquiv

end Homs

namespace Submodule

variable (R A) {M}

variable [CommSemiring R] [Semiring A] [Algebra R A] [AddCommMonoid M]

variable [Module R M] [Module A M] [IsScalarTower R A M]

/- warning: submodule.restrict_scalars_span -> Submodule.restrictScalars_span is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) (A : Type.{u2}) {M : Type.{u3}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_3 : Algebra.{u1, u2} R A _inst_1 _inst_2] [_inst_4 : AddCommMonoid.{u3} M] [_inst_5 : Module.{u1, u3} R M (CommSemiring.toSemiring.{u1} R _inst_1) _inst_4] [_inst_6 : Module.{u2, u3} A M _inst_2 _inst_4] [_inst_7 : IsScalarTower.{u1, u2, u3} R A M (SMulZeroClass.toHasSmul.{u1, u2} R A (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2)))))) (SMulWithZero.toSmulZeroClass.{u1, u2} R A (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2)))))) (MulActionWithZero.toSMulWithZero.{u1, u2} R A (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2)))))) (Module.toMulActionWithZero.{u1, u2} R A (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3))))) (SMulZeroClass.toHasSmul.{u2, u3} A M (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4))) (SMulWithZero.toSmulZeroClass.{u2, u3} A M (MulZeroClass.toHasZero.{u2} A (MulZeroOneClass.toMulZeroClass.{u2} A (MonoidWithZero.toMulZeroOneClass.{u2} A (Semiring.toMonoidWithZero.{u2} A _inst_2)))) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4))) (MulActionWithZero.toSMulWithZero.{u2, u3} A M (Semiring.toMonoidWithZero.{u2} A _inst_2) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4))) (Module.toMulActionWithZero.{u2, u3} A M _inst_2 _inst_4 _inst_6)))) (SMulZeroClass.toHasSmul.{u1, u3} R M (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4))) (SMulWithZero.toSmulZeroClass.{u1, u3} R M (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4))) (MulActionWithZero.toSMulWithZero.{u1, u3} R M (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4))) (Module.toMulActionWithZero.{u1, u3} R M (CommSemiring.toSemiring.{u1} R _inst_1) _inst_4 _inst_5))))], (Function.Surjective.{succ u1, succ u2} R A (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} A _inst_2)) (fun (_x : RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} A _inst_2)) => R -> A) (RingHom.hasCoeToFun.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} A _inst_2)) (algebraMap.{u1, u2} R A _inst_1 _inst_2 _inst_3))) -> (forall (X : Set.{u3} M), Eq.{succ u3} (Submodule.{u1, u3} R M (CommSemiring.toSemiring.{u1} R _inst_1) _inst_4 _inst_5) (Submodule.restrictScalars.{u1, u2, u3} R A M _inst_2 _inst_4 (CommSemiring.toSemiring.{u1} R _inst_1) _inst_5 _inst_6 (SMulZeroClass.toHasSmul.{u1, u2} R A (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2)))))) (SMulWithZero.toSmulZeroClass.{u1, u2} R A (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2)))))) (MulActionWithZero.toSMulWithZero.{u1, u2} R A (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2)))))) (Module.toMulActionWithZero.{u1, u2} R A (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3))))) _inst_7 (Submodule.span.{u2, u3} A M _inst_2 _inst_4 _inst_6 X)) (Submodule.span.{u1, u3} R M (CommSemiring.toSemiring.{u1} R _inst_1) _inst_4 _inst_5 X))
but is expected to have type
  forall (R : Type.{u1}) (A : Type.{u2}) {M : Type.{u3}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_3 : Algebra.{u1, u2} R A _inst_1 _inst_2] [_inst_4 : AddCommMonoid.{u3} M] [_inst_5 : Module.{u1, u3} R M (CommSemiring.toSemiring.{u1} R _inst_1) _inst_4] [_inst_6 : Module.{u2, u3} A M _inst_2 _inst_4] [_inst_7 : IsScalarTower.{u1, u2, u3} R A M (Algebra.toSMul.{u1, u2} R A _inst_1 _inst_2 _inst_3) (SMulZeroClass.toSMul.{u2, u3} A M (AddMonoid.toZero.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4)) (SMulWithZero.toSMulZeroClass.{u2, u3} A M (MonoidWithZero.toZero.{u2} A (Semiring.toMonoidWithZero.{u2} A _inst_2)) (AddMonoid.toZero.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4)) (MulActionWithZero.toSMulWithZero.{u2, u3} A M (Semiring.toMonoidWithZero.{u2} A _inst_2) (AddMonoid.toZero.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4)) (Module.toMulActionWithZero.{u2, u3} A M _inst_2 _inst_4 _inst_6)))) (SMulZeroClass.toSMul.{u1, u3} R M (AddMonoid.toZero.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4)) (SMulWithZero.toSMulZeroClass.{u1, u3} R M (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R _inst_1)) (AddMonoid.toZero.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4)) (MulActionWithZero.toSMulWithZero.{u1, u3} R M (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (AddMonoid.toZero.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4)) (Module.toMulActionWithZero.{u1, u3} R M (CommSemiring.toSemiring.{u1} R _inst_1) _inst_4 _inst_5))))], (Function.Surjective.{succ u1, succ u2} R A (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} A _inst_2)) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => A) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} A _inst_2)) R A (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} A _inst_2)) R A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2)) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} A _inst_2)) R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} A _inst_2) (RingHom.instRingHomClassRingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} A _inst_2))))) (algebraMap.{u1, u2} R A _inst_1 _inst_2 _inst_3))) -> (forall (X : Set.{u3} M), Eq.{succ u3} (Submodule.{u1, u3} R M (CommSemiring.toSemiring.{u1} R _inst_1) _inst_4 _inst_5) (Submodule.restrictScalars.{u1, u2, u3} R A M _inst_2 _inst_4 (CommSemiring.toSemiring.{u1} R _inst_1) _inst_5 _inst_6 (Algebra.toSMul.{u1, u2} R A _inst_1 _inst_2 _inst_3) _inst_7 (Submodule.span.{u2, u3} A M _inst_2 _inst_4 _inst_6 X)) (Submodule.span.{u1, u3} R M (CommSemiring.toSemiring.{u1} R _inst_1) _inst_4 _inst_5 X))
Case conversion may be inaccurate. Consider using '#align submodule.restrict_scalars_span Submodule.restrictScalars_spanₓ'. -/
/-- If `A` is an `R`-algebra such that the induced morphism `R →+* A` is surjective, then the
`R`-module generated by a set `X` equals the `A`-module generated by `X`. -/
theorem restrictScalars_span (hsur : Function.Surjective (algebraMap R A)) (X : Set M) :
    restrictScalars R (span A X) = span R X :=
  by
  refine' ((span_le_restrict_scalars R A X).antisymm fun m hm => _).symm
  refine' span_induction hm subset_span (zero_mem _) (fun _ _ => add_mem) fun a m hm => _
  obtain ⟨r, rfl⟩ := hsur a
  simpa [algebraMap_smul] using smul_mem _ r hm
#align submodule.restrict_scalars_span Submodule.restrictScalars_span

/- warning: submodule.coe_span_eq_span_of_surjective -> Submodule.coe_span_eq_span_of_surjective is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) (A : Type.{u2}) {M : Type.{u3}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_3 : Algebra.{u1, u2} R A _inst_1 _inst_2] [_inst_4 : AddCommMonoid.{u3} M] [_inst_5 : Module.{u1, u3} R M (CommSemiring.toSemiring.{u1} R _inst_1) _inst_4] [_inst_6 : Module.{u2, u3} A M _inst_2 _inst_4] [_inst_7 : IsScalarTower.{u1, u2, u3} R A M (SMulZeroClass.toHasSmul.{u1, u2} R A (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2)))))) (SMulWithZero.toSmulZeroClass.{u1, u2} R A (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2)))))) (MulActionWithZero.toSMulWithZero.{u1, u2} R A (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2)))))) (Module.toMulActionWithZero.{u1, u2} R A (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3))))) (SMulZeroClass.toHasSmul.{u2, u3} A M (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4))) (SMulWithZero.toSmulZeroClass.{u2, u3} A M (MulZeroClass.toHasZero.{u2} A (MulZeroOneClass.toMulZeroClass.{u2} A (MonoidWithZero.toMulZeroOneClass.{u2} A (Semiring.toMonoidWithZero.{u2} A _inst_2)))) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4))) (MulActionWithZero.toSMulWithZero.{u2, u3} A M (Semiring.toMonoidWithZero.{u2} A _inst_2) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4))) (Module.toMulActionWithZero.{u2, u3} A M _inst_2 _inst_4 _inst_6)))) (SMulZeroClass.toHasSmul.{u1, u3} R M (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4))) (SMulWithZero.toSmulZeroClass.{u1, u3} R M (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4))) (MulActionWithZero.toSMulWithZero.{u1, u3} R M (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4))) (Module.toMulActionWithZero.{u1, u3} R M (CommSemiring.toSemiring.{u1} R _inst_1) _inst_4 _inst_5))))], (Function.Surjective.{succ u1, succ u2} R A (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} A _inst_2)) (fun (_x : RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} A _inst_2)) => R -> A) (RingHom.hasCoeToFun.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} A _inst_2)) (algebraMap.{u1, u2} R A _inst_1 _inst_2 _inst_3))) -> (forall (s : Set.{u3} M), Eq.{succ u3} (Set.{u3} M) ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (Submodule.{u2, u3} A M _inst_2 _inst_4 _inst_6) (Set.{u3} M) (HasLiftT.mk.{succ u3, succ u3} (Submodule.{u2, u3} A M _inst_2 _inst_4 _inst_6) (Set.{u3} M) (CoeTCₓ.coe.{succ u3, succ u3} (Submodule.{u2, u3} A M _inst_2 _inst_4 _inst_6) (Set.{u3} M) (SetLike.Set.hasCoeT.{u3, u3} (Submodule.{u2, u3} A M _inst_2 _inst_4 _inst_6) M (Submodule.setLike.{u2, u3} A M _inst_2 _inst_4 _inst_6)))) (Submodule.span.{u2, u3} A M _inst_2 _inst_4 _inst_6 s)) ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (Submodule.{u1, u3} R M (CommSemiring.toSemiring.{u1} R _inst_1) _inst_4 _inst_5) (Set.{u3} M) (HasLiftT.mk.{succ u3, succ u3} (Submodule.{u1, u3} R M (CommSemiring.toSemiring.{u1} R _inst_1) _inst_4 _inst_5) (Set.{u3} M) (CoeTCₓ.coe.{succ u3, succ u3} (Submodule.{u1, u3} R M (CommSemiring.toSemiring.{u1} R _inst_1) _inst_4 _inst_5) (Set.{u3} M) (SetLike.Set.hasCoeT.{u3, u3} (Submodule.{u1, u3} R M (CommSemiring.toSemiring.{u1} R _inst_1) _inst_4 _inst_5) M (Submodule.setLike.{u1, u3} R M (CommSemiring.toSemiring.{u1} R _inst_1) _inst_4 _inst_5)))) (Submodule.span.{u1, u3} R M (CommSemiring.toSemiring.{u1} R _inst_1) _inst_4 _inst_5 s)))
but is expected to have type
  forall (R : Type.{u1}) (A : Type.{u2}) {M : Type.{u3}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_3 : Algebra.{u1, u2} R A _inst_1 _inst_2] [_inst_4 : AddCommMonoid.{u3} M] [_inst_5 : Module.{u1, u3} R M (CommSemiring.toSemiring.{u1} R _inst_1) _inst_4] [_inst_6 : Module.{u2, u3} A M _inst_2 _inst_4] [_inst_7 : IsScalarTower.{u1, u2, u3} R A M (Algebra.toSMul.{u1, u2} R A _inst_1 _inst_2 _inst_3) (SMulZeroClass.toSMul.{u2, u3} A M (AddMonoid.toZero.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4)) (SMulWithZero.toSMulZeroClass.{u2, u3} A M (MonoidWithZero.toZero.{u2} A (Semiring.toMonoidWithZero.{u2} A _inst_2)) (AddMonoid.toZero.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4)) (MulActionWithZero.toSMulWithZero.{u2, u3} A M (Semiring.toMonoidWithZero.{u2} A _inst_2) (AddMonoid.toZero.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4)) (Module.toMulActionWithZero.{u2, u3} A M _inst_2 _inst_4 _inst_6)))) (SMulZeroClass.toSMul.{u1, u3} R M (AddMonoid.toZero.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4)) (SMulWithZero.toSMulZeroClass.{u1, u3} R M (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R _inst_1)) (AddMonoid.toZero.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4)) (MulActionWithZero.toSMulWithZero.{u1, u3} R M (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (AddMonoid.toZero.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4)) (Module.toMulActionWithZero.{u1, u3} R M (CommSemiring.toSemiring.{u1} R _inst_1) _inst_4 _inst_5))))], (Function.Surjective.{succ u1, succ u2} R A (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} A _inst_2)) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => A) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} A _inst_2)) R A (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} A _inst_2)) R A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2)) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} A _inst_2)) R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} A _inst_2) (RingHom.instRingHomClassRingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} A _inst_2))))) (algebraMap.{u1, u2} R A _inst_1 _inst_2 _inst_3))) -> (forall (s : Set.{u3} M), Eq.{succ u3} (Set.{u3} M) (SetLike.coe.{u3, u3} (Submodule.{u2, u3} A M _inst_2 _inst_4 _inst_6) M (Submodule.setLike.{u2, u3} A M _inst_2 _inst_4 _inst_6) (Submodule.span.{u2, u3} A M _inst_2 _inst_4 _inst_6 s)) (SetLike.coe.{u3, u3} (Submodule.{u1, u3} R M (CommSemiring.toSemiring.{u1} R _inst_1) _inst_4 _inst_5) M (Submodule.setLike.{u1, u3} R M (CommSemiring.toSemiring.{u1} R _inst_1) _inst_4 _inst_5) (Submodule.span.{u1, u3} R M (CommSemiring.toSemiring.{u1} R _inst_1) _inst_4 _inst_5 s)))
Case conversion may be inaccurate. Consider using '#align submodule.coe_span_eq_span_of_surjective Submodule.coe_span_eq_span_of_surjectiveₓ'. -/
theorem coe_span_eq_span_of_surjective (h : Function.Surjective (algebraMap R A)) (s : Set M) :
    (Submodule.span A s : Set M) = Submodule.span R s :=
  congr_arg coe (Submodule.restrictScalars_span R A h s)
#align submodule.coe_span_eq_span_of_surjective Submodule.coe_span_eq_span_of_surjective

end Submodule

section Semiring

variable {R S A}

namespace Submodule

section Module

variable [Semiring R] [Semiring S] [AddCommMonoid A]

variable [Module R S] [Module S A] [Module R A] [IsScalarTower R S A]

open IsScalarTower

#print Submodule.smul_mem_span_smul_of_mem /-
theorem smul_mem_span_smul_of_mem {s : Set S} {t : Set A} {k : S} (hks : k ∈ span R s) {x : A}
    (hx : x ∈ t) : k • x ∈ span R (s • t) :=
  span_induction hks (fun c hc => subset_span <| Set.mem_smul.2 ⟨c, x, hc, hx, rfl⟩)
    (by rw [zero_smul]; exact zero_mem _)
    (fun c₁ c₂ ih₁ ih₂ => by rw [add_smul]; exact add_mem ih₁ ih₂) fun b c hc => by
    rw [IsScalarTower.smul_assoc]; exact smul_mem _ _ hc
#align submodule.smul_mem_span_smul_of_mem Submodule.smul_mem_span_smul_of_mem
-/

variable [SMulCommClass R S A]

/- warning: submodule.smul_mem_span_smul -> Submodule.smul_mem_span_smul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.smul_mem_span_smul Submodule.smul_mem_span_smulₓ'. -/
theorem smul_mem_span_smul {s : Set S} (hs : span R s = ⊤) {t : Set A} {k : S} {x : A}
    (hx : x ∈ span R t) : k • x ∈ span R (s • t) :=
  span_induction hx (fun x hx => smul_mem_span_smul_of_mem (hs.symm ▸ mem_top) hx)
    (by rw [smul_zero]; exact zero_mem _)
    (fun x y ihx ihy => by rw [smul_add]; exact add_mem ihx ihy) fun c x hx =>
    smul_comm c k x ▸ smul_mem _ _ hx
#align submodule.smul_mem_span_smul Submodule.smul_mem_span_smul

/- warning: submodule.smul_mem_span_smul' -> Submodule.smul_mem_span_smul' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.smul_mem_span_smul' Submodule.smul_mem_span_smul'ₓ'. -/
theorem smul_mem_span_smul' {s : Set S} (hs : span R s = ⊤) {t : Set A} {k : S} {x : A}
    (hx : x ∈ span R (s • t)) : k • x ∈ span R (s • t) :=
  span_induction hx
    (fun x hx => by
      let ⟨p, q, hp, hq, hpq⟩ := Set.mem_smul.1 hx
      rw [← hpq, smul_smul]; exact smul_mem_span_smul_of_mem (hs.symm ▸ mem_top) hq)
    (by rw [smul_zero]; exact zero_mem _)
    (fun x y ihx ihy => by rw [smul_add]; exact add_mem ihx ihy) fun c x hx =>
    smul_comm c k x ▸ smul_mem _ _ hx
#align submodule.smul_mem_span_smul' Submodule.smul_mem_span_smul'

/- warning: submodule.span_smul_of_span_eq_top -> Submodule.span_smul_of_span_eq_top is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.span_smul_of_span_eq_top Submodule.span_smul_of_span_eq_topₓ'. -/
theorem span_smul_of_span_eq_top {s : Set S} (hs : span R s = ⊤) (t : Set A) :
    span R (s • t) = (span S t).restrictScalars R :=
  le_antisymm
    (span_le.2 fun x hx =>
      let ⟨p, q, hps, hqt, hpqx⟩ := Set.mem_smul.1 hx
      hpqx ▸ (span S t).smul_mem p (subset_span hqt))
    fun p hp =>
    span_induction hp (fun x hx => one_smul S x ▸ smul_mem_span_smul hs (subset_span hx))
      (zero_mem _) (fun _ _ => add_mem) fun k x hx => smul_mem_span_smul' hs hx
#align submodule.span_smul_of_span_eq_top Submodule.span_smul_of_span_eq_top

end Module

section Algebra

variable [CommSemiring R] [Semiring S] [AddCommMonoid A]

variable [Algebra R S] [Module S A] [Module R A] [IsScalarTower R S A]

/- warning: submodule.span_algebra_map_image -> Submodule.span_algebraMap_image is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} S] [_inst_4 : Algebra.{u1, u2} R S _inst_1 _inst_2] (a : Set.{u1} R), Eq.{succ u2} (Submodule.{u1, u2} R S (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S _inst_2))) (Algebra.toModule.{u1, u2} R S _inst_1 _inst_2 _inst_4)) (Submodule.span.{u1, u2} R S (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S _inst_2))) (Algebra.toModule.{u1, u2} R S _inst_1 _inst_2 _inst_4) (Set.image.{u1, u2} R S (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) (fun (_x : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) => R -> S) (RingHom.hasCoeToFun.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) (algebraMap.{u1, u2} R S _inst_1 _inst_2 _inst_4)) a)) (Submodule.map.{u1, u1, u1, u2, max u1 u2} R R R S (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S _inst_2))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Algebra.toModule.{u1, u2} R S _inst_1 _inst_2 _inst_4) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (RingHomSurjective.ids.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (LinearMap.{u1, u1, u1, u2} R R (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) R S (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S _inst_2))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Algebra.toModule.{u1, u2} R S _inst_1 _inst_2 _inst_4)) (LinearMap.semilinearMapClass.{u1, u1, u1, u2} R R R S (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S _inst_2))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Algebra.toModule.{u1, u2} R S _inst_1 _inst_2 _inst_4) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Algebra.linearMap.{u1, u2} R S _inst_1 _inst_2 _inst_4) (Submodule.span.{u1, u1} R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) a))
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} S] [_inst_4 : Algebra.{u1, u2} R S _inst_1 _inst_2] (a : Set.{u1} R), Eq.{succ u2} (Submodule.{u1, u2} R S (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S _inst_2))) (Algebra.toModule.{u1, u2} R S _inst_1 _inst_2 _inst_4)) (Submodule.span.{u1, u2} R S (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S _inst_2))) (Algebra.toModule.{u1, u2} R S _inst_1 _inst_2 _inst_4) (Set.image.{u1, u2} R S (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) R S (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S _inst_2))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S _inst_2)) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S _inst_2) (RingHom.instRingHomClassRingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S _inst_2))))) (algebraMap.{u1, u2} R S _inst_1 _inst_2 _inst_4)) a)) (Submodule.map.{u1, u1, u1, u2, max u1 u2} R R R S (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S _inst_2))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Algebra.toModule.{u1, u2} R S _inst_1 _inst_2 _inst_4) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (RingHomSurjective.ids.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (LinearMap.{u1, u1, u1, u2} R R (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) R S (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S _inst_2))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Algebra.toModule.{u1, u2} R S _inst_1 _inst_2 _inst_4)) (LinearMap.semilinearMapClass.{u1, u1, u1, u2} R R R S (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S _inst_2))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Algebra.toModule.{u1, u2} R S _inst_1 _inst_2 _inst_4) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Algebra.linearMap.{u1, u2} R S _inst_1 _inst_2 _inst_4) (Submodule.span.{u1, u1} R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) a))
Case conversion may be inaccurate. Consider using '#align submodule.span_algebra_map_image Submodule.span_algebraMap_imageₓ'. -/
/-- A variant of `submodule.span_image` for `algebra_map`. -/
theorem span_algebraMap_image (a : Set R) :
    Submodule.span R (algebraMap R S '' a) = (Submodule.span R a).map (Algebra.linearMap R S) :=
  (Submodule.span_image <| Algebra.linearMap R S).trans rfl
#align submodule.span_algebra_map_image Submodule.span_algebraMap_image

/- warning: submodule.span_algebra_map_image_of_tower -> Submodule.span_algebraMap_image_of_tower is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.span_algebra_map_image_of_tower Submodule.span_algebraMap_image_of_towerₓ'. -/
theorem span_algebraMap_image_of_tower {S T : Type _} [CommSemiring S] [Semiring T] [Module R S]
    [IsScalarTower R S S] [Algebra R T] [Algebra S T] [IsScalarTower R S T] (a : Set S) :
    Submodule.span R (algebraMap S T '' a) =
      (Submodule.span R a).map ((Algebra.linearMap S T).restrictScalars R) :=
  (Submodule.span_image <| (Algebra.linearMap S T).restrictScalars R).trans rfl
#align submodule.span_algebra_map_image_of_tower Submodule.span_algebraMap_image_of_tower

/- warning: submodule.map_mem_span_algebra_map_image -> Submodule.map_mem_span_algebraMap_image is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.map_mem_span_algebra_map_image Submodule.map_mem_span_algebraMap_imageₓ'. -/
theorem map_mem_span_algebraMap_image {S T : Type _} [CommSemiring S] [Semiring T] [Algebra R S]
    [Algebra R T] [Algebra S T] [IsScalarTower R S T] (x : S) (a : Set S)
    (hx : x ∈ Submodule.span R a) : algebraMap S T x ∈ Submodule.span R (algebraMap S T '' a) := by
  rw [span_algebra_map_image_of_tower, mem_map]; exact ⟨x, hx, rfl⟩
#align submodule.map_mem_span_algebra_map_image Submodule.map_mem_span_algebraMap_image

end Algebra

end Submodule

end Semiring

section Ring

namespace Algebra

variable [CommSemiring R] [Semiring A] [Algebra R A]

variable [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M]

/- warning: algebra.lsmul_injective -> Algebra.lsmul_injective is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebra.lsmul_injective Algebra.lsmul_injectiveₓ'. -/
theorem lsmul_injective [NoZeroSMulDivisors A M] {x : A} (hx : x ≠ 0) :
    Function.Injective (lsmul R M x) :=
  smul_right_injective _ hx
#align algebra.lsmul_injective Algebra.lsmul_injective

end Algebra

end Ring

