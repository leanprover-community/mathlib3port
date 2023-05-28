/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module category_theory.single_obj
! leanprover-community/mathlib commit c085f3044fe585c575e322bfab45b3633c48d820
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Endomorphism
import Mathbin.CategoryTheory.Category.Cat
import Mathbin.Algebra.Category.Mon.Basic
import Mathbin.Combinatorics.Quiver.SingleObj

/-!
# Single-object category

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Single object category with a given monoid of endomorphisms.
It is defined to facilitate transfering some definitions and lemmas (e.g., conjugacy etc.)
from category theory to monoids and groups.

## Main definitions

Given a type `α` with a monoid structure, `single_obj α` is `unit` type with `category` structure
such that `End (single_obj α).star` is the monoid `α`.  This can be extended to a functor `Mon ⥤
Cat`.

If `α` is a group, then `single_obj α` is a groupoid.

An element `x : α` can be reinterpreted as an element of `End (single_obj.star α)` using
`single_obj.to_End`.

## Implementation notes

- `category_struct.comp` on `End (single_obj.star α)` is `flip (*)`, not `(*)`. This way
  multiplication on `End` agrees with the multiplication on `α`.

- By default, Lean puts instances into `category_theory` namespace instead of
  `category_theory.single_obj`, so we give all names explicitly.
-/


universe u v w

namespace CategoryTheory

#print CategoryTheory.SingleObj /-
/-- Abbreviation that allows writing `category_theory.single_obj` rather than `quiver.single_obj`.
-/
abbrev SingleObj :=
  Quiver.SingleObj
#align category_theory.single_obj CategoryTheory.SingleObj
-/

namespace SingleObj

variable (α : Type u)

#print CategoryTheory.SingleObj.categoryStruct /-
/-- One and `flip (*)` become `id` and `comp` for morphisms of the single object category. -/
instance categoryStruct [One α] [Mul α] : CategoryStruct (SingleObj α)
    where
  Hom _ _ := α
  comp _ _ _ x y := y * x
  id _ := 1
#align category_theory.single_obj.category_struct CategoryTheory.SingleObj.categoryStruct
-/

#print CategoryTheory.SingleObj.category /-
/-- Monoid laws become category laws for the single object category. -/
instance category [Monoid α] : Category (SingleObj α)
    where
  comp_id' _ _ := one_mul
  id_comp' _ _ := mul_one
  assoc' _ _ _ _ x y z := (mul_assoc z y x).symm
#align category_theory.single_obj.category CategoryTheory.SingleObj.category
-/

/- warning: category_theory.single_obj.id_as_one -> CategoryTheory.SingleObj.id_as_one is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : Monoid.{u1} α] (x : CategoryTheory.SingleObj.{u1} α), Eq.{succ u1} (Quiver.Hom.{succ u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.CategoryStruct.toQuiver.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.categoryStruct.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))) x x) (CategoryTheory.CategoryStruct.id.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.categoryStruct.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) x) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.CategoryStruct.toQuiver.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.categoryStruct.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))) x x) 1 (OfNat.mk.{u1} (Quiver.Hom.{succ u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.CategoryStruct.toQuiver.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.categoryStruct.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))) x x) 1 (One.one.{u1} (Quiver.Hom.{succ u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.CategoryStruct.toQuiver.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.categoryStruct.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))) x x) (MulOneClass.toHasOne.{u1} (Quiver.Hom.{succ u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.CategoryStruct.toQuiver.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.categoryStruct.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))) x x) (Monoid.toMulOneClass.{u1} (Quiver.Hom.{succ u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.CategoryStruct.toQuiver.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.categoryStruct.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))) x x) _inst_1)))))
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : Monoid.{u1} α] (x : CategoryTheory.SingleObj.{u1} α), Eq.{succ u1} (Quiver.Hom.{succ u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.CategoryStruct.toQuiver.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.categoryStruct.{u1} α (Monoid.toOne.{u1} α _inst_1) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))) x x) (CategoryTheory.CategoryStruct.id.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.categoryStruct.{u1} α (Monoid.toOne.{u1} α _inst_1) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) x) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.CategoryStruct.toQuiver.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.categoryStruct.{u1} α (Monoid.toOne.{u1} α _inst_1) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))) x x) 1 (One.toOfNat1.{u1} (Quiver.Hom.{succ u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.CategoryStruct.toQuiver.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.categoryStruct.{u1} α (Monoid.toOne.{u1} α _inst_1) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))) x x) (Monoid.toOne.{u1} (Quiver.Hom.{succ u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.CategoryStruct.toQuiver.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.categoryStruct.{u1} α (Monoid.toOne.{u1} α _inst_1) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))) x x) _inst_1)))
Case conversion may be inaccurate. Consider using '#align category_theory.single_obj.id_as_one CategoryTheory.SingleObj.id_as_oneₓ'. -/
theorem id_as_one [Monoid α] (x : SingleObj α) : 𝟙 x = 1 :=
  rfl
#align category_theory.single_obj.id_as_one CategoryTheory.SingleObj.id_as_one

/- warning: category_theory.single_obj.comp_as_mul -> CategoryTheory.SingleObj.comp_as_mul is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : Monoid.{u1} α] {x : CategoryTheory.SingleObj.{u1} α} {y : CategoryTheory.SingleObj.{u1} α} {z : CategoryTheory.SingleObj.{u1} α} (f : Quiver.Hom.{succ u1, 0} (CategoryTheory.SingleObj.{u1} α) (Quiver.SingleObj.quiver.{u1} α) x y) (g : Quiver.Hom.{succ u1, 0} (CategoryTheory.SingleObj.{u1} α) (Quiver.SingleObj.quiver.{u1} α) y z), Eq.{succ u1} (Quiver.Hom.{succ u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.CategoryStruct.toQuiver.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.categoryStruct.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))) x z) (CategoryTheory.CategoryStruct.comp.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.categoryStruct.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) x y z f g) (HMul.hMul.{u1, u1, u1} (Quiver.Hom.{succ u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.CategoryStruct.toQuiver.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.categoryStruct.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))) x z) (Quiver.Hom.{succ u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.CategoryStruct.toQuiver.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.categoryStruct.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))) x z) (Quiver.Hom.{succ u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.CategoryStruct.toQuiver.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.categoryStruct.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))) x z) (instHMul.{u1} (Quiver.Hom.{succ u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.CategoryStruct.toQuiver.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.categoryStruct.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))) x z) (MulOneClass.toHasMul.{u1} (Quiver.Hom.{succ u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.CategoryStruct.toQuiver.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.categoryStruct.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))) x z) (Monoid.toMulOneClass.{u1} (Quiver.Hom.{succ u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.CategoryStruct.toQuiver.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.categoryStruct.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))) x z) _inst_1))) g f)
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : Monoid.{u1} α] {x : CategoryTheory.SingleObj.{u1} α} {y : CategoryTheory.SingleObj.{u1} α} {z : CategoryTheory.SingleObj.{u1} α} (f : Quiver.Hom.{succ u1, 0} (CategoryTheory.SingleObj.{u1} α) (Quiver.SingleObj.instQuiverSingleObj.{u1} α) x y) (g : Quiver.Hom.{succ u1, 0} (CategoryTheory.SingleObj.{u1} α) (Quiver.SingleObj.instQuiverSingleObj.{u1} α) y z), Eq.{succ u1} (Quiver.Hom.{succ u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.CategoryStruct.toQuiver.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.categoryStruct.{u1} α (Monoid.toOne.{u1} α _inst_1) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))) x z) (CategoryTheory.CategoryStruct.comp.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.categoryStruct.{u1} α (Monoid.toOne.{u1} α _inst_1) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) x y z f g) (HMul.hMul.{u1, u1, u1} (Quiver.Hom.{succ u1, 0} (CategoryTheory.SingleObj.{u1} α) (Quiver.SingleObj.instQuiverSingleObj.{u1} α) y z) (Quiver.Hom.{succ u1, 0} (CategoryTheory.SingleObj.{u1} α) (Quiver.SingleObj.instQuiverSingleObj.{u1} α) x y) (Quiver.Hom.{succ u1, 0} (CategoryTheory.SingleObj.{u1} α) (Quiver.SingleObj.instQuiverSingleObj.{u1} α) y z) (instHMul.{u1} (Quiver.Hom.{succ u1, 0} (CategoryTheory.SingleObj.{u1} α) (Quiver.SingleObj.instQuiverSingleObj.{u1} α) y z) (MulOneClass.toMul.{u1} (Quiver.Hom.{succ u1, 0} (CategoryTheory.SingleObj.{u1} α) (Quiver.SingleObj.instQuiverSingleObj.{u1} α) y z) (Monoid.toMulOneClass.{u1} (Quiver.Hom.{succ u1, 0} (CategoryTheory.SingleObj.{u1} α) (Quiver.SingleObj.instQuiverSingleObj.{u1} α) y z) _inst_1))) g f)
Case conversion may be inaccurate. Consider using '#align category_theory.single_obj.comp_as_mul CategoryTheory.SingleObj.comp_as_mulₓ'. -/
theorem comp_as_mul [Monoid α] {x y z : SingleObj α} (f : x ⟶ y) (g : y ⟶ z) : f ≫ g = g * f :=
  rfl
#align category_theory.single_obj.comp_as_mul CategoryTheory.SingleObj.comp_as_mul

#print CategoryTheory.SingleObj.groupoid /-
/-- Groupoid structure on `single_obj α`.

See <https://stacks.math.columbia.edu/tag/0019>.
-/
instance groupoid [Group α] : Groupoid (SingleObj α)
    where
  inv _ _ x := x⁻¹
  inv_comp' _ _ := mul_right_inv
  comp_inv' _ _ := mul_left_inv
#align category_theory.single_obj.groupoid CategoryTheory.SingleObj.groupoid
-/

/- warning: category_theory.single_obj.inv_as_inv -> CategoryTheory.SingleObj.inv_as_inv is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : Group.{u1} α] {x : CategoryTheory.SingleObj.{u1} α} {y : CategoryTheory.SingleObj.{u1} α} (f : Quiver.Hom.{succ u1, 0} (CategoryTheory.SingleObj.{u1} α) (Quiver.SingleObj.quiver.{u1} α) x y), Eq.{succ u1} (Quiver.Hom.{succ u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.CategoryStruct.toQuiver.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.Category.toCategoryStruct.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.category.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) y x) (CategoryTheory.inv.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.category.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) x y f (CategoryTheory.IsIso.of_groupoid.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.groupoid.{u1} α _inst_1) x y f)) (Inv.inv.{u1} (Quiver.Hom.{succ u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.CategoryStruct.toQuiver.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.Category.toCategoryStruct.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.category.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) y x) (DivInvMonoid.toHasInv.{u1} (Quiver.Hom.{succ u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.CategoryStruct.toQuiver.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.Category.toCategoryStruct.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.category.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) y x) (Group.toDivInvMonoid.{u1} (Quiver.Hom.{succ u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.CategoryStruct.toQuiver.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.Category.toCategoryStruct.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.category.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) y x) _inst_1)) f)
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : Group.{u1} α] {x : CategoryTheory.SingleObj.{u1} α} {y : CategoryTheory.SingleObj.{u1} α} (f : Quiver.Hom.{succ u1, 0} (CategoryTheory.SingleObj.{u1} α) (Quiver.SingleObj.instQuiverSingleObj.{u1} α) x y), Eq.{succ u1} (Quiver.Hom.{succ u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.CategoryStruct.toQuiver.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.Category.toCategoryStruct.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.category.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) y x) (CategoryTheory.inv.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.category.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) x y f (CategoryTheory.IsIso.of_groupoid.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.groupoid.{u1} α _inst_1) x y f)) (Inv.inv.{u1} (Quiver.Hom.{succ u1, 0} (CategoryTheory.SingleObj.{u1} α) (Quiver.SingleObj.instQuiverSingleObj.{u1} α) x y) (InvOneClass.toInv.{u1} (Quiver.Hom.{succ u1, 0} (CategoryTheory.SingleObj.{u1} α) (Quiver.SingleObj.instQuiverSingleObj.{u1} α) x y) (DivInvOneMonoid.toInvOneClass.{u1} (Quiver.Hom.{succ u1, 0} (CategoryTheory.SingleObj.{u1} α) (Quiver.SingleObj.instQuiverSingleObj.{u1} α) x y) (DivisionMonoid.toDivInvOneMonoid.{u1} (Quiver.Hom.{succ u1, 0} (CategoryTheory.SingleObj.{u1} α) (Quiver.SingleObj.instQuiverSingleObj.{u1} α) x y) (Group.toDivisionMonoid.{u1} (Quiver.Hom.{succ u1, 0} (CategoryTheory.SingleObj.{u1} α) (Quiver.SingleObj.instQuiverSingleObj.{u1} α) x y) _inst_1)))) f)
Case conversion may be inaccurate. Consider using '#align category_theory.single_obj.inv_as_inv CategoryTheory.SingleObj.inv_as_invₓ'. -/
theorem inv_as_inv [Group α] {x y : SingleObj α} (f : x ⟶ y) : inv f = f⁻¹ := by ext;
  rw [comp_as_mul, inv_mul_self, id_as_one]
#align category_theory.single_obj.inv_as_inv CategoryTheory.SingleObj.inv_as_inv

#print CategoryTheory.SingleObj.star /-
/-- Abbreviation that allows writing `category_theory.single_obj.star` rather than
`quiver.single_obj.star`.
-/
abbrev star : SingleObj α :=
  Quiver.SingleObj.star α
#align category_theory.single_obj.star CategoryTheory.SingleObj.star
-/

/- warning: category_theory.single_obj.to_End -> CategoryTheory.SingleObj.toEnd is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : Monoid.{u1} α], MulEquiv.{u1, u1} α (CategoryTheory.End.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.categoryStruct.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (CategoryTheory.SingleObj.star.{u1} α)) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (CategoryTheory.End.mul.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.categoryStruct.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (CategoryTheory.SingleObj.star.{u1} α))
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : Monoid.{u1} α], MulEquiv.{u1, u1} α (CategoryTheory.End.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.categoryStruct.{u1} α (Monoid.toOne.{u1} α _inst_1) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (CategoryTheory.SingleObj.star.{u1} α)) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (CategoryTheory.End.mul.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.categoryStruct.{u1} α (Monoid.toOne.{u1} α _inst_1) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (CategoryTheory.SingleObj.star.{u1} α))
Case conversion may be inaccurate. Consider using '#align category_theory.single_obj.to_End CategoryTheory.SingleObj.toEndₓ'. -/
/-- The endomorphisms monoid of the only object in `single_obj α` is equivalent to the original
     monoid α. -/
def toEnd [Monoid α] : α ≃* End (SingleObj.star α) :=
  { Equiv.refl α with map_mul' := fun x y => rfl }
#align category_theory.single_obj.to_End CategoryTheory.SingleObj.toEnd

/- warning: category_theory.single_obj.to_End_def -> CategoryTheory.SingleObj.toEnd_def is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : Monoid.{u1} α] (x : α), Eq.{succ u1} (CategoryTheory.End.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.categoryStruct.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (CategoryTheory.SingleObj.star.{u1} α)) (coeFn.{succ u1, succ u1} (MulEquiv.{u1, u1} α (CategoryTheory.End.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.categoryStruct.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (CategoryTheory.SingleObj.star.{u1} α)) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (CategoryTheory.End.mul.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.categoryStruct.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (CategoryTheory.SingleObj.star.{u1} α))) (fun (_x : MulEquiv.{u1, u1} α (CategoryTheory.End.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.categoryStruct.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (CategoryTheory.SingleObj.star.{u1} α)) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (CategoryTheory.End.mul.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.categoryStruct.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (CategoryTheory.SingleObj.star.{u1} α))) => α -> (CategoryTheory.End.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.categoryStruct.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (CategoryTheory.SingleObj.star.{u1} α))) (MulEquiv.hasCoeToFun.{u1, u1} α (CategoryTheory.End.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.categoryStruct.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (CategoryTheory.SingleObj.star.{u1} α)) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (CategoryTheory.End.mul.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.categoryStruct.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (CategoryTheory.SingleObj.star.{u1} α))) (CategoryTheory.SingleObj.toEnd.{u1} α _inst_1) x) x
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : Monoid.{u1} α] (x : α), Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => CategoryTheory.End.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.categoryStruct.{u1} α (Monoid.toOne.{u1} α _inst_1) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (CategoryTheory.SingleObj.star.{u1} α)) x) (FunLike.coe.{succ u1, succ u1, succ u1} (MulEquiv.{u1, u1} α (CategoryTheory.End.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.categoryStruct.{u1} α (Monoid.toOne.{u1} α _inst_1) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (CategoryTheory.SingleObj.star.{u1} α)) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (CategoryTheory.End.mul.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.categoryStruct.{u1} α (Monoid.toOne.{u1} α _inst_1) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (CategoryTheory.SingleObj.star.{u1} α))) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => CategoryTheory.End.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.categoryStruct.{u1} α (Monoid.toOne.{u1} α _inst_1) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (CategoryTheory.SingleObj.star.{u1} α)) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (MulEquiv.{u1, u1} α (CategoryTheory.End.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.categoryStruct.{u1} α (Monoid.toOne.{u1} α _inst_1) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (CategoryTheory.SingleObj.star.{u1} α)) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (CategoryTheory.End.mul.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.categoryStruct.{u1} α (Monoid.toOne.{u1} α _inst_1) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (CategoryTheory.SingleObj.star.{u1} α))) α (CategoryTheory.End.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.categoryStruct.{u1} α (Monoid.toOne.{u1} α _inst_1) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (CategoryTheory.SingleObj.star.{u1} α)) (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (MulEquiv.{u1, u1} α (CategoryTheory.End.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.categoryStruct.{u1} α (Monoid.toOne.{u1} α _inst_1) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (CategoryTheory.SingleObj.star.{u1} α)) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (CategoryTheory.End.mul.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.categoryStruct.{u1} α (Monoid.toOne.{u1} α _inst_1) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (CategoryTheory.SingleObj.star.{u1} α))) α (CategoryTheory.End.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.categoryStruct.{u1} α (Monoid.toOne.{u1} α _inst_1) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (CategoryTheory.SingleObj.star.{u1} α)) (MulEquivClass.toEquivLike.{u1, u1, u1} (MulEquiv.{u1, u1} α (CategoryTheory.End.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.categoryStruct.{u1} α (Monoid.toOne.{u1} α _inst_1) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (CategoryTheory.SingleObj.star.{u1} α)) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (CategoryTheory.End.mul.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.categoryStruct.{u1} α (Monoid.toOne.{u1} α _inst_1) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (CategoryTheory.SingleObj.star.{u1} α))) α (CategoryTheory.End.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.categoryStruct.{u1} α (Monoid.toOne.{u1} α _inst_1) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (CategoryTheory.SingleObj.star.{u1} α)) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (CategoryTheory.End.mul.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.categoryStruct.{u1} α (Monoid.toOne.{u1} α _inst_1) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (CategoryTheory.SingleObj.star.{u1} α)) (MulEquiv.instMulEquivClassMulEquiv.{u1, u1} α (CategoryTheory.End.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.categoryStruct.{u1} α (Monoid.toOne.{u1} α _inst_1) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (CategoryTheory.SingleObj.star.{u1} α)) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (CategoryTheory.End.mul.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.categoryStruct.{u1} α (Monoid.toOne.{u1} α _inst_1) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (CategoryTheory.SingleObj.star.{u1} α)))))) (CategoryTheory.SingleObj.toEnd.{u1} α _inst_1) x) x
Case conversion may be inaccurate. Consider using '#align category_theory.single_obj.to_End_def CategoryTheory.SingleObj.toEnd_defₓ'. -/
theorem toEnd_def [Monoid α] (x : α) : toEnd α x = x :=
  rfl
#align category_theory.single_obj.to_End_def CategoryTheory.SingleObj.toEnd_def

#print CategoryTheory.SingleObj.mapHom /-
/-- There is a 1-1 correspondence between monoid homomorphisms `α → β` and functors between the
    corresponding single-object categories. It means that `single_obj` is a fully faithful
    functor.

See <https://stacks.math.columbia.edu/tag/001F> --
although we do not characterize when the functor is full or faithful.
-/
def mapHom (α : Type u) (β : Type v) [Monoid α] [Monoid β] : (α →* β) ≃ SingleObj α ⥤ SingleObj β
    where
  toFun f :=
    { obj := id
      map := fun _ _ => ⇑f
      map_id' := fun _ => f.map_one
      map_comp' := fun _ _ _ x y => f.map_mul y x }
  invFun f :=
    { toFun := @Functor.map _ _ _ _ f (SingleObj.star α) (SingleObj.star α)
      map_one' := f.map_id _
      map_mul' := fun x y => f.map_comp y x }
  left_inv := fun ⟨f, h₁, h₂⟩ => rfl
  right_inv f := by cases f <;> obviously
#align category_theory.single_obj.map_hom CategoryTheory.SingleObj.mapHom
-/

#print CategoryTheory.SingleObj.mapHom_id /-
theorem mapHom_id (α : Type u) [Monoid α] : mapHom α α (MonoidHom.id α) = 𝟭 _ :=
  rfl
#align category_theory.single_obj.map_hom_id CategoryTheory.SingleObj.mapHom_id
-/

#print CategoryTheory.SingleObj.mapHom_comp /-
theorem mapHom_comp {α : Type u} {β : Type v} [Monoid α] [Monoid β] (f : α →* β) {γ : Type w}
    [Monoid γ] (g : β →* γ) : mapHom α γ (g.comp f) = mapHom α β f ⋙ mapHom β γ g :=
  rfl
#align category_theory.single_obj.map_hom_comp CategoryTheory.SingleObj.mapHom_comp
-/

#print CategoryTheory.SingleObj.differenceFunctor /-
/-- Given a function `f : C → G` from a category to a group, we get a functor
    `C ⥤ G` sending any morphism `x ⟶ y` to `f y * (f x)⁻¹`. -/
@[simps]
def differenceFunctor {C G} [Category C] [Group G] (f : C → G) : C ⥤ SingleObj G
    where
  obj _ := ()
  map x y _ := f y * (f x)⁻¹
  map_id' := by intro ; rw [single_obj.id_as_one, mul_right_inv]
  map_comp' := by intros ;
    rw [single_obj.comp_as_mul, ← mul_assoc, mul_left_inj, mul_assoc, inv_mul_self, mul_one]
#align category_theory.single_obj.difference_functor CategoryTheory.SingleObj.differenceFunctor
-/

end SingleObj

end CategoryTheory

open CategoryTheory

namespace MonoidHom

#print MonoidHom.toFunctor /-
/-- Reinterpret a monoid homomorphism `f : α → β` as a functor `(single_obj α) ⥤ (single_obj β)`.
See also `category_theory.single_obj.map_hom` for an equivalence between these types. -/
@[reducible]
def toFunctor {α : Type u} {β : Type v} [Monoid α] [Monoid β] (f : α →* β) :
    SingleObj α ⥤ SingleObj β :=
  SingleObj.mapHom α β f
#align monoid_hom.to_functor MonoidHom.toFunctor
-/

#print MonoidHom.id_toFunctor /-
@[simp]
theorem id_toFunctor (α : Type u) [Monoid α] : (id α).toFunctor = 𝟭 _ :=
  rfl
#align monoid_hom.id_to_functor MonoidHom.id_toFunctor
-/

#print MonoidHom.comp_toFunctor /-
@[simp]
theorem comp_toFunctor {α : Type u} {β : Type v} [Monoid α] [Monoid β] (f : α →* β) {γ : Type w}
    [Monoid γ] (g : β →* γ) : (g.comp f).toFunctor = f.toFunctor ⋙ g.toFunctor :=
  rfl
#align monoid_hom.comp_to_functor MonoidHom.comp_toFunctor
-/

end MonoidHom

namespace Units

variable (α : Type u) [Monoid α]

/- warning: units.to_Aut -> Units.toAut is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : Monoid.{u1} α], MulEquiv.{u1, u1} (Units.{u1} α _inst_1) (CategoryTheory.Aut.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.category.{u1} α _inst_1) (CategoryTheory.SingleObj.star.{u1} α)) (MulOneClass.toHasMul.{u1} (Units.{u1} α _inst_1) (Units.mulOneClass.{u1} α _inst_1)) (MulOneClass.toHasMul.{u1} (CategoryTheory.Aut.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.category.{u1} α _inst_1) (CategoryTheory.SingleObj.star.{u1} α)) (Monoid.toMulOneClass.{u1} (CategoryTheory.Aut.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.category.{u1} α _inst_1) (CategoryTheory.SingleObj.star.{u1} α)) (DivInvMonoid.toMonoid.{u1} (CategoryTheory.Aut.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.category.{u1} α _inst_1) (CategoryTheory.SingleObj.star.{u1} α)) (Group.toDivInvMonoid.{u1} (CategoryTheory.Aut.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.category.{u1} α _inst_1) (CategoryTheory.SingleObj.star.{u1} α)) (CategoryTheory.Aut.group.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.category.{u1} α _inst_1) (CategoryTheory.SingleObj.star.{u1} α))))))
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : Monoid.{u1} α], MulEquiv.{u1, u1} (Units.{u1} α _inst_1) (CategoryTheory.Aut.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.category.{u1} α _inst_1) (CategoryTheory.SingleObj.star.{u1} α)) (MulOneClass.toMul.{u1} (Units.{u1} α _inst_1) (Units.instMulOneClassUnits.{u1} α _inst_1)) (MulOneClass.toMul.{u1} (CategoryTheory.Aut.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.category.{u1} α _inst_1) (CategoryTheory.SingleObj.star.{u1} α)) (Monoid.toMulOneClass.{u1} (CategoryTheory.Aut.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.category.{u1} α _inst_1) (CategoryTheory.SingleObj.star.{u1} α)) (DivInvMonoid.toMonoid.{u1} (CategoryTheory.Aut.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.category.{u1} α _inst_1) (CategoryTheory.SingleObj.star.{u1} α)) (Group.toDivInvMonoid.{u1} (CategoryTheory.Aut.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.category.{u1} α _inst_1) (CategoryTheory.SingleObj.star.{u1} α)) (CategoryTheory.Aut.instGroupAut.{u1, 0} (CategoryTheory.SingleObj.{u1} α) (CategoryTheory.SingleObj.category.{u1} α _inst_1) (CategoryTheory.SingleObj.star.{u1} α))))))
Case conversion may be inaccurate. Consider using '#align units.to_Aut Units.toAutₓ'. -/
/-- The units in a monoid are (multiplicatively) equivalent to
the automorphisms of `star` when we think of the monoid as a single-object category. -/
def toAut : αˣ ≃* Aut (SingleObj.star α) :=
  (Units.mapEquiv (SingleObj.toEnd α)).trans <| Aut.unitsEndEquivAut _
#align units.to_Aut Units.toAut

/- warning: units.to_Aut_hom -> Units.toAut_hom is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align units.to_Aut_hom Units.toAut_homₓ'. -/
@[simp]
theorem toAut_hom (x : αˣ) : (toAut α x).Hom = SingleObj.toEnd α x :=
  rfl
#align units.to_Aut_hom Units.toAut_hom

/- warning: units.to_Aut_inv -> Units.toAut_inv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align units.to_Aut_inv Units.toAut_invₓ'. -/
@[simp]
theorem toAut_inv (x : αˣ) : (toAut α x).inv = SingleObj.toEnd α (x⁻¹ : αˣ) :=
  rfl
#align units.to_Aut_inv Units.toAut_inv

end Units

namespace MonCat

open CategoryTheory

#print MonCat.toCat /-
/-- The fully faithful functor from `Mon` to `Cat`. -/
def toCat : MonCat ⥤ Cat where
  obj x := Cat.of (SingleObj x)
  map x y f := SingleObj.mapHom x y f
#align Mon.to_Cat MonCat.toCat
-/

#print MonCat.toCatFull /-
instance toCatFull : Full toCat
    where
  preimage x y := (SingleObj.mapHom x y).invFun
  witness' x y := by apply Equiv.right_inv
#align Mon.to_Cat_full MonCat.toCatFull
-/

#print MonCat.toCat_faithful /-
instance toCat_faithful : Faithful toCat where map_injective' x y := by apply Equiv.injective
#align Mon.to_Cat_faithful MonCat.toCat_faithful
-/

end MonCat

