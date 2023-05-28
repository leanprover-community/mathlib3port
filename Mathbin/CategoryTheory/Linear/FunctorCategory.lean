/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module category_theory.linear.functor_category
! leanprover-community/mathlib commit 69c6a5a12d8a2b159f20933e60115a4f2de62b58
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Preadditive.FunctorCategory
import Mathbin.CategoryTheory.Linear.Basic

/-!
# Linear structure on functor categories

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

If `C` and `D` are categories and `D` is `R`-linear,
then `C ⥤ D` is also `R`-linear.

-/


open BigOperators

namespace CategoryTheory

open CategoryTheory.Limits Linear

variable {R : Type _} [Semiring R]

variable {C D : Type _} [Category C] [Category D] [Preadditive D] [Linear R D]

#print CategoryTheory.functorCategoryLinear /-
instance functorCategoryLinear : Linear R (C ⥤ D)
    where
  homModule F G :=
    { smul := fun r α =>
        { app := fun X => r • α.app X
          naturality' := by intros ; rw [comp_smul, smul_comp, α.naturality] }
      one_smul := by intros ; ext; apply one_smul
      zero_smul := by intros ; ext; apply zero_smul
      smul_zero := by intros ; ext; apply smul_zero
      add_smul := by intros ; ext; apply add_smul
      smul_add := by intros ; ext; apply smul_add
      mul_smul := by intros ; ext; apply mul_smul }
  smul_comp' := by intros ; ext; apply smul_comp
  comp_smul' := by intros ; ext; apply comp_smul
#align category_theory.functor_category_linear CategoryTheory.functorCategoryLinear
-/

namespace NatTrans

variable {F G : C ⥤ D}

/- warning: category_theory.nat_trans.app_linear_map -> CategoryTheory.NatTrans.appLinearMap is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {C : Type.{u2}} {D : Type.{u3}} [_inst_2 : CategoryTheory.Category.{u4, u2} C] [_inst_3 : CategoryTheory.Category.{u5, u3} D] [_inst_4 : CategoryTheory.Preadditive.{u5, u3} D _inst_3] [_inst_5 : CategoryTheory.Linear.{u1, u5, u3} R _inst_1 D _inst_3 _inst_4] {F : CategoryTheory.Functor.{u4, u5, u2, u3} C _inst_2 D _inst_3} {G : CategoryTheory.Functor.{u4, u5, u2, u3} C _inst_2 D _inst_3} (X : C), LinearMap.{u1, u1, max u2 u5, u5} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (Quiver.Hom.{succ (max u2 u5), max u4 u5 u2 u3} (CategoryTheory.Functor.{u4, u5, u2, u3} C _inst_2 D _inst_3) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u5, max u4 u5 u2 u3} (CategoryTheory.Functor.{u4, u5, u2, u3} C _inst_2 D _inst_3) (CategoryTheory.Category.toCategoryStruct.{max u2 u5, max u4 u5 u2 u3} (CategoryTheory.Functor.{u4, u5, u2, u3} C _inst_2 D _inst_3) (CategoryTheory.Functor.category.{u4, u5, u2, u3} C _inst_2 D _inst_3))) F G) (Quiver.Hom.{succ u5, u3} D (CategoryTheory.CategoryStruct.toQuiver.{u5, u3} D (CategoryTheory.Category.toCategoryStruct.{u5, u3} D _inst_3)) (CategoryTheory.Functor.obj.{u4, u5, u2, u3} C _inst_2 D _inst_3 F X) (CategoryTheory.Functor.obj.{u4, u5, u2, u3} C _inst_2 D _inst_3 G X)) (AddCommGroup.toAddCommMonoid.{max u2 u5} (Quiver.Hom.{succ (max u2 u5), max u4 u5 u2 u3} (CategoryTheory.Functor.{u4, u5, u2, u3} C _inst_2 D _inst_3) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u5, max u4 u5 u2 u3} (CategoryTheory.Functor.{u4, u5, u2, u3} C _inst_2 D _inst_3) (CategoryTheory.Category.toCategoryStruct.{max u2 u5, max u4 u5 u2 u3} (CategoryTheory.Functor.{u4, u5, u2, u3} C _inst_2 D _inst_3) (CategoryTheory.Functor.category.{u4, u5, u2, u3} C _inst_2 D _inst_3))) F G) (CategoryTheory.Preadditive.homGroup.{max u2 u5, max u4 u5 u2 u3} (CategoryTheory.Functor.{u4, u5, u2, u3} C _inst_2 D _inst_3) (CategoryTheory.Functor.category.{u4, u5, u2, u3} C _inst_2 D _inst_3) (CategoryTheory.functorCategoryPreadditive.{u2, u3, u4, u5} C D _inst_2 _inst_3 _inst_4) F G)) (AddCommGroup.toAddCommMonoid.{u5} (Quiver.Hom.{succ u5, u3} D (CategoryTheory.CategoryStruct.toQuiver.{u5, u3} D (CategoryTheory.Category.toCategoryStruct.{u5, u3} D _inst_3)) (CategoryTheory.Functor.obj.{u4, u5, u2, u3} C _inst_2 D _inst_3 F X) (CategoryTheory.Functor.obj.{u4, u5, u2, u3} C _inst_2 D _inst_3 G X)) (CategoryTheory.Preadditive.homGroup.{u5, u3} D _inst_3 _inst_4 (CategoryTheory.Functor.obj.{u4, u5, u2, u3} C _inst_2 D _inst_3 F X) (CategoryTheory.Functor.obj.{u4, u5, u2, u3} C _inst_2 D _inst_3 G X))) (CategoryTheory.Linear.homModule.{u1, max u2 u5, max u4 u5 u2 u3} R _inst_1 (CategoryTheory.Functor.{u4, u5, u2, u3} C _inst_2 D _inst_3) (CategoryTheory.Functor.category.{u4, u5, u2, u3} C _inst_2 D _inst_3) (CategoryTheory.functorCategoryPreadditive.{u2, u3, u4, u5} C D _inst_2 _inst_3 _inst_4) (CategoryTheory.functorCategoryLinear.{u1, u2, u3, u4, u5} R _inst_1 C D _inst_2 _inst_3 _inst_4 _inst_5) F G) (CategoryTheory.Linear.homModule.{u1, u5, u3} R _inst_1 D _inst_3 _inst_4 _inst_5 (CategoryTheory.Functor.obj.{u4, u5, u2, u3} C _inst_2 D _inst_3 F X) (CategoryTheory.Functor.obj.{u4, u5, u2, u3} C _inst_2 D _inst_3 G X))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {C : Type.{u2}} {D : Type.{u3}} [_inst_2 : CategoryTheory.Category.{u4, u2} C] [_inst_3 : CategoryTheory.Category.{u5, u3} D] [_inst_4 : CategoryTheory.Preadditive.{u5, u3} D _inst_3] [_inst_5 : CategoryTheory.Linear.{u1, u5, u3} R _inst_1 D _inst_3 _inst_4] {F : CategoryTheory.Functor.{u4, u5, u2, u3} C _inst_2 D _inst_3} {G : CategoryTheory.Functor.{u4, u5, u2, u3} C _inst_2 D _inst_3} (X : C), LinearMap.{u1, u1, max u2 u5, u5} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (Quiver.Hom.{succ (max u2 u5), max (max (max u2 u3) u4) u5} (CategoryTheory.Functor.{u4, u5, u2, u3} C _inst_2 D _inst_3) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u5, max (max (max u2 u3) u4) u5} (CategoryTheory.Functor.{u4, u5, u2, u3} C _inst_2 D _inst_3) (CategoryTheory.Category.toCategoryStruct.{max u2 u5, max (max (max u2 u3) u4) u5} (CategoryTheory.Functor.{u4, u5, u2, u3} C _inst_2 D _inst_3) (CategoryTheory.Functor.category.{u4, u5, u2, u3} C _inst_2 D _inst_3))) F G) (Quiver.Hom.{succ u5, u3} D (CategoryTheory.CategoryStruct.toQuiver.{u5, u3} D (CategoryTheory.Category.toCategoryStruct.{u5, u3} D _inst_3)) (Prefunctor.obj.{succ u4, succ u5, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} C (CategoryTheory.Category.toCategoryStruct.{u4, u2} C _inst_2)) D (CategoryTheory.CategoryStruct.toQuiver.{u5, u3} D (CategoryTheory.Category.toCategoryStruct.{u5, u3} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u4, u5, u2, u3} C _inst_2 D _inst_3 F) X) (Prefunctor.obj.{succ u4, succ u5, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} C (CategoryTheory.Category.toCategoryStruct.{u4, u2} C _inst_2)) D (CategoryTheory.CategoryStruct.toQuiver.{u5, u3} D (CategoryTheory.Category.toCategoryStruct.{u5, u3} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u4, u5, u2, u3} C _inst_2 D _inst_3 G) X)) (AddCommGroup.toAddCommMonoid.{max u2 u5} (Quiver.Hom.{succ (max u2 u5), max (max (max u2 u3) u4) u5} (CategoryTheory.Functor.{u4, u5, u2, u3} C _inst_2 D _inst_3) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u5, max (max (max u2 u3) u4) u5} (CategoryTheory.Functor.{u4, u5, u2, u3} C _inst_2 D _inst_3) (CategoryTheory.Category.toCategoryStruct.{max u2 u5, max (max (max u2 u3) u4) u5} (CategoryTheory.Functor.{u4, u5, u2, u3} C _inst_2 D _inst_3) (CategoryTheory.Functor.category.{u4, u5, u2, u3} C _inst_2 D _inst_3))) F G) (CategoryTheory.Preadditive.homGroup.{max u2 u5, max (max (max u2 u3) u4) u5} (CategoryTheory.Functor.{u4, u5, u2, u3} C _inst_2 D _inst_3) (CategoryTheory.Functor.category.{u4, u5, u2, u3} C _inst_2 D _inst_3) (CategoryTheory.functorCategoryPreadditive.{u2, u3, u4, u5} C D _inst_2 _inst_3 _inst_4) F G)) (AddCommGroup.toAddCommMonoid.{u5} (Quiver.Hom.{succ u5, u3} D (CategoryTheory.CategoryStruct.toQuiver.{u5, u3} D (CategoryTheory.Category.toCategoryStruct.{u5, u3} D _inst_3)) (Prefunctor.obj.{succ u4, succ u5, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} C (CategoryTheory.Category.toCategoryStruct.{u4, u2} C _inst_2)) D (CategoryTheory.CategoryStruct.toQuiver.{u5, u3} D (CategoryTheory.Category.toCategoryStruct.{u5, u3} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u4, u5, u2, u3} C _inst_2 D _inst_3 F) X) (Prefunctor.obj.{succ u4, succ u5, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} C (CategoryTheory.Category.toCategoryStruct.{u4, u2} C _inst_2)) D (CategoryTheory.CategoryStruct.toQuiver.{u5, u3} D (CategoryTheory.Category.toCategoryStruct.{u5, u3} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u4, u5, u2, u3} C _inst_2 D _inst_3 G) X)) (CategoryTheory.Preadditive.homGroup.{u5, u3} D _inst_3 _inst_4 (Prefunctor.obj.{succ u4, succ u5, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} C (CategoryTheory.Category.toCategoryStruct.{u4, u2} C _inst_2)) D (CategoryTheory.CategoryStruct.toQuiver.{u5, u3} D (CategoryTheory.Category.toCategoryStruct.{u5, u3} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u4, u5, u2, u3} C _inst_2 D _inst_3 F) X) (Prefunctor.obj.{succ u4, succ u5, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} C (CategoryTheory.Category.toCategoryStruct.{u4, u2} C _inst_2)) D (CategoryTheory.CategoryStruct.toQuiver.{u5, u3} D (CategoryTheory.Category.toCategoryStruct.{u5, u3} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u4, u5, u2, u3} C _inst_2 D _inst_3 G) X))) (CategoryTheory.Linear.homModule.{u1, max u2 u5, max (max (max u2 u3) u4) u5} R _inst_1 (CategoryTheory.Functor.{u4, u5, u2, u3} C _inst_2 D _inst_3) (CategoryTheory.Functor.category.{u4, u5, u2, u3} C _inst_2 D _inst_3) (CategoryTheory.functorCategoryPreadditive.{u2, u3, u4, u5} C D _inst_2 _inst_3 _inst_4) (CategoryTheory.functorCategoryLinear.{u1, u2, u3, u4, u5} R _inst_1 C D _inst_2 _inst_3 _inst_4 _inst_5) F G) (CategoryTheory.Linear.homModule.{u1, u5, u3} R _inst_1 D _inst_3 _inst_4 _inst_5 (Prefunctor.obj.{succ u4, succ u5, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} C (CategoryTheory.Category.toCategoryStruct.{u4, u2} C _inst_2)) D (CategoryTheory.CategoryStruct.toQuiver.{u5, u3} D (CategoryTheory.Category.toCategoryStruct.{u5, u3} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u4, u5, u2, u3} C _inst_2 D _inst_3 F) X) (Prefunctor.obj.{succ u4, succ u5, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} C (CategoryTheory.Category.toCategoryStruct.{u4, u2} C _inst_2)) D (CategoryTheory.CategoryStruct.toQuiver.{u5, u3} D (CategoryTheory.Category.toCategoryStruct.{u5, u3} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u4, u5, u2, u3} C _inst_2 D _inst_3 G) X))
Case conversion may be inaccurate. Consider using '#align category_theory.nat_trans.app_linear_map CategoryTheory.NatTrans.appLinearMapₓ'. -/
/-- Application of a natural transformation at a fixed object,
as group homomorphism -/
@[simps]
def appLinearMap (X : C) : (F ⟶ G) →ₗ[R] F.obj X ⟶ G.obj X
    where
  toFun α := α.app X
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
#align category_theory.nat_trans.app_linear_map CategoryTheory.NatTrans.appLinearMap

/- warning: category_theory.nat_trans.app_smul -> CategoryTheory.NatTrans.app_smul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.nat_trans.app_smul CategoryTheory.NatTrans.app_smulₓ'. -/
@[simp]
theorem app_smul (X : C) (r : R) (α : F ⟶ G) : (r • α).app X = r • α.app X :=
  rfl
#align category_theory.nat_trans.app_smul CategoryTheory.NatTrans.app_smul

end NatTrans

end CategoryTheory

