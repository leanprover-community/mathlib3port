/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel

! This file was ported from Lean 3 source module category_theory.preadditive.yoneda.basic
! leanprover-community/mathlib commit 9d2f0748e6c50d7a2657c564b1ff2c695b39148d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.Yoneda
import Mathbin.CategoryTheory.Preadditive.Opposite
import Mathbin.Algebra.Category.Module.Basic
import Mathbin.Algebra.Category.Group.Preadditive

/-!
# The Yoneda embedding for preadditive categories

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The Yoneda embedding for preadditive categories sends an object `Y` to the presheaf sending an
object `X` to the group of morphisms `X ⟶ Y`. At each point, we get an additional `End Y`-module
structure.

We also show that this presheaf is additive and that it is compatible with the normal Yoneda
embedding in the expected way and deduce that the preadditive Yoneda embedding is fully faithful.

## TODO
* The Yoneda embedding is additive itself

-/


universe v u

open CategoryTheory.Preadditive Opposite CategoryTheory.Limits

noncomputable section

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]

/- warning: category_theory.preadditive_yoneda_obj -> CategoryTheory.preadditiveYonedaObj is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} C _inst_1] (Y : C), CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (ModuleCat.{u1, u1} (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) Y) (CategoryTheory.Preadditive.CategoryTheory.End.ring.{u1, u2} C _inst_1 _inst_2 Y)) (ModuleCat.moduleCategory.{u1, u1} (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) Y) (CategoryTheory.Preadditive.CategoryTheory.End.ring.{u1, u2} C _inst_1 _inst_2 Y))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} C _inst_1] (Y : C), CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (ModuleCat.{u1, u1} (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) Y) (CategoryTheory.Preadditive.instRingEndToCategoryStruct.{u1, u2} C _inst_1 _inst_2 Y)) (ModuleCat.moduleCategory.{u1, u1} (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) Y) (CategoryTheory.Preadditive.instRingEndToCategoryStruct.{u1, u2} C _inst_1 _inst_2 Y))
Case conversion may be inaccurate. Consider using '#align category_theory.preadditive_yoneda_obj CategoryTheory.preadditiveYonedaObjₓ'. -/
/-- The Yoneda embedding for preadditive categories sends an object `Y` to the presheaf sending an
object `X` to the `End Y`-module of morphisms `X ⟶ Y`.
-/
@[simps]
def preadditiveYonedaObj (Y : C) : Cᵒᵖ ⥤ ModuleCat.{v} (End Y)
    where
  obj X := ModuleCat.of _ (X.unop ⟶ Y)
  map X X' f :=
    { toFun := fun g => f.unop ≫ g
      map_add' := fun g g' => comp_add _ _ _ _ _ _
      map_smul' := fun r g => Eq.symm <| Category.assoc _ _ _ }
#align category_theory.preadditive_yoneda_obj CategoryTheory.preadditiveYonedaObj

#print CategoryTheory.preadditiveYoneda /-
/-- The Yoneda embedding for preadditive categories sends an object `Y` to the presheaf sending an
object `X` to the group of morphisms `X ⟶ Y`. At each point, we get an additional `End Y`-module
structure, see `preadditive_yoneda_obj`.
-/
@[simps]
def preadditiveYoneda : C ⥤ Cᵒᵖ ⥤ AddCommGroupCat.{v}
    where
  obj Y := preadditiveYonedaObj Y ⋙ forget₂ _ _
  map Y Y' f :=
    { app := fun X =>
        { toFun := fun g => g ≫ f
          map_zero' := Limits.zero_comp
          map_add' := fun g g' => add_comp _ _ _ _ _ _ }
      naturality' := fun X X' g => AddCommGroupCat.ext _ _ _ _ fun x => Category.assoc _ _ _ }
  map_id' X := by
    ext
    simp
  map_comp' X Y Z f g := by
    ext
    simp
#align category_theory.preadditive_yoneda CategoryTheory.preadditiveYoneda
-/

/- warning: category_theory.preadditive_coyoneda_obj -> CategoryTheory.preadditiveCoyonedaObj is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} C _inst_1] (X : Opposite.{succ u2} C), CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 (ModuleCat.{u1, u1} (CategoryTheory.End.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1)) X) (CategoryTheory.Preadditive.CategoryTheory.End.ring.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Opposite.preadditive.{u2, u1} C _inst_1 _inst_2) X)) (ModuleCat.moduleCategory.{u1, u1} (CategoryTheory.End.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1)) X) (CategoryTheory.Preadditive.CategoryTheory.End.ring.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Opposite.preadditive.{u2, u1} C _inst_1 _inst_2) X))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} C _inst_1] (X : Opposite.{succ u2} C), CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 (ModuleCat.{u1, u1} (CategoryTheory.End.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1)) X) (CategoryTheory.Preadditive.instRingEndToCategoryStruct.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.instPreadditiveOppositeOpposite.{u2, u1} C _inst_1 _inst_2) X)) (ModuleCat.moduleCategory.{u1, u1} (CategoryTheory.End.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1)) X) (CategoryTheory.Preadditive.instRingEndToCategoryStruct.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.instPreadditiveOppositeOpposite.{u2, u1} C _inst_1 _inst_2) X))
Case conversion may be inaccurate. Consider using '#align category_theory.preadditive_coyoneda_obj CategoryTheory.preadditiveCoyonedaObjₓ'. -/
/-- The Yoneda embedding for preadditive categories sends an object `X` to the copresheaf sending an
object `Y` to the `End X`-module of morphisms `X ⟶ Y`.
-/
@[simps]
def preadditiveCoyonedaObj (X : Cᵒᵖ) : C ⥤ ModuleCat.{v} (End X)
    where
  obj Y := ModuleCat.of _ (unop X ⟶ Y)
  map Y Y' f :=
    { toFun := fun g => g ≫ f
      map_add' := fun g g' => add_comp _ _ _ _ _ _
      map_smul' := fun r g => Category.assoc _ _ _ }
#align category_theory.preadditive_coyoneda_obj CategoryTheory.preadditiveCoyonedaObj

#print CategoryTheory.preadditiveCoyoneda /-
/-- The Yoneda embedding for preadditive categories sends an object `X` to the copresheaf sending an
object `Y` to the group of morphisms `X ⟶ Y`. At each point, we get an additional `End X`-module
structure, see `preadditive_coyoneda_obj`.
-/
@[simps]
def preadditiveCoyoneda : Cᵒᵖ ⥤ C ⥤ AddCommGroupCat.{v}
    where
  obj X := preadditiveCoyonedaObj X ⋙ forget₂ _ _
  map X X' f :=
    { app := fun Y =>
        { toFun := fun g => f.unop ≫ g
          map_zero' := Limits.comp_zero
          map_add' := fun g g' => comp_add _ _ _ _ _ _ }
      naturality' := fun Y Y' g =>
        AddCommGroupCat.ext _ _ _ _ fun x => Eq.symm <| Category.assoc _ _ _ }
  map_id' X := by
    ext
    simp
  map_comp' X Y Z f g := by
    ext
    simp
#align category_theory.preadditive_coyoneda CategoryTheory.preadditiveCoyoneda
-/

/- warning: category_theory.additive_yoneda_obj -> CategoryTheory.additive_yonedaObj is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} C _inst_1] (X : C), CategoryTheory.Functor.Additive.{u2, succ u1, u1, u1} (Opposite.{succ u2} C) (ModuleCat.{u1, u1} (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.Preadditive.CategoryTheory.End.ring.{u1, u2} C _inst_1 _inst_2 X)) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (ModuleCat.moduleCategory.{u1, u1} (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.Preadditive.CategoryTheory.End.ring.{u1, u2} C _inst_1 _inst_2 X)) (CategoryTheory.Opposite.preadditive.{u2, u1} C _inst_1 _inst_2) (ModuleCat.CategoryTheory.preadditive.{u1, u1} (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.Preadditive.CategoryTheory.End.ring.{u1, u2} C _inst_1 _inst_2 X)) (CategoryTheory.preadditiveYonedaObj.{u1, u2} C _inst_1 _inst_2 X)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} C _inst_1] (X : C), CategoryTheory.Functor.Additive.{u2, succ u1, u1, u1} (Opposite.{succ u2} C) (ModuleCat.{u1, u1} (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.Preadditive.instRingEndToCategoryStruct.{u1, u2} C _inst_1 _inst_2 X)) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (ModuleCat.moduleCategory.{u1, u1} (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.Preadditive.instRingEndToCategoryStruct.{u1, u2} C _inst_1 _inst_2 X)) (CategoryTheory.instPreadditiveOppositeOpposite.{u2, u1} C _inst_1 _inst_2) (ModuleCat.instPreadditiveModuleCatModuleCategory.{u1, u1} (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.Preadditive.instRingEndToCategoryStruct.{u1, u2} C _inst_1 _inst_2 X)) (CategoryTheory.preadditiveYonedaObj.{u1, u2} C _inst_1 _inst_2 X)
Case conversion may be inaccurate. Consider using '#align category_theory.additive_yoneda_obj CategoryTheory.additive_yonedaObjₓ'. -/
instance additive_yonedaObj (X : C) : Functor.Additive (preadditiveYonedaObj X) where
#align category_theory.additive_yoneda_obj CategoryTheory.additive_yonedaObj

/- warning: category_theory.additive_yoneda_obj' -> CategoryTheory.additive_yonedaObj' is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} C _inst_1] (X : C), CategoryTheory.Functor.Additive.{u2, succ u1, u1, u1} (Opposite.{succ u2} C) AddCommGroupCat.{u1} (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) AddCommGroupCat.largeCategory.{u1} (CategoryTheory.Opposite.preadditive.{u2, u1} C _inst_1 _inst_2) AddCommGroupCat.CategoryTheory.preadditive.{u1} (CategoryTheory.Functor.obj.{u1, max u2 u1, u2, max u1 u2 (succ u1)} C _inst_1 (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1}) (CategoryTheory.preadditiveYoneda.{u1, u2} C _inst_1 _inst_2) X)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} C _inst_1] (X : C), CategoryTheory.Functor.Additive.{u2, succ u1, u1, u1} (Opposite.{succ u2} C) AddCommGroupCat.{u1} (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) instAddCommGroupCatLargeCategory.{u1} (CategoryTheory.instPreadditiveOppositeOpposite.{u2, u1} C _inst_1 _inst_2) AddCommGroupCat.instPreadditiveAddCommGroupCatInstAddCommGroupCatLargeCategory.{u1} (Prefunctor.obj.{succ u1, max (succ u1) (succ u2), u2, max (succ u1) u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1}))) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u2, max u2 (succ u1)} C _inst_1 (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1}) (CategoryTheory.preadditiveYoneda.{u1, u2} C _inst_1 _inst_2)) X)
Case conversion may be inaccurate. Consider using '#align category_theory.additive_yoneda_obj' CategoryTheory.additive_yonedaObj'ₓ'. -/
instance additive_yonedaObj' (X : C) : Functor.Additive (preadditiveYoneda.obj X) where
#align category_theory.additive_yoneda_obj' CategoryTheory.additive_yonedaObj'

/- warning: category_theory.additive_coyoneda_obj -> CategoryTheory.additive_coyonedaObj is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} C _inst_1] (X : Opposite.{succ u2} C), CategoryTheory.Functor.Additive.{u2, succ u1, u1, u1} C (ModuleCat.{u1, u1} (CategoryTheory.End.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1)) X) (CategoryTheory.Preadditive.CategoryTheory.End.ring.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Opposite.preadditive.{u2, u1} C _inst_1 _inst_2) X)) _inst_1 (ModuleCat.moduleCategory.{u1, u1} (CategoryTheory.End.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1)) X) (CategoryTheory.Preadditive.CategoryTheory.End.ring.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Opposite.preadditive.{u2, u1} C _inst_1 _inst_2) X)) _inst_2 (ModuleCat.CategoryTheory.preadditive.{u1, u1} (CategoryTheory.End.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1)) X) (CategoryTheory.Preadditive.CategoryTheory.End.ring.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Opposite.preadditive.{u2, u1} C _inst_1 _inst_2) X)) (CategoryTheory.preadditiveCoyonedaObj.{u1, u2} C _inst_1 _inst_2 X)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} C _inst_1] (X : Opposite.{succ u2} C), CategoryTheory.Functor.Additive.{u2, succ u1, u1, u1} C (ModuleCat.{u1, u1} (CategoryTheory.End.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1)) X) (CategoryTheory.Preadditive.instRingEndToCategoryStruct.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.instPreadditiveOppositeOpposite.{u2, u1} C _inst_1 _inst_2) X)) _inst_1 (ModuleCat.moduleCategory.{u1, u1} (CategoryTheory.End.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1)) X) (CategoryTheory.Preadditive.instRingEndToCategoryStruct.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.instPreadditiveOppositeOpposite.{u2, u1} C _inst_1 _inst_2) X)) _inst_2 (ModuleCat.instPreadditiveModuleCatModuleCategory.{u1, u1} (CategoryTheory.End.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1)) X) (CategoryTheory.Preadditive.instRingEndToCategoryStruct.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.instPreadditiveOppositeOpposite.{u2, u1} C _inst_1 _inst_2) X)) (CategoryTheory.preadditiveCoyonedaObj.{u1, u2} C _inst_1 _inst_2 X)
Case conversion may be inaccurate. Consider using '#align category_theory.additive_coyoneda_obj CategoryTheory.additive_coyonedaObjₓ'. -/
instance additive_coyonedaObj (X : Cᵒᵖ) : Functor.Additive (preadditiveCoyonedaObj X) where
#align category_theory.additive_coyoneda_obj CategoryTheory.additive_coyonedaObj

/- warning: category_theory.additive_coyoneda_obj' -> CategoryTheory.additive_coyonedaObj' is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} C _inst_1] (X : Opposite.{succ u2} C), CategoryTheory.Functor.Additive.{u2, succ u1, u1, u1} C AddCommGroupCat.{u1} _inst_1 AddCommGroupCat.largeCategory.{u1} _inst_2 AddCommGroupCat.CategoryTheory.preadditive.{u1} (CategoryTheory.Functor.obj.{u1, max u2 u1, u2, max u1 u2 (succ u1)} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1}) (CategoryTheory.preadditiveCoyoneda.{u1, u2} C _inst_1 _inst_2) X)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} C _inst_1] (X : Opposite.{succ u2} C), CategoryTheory.Functor.Additive.{u2, succ u1, u1, u1} C AddCommGroupCat.{u1} _inst_1 instAddCommGroupCatLargeCategory.{u1} _inst_2 AddCommGroupCat.instPreadditiveAddCommGroupCatInstAddCommGroupCatLargeCategory.{u1} (Prefunctor.obj.{succ u1, max (succ u2) (succ u1), u2, max u2 (succ u1)} (Opposite.{succ u2} C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1))) (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1}))) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u2, max u2 (succ u1)} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1}) (CategoryTheory.preadditiveCoyoneda.{u1, u2} C _inst_1 _inst_2)) X)
Case conversion may be inaccurate. Consider using '#align category_theory.additive_coyoneda_obj' CategoryTheory.additive_coyonedaObj'ₓ'. -/
instance additive_coyonedaObj' (X : Cᵒᵖ) : Functor.Additive (preadditiveCoyoneda.obj X) where
#align category_theory.additive_coyoneda_obj' CategoryTheory.additive_coyonedaObj'

/- warning: category_theory.whiskering_preadditive_yoneda -> CategoryTheory.whiskering_preadditiveYoneda is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.whiskering_preadditive_yoneda CategoryTheory.whiskering_preadditiveYonedaₓ'. -/
/-- Composing the preadditive yoneda embedding with the forgetful functor yields the regular
Yoneda embedding.
-/
@[simp]
theorem whiskering_preadditiveYoneda :
    preadditiveYoneda ⋙
        (whiskeringRight Cᵒᵖ AddCommGroupCat (Type v)).obj (forget AddCommGroupCat) =
      yoneda :=
  rfl
#align category_theory.whiskering_preadditive_yoneda CategoryTheory.whiskering_preadditiveYoneda

/- warning: category_theory.whiskering_preadditive_coyoneda -> CategoryTheory.whiskering_preadditiveCoyoneda is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} C _inst_1], Eq.{succ (max u1 (max u2 u1) u2 u1 u2 (succ u1))} (CategoryTheory.Functor.{u1, max u2 u1, u2, max u1 u2 (succ u1)} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.comp.{u1, max u2 u1, max u2 u1, u2, max u1 u2 (succ u1), max u1 u2 (succ u1)} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1}) (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.preadditiveCoyoneda.{u1, u2} C _inst_1 _inst_2) (CategoryTheory.Functor.obj.{succ u1, max (max u1 u2 (succ u1)) u2 u1, succ u1, max (max u2 u1) u1 u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, succ u1, succ u1} AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1} Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, succ u1, succ u1} AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1} Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.{max u2 u1, max u2 u1, max u1 u2 (succ u1), max u1 u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1}) (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.category.{max u2 u1, max u2 u1, max u1 u2 (succ u1), max u1 u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1}) (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.whiskeringRight.{u2, u1, succ u1, u1, succ u1, u1} C _inst_1 AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1} Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.forget.{succ u1, u1, u1} AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1} AddCommGroupCat.concreteCategory.{u1}))) (CategoryTheory.coyoneda.{u1, u2} C _inst_1)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} C _inst_1], Eq.{max (succ u2) (succ (succ u1))} (CategoryTheory.Functor.{u1, max u2 u1, u2, max u2 (succ u1)} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.comp.{u1, max u2 u1, max u2 u1, u2, max u2 (succ u1), max u2 (succ u1)} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1}) (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.preadditiveCoyoneda.{u1, u2} C _inst_1 _inst_2) (Prefunctor.obj.{succ (succ u1), max (max (succ u2) (succ u1)) (succ (succ u1)), succ u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, succ u1, succ u1} AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{succ u1, succ u1} (CategoryTheory.Functor.{u1, u1, succ u1, succ u1} AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{succ u1, succ u1} (CategoryTheory.Functor.{u1, u1, succ u1, succ u1} AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, succ u1, succ u1} AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} Type.{u1} CategoryTheory.types.{u1}))) (CategoryTheory.Functor.{max u2 u1, max u2 u1, max (max (succ u1) u2) u1, max (max (succ u1) u2) u1} (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1}) (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.CategoryStruct.toQuiver.{max (max u2 u1) (succ u1), max u2 (succ u1)} (CategoryTheory.Functor.{max u2 u1, max u2 u1, max (max (succ u1) u2) u1, max (max (succ u1) u2) u1} (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1}) (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Category.toCategoryStruct.{max (max u2 u1) (succ u1), max u2 (succ u1)} (CategoryTheory.Functor.{max u2 u1, max u2 u1, max (max (succ u1) u2) u1, max (max (succ u1) u2) u1} (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1}) (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.category.{max u2 u1, max u2 u1, max (max u2 (succ u1)) u1, max (max u2 (succ u1)) u1} (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1}) (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1})))) (CategoryTheory.Functor.toPrefunctor.{succ u1, max (max u2 u1) (succ u1), succ u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, succ u1, succ u1} AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, succ u1, succ u1} AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.{max u2 u1, max u2 u1, max (max (succ u1) u2) u1, max (max (succ u1) u2) u1} (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1}) (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.category.{max u2 u1, max u2 u1, max (max u2 (succ u1)) u1, max (max u2 (succ u1)) u1} (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1}) (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.whiskeringRight.{u2, u1, succ u1, u1, succ u1, u1} C _inst_1 AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.forget.{succ u1, u1, u1} AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} AddCommGroupCat.concreteCategory.{u1}))) (CategoryTheory.coyoneda.{u1, u2} C _inst_1)
Case conversion may be inaccurate. Consider using '#align category_theory.whiskering_preadditive_coyoneda CategoryTheory.whiskering_preadditiveCoyonedaₓ'. -/
/-- Composing the preadditive yoneda embedding with the forgetful functor yields the regular
Yoneda embedding.
-/
@[simp]
theorem whiskering_preadditiveCoyoneda :
    preadditiveCoyoneda ⋙
        (whiskeringRight C AddCommGroupCat (Type v)).obj (forget AddCommGroupCat) =
      coyoneda :=
  rfl
#align category_theory.whiskering_preadditive_coyoneda CategoryTheory.whiskering_preadditiveCoyoneda

#print CategoryTheory.full_preadditiveYoneda /-
instance full_preadditiveYoneda : Full (preadditiveYoneda : C ⥤ Cᵒᵖ ⥤ AddCommGroupCat) :=
  let yoneda_full :
    Full
      (preadditiveYoneda ⋙
        (whiskeringRight Cᵒᵖ AddCommGroupCat (Type v)).obj (forget AddCommGroupCat)) :=
    Yoneda.yonedaFull
  full.of_comp_faithful preadditive_yoneda
    ((whiskering_right Cᵒᵖ AddCommGroupCat (Type v)).obj (forget AddCommGroupCat))
#align category_theory.preadditive_yoneda_full CategoryTheory.full_preadditiveYoneda
-/

#print CategoryTheory.full_preadditiveCoyoneda /-
instance full_preadditiveCoyoneda : Full (preadditiveCoyoneda : Cᵒᵖ ⥤ C ⥤ AddCommGroupCat) :=
  let coyoneda_full :
    Full
      (preadditiveCoyoneda ⋙
        (whiskeringRight C AddCommGroupCat (Type v)).obj (forget AddCommGroupCat)) :=
    Coyoneda.coyonedaFull
  full.of_comp_faithful preadditive_coyoneda
    ((whiskering_right C AddCommGroupCat (Type v)).obj (forget AddCommGroupCat))
#align category_theory.preadditive_coyoneda_full CategoryTheory.full_preadditiveCoyoneda
-/

#print CategoryTheory.faithful_preadditiveYoneda /-
instance faithful_preadditiveYoneda : Faithful (preadditiveYoneda : C ⥤ Cᵒᵖ ⥤ AddCommGroupCat) :=
  Faithful.of_comp_eq whiskering_preadditiveYoneda
#align category_theory.preadditive_yoneda_faithful CategoryTheory.faithful_preadditiveYoneda
-/

#print CategoryTheory.faithful_preadditiveCoyoneda /-
instance faithful_preadditiveCoyoneda :
    Faithful (preadditiveCoyoneda : Cᵒᵖ ⥤ C ⥤ AddCommGroupCat) :=
  Faithful.of_comp_eq whiskering_preadditiveCoyoneda
#align category_theory.preadditive_coyoneda_faithful CategoryTheory.faithful_preadditiveCoyoneda
-/

end CategoryTheory

