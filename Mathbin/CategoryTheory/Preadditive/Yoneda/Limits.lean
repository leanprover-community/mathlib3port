/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel

! This file was ported from Lean 3 source module category_theory.preadditive.yoneda.limits
! leanprover-community/mathlib commit 0b7c740e25651db0ba63648fbae9f9d6f941e31b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Preadditive.Yoneda.Basic
import Mathbin.Algebra.Category.Module.Abelian

/-!
# The Yoneda embedding for preadditive categories preserves limits

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The Yoneda embedding for preadditive categories preserves limits.

## Implementation notes

This is in a separate file to avoid having to import the development of the abelian structure on
`Module` in the main file about the preadditive Yoneda embedding.

-/


universe v u

open CategoryTheory.Preadditive Opposite CategoryTheory.Limits

noncomputable section

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]

/- warning: category_theory.preserves_limits_preadditive_yoneda_obj -> CategoryTheory.preservesLimitsPreadditiveYonedaObj is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} C _inst_1] (X : C), CategoryTheory.Limits.PreservesLimits.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (ModuleCat.{u1, u1} (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.Preadditive.CategoryTheory.End.ring.{u1, u2} C _inst_1 _inst_2 X)) (ModuleCat.moduleCategory.{u1, u1} (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.Preadditive.CategoryTheory.End.ring.{u1, u2} C _inst_1 _inst_2 X)) (CategoryTheory.preadditiveYonedaObj.{u1, u2} C _inst_1 _inst_2 X)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} C _inst_1] (X : C), CategoryTheory.Limits.PreservesLimits.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (ModuleCat.{u1, u1} (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.Preadditive.instRingEndToCategoryStruct.{u1, u2} C _inst_1 _inst_2 X)) (ModuleCat.moduleCategory.{u1, u1} (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.Preadditive.instRingEndToCategoryStruct.{u1, u2} C _inst_1 _inst_2 X)) (CategoryTheory.preadditiveYonedaObj.{u1, u2} C _inst_1 _inst_2 X)
Case conversion may be inaccurate. Consider using '#align category_theory.preserves_limits_preadditive_yoneda_obj CategoryTheory.preservesLimitsPreadditiveYonedaObjₓ'. -/
instance preservesLimitsPreadditiveYonedaObj (X : C) : PreservesLimits (preadditiveYonedaObj X) :=
  have : PreservesLimits (preadditiveYonedaObj X ⋙ forget _) :=
    (inferInstance : PreservesLimits (yoneda.obj X))
  preserves_limits_of_reflects_of_preserves _ (forget _)
#align category_theory.preserves_limits_preadditive_yoneda_obj CategoryTheory.preservesLimitsPreadditiveYonedaObj

/- warning: category_theory.preserves_limits_preadditive_coyoneda_obj -> CategoryTheory.preservesLimitsPreadditiveCoyonedaObj is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} C _inst_1] (X : Opposite.{succ u2} C), CategoryTheory.Limits.PreservesLimits.{u1, u1, u2, succ u1} C _inst_1 (ModuleCat.{u1, u1} (CategoryTheory.End.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1)) X) (CategoryTheory.Preadditive.CategoryTheory.End.ring.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Opposite.preadditive.{u2, u1} C _inst_1 _inst_2) X)) (ModuleCat.moduleCategory.{u1, u1} (CategoryTheory.End.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1)) X) (CategoryTheory.Preadditive.CategoryTheory.End.ring.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Opposite.preadditive.{u2, u1} C _inst_1 _inst_2) X)) (CategoryTheory.preadditiveCoyonedaObj.{u1, u2} C _inst_1 _inst_2 X)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} C _inst_1] (X : Opposite.{succ u2} C), CategoryTheory.Limits.PreservesLimits.{u1, u1, u2, succ u1} C _inst_1 (ModuleCat.{u1, u1} (CategoryTheory.End.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1)) X) (CategoryTheory.Preadditive.instRingEndToCategoryStruct.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.instPreadditiveOppositeOpposite.{u2, u1} C _inst_1 _inst_2) X)) (ModuleCat.moduleCategory.{u1, u1} (CategoryTheory.End.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1)) X) (CategoryTheory.Preadditive.instRingEndToCategoryStruct.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.instPreadditiveOppositeOpposite.{u2, u1} C _inst_1 _inst_2) X)) (CategoryTheory.preadditiveCoyonedaObj.{u1, u2} C _inst_1 _inst_2 X)
Case conversion may be inaccurate. Consider using '#align category_theory.preserves_limits_preadditive_coyoneda_obj CategoryTheory.preservesLimitsPreadditiveCoyonedaObjₓ'. -/
instance preservesLimitsPreadditiveCoyonedaObj (X : Cᵒᵖ) :
    PreservesLimits (preadditiveCoyonedaObj X) :=
  have : PreservesLimits (preadditiveCoyonedaObj X ⋙ forget _) :=
    (inferInstance : PreservesLimits (coyoneda.obj X))
  preserves_limits_of_reflects_of_preserves _ (forget _)
#align category_theory.preserves_limits_preadditive_coyoneda_obj CategoryTheory.preservesLimitsPreadditiveCoyonedaObj

/- warning: category_theory.preserves_limits_preadditive_yoneda.obj -> CategoryTheory.PreservesLimitsPreadditiveYoneda.obj is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} C _inst_1] (X : C), CategoryTheory.Limits.PreservesLimits.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1} (CategoryTheory.Functor.obj.{u1, max u2 u1, u2, max u1 u2 (succ u1)} C _inst_1 (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1}) (CategoryTheory.preadditiveYoneda.{u1, u2} C _inst_1 _inst_2) X)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} C _inst_1] (X : C), CategoryTheory.Limits.PreservesLimits.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} (Prefunctor.obj.{succ u1, max (succ u1) (succ u2), u2, max (succ u1) u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1}))) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u2, max u2 (succ u1)} C _inst_1 (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1}) (CategoryTheory.preadditiveYoneda.{u1, u2} C _inst_1 _inst_2)) X)
Case conversion may be inaccurate. Consider using '#align category_theory.preserves_limits_preadditive_yoneda.obj CategoryTheory.PreservesLimitsPreadditiveYoneda.objₓ'. -/
instance PreservesLimitsPreadditiveYoneda.obj (X : C) : PreservesLimits (preadditiveYoneda.obj X) :=
  show PreservesLimits (preadditiveYonedaObj X ⋙ forget₂ _ _) from inferInstance
#align category_theory.preserves_limits_preadditive_yoneda.obj CategoryTheory.PreservesLimitsPreadditiveYoneda.obj

/- warning: category_theory.preserves_limits_preadditive_coyoneda.obj -> CategoryTheory.PreservesLimitsPreadditiveCoyoneda.obj is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} C _inst_1] (X : Opposite.{succ u2} C), CategoryTheory.Limits.PreservesLimits.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1} (CategoryTheory.Functor.obj.{u1, max u2 u1, u2, max u1 u2 (succ u1)} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1}) (CategoryTheory.preadditiveCoyoneda.{u1, u2} C _inst_1 _inst_2) X)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} C _inst_1] (X : Opposite.{succ u2} C), CategoryTheory.Limits.PreservesLimits.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} (Prefunctor.obj.{succ u1, max (succ u2) (succ u1), u2, max u2 (succ u1)} (Opposite.{succ u2} C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1))) (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1}))) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u2, max u2 (succ u1)} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1}) (CategoryTheory.preadditiveCoyoneda.{u1, u2} C _inst_1 _inst_2)) X)
Case conversion may be inaccurate. Consider using '#align category_theory.preserves_limits_preadditive_coyoneda.obj CategoryTheory.PreservesLimitsPreadditiveCoyoneda.objₓ'. -/
instance PreservesLimitsPreadditiveCoyoneda.obj (X : Cᵒᵖ) :
    PreservesLimits (preadditiveCoyoneda.obj X) :=
  show PreservesLimits (preadditiveCoyonedaObj X ⋙ forget₂ _ _) from inferInstance
#align category_theory.preserves_limits_preadditive_coyoneda.obj CategoryTheory.PreservesLimitsPreadditiveCoyoneda.obj

end CategoryTheory

