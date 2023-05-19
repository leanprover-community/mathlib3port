/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module topology.sheaves.limits
! leanprover-community/mathlib commit 70fd9563a21e7b963887c9360bd29b2393e6225a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Sheaves.Sheaf
import Mathbin.CategoryTheory.Sites.Limits
import Mathbin.CategoryTheory.Limits.FunctorCategory

/-!
# Presheaves in `C` have limits and colimits when `C` does.
-/


noncomputable section

universe v u

open CategoryTheory

open CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {J : Type v} [SmallCategory J]

namespace TopCat

instance [HasLimits C] (X : TopCat) : HasLimits (Presheaf C X) :=
  Limits.functorCategoryHasLimitsOfSize.{v, v}

instance [HasColimits C] (X : TopCat) : HasColimitsOfSize.{v} (Presheaf C X) :=
  Limits.functorCategoryHasColimitsOfSize

instance [HasLimits C] (X : TopCat) : CreatesLimits (Sheaf.forget C X) :=
  Sheaf.CategoryTheory.SheafToPresheaf.CategoryTheory.createsLimits.{u, v, v}

instance [HasLimits C] (X : TopCat) : HasLimitsOfSize.{v} (Sheaf.{v} C X) :=
  has_limits_of_has_limits_creates_limits (Sheaf.forget C X)

/- warning: Top.is_sheaf_of_is_limit -> TopCat.isSheaf_of_isLimit is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {J : Type.{u1}} [_inst_2 : CategoryTheory.SmallCategory.{u1} J] [_inst_3 : CategoryTheory.Limits.HasLimits.{u1, u2} C _inst_1] {X : TopCat.{u1}} (F : CategoryTheory.Functor.{u1, u1, u1, max u2 u1} J _inst_2 (TopCat.Presheaf.{u1, u1, u2} C _inst_1 X) (TopCat.Presheaf.category.{u1, u1, u2} C _inst_1 X)), (forall (j : J), TopCat.Presheaf.IsSheaf.{u1, u1, u2} C _inst_1 X (CategoryTheory.Functor.obj.{u1, u1, u1, max u2 u1} J _inst_2 (TopCat.Presheaf.{u1, u1, u2} C _inst_1 X) (TopCat.Presheaf.category.{u1, u1, u2} C _inst_1 X) F j)) -> (forall {c : CategoryTheory.Limits.Cone.{u1, u1, u1, max u2 u1} J _inst_2 (TopCat.Presheaf.{u1, u1, u2} C _inst_1 X) (TopCat.Presheaf.category.{u1, u1, u2} C _inst_1 X) F}, (CategoryTheory.Limits.IsLimit.{u1, u1, u1, max u2 u1} J _inst_2 (TopCat.Presheaf.{u1, u1, u2} C _inst_1 X) (TopCat.Presheaf.category.{u1, u1, u2} C _inst_1 X) F c) -> (TopCat.Presheaf.IsSheaf.{u1, u1, u2} C _inst_1 X (CategoryTheory.Limits.Cone.pt.{u1, u1, u1, max u2 u1} J _inst_2 (TopCat.Presheaf.{u1, u1, u2} C _inst_1 X) (TopCat.Presheaf.category.{u1, u1, u2} C _inst_1 X) F c)))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {J : Type.{u1}} [_inst_2 : CategoryTheory.SmallCategory.{u1} J] [_inst_3 : CategoryTheory.Limits.HasLimits.{u1, u2} C _inst_1] {X : TopCat.{u1}} (F : CategoryTheory.Functor.{u1, u1, u1, max u1 u2} J _inst_2 (TopCat.Presheaf.{u1, u1, u2} C _inst_1 X) (TopCat.instCategoryPresheaf.{u1, u1, u2} C _inst_1 X)), (forall (j : J), TopCat.Presheaf.IsSheaf.{u1, u1, u2} C _inst_1 X (Prefunctor.obj.{succ u1, succ u1, u1, max u2 u1} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) (TopCat.Presheaf.{u1, u1, u2} C _inst_1 X) (CategoryTheory.CategoryStruct.toQuiver.{u1, max u2 u1} (TopCat.Presheaf.{u1, u1, u2} C _inst_1 X) (CategoryTheory.Category.toCategoryStruct.{u1, max u2 u1} (TopCat.Presheaf.{u1, u1, u2} C _inst_1 X) (TopCat.instCategoryPresheaf.{u1, u1, u2} C _inst_1 X))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u1, max u2 u1} J _inst_2 (TopCat.Presheaf.{u1, u1, u2} C _inst_1 X) (TopCat.instCategoryPresheaf.{u1, u1, u2} C _inst_1 X) F) j)) -> (forall {c : CategoryTheory.Limits.Cone.{u1, u1, u1, max u2 u1} J _inst_2 (TopCat.Presheaf.{u1, u1, u2} C _inst_1 X) (TopCat.instCategoryPresheaf.{u1, u1, u2} C _inst_1 X) F}, (CategoryTheory.Limits.IsLimit.{u1, u1, u1, max u2 u1} J _inst_2 (TopCat.Presheaf.{u1, u1, u2} C _inst_1 X) (TopCat.instCategoryPresheaf.{u1, u1, u2} C _inst_1 X) F c) -> (TopCat.Presheaf.IsSheaf.{u1, u1, u2} C _inst_1 X (CategoryTheory.Limits.Cone.pt.{u1, u1, u1, max u2 u1} J _inst_2 (TopCat.Presheaf.{u1, u1, u2} C _inst_1 X) (TopCat.instCategoryPresheaf.{u1, u1, u2} C _inst_1 X) F c)))
Case conversion may be inaccurate. Consider using '#align Top.is_sheaf_of_is_limit TopCat.isSheaf_of_isLimitₓ'. -/
theorem isSheaf_of_isLimit [HasLimits C] {X : TopCat} (F : J ⥤ Presheaf.{v} C X)
    (H : ∀ j, (F.obj j).IsSheaf) {c : Cone F} (hc : IsLimit c) : c.pt.IsSheaf :=
  by
  let F' : J ⥤ sheaf C X :=
    { obj := fun j => ⟨F.obj j, H j⟩
      map := fun X Y f => ⟨F.map f⟩ }
  let e : F' ⋙ sheaf.forget C X ≅ F := nat_iso.of_components (fun _ => iso.refl _) (by tidy)
  exact
    presheaf.is_sheaf_of_iso
      ((is_limit_of_preserves (sheaf.forget C X) (limit.is_limit F')).conePointsIsoOfNatIso hc e)
      (limit F').2
#align Top.is_sheaf_of_is_limit TopCat.isSheaf_of_isLimit

/- warning: Top.limit_is_sheaf -> TopCat.limit_isSheaf is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {J : Type.{u1}} [_inst_2 : CategoryTheory.SmallCategory.{u1} J] [_inst_3 : CategoryTheory.Limits.HasLimits.{u1, u2} C _inst_1] {X : TopCat.{u1}} (F : CategoryTheory.Functor.{u1, u1, u1, max u2 u1} J _inst_2 (TopCat.Presheaf.{u1, u1, u2} C _inst_1 X) (TopCat.Presheaf.category.{u1, u1, u2} C _inst_1 X)), (forall (j : J), TopCat.Presheaf.IsSheaf.{u1, u1, u2} C _inst_1 X (CategoryTheory.Functor.obj.{u1, u1, u1, max u2 u1} J _inst_2 (TopCat.Presheaf.{u1, u1, u2} C _inst_1 X) (TopCat.Presheaf.category.{u1, u1, u2} C _inst_1 X) F j)) -> (TopCat.Presheaf.IsSheaf.{u1, u1, u2} C _inst_1 X (CategoryTheory.Limits.limit.{u1, u1, u1, max u2 u1} J _inst_2 (TopCat.Presheaf.{u1, u1, u2} C _inst_1 X) (TopCat.Presheaf.category.{u1, u1, u2} C _inst_1 X) F (CategoryTheory.Limits.hasLimitOfHasLimitsOfShape.{u1, u1, u1, max u2 u1} (TopCat.Presheaf.{u1, u1, u2} C _inst_1 X) (TopCat.Presheaf.category.{u1, u1, u2} C _inst_1 X) J _inst_2 (CategoryTheory.Limits.hasLimitsOfShapeOfHasLimits.{u1, u1, u1, max u2 u1} (TopCat.Presheaf.{u1, u1, u2} C _inst_1 X) (TopCat.Presheaf.category.{u1, u1, u2} C _inst_1 X) J _inst_2 (TopCat.Presheaf.CategoryTheory.Limits.hasLimits.{u1, u2} C _inst_1 _inst_3 X)) F)))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {J : Type.{u1}} [_inst_2 : CategoryTheory.SmallCategory.{u1} J] [_inst_3 : CategoryTheory.Limits.HasLimits.{u1, u2} C _inst_1] {X : TopCat.{u1}} (F : CategoryTheory.Functor.{u1, u1, u1, max u1 u2} J _inst_2 (TopCat.Presheaf.{u1, u1, u2} C _inst_1 X) (TopCat.instCategoryPresheaf.{u1, u1, u2} C _inst_1 X)), (forall (j : J), TopCat.Presheaf.IsSheaf.{u1, u1, u2} C _inst_1 X (Prefunctor.obj.{succ u1, succ u1, u1, max u2 u1} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) (TopCat.Presheaf.{u1, u1, u2} C _inst_1 X) (CategoryTheory.CategoryStruct.toQuiver.{u1, max u2 u1} (TopCat.Presheaf.{u1, u1, u2} C _inst_1 X) (CategoryTheory.Category.toCategoryStruct.{u1, max u2 u1} (TopCat.Presheaf.{u1, u1, u2} C _inst_1 X) (TopCat.instCategoryPresheaf.{u1, u1, u2} C _inst_1 X))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u1, max u2 u1} J _inst_2 (TopCat.Presheaf.{u1, u1, u2} C _inst_1 X) (TopCat.instCategoryPresheaf.{u1, u1, u2} C _inst_1 X) F) j)) -> (TopCat.Presheaf.IsSheaf.{u1, u1, u2} C _inst_1 X (CategoryTheory.Limits.limit.{u1, u1, u1, max u2 u1} J _inst_2 (TopCat.Presheaf.{u1, u1, u2} C _inst_1 X) (TopCat.instCategoryPresheaf.{u1, u1, u2} C _inst_1 X) F (CategoryTheory.Limits.hasLimitOfHasLimitsOfShape.{u1, u1, u1, max u2 u1} (TopCat.Presheaf.{u1, u1, u2} C _inst_1 X) (TopCat.instCategoryPresheaf.{u1, u1, u2} C _inst_1 X) J _inst_2 (CategoryTheory.Limits.hasLimitsOfShapeOfHasLimits.{u1, u1, u1, max u2 u1} (TopCat.Presheaf.{u1, u1, u2} C _inst_1 X) (TopCat.instCategoryPresheaf.{u1, u1, u2} C _inst_1 X) J _inst_2 (TopCat.instHasLimitsPresheafInstCategoryPresheaf.{u1, u2} C _inst_1 _inst_3 X)) F)))
Case conversion may be inaccurate. Consider using '#align Top.limit_is_sheaf TopCat.limit_isSheafₓ'. -/
theorem limit_isSheaf [HasLimits C] {X : TopCat} (F : J ⥤ Presheaf.{v} C X)
    (H : ∀ j, (F.obj j).IsSheaf) : (limit F).IsSheaf :=
  isSheaf_of_isLimit F H (limit.isLimit F)
#align Top.limit_is_sheaf TopCat.limit_isSheaf

end TopCat

