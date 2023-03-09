/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel

! This file was ported from Lean 3 source module category_theory.limits.full_subcategory
! leanprover-community/mathlib commit f47581155c818e6361af4e4fda60d27d020c226b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.Creates

/-!
# Limits in full subcategories

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We introduce the notion of a property closed under taking limits and show that if `P` is closed
under taking limits, then limits in `full_subcategory P` can be constructed from limits in `C`.
More precisely, the inclusion creates such limits.

-/


noncomputable section

universe w' w v u

open CategoryTheory

namespace CategoryTheory.Limits

#print CategoryTheory.Limits.ClosedUnderLimitsOfShape /-
/-- We say that a property is closed under limits of shape `J` if whenever all objects in a
    `J`-shaped diagram have the property, any limit of this diagram also has the property. -/
def ClosedUnderLimitsOfShape {C : Type u} [Category.{v} C] (J : Type w) [Category.{w'} J]
    (P : C → Prop) : Prop :=
  ∀ ⦃F : J ⥤ C⦄ ⦃c : Cone F⦄ (hc : IsLimit c), (∀ j, P (F.obj j)) → P c.pt
#align category_theory.limits.closed_under_limits_of_shape CategoryTheory.Limits.ClosedUnderLimitsOfShape
-/

#print CategoryTheory.Limits.ClosedUnderColimitsOfShape /-
/-- We say that a property is closed under colimits of shape `J` if whenever all objects in a
    `J`-shaped diagram have the property, any colimit of this diagram also has the property. -/
def ClosedUnderColimitsOfShape {C : Type u} [Category.{v} C] (J : Type w) [Category.{w'} J]
    (P : C → Prop) : Prop :=
  ∀ ⦃F : J ⥤ C⦄ ⦃c : Cocone F⦄ (hc : IsColimit c), (∀ j, P (F.obj j)) → P c.pt
#align category_theory.limits.closed_under_colimits_of_shape CategoryTheory.Limits.ClosedUnderColimitsOfShape
-/

section

variable {C : Type u} [Category.{v} C] {J : Type w} [Category.{w'} J] {P : C → Prop}

/- warning: category_theory.limits.closed_under_limits_of_shape.limit -> CategoryTheory.Limits.ClosedUnderLimitsOfShape.limit is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u3, u4} C] {J : Type.{u2}} [_inst_2 : CategoryTheory.Category.{u1, u2} J] {P : C -> Prop}, (CategoryTheory.Limits.ClosedUnderLimitsOfShape.{u1, u2, u3, u4} C _inst_1 J _inst_2 P) -> (forall {F : CategoryTheory.Functor.{u1, u3, u2, u4} J _inst_2 C _inst_1} [_inst_3 : CategoryTheory.Limits.HasLimit.{u1, u2, u3, u4} J _inst_2 C _inst_1 F], (forall (j : J), P (CategoryTheory.Functor.obj.{u1, u3, u2, u4} J _inst_2 C _inst_1 F j)) -> (P (CategoryTheory.Limits.limit.{u1, u2, u3, u4} J _inst_2 C _inst_1 F _inst_3)))
but is expected to have type
  forall {C : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u3, u4} C] {J : Type.{u2}} [_inst_2 : CategoryTheory.Category.{u1, u2} J] {P : C -> Prop}, (CategoryTheory.Limits.ClosedUnderLimitsOfShape.{u1, u2, u3, u4} C _inst_1 J _inst_2 P) -> (forall {F : CategoryTheory.Functor.{u1, u3, u2, u4} J _inst_2 C _inst_1} [_inst_3 : CategoryTheory.Limits.HasLimit.{u1, u2, u3, u4} J _inst_2 C _inst_1 F], (forall (j : J), P (Prefunctor.obj.{succ u1, succ u3, u2, u4} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} J (CategoryTheory.Category.toCategoryStruct.{u1, u2} J _inst_2)) C (CategoryTheory.CategoryStruct.toQuiver.{u3, u4} C (CategoryTheory.Category.toCategoryStruct.{u3, u4} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u3, u2, u4} J _inst_2 C _inst_1 F) j)) -> (P (CategoryTheory.Limits.limit.{u1, u2, u3, u4} J _inst_2 C _inst_1 F _inst_3)))
Case conversion may be inaccurate. Consider using '#align category_theory.limits.closed_under_limits_of_shape.limit CategoryTheory.Limits.ClosedUnderLimitsOfShape.limitₓ'. -/
theorem ClosedUnderLimitsOfShape.limit (h : ClosedUnderLimitsOfShape J P) {F : J ⥤ C} [HasLimit F] :
    (∀ j, P (F.obj j)) → P (limit F) :=
  h (limit.isLimit _)
#align category_theory.limits.closed_under_limits_of_shape.limit CategoryTheory.Limits.ClosedUnderLimitsOfShape.limit

/- warning: category_theory.limits.closed_under_colimits_of_shape.colimit -> CategoryTheory.Limits.ClosedUnderColimitsOfShape.colimit is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u3, u4} C] {J : Type.{u2}} [_inst_2 : CategoryTheory.Category.{u1, u2} J] {P : C -> Prop}, (CategoryTheory.Limits.ClosedUnderColimitsOfShape.{u1, u2, u3, u4} C _inst_1 J _inst_2 P) -> (forall {F : CategoryTheory.Functor.{u1, u3, u2, u4} J _inst_2 C _inst_1} [_inst_3 : CategoryTheory.Limits.HasColimit.{u1, u2, u3, u4} J _inst_2 C _inst_1 F], (forall (j : J), P (CategoryTheory.Functor.obj.{u1, u3, u2, u4} J _inst_2 C _inst_1 F j)) -> (P (CategoryTheory.Limits.colimit.{u1, u2, u3, u4} J _inst_2 C _inst_1 F _inst_3)))
but is expected to have type
  forall {C : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u3, u4} C] {J : Type.{u2}} [_inst_2 : CategoryTheory.Category.{u1, u2} J] {P : C -> Prop}, (CategoryTheory.Limits.ClosedUnderColimitsOfShape.{u1, u2, u3, u4} C _inst_1 J _inst_2 P) -> (forall {F : CategoryTheory.Functor.{u1, u3, u2, u4} J _inst_2 C _inst_1} [_inst_3 : CategoryTheory.Limits.HasColimit.{u1, u2, u3, u4} J _inst_2 C _inst_1 F], (forall (j : J), P (Prefunctor.obj.{succ u1, succ u3, u2, u4} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} J (CategoryTheory.Category.toCategoryStruct.{u1, u2} J _inst_2)) C (CategoryTheory.CategoryStruct.toQuiver.{u3, u4} C (CategoryTheory.Category.toCategoryStruct.{u3, u4} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u3, u2, u4} J _inst_2 C _inst_1 F) j)) -> (P (CategoryTheory.Limits.colimit.{u1, u2, u3, u4} J _inst_2 C _inst_1 F _inst_3)))
Case conversion may be inaccurate. Consider using '#align category_theory.limits.closed_under_colimits_of_shape.colimit CategoryTheory.Limits.ClosedUnderColimitsOfShape.colimitₓ'. -/
theorem ClosedUnderColimitsOfShape.colimit (h : ClosedUnderColimitsOfShape J P) {F : J ⥤ C}
    [HasColimit F] : (∀ j, P (F.obj j)) → P (colimit F) :=
  h (colimit.isColimit _)
#align category_theory.limits.closed_under_colimits_of_shape.colimit CategoryTheory.Limits.ClosedUnderColimitsOfShape.colimit

end

section

variable {J : Type w} [Category.{w'} J] {C : Type u} [Category.{v} C] {P : C → Prop}

/- warning: category_theory.limits.creates_limit_full_subcategory_inclusion' -> CategoryTheory.Limits.createsLimitFullSubcategoryInclusion' is a dubious translation:
lean 3 declaration is
  forall {J : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} J] {C : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u3, u4} C] {P : C -> Prop} (F : CategoryTheory.Functor.{u1, u3, u2, u4} J _inst_1 (CategoryTheory.FullSubcategoryₓ.{u3, u4} C _inst_2 P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P)) {c : CategoryTheory.Limits.Cone.{u1, u3, u2, u4} J _inst_1 C _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u3, u2, u4, u4} J _inst_1 (CategoryTheory.FullSubcategoryₓ.{u3, u4} C _inst_2 P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P) C _inst_2 F (CategoryTheory.fullSubcategoryInclusion.{u3, u4} C _inst_2 P))}, (CategoryTheory.Limits.IsLimit.{u1, u3, u2, u4} J _inst_1 C _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u3, u2, u4, u4} J _inst_1 (CategoryTheory.FullSubcategoryₓ.{u3, u4} C _inst_2 P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P) C _inst_2 F (CategoryTheory.fullSubcategoryInclusion.{u3, u4} C _inst_2 P)) c) -> (P (CategoryTheory.Limits.Cone.pt.{u1, u3, u2, u4} J _inst_1 C _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u3, u2, u4, u4} J _inst_1 (CategoryTheory.FullSubcategoryₓ.{u3, u4} C _inst_2 P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P) C _inst_2 F (CategoryTheory.fullSubcategoryInclusion.{u3, u4} C _inst_2 P)) c)) -> (CategoryTheory.CreatesLimit.{u1, u2, u3, u3, u4, u4} (CategoryTheory.FullSubcategoryₓ.{u3, u4} C _inst_2 P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P) C _inst_2 J _inst_1 F (CategoryTheory.fullSubcategoryInclusion.{u3, u4} C _inst_2 P))
but is expected to have type
  forall {J : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} J] {C : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u3, u4} C] {P : C -> Prop} (F : CategoryTheory.Functor.{u1, u3, u2, u4} J _inst_1 (CategoryTheory.FullSubcategory.{u4} C P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P)) {c : CategoryTheory.Limits.Cone.{u1, u3, u2, u4} J _inst_1 C _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u3, u2, u4, u4} J _inst_1 (CategoryTheory.FullSubcategory.{u4} C P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P) C _inst_2 F (CategoryTheory.fullSubcategoryInclusion.{u3, u4} C _inst_2 P))}, (CategoryTheory.Limits.IsLimit.{u1, u3, u2, u4} J _inst_1 C _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u3, u2, u4, u4} J _inst_1 (CategoryTheory.FullSubcategory.{u4} C P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P) C _inst_2 F (CategoryTheory.fullSubcategoryInclusion.{u3, u4} C _inst_2 P)) c) -> (P (CategoryTheory.Limits.Cone.pt.{u1, u3, u2, u4} J _inst_1 C _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u3, u2, u4, u4} J _inst_1 (CategoryTheory.FullSubcategory.{u4} C P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P) C _inst_2 F (CategoryTheory.fullSubcategoryInclusion.{u3, u4} C _inst_2 P)) c)) -> (CategoryTheory.CreatesLimit.{u1, u2, u3, u3, u4, u4} (CategoryTheory.FullSubcategory.{u4} C P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P) C _inst_2 J _inst_1 F (CategoryTheory.fullSubcategoryInclusion.{u3, u4} C _inst_2 P))
Case conversion may be inaccurate. Consider using '#align category_theory.limits.creates_limit_full_subcategory_inclusion' CategoryTheory.Limits.createsLimitFullSubcategoryInclusion'ₓ'. -/
/-- If a `J`-shaped diagram in `full_subcategory P` has a limit cone in `C` whose cone point lives
    in the full subcategory, then this defines a limit in the full subcategory. -/
def createsLimitFullSubcategoryInclusion' (F : J ⥤ FullSubcategory P)
    {c : Cone (F ⋙ fullSubcategoryInclusion P)} (hc : IsLimit c) (h : P c.pt) :
    CreatesLimit F (fullSubcategoryInclusion P) :=
  createsLimitOfFullyFaithfulOfIso' hc ⟨_, h⟩ (Iso.refl _)
#align category_theory.limits.creates_limit_full_subcategory_inclusion' CategoryTheory.Limits.createsLimitFullSubcategoryInclusion'

/- warning: category_theory.limits.creates_limit_full_subcategory_inclusion -> CategoryTheory.Limits.createsLimitFullSubcategoryInclusion is a dubious translation:
lean 3 declaration is
  forall {J : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} J] {C : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u3, u4} C] {P : C -> Prop} (F : CategoryTheory.Functor.{u1, u3, u2, u4} J _inst_1 (CategoryTheory.FullSubcategoryₓ.{u3, u4} C _inst_2 P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P)) [_inst_3 : CategoryTheory.Limits.HasLimit.{u1, u2, u3, u4} J _inst_1 C _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u3, u2, u4, u4} J _inst_1 (CategoryTheory.FullSubcategoryₓ.{u3, u4} C _inst_2 P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P) C _inst_2 F (CategoryTheory.fullSubcategoryInclusion.{u3, u4} C _inst_2 P))], (P (CategoryTheory.Limits.limit.{u1, u2, u3, u4} J _inst_1 C _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u3, u2, u4, u4} J _inst_1 (CategoryTheory.FullSubcategoryₓ.{u3, u4} C _inst_2 P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P) C _inst_2 F (CategoryTheory.fullSubcategoryInclusion.{u3, u4} C _inst_2 P)) _inst_3)) -> (CategoryTheory.CreatesLimit.{u1, u2, u3, u3, u4, u4} (CategoryTheory.FullSubcategoryₓ.{u3, u4} C _inst_2 P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P) C _inst_2 J _inst_1 F (CategoryTheory.fullSubcategoryInclusion.{u3, u4} C _inst_2 P))
but is expected to have type
  forall {J : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} J] {C : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u3, u4} C] {P : C -> Prop} (F : CategoryTheory.Functor.{u1, u3, u2, u4} J _inst_1 (CategoryTheory.FullSubcategory.{u4} C P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P)) [_inst_3 : CategoryTheory.Limits.HasLimit.{u1, u2, u3, u4} J _inst_1 C _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u3, u2, u4, u4} J _inst_1 (CategoryTheory.FullSubcategory.{u4} C P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P) C _inst_2 F (CategoryTheory.fullSubcategoryInclusion.{u3, u4} C _inst_2 P))], (P (CategoryTheory.Limits.limit.{u1, u2, u3, u4} J _inst_1 C _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u3, u2, u4, u4} J _inst_1 (CategoryTheory.FullSubcategory.{u4} C P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P) C _inst_2 F (CategoryTheory.fullSubcategoryInclusion.{u3, u4} C _inst_2 P)) _inst_3)) -> (CategoryTheory.CreatesLimit.{u1, u2, u3, u3, u4, u4} (CategoryTheory.FullSubcategory.{u4} C P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P) C _inst_2 J _inst_1 F (CategoryTheory.fullSubcategoryInclusion.{u3, u4} C _inst_2 P))
Case conversion may be inaccurate. Consider using '#align category_theory.limits.creates_limit_full_subcategory_inclusion CategoryTheory.Limits.createsLimitFullSubcategoryInclusionₓ'. -/
/-- If a `J`-shaped diagram in `full_subcategory P` has a limit in `C` whose cone point lives in the
    full subcategory, then this defines a limit in the full subcategory. -/
def createsLimitFullSubcategoryInclusion (F : J ⥤ FullSubcategory P)
    [HasLimit (F ⋙ fullSubcategoryInclusion P)] (h : P (limit (F ⋙ fullSubcategoryInclusion P))) :
    CreatesLimit F (fullSubcategoryInclusion P) :=
  createsLimitFullSubcategoryInclusion' F (limit.isLimit _) h
#align category_theory.limits.creates_limit_full_subcategory_inclusion CategoryTheory.Limits.createsLimitFullSubcategoryInclusion

/- warning: category_theory.limits.creates_colimit_full_subcategory_inclusion' -> CategoryTheory.Limits.createsColimitFullSubcategoryInclusion' is a dubious translation:
lean 3 declaration is
  forall {J : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} J] {C : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u3, u4} C] {P : C -> Prop} (F : CategoryTheory.Functor.{u1, u3, u2, u4} J _inst_1 (CategoryTheory.FullSubcategoryₓ.{u3, u4} C _inst_2 P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P)) {c : CategoryTheory.Limits.Cocone.{u1, u3, u2, u4} J _inst_1 C _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u3, u2, u4, u4} J _inst_1 (CategoryTheory.FullSubcategoryₓ.{u3, u4} C _inst_2 P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P) C _inst_2 F (CategoryTheory.fullSubcategoryInclusion.{u3, u4} C _inst_2 P))}, (CategoryTheory.Limits.IsColimit.{u1, u3, u2, u4} J _inst_1 C _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u3, u2, u4, u4} J _inst_1 (CategoryTheory.FullSubcategoryₓ.{u3, u4} C _inst_2 P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P) C _inst_2 F (CategoryTheory.fullSubcategoryInclusion.{u3, u4} C _inst_2 P)) c) -> (P (CategoryTheory.Limits.Cocone.pt.{u1, u3, u2, u4} J _inst_1 C _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u3, u2, u4, u4} J _inst_1 (CategoryTheory.FullSubcategoryₓ.{u3, u4} C _inst_2 P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P) C _inst_2 F (CategoryTheory.fullSubcategoryInclusion.{u3, u4} C _inst_2 P)) c)) -> (CategoryTheory.CreatesColimit.{u1, u2, u3, u3, u4, u4} (CategoryTheory.FullSubcategoryₓ.{u3, u4} C _inst_2 P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P) C _inst_2 J _inst_1 F (CategoryTheory.fullSubcategoryInclusion.{u3, u4} C _inst_2 P))
but is expected to have type
  forall {J : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} J] {C : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u3, u4} C] {P : C -> Prop} (F : CategoryTheory.Functor.{u1, u3, u2, u4} J _inst_1 (CategoryTheory.FullSubcategory.{u4} C P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P)) {c : CategoryTheory.Limits.Cocone.{u1, u3, u2, u4} J _inst_1 C _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u3, u2, u4, u4} J _inst_1 (CategoryTheory.FullSubcategory.{u4} C P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P) C _inst_2 F (CategoryTheory.fullSubcategoryInclusion.{u3, u4} C _inst_2 P))}, (CategoryTheory.Limits.IsColimit.{u1, u3, u2, u4} J _inst_1 C _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u3, u2, u4, u4} J _inst_1 (CategoryTheory.FullSubcategory.{u4} C P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P) C _inst_2 F (CategoryTheory.fullSubcategoryInclusion.{u3, u4} C _inst_2 P)) c) -> (P (CategoryTheory.Limits.Cocone.pt.{u1, u3, u2, u4} J _inst_1 C _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u3, u2, u4, u4} J _inst_1 (CategoryTheory.FullSubcategory.{u4} C P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P) C _inst_2 F (CategoryTheory.fullSubcategoryInclusion.{u3, u4} C _inst_2 P)) c)) -> (CategoryTheory.CreatesColimit.{u1, u2, u3, u3, u4, u4} (CategoryTheory.FullSubcategory.{u4} C P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P) C _inst_2 J _inst_1 F (CategoryTheory.fullSubcategoryInclusion.{u3, u4} C _inst_2 P))
Case conversion may be inaccurate. Consider using '#align category_theory.limits.creates_colimit_full_subcategory_inclusion' CategoryTheory.Limits.createsColimitFullSubcategoryInclusion'ₓ'. -/
/-- If a `J`-shaped diagram in `full_subcategory P` has a colimit cocone in `C` whose cocone point
    lives in the full subcategory, then this defines a colimit in the full subcategory. -/
def createsColimitFullSubcategoryInclusion' (F : J ⥤ FullSubcategory P)
    {c : Cocone (F ⋙ fullSubcategoryInclusion P)} (hc : IsColimit c) (h : P c.pt) :
    CreatesColimit F (fullSubcategoryInclusion P) :=
  createsColimitOfFullyFaithfulOfIso' hc ⟨_, h⟩ (Iso.refl _)
#align category_theory.limits.creates_colimit_full_subcategory_inclusion' CategoryTheory.Limits.createsColimitFullSubcategoryInclusion'

/- warning: category_theory.limits.creates_colimit_full_subcategory_inclusion -> CategoryTheory.Limits.createsColimitFullSubcategoryInclusion is a dubious translation:
lean 3 declaration is
  forall {J : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} J] {C : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u3, u4} C] {P : C -> Prop} (F : CategoryTheory.Functor.{u1, u3, u2, u4} J _inst_1 (CategoryTheory.FullSubcategoryₓ.{u3, u4} C _inst_2 P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P)) [_inst_3 : CategoryTheory.Limits.HasColimit.{u1, u2, u3, u4} J _inst_1 C _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u3, u2, u4, u4} J _inst_1 (CategoryTheory.FullSubcategoryₓ.{u3, u4} C _inst_2 P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P) C _inst_2 F (CategoryTheory.fullSubcategoryInclusion.{u3, u4} C _inst_2 P))], (P (CategoryTheory.Limits.colimit.{u1, u2, u3, u4} J _inst_1 C _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u3, u2, u4, u4} J _inst_1 (CategoryTheory.FullSubcategoryₓ.{u3, u4} C _inst_2 P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P) C _inst_2 F (CategoryTheory.fullSubcategoryInclusion.{u3, u4} C _inst_2 P)) _inst_3)) -> (CategoryTheory.CreatesColimit.{u1, u2, u3, u3, u4, u4} (CategoryTheory.FullSubcategoryₓ.{u3, u4} C _inst_2 P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P) C _inst_2 J _inst_1 F (CategoryTheory.fullSubcategoryInclusion.{u3, u4} C _inst_2 P))
but is expected to have type
  forall {J : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} J] {C : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u3, u4} C] {P : C -> Prop} (F : CategoryTheory.Functor.{u1, u3, u2, u4} J _inst_1 (CategoryTheory.FullSubcategory.{u4} C P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P)) [_inst_3 : CategoryTheory.Limits.HasColimit.{u1, u2, u3, u4} J _inst_1 C _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u3, u2, u4, u4} J _inst_1 (CategoryTheory.FullSubcategory.{u4} C P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P) C _inst_2 F (CategoryTheory.fullSubcategoryInclusion.{u3, u4} C _inst_2 P))], (P (CategoryTheory.Limits.colimit.{u1, u2, u3, u4} J _inst_1 C _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u3, u2, u4, u4} J _inst_1 (CategoryTheory.FullSubcategory.{u4} C P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P) C _inst_2 F (CategoryTheory.fullSubcategoryInclusion.{u3, u4} C _inst_2 P)) _inst_3)) -> (CategoryTheory.CreatesColimit.{u1, u2, u3, u3, u4, u4} (CategoryTheory.FullSubcategory.{u4} C P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P) C _inst_2 J _inst_1 F (CategoryTheory.fullSubcategoryInclusion.{u3, u4} C _inst_2 P))
Case conversion may be inaccurate. Consider using '#align category_theory.limits.creates_colimit_full_subcategory_inclusion CategoryTheory.Limits.createsColimitFullSubcategoryInclusionₓ'. -/
/-- If a `J`-shaped diagram in `full_subcategory P` has a colimit in `C` whose cocone point lives in
    the full subcategory, then this defines a colimit in the full subcategory. -/
def createsColimitFullSubcategoryInclusion (F : J ⥤ FullSubcategory P)
    [HasColimit (F ⋙ fullSubcategoryInclusion P)]
    (h : P (colimit (F ⋙ fullSubcategoryInclusion P))) :
    CreatesColimit F (fullSubcategoryInclusion P) :=
  createsColimitFullSubcategoryInclusion' F (colimit.isColimit _) h
#align category_theory.limits.creates_colimit_full_subcategory_inclusion CategoryTheory.Limits.createsColimitFullSubcategoryInclusion

/- warning: category_theory.limits.creates_limit_full_subcategory_inclusion_of_closed -> CategoryTheory.Limits.createsLimitFullSubcategoryInclusionOfClosed is a dubious translation:
lean 3 declaration is
  forall {J : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} J] {C : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u3, u4} C] {P : C -> Prop}, (CategoryTheory.Limits.ClosedUnderLimitsOfShape.{u1, u2, u3, u4} C _inst_2 J _inst_1 P) -> (forall (F : CategoryTheory.Functor.{u1, u3, u2, u4} J _inst_1 (CategoryTheory.FullSubcategoryₓ.{u3, u4} C _inst_2 P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P)) [_inst_3 : CategoryTheory.Limits.HasLimit.{u1, u2, u3, u4} J _inst_1 C _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u3, u2, u4, u4} J _inst_1 (CategoryTheory.FullSubcategoryₓ.{u3, u4} C _inst_2 P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P) C _inst_2 F (CategoryTheory.fullSubcategoryInclusion.{u3, u4} C _inst_2 P))], CategoryTheory.CreatesLimit.{u1, u2, u3, u3, u4, u4} (CategoryTheory.FullSubcategoryₓ.{u3, u4} C _inst_2 P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P) C _inst_2 J _inst_1 F (CategoryTheory.fullSubcategoryInclusion.{u3, u4} C _inst_2 P))
but is expected to have type
  forall {J : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} J] {C : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u3, u4} C] {P : C -> Prop}, (CategoryTheory.Limits.ClosedUnderLimitsOfShape.{u1, u2, u3, u4} C _inst_2 J _inst_1 P) -> (forall (F : CategoryTheory.Functor.{u1, u3, u2, u4} J _inst_1 (CategoryTheory.FullSubcategory.{u4} C P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P)) [_inst_3 : CategoryTheory.Limits.HasLimit.{u1, u2, u3, u4} J _inst_1 C _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u3, u2, u4, u4} J _inst_1 (CategoryTheory.FullSubcategory.{u4} C P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P) C _inst_2 F (CategoryTheory.fullSubcategoryInclusion.{u3, u4} C _inst_2 P))], CategoryTheory.CreatesLimit.{u1, u2, u3, u3, u4, u4} (CategoryTheory.FullSubcategory.{u4} C P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P) C _inst_2 J _inst_1 F (CategoryTheory.fullSubcategoryInclusion.{u3, u4} C _inst_2 P))
Case conversion may be inaccurate. Consider using '#align category_theory.limits.creates_limit_full_subcategory_inclusion_of_closed CategoryTheory.Limits.createsLimitFullSubcategoryInclusionOfClosedₓ'. -/
/-- If `P` is closed under limits of shape `J`, then the inclusion creates such limits. -/
def createsLimitFullSubcategoryInclusionOfClosed (h : ClosedUnderLimitsOfShape J P)
    (F : J ⥤ FullSubcategory P) [HasLimit (F ⋙ fullSubcategoryInclusion P)] :
    CreatesLimit F (fullSubcategoryInclusion P) :=
  createsLimitFullSubcategoryInclusion F (h.limit fun j => (F.obj j).property)
#align category_theory.limits.creates_limit_full_subcategory_inclusion_of_closed CategoryTheory.Limits.createsLimitFullSubcategoryInclusionOfClosed

/- warning: category_theory.limits.creates_limits_of_shape_full_subcategory_inclusion -> CategoryTheory.Limits.createsLimitsOfShapeFullSubcategoryInclusion is a dubious translation:
lean 3 declaration is
  forall {J : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} J] {C : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u3, u4} C] {P : C -> Prop}, (CategoryTheory.Limits.ClosedUnderLimitsOfShape.{u1, u2, u3, u4} C _inst_2 J _inst_1 P) -> (forall [_inst_3 : CategoryTheory.Limits.HasLimitsOfShape.{u1, u2, u3, u4} J _inst_1 C _inst_2], CategoryTheory.CreatesLimitsOfShape.{u1, u2, u3, u3, u4, u4} (CategoryTheory.FullSubcategoryₓ.{u3, u4} C _inst_2 P) (CategoryTheory.InducedCategory.category.{u3, u4, u4} (CategoryTheory.FullSubcategoryₓ.{u3, u4} C _inst_2 P) C _inst_2 (CategoryTheory.FullSubcategoryₓ.obj.{u3, u4} C _inst_2 P)) C _inst_2 J _inst_1 (CategoryTheory.fullSubcategoryInclusion.{u3, u4} C _inst_2 P))
but is expected to have type
  forall {J : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} J] {C : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u3, u4} C] {P : C -> Prop}, (CategoryTheory.Limits.ClosedUnderLimitsOfShape.{u1, u2, u3, u4} C _inst_2 J _inst_1 P) -> (forall [_inst_3 : CategoryTheory.Limits.HasLimitsOfShape.{u1, u2, u3, u4} J _inst_1 C _inst_2], CategoryTheory.CreatesLimitsOfShape.{u1, u2, u3, u3, u4, u4} (CategoryTheory.FullSubcategory.{u4} C P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P) C _inst_2 J _inst_1 (CategoryTheory.fullSubcategoryInclusion.{u3, u4} C _inst_2 P))
Case conversion may be inaccurate. Consider using '#align category_theory.limits.creates_limits_of_shape_full_subcategory_inclusion CategoryTheory.Limits.createsLimitsOfShapeFullSubcategoryInclusionₓ'. -/
/-- If `P` is closed under limits of shape `J`, then the inclusion creates such limits. -/
def createsLimitsOfShapeFullSubcategoryInclusion (h : ClosedUnderLimitsOfShape J P)
    [HasLimitsOfShape J C] : CreatesLimitsOfShape J (fullSubcategoryInclusion P)
    where CreatesLimit F := createsLimitFullSubcategoryInclusionOfClosed h F
#align category_theory.limits.creates_limits_of_shape_full_subcategory_inclusion CategoryTheory.Limits.createsLimitsOfShapeFullSubcategoryInclusion

/- warning: category_theory.limits.has_limit_of_closed_under_limits -> CategoryTheory.Limits.hasLimit_of_closed_under_limits is a dubious translation:
lean 3 declaration is
  forall {J : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} J] {C : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u3, u4} C] {P : C -> Prop}, (CategoryTheory.Limits.ClosedUnderLimitsOfShape.{u1, u2, u3, u4} C _inst_2 J _inst_1 P) -> (forall (F : CategoryTheory.Functor.{u1, u3, u2, u4} J _inst_1 (CategoryTheory.FullSubcategoryₓ.{u3, u4} C _inst_2 P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P)) [_inst_3 : CategoryTheory.Limits.HasLimit.{u1, u2, u3, u4} J _inst_1 C _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u3, u2, u4, u4} J _inst_1 (CategoryTheory.FullSubcategoryₓ.{u3, u4} C _inst_2 P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P) C _inst_2 F (CategoryTheory.fullSubcategoryInclusion.{u3, u4} C _inst_2 P))], CategoryTheory.Limits.HasLimit.{u1, u2, u3, u4} J _inst_1 (CategoryTheory.FullSubcategoryₓ.{u3, u4} C _inst_2 P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P) F)
but is expected to have type
  forall {J : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} J] {C : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u3, u4} C] {P : C -> Prop}, (CategoryTheory.Limits.ClosedUnderLimitsOfShape.{u1, u2, u3, u4} C _inst_2 J _inst_1 P) -> (forall (F : CategoryTheory.Functor.{u1, u3, u2, u4} J _inst_1 (CategoryTheory.FullSubcategory.{u4} C P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P)) [_inst_3 : CategoryTheory.Limits.HasLimit.{u1, u2, u3, u4} J _inst_1 C _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u3, u2, u4, u4} J _inst_1 (CategoryTheory.FullSubcategory.{u4} C P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P) C _inst_2 F (CategoryTheory.fullSubcategoryInclusion.{u3, u4} C _inst_2 P))], CategoryTheory.Limits.HasLimit.{u1, u2, u3, u4} J _inst_1 (CategoryTheory.FullSubcategory.{u4} C P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P) F)
Case conversion may be inaccurate. Consider using '#align category_theory.limits.has_limit_of_closed_under_limits CategoryTheory.Limits.hasLimit_of_closed_under_limitsₓ'. -/
theorem hasLimit_of_closed_under_limits (h : ClosedUnderLimitsOfShape J P)
    (F : J ⥤ FullSubcategory P) [HasLimit (F ⋙ fullSubcategoryInclusion P)] : HasLimit F :=
  have : CreatesLimit F (fullSubcategoryInclusion P) :=
    createsLimitFullSubcategoryInclusionOfClosed h F
  has_limit_of_created F (full_subcategory_inclusion P)
#align category_theory.limits.has_limit_of_closed_under_limits CategoryTheory.Limits.hasLimit_of_closed_under_limits

/- warning: category_theory.limits.has_limits_of_shape_of_closed_under_limits -> CategoryTheory.Limits.hasLimitsOfShape_of_closed_under_limits is a dubious translation:
lean 3 declaration is
  forall {J : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} J] {C : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u3, u4} C] {P : C -> Prop}, (CategoryTheory.Limits.ClosedUnderLimitsOfShape.{u1, u2, u3, u4} C _inst_2 J _inst_1 P) -> (forall [_inst_3 : CategoryTheory.Limits.HasLimitsOfShape.{u1, u2, u3, u4} J _inst_1 C _inst_2], CategoryTheory.Limits.HasLimitsOfShape.{u1, u2, u3, u4} J _inst_1 (CategoryTheory.FullSubcategoryₓ.{u3, u4} C _inst_2 P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P))
but is expected to have type
  forall {J : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} J] {C : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u3, u4} C] {P : C -> Prop}, (CategoryTheory.Limits.ClosedUnderLimitsOfShape.{u1, u2, u3, u4} C _inst_2 J _inst_1 P) -> (forall [_inst_3 : CategoryTheory.Limits.HasLimitsOfShape.{u1, u2, u3, u4} J _inst_1 C _inst_2], CategoryTheory.Limits.HasLimitsOfShape.{u1, u2, u3, u4} J _inst_1 (CategoryTheory.FullSubcategory.{u4} C P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P))
Case conversion may be inaccurate. Consider using '#align category_theory.limits.has_limits_of_shape_of_closed_under_limits CategoryTheory.Limits.hasLimitsOfShape_of_closed_under_limitsₓ'. -/
theorem hasLimitsOfShape_of_closed_under_limits (h : ClosedUnderLimitsOfShape J P)
    [HasLimitsOfShape J C] : HasLimitsOfShape J (FullSubcategory P) :=
  { HasLimit := fun F => hasLimit_of_closed_under_limits h F }
#align category_theory.limits.has_limits_of_shape_of_closed_under_limits CategoryTheory.Limits.hasLimitsOfShape_of_closed_under_limits

/- warning: category_theory.limits.creates_colimit_full_subcategory_inclusion_of_closed -> CategoryTheory.Limits.createsColimitFullSubcategoryInclusionOfClosed is a dubious translation:
lean 3 declaration is
  forall {J : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} J] {C : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u3, u4} C] {P : C -> Prop}, (CategoryTheory.Limits.ClosedUnderColimitsOfShape.{u1, u2, u3, u4} C _inst_2 J _inst_1 P) -> (forall (F : CategoryTheory.Functor.{u1, u3, u2, u4} J _inst_1 (CategoryTheory.FullSubcategoryₓ.{u3, u4} C _inst_2 P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P)) [_inst_3 : CategoryTheory.Limits.HasColimit.{u1, u2, u3, u4} J _inst_1 C _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u3, u2, u4, u4} J _inst_1 (CategoryTheory.FullSubcategoryₓ.{u3, u4} C _inst_2 P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P) C _inst_2 F (CategoryTheory.fullSubcategoryInclusion.{u3, u4} C _inst_2 P))], CategoryTheory.CreatesColimit.{u1, u2, u3, u3, u4, u4} (CategoryTheory.FullSubcategoryₓ.{u3, u4} C _inst_2 P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P) C _inst_2 J _inst_1 F (CategoryTheory.fullSubcategoryInclusion.{u3, u4} C _inst_2 P))
but is expected to have type
  forall {J : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} J] {C : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u3, u4} C] {P : C -> Prop}, (CategoryTheory.Limits.ClosedUnderColimitsOfShape.{u1, u2, u3, u4} C _inst_2 J _inst_1 P) -> (forall (F : CategoryTheory.Functor.{u1, u3, u2, u4} J _inst_1 (CategoryTheory.FullSubcategory.{u4} C P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P)) [_inst_3 : CategoryTheory.Limits.HasColimit.{u1, u2, u3, u4} J _inst_1 C _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u3, u2, u4, u4} J _inst_1 (CategoryTheory.FullSubcategory.{u4} C P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P) C _inst_2 F (CategoryTheory.fullSubcategoryInclusion.{u3, u4} C _inst_2 P))], CategoryTheory.CreatesColimit.{u1, u2, u3, u3, u4, u4} (CategoryTheory.FullSubcategory.{u4} C P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P) C _inst_2 J _inst_1 F (CategoryTheory.fullSubcategoryInclusion.{u3, u4} C _inst_2 P))
Case conversion may be inaccurate. Consider using '#align category_theory.limits.creates_colimit_full_subcategory_inclusion_of_closed CategoryTheory.Limits.createsColimitFullSubcategoryInclusionOfClosedₓ'. -/
/-- If `P` is closed under colimits of shape `J`, then the inclusion creates such colimits. -/
def createsColimitFullSubcategoryInclusionOfClosed (h : ClosedUnderColimitsOfShape J P)
    (F : J ⥤ FullSubcategory P) [HasColimit (F ⋙ fullSubcategoryInclusion P)] :
    CreatesColimit F (fullSubcategoryInclusion P) :=
  createsColimitFullSubcategoryInclusion F (h.colimit fun j => (F.obj j).property)
#align category_theory.limits.creates_colimit_full_subcategory_inclusion_of_closed CategoryTheory.Limits.createsColimitFullSubcategoryInclusionOfClosed

/- warning: category_theory.limits.creates_colimits_of_shape_full_subcategory_inclusion -> CategoryTheory.Limits.createsColimitsOfShapeFullSubcategoryInclusion is a dubious translation:
lean 3 declaration is
  forall {J : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} J] {C : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u3, u4} C] {P : C -> Prop}, (CategoryTheory.Limits.ClosedUnderColimitsOfShape.{u1, u2, u3, u4} C _inst_2 J _inst_1 P) -> (forall [_inst_3 : CategoryTheory.Limits.HasColimitsOfShape.{u1, u2, u3, u4} J _inst_1 C _inst_2], CategoryTheory.CreatesColimitsOfShape.{u1, u2, u3, u3, u4, u4} (CategoryTheory.FullSubcategoryₓ.{u3, u4} C _inst_2 P) (CategoryTheory.InducedCategory.category.{u3, u4, u4} (CategoryTheory.FullSubcategoryₓ.{u3, u4} C _inst_2 P) C _inst_2 (CategoryTheory.FullSubcategoryₓ.obj.{u3, u4} C _inst_2 P)) C _inst_2 J _inst_1 (CategoryTheory.fullSubcategoryInclusion.{u3, u4} C _inst_2 P))
but is expected to have type
  forall {J : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} J] {C : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u3, u4} C] {P : C -> Prop}, (CategoryTheory.Limits.ClosedUnderColimitsOfShape.{u1, u2, u3, u4} C _inst_2 J _inst_1 P) -> (forall [_inst_3 : CategoryTheory.Limits.HasColimitsOfShape.{u1, u2, u3, u4} J _inst_1 C _inst_2], CategoryTheory.CreatesColimitsOfShape.{u1, u2, u3, u3, u4, u4} (CategoryTheory.FullSubcategory.{u4} C P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P) C _inst_2 J _inst_1 (CategoryTheory.fullSubcategoryInclusion.{u3, u4} C _inst_2 P))
Case conversion may be inaccurate. Consider using '#align category_theory.limits.creates_colimits_of_shape_full_subcategory_inclusion CategoryTheory.Limits.createsColimitsOfShapeFullSubcategoryInclusionₓ'. -/
/-- If `P` is closed under colimits of shape `J`, then the inclusion creates such colimits. -/
def createsColimitsOfShapeFullSubcategoryInclusion (h : ClosedUnderColimitsOfShape J P)
    [HasColimitsOfShape J C] : CreatesColimitsOfShape J (fullSubcategoryInclusion P)
    where CreatesColimit F := createsColimitFullSubcategoryInclusionOfClosed h F
#align category_theory.limits.creates_colimits_of_shape_full_subcategory_inclusion CategoryTheory.Limits.createsColimitsOfShapeFullSubcategoryInclusion

/- warning: category_theory.limits.has_colimit_of_closed_under_colimits -> CategoryTheory.Limits.hasColimit_of_closed_under_colimits is a dubious translation:
lean 3 declaration is
  forall {J : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} J] {C : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u3, u4} C] {P : C -> Prop}, (CategoryTheory.Limits.ClosedUnderColimitsOfShape.{u1, u2, u3, u4} C _inst_2 J _inst_1 P) -> (forall (F : CategoryTheory.Functor.{u1, u3, u2, u4} J _inst_1 (CategoryTheory.FullSubcategoryₓ.{u3, u4} C _inst_2 P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P)) [_inst_3 : CategoryTheory.Limits.HasColimit.{u1, u2, u3, u4} J _inst_1 C _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u3, u2, u4, u4} J _inst_1 (CategoryTheory.FullSubcategoryₓ.{u3, u4} C _inst_2 P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P) C _inst_2 F (CategoryTheory.fullSubcategoryInclusion.{u3, u4} C _inst_2 P))], CategoryTheory.Limits.HasColimit.{u1, u2, u3, u4} J _inst_1 (CategoryTheory.FullSubcategoryₓ.{u3, u4} C _inst_2 P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P) F)
but is expected to have type
  forall {J : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} J] {C : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u3, u4} C] {P : C -> Prop}, (CategoryTheory.Limits.ClosedUnderColimitsOfShape.{u1, u2, u3, u4} C _inst_2 J _inst_1 P) -> (forall (F : CategoryTheory.Functor.{u1, u3, u2, u4} J _inst_1 (CategoryTheory.FullSubcategory.{u4} C P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P)) [_inst_3 : CategoryTheory.Limits.HasColimit.{u1, u2, u3, u4} J _inst_1 C _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u3, u2, u4, u4} J _inst_1 (CategoryTheory.FullSubcategory.{u4} C P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P) C _inst_2 F (CategoryTheory.fullSubcategoryInclusion.{u3, u4} C _inst_2 P))], CategoryTheory.Limits.HasColimit.{u1, u2, u3, u4} J _inst_1 (CategoryTheory.FullSubcategory.{u4} C P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P) F)
Case conversion may be inaccurate. Consider using '#align category_theory.limits.has_colimit_of_closed_under_colimits CategoryTheory.Limits.hasColimit_of_closed_under_colimitsₓ'. -/
theorem hasColimit_of_closed_under_colimits (h : ClosedUnderColimitsOfShape J P)
    (F : J ⥤ FullSubcategory P) [HasColimit (F ⋙ fullSubcategoryInclusion P)] : HasColimit F :=
  have : CreatesColimit F (fullSubcategoryInclusion P) :=
    createsColimitFullSubcategoryInclusionOfClosed h F
  has_colimit_of_created F (full_subcategory_inclusion P)
#align category_theory.limits.has_colimit_of_closed_under_colimits CategoryTheory.Limits.hasColimit_of_closed_under_colimits

/- warning: category_theory.limits.has_colimits_of_shape_of_closed_under_colimits -> CategoryTheory.Limits.hasColimitsOfShape_of_closed_under_colimits is a dubious translation:
lean 3 declaration is
  forall {J : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} J] {C : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u3, u4} C] {P : C -> Prop}, (CategoryTheory.Limits.ClosedUnderColimitsOfShape.{u1, u2, u3, u4} C _inst_2 J _inst_1 P) -> (forall [_inst_3 : CategoryTheory.Limits.HasColimitsOfShape.{u1, u2, u3, u4} J _inst_1 C _inst_2], CategoryTheory.Limits.HasColimitsOfShape.{u1, u2, u3, u4} J _inst_1 (CategoryTheory.FullSubcategoryₓ.{u3, u4} C _inst_2 P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P))
but is expected to have type
  forall {J : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} J] {C : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u3, u4} C] {P : C -> Prop}, (CategoryTheory.Limits.ClosedUnderColimitsOfShape.{u1, u2, u3, u4} C _inst_2 J _inst_1 P) -> (forall [_inst_3 : CategoryTheory.Limits.HasColimitsOfShape.{u1, u2, u3, u4} J _inst_1 C _inst_2], CategoryTheory.Limits.HasColimitsOfShape.{u1, u2, u3, u4} J _inst_1 (CategoryTheory.FullSubcategory.{u4} C P) (CategoryTheory.FullSubcategory.category.{u3, u4} C _inst_2 P))
Case conversion may be inaccurate. Consider using '#align category_theory.limits.has_colimits_of_shape_of_closed_under_colimits CategoryTheory.Limits.hasColimitsOfShape_of_closed_under_colimitsₓ'. -/
theorem hasColimitsOfShape_of_closed_under_colimits (h : ClosedUnderColimitsOfShape J P)
    [HasColimitsOfShape J C] : HasColimitsOfShape J (FullSubcategory P) :=
  { HasColimit := fun F => hasColimit_of_closed_under_colimits h F }
#align category_theory.limits.has_colimits_of_shape_of_closed_under_colimits CategoryTheory.Limits.hasColimitsOfShape_of_closed_under_colimits

end

end CategoryTheory.Limits

