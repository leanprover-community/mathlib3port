/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel

! This file was ported from Lean 3 source module category_theory.preadditive.generator
! leanprover-community/mathlib commit 09f981f72d43749f1fa072deade828d9c1e185bb
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Generator
import Mathbin.CategoryTheory.Preadditive.Yoneda.Basic

/-!
# Separators in preadditive categories

This file contains characterizations of separating sets and objects that are valid in all
preadditive categories.

-/


universe v u

open CategoryTheory Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]

#print CategoryTheory.Preadditive.isSeparating_iff /-
theorem Preadditive.isSeparating_iff (𝒢 : Set C) :
    IsSeparating 𝒢 ↔ ∀ ⦃X Y : C⦄ (f : X ⟶ Y), (∀ G ∈ 𝒢, ∀ (h : G ⟶ X), h ≫ f = 0) → f = 0 :=
  ⟨fun h𝒢 X Y f hf => h𝒢 _ _ (by simpa only [limits.comp_zero] using hf), fun h𝒢 X Y f g hfg =>
    sub_eq_zero.1 <| h𝒢 _ (by simpa only [preadditive.comp_sub, sub_eq_zero] using hfg)⟩
#align category_theory.preadditive.is_separating_iff CategoryTheory.Preadditive.isSeparating_iff
-/

#print CategoryTheory.Preadditive.isCoseparating_iff /-
theorem Preadditive.isCoseparating_iff (𝒢 : Set C) :
    IsCoseparating 𝒢 ↔ ∀ ⦃X Y : C⦄ (f : X ⟶ Y), (∀ G ∈ 𝒢, ∀ (h : Y ⟶ G), f ≫ h = 0) → f = 0 :=
  ⟨fun h𝒢 X Y f hf => h𝒢 _ _ (by simpa only [limits.zero_comp] using hf), fun h𝒢 X Y f g hfg =>
    sub_eq_zero.1 <| h𝒢 _ (by simpa only [preadditive.sub_comp, sub_eq_zero] using hfg)⟩
#align category_theory.preadditive.is_coseparating_iff CategoryTheory.Preadditive.isCoseparating_iff
-/

#print CategoryTheory.Preadditive.isSeparator_iff /-
theorem Preadditive.isSeparator_iff (G : C) :
    IsSeparator G ↔ ∀ ⦃X Y : C⦄ (f : X ⟶ Y), (∀ h : G ⟶ X, h ≫ f = 0) → f = 0 :=
  ⟨fun hG X Y f hf => hG.def _ _ (by simpa only [limits.comp_zero] using hf), fun hG =>
    (isSeparator_def _).2 fun X Y f g hfg =>
      sub_eq_zero.1 <| hG _ (by simpa only [preadditive.comp_sub, sub_eq_zero] using hfg)⟩
#align category_theory.preadditive.is_separator_iff CategoryTheory.Preadditive.isSeparator_iff
-/

#print CategoryTheory.Preadditive.isCoseparator_iff /-
theorem Preadditive.isCoseparator_iff (G : C) :
    IsCoseparator G ↔ ∀ ⦃X Y : C⦄ (f : X ⟶ Y), (∀ h : Y ⟶ G, f ≫ h = 0) → f = 0 :=
  ⟨fun hG X Y f hf => hG.def _ _ (by simpa only [limits.zero_comp] using hf), fun hG =>
    (isCoseparator_def _).2 fun X Y f g hfg =>
      sub_eq_zero.1 <| hG _ (by simpa only [preadditive.sub_comp, sub_eq_zero] using hfg)⟩
#align category_theory.preadditive.is_coseparator_iff CategoryTheory.Preadditive.isCoseparator_iff
-/

/- warning: category_theory.is_separator_iff_faithful_preadditive_coyoneda -> CategoryTheory.isSeparator_iff_faithful_preadditiveCoyoneda is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} C _inst_1] (G : C), Iff (CategoryTheory.IsSeparator.{u1, u2} C _inst_1 G) (CategoryTheory.Faithful.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1} (CategoryTheory.Functor.obj.{u1, max u2 u1, u2, max u1 u2 (succ u1)} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1}) (CategoryTheory.preadditiveCoyoneda.{u1, u2} C _inst_1 _inst_2) (Opposite.op.{succ u2} C G)))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} C _inst_1] (G : C), Iff (CategoryTheory.IsSeparator.{u1, u2} C _inst_1 G) (CategoryTheory.Faithful.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1} (Prefunctor.obj.{succ u1, max (succ u2) (succ u1), u2, max u2 (succ u1)} (Opposite.{succ u2} C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1))) (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1}))) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u2, max u2 (succ u1)} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1}) (CategoryTheory.preadditiveCoyoneda.{u1, u2} C _inst_1 _inst_2)) (Opposite.op.{succ u2} C G)))
Case conversion may be inaccurate. Consider using '#align category_theory.is_separator_iff_faithful_preadditive_coyoneda CategoryTheory.isSeparator_iff_faithful_preadditiveCoyonedaₓ'. -/
theorem isSeparator_iff_faithful_preadditiveCoyoneda (G : C) :
    IsSeparator G ↔ Faithful (preadditiveCoyoneda.obj (op G)) :=
  by
  rw [is_separator_iff_faithful_coyoneda_obj, ← whiskering_preadditive_coyoneda, functor.comp_obj,
    whiskering_right_obj_obj]
  exact ⟨fun h => faithful.of_comp _ (forget AddCommGroupCat), fun h => faithful.comp _ _⟩
#align category_theory.is_separator_iff_faithful_preadditive_coyoneda CategoryTheory.isSeparator_iff_faithful_preadditiveCoyoneda

/- warning: category_theory.is_separator_iff_faithful_preadditive_coyoneda_obj -> CategoryTheory.isSeparator_iff_faithful_preadditiveCoyonedaObj is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} C _inst_1] (G : C), Iff (CategoryTheory.IsSeparator.{u1, u2} C _inst_1 G) (CategoryTheory.Faithful.{u1, u1, u2, succ u1} C _inst_1 (ModuleCat.{u1, u1} (CategoryTheory.End.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1)) (Opposite.op.{succ u2} C G)) (CategoryTheory.Preadditive.CategoryTheory.End.ring.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Opposite.preadditive.{u2, u1} C _inst_1 _inst_2) (Opposite.op.{succ u2} C G))) (ModuleCat.moduleCategory.{u1, u1} (CategoryTheory.End.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1)) (Opposite.op.{succ u2} C G)) (CategoryTheory.Preadditive.CategoryTheory.End.ring.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Opposite.preadditive.{u2, u1} C _inst_1 _inst_2) (Opposite.op.{succ u2} C G))) (CategoryTheory.preadditiveCoyonedaObj.{u1, u2} C _inst_1 _inst_2 (Opposite.op.{succ u2} C G)))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} C _inst_1] (G : C), Iff (CategoryTheory.IsSeparator.{u1, u2} C _inst_1 G) (CategoryTheory.Faithful.{u1, u1, u2, succ u1} C _inst_1 (ModuleCat.{u1, u1} (CategoryTheory.End.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1)) (Opposite.op.{succ u2} C G)) (CategoryTheory.Preadditive.instRingEndToCategoryStruct.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.instPreadditiveOppositeOpposite.{u2, u1} C _inst_1 _inst_2) (Opposite.op.{succ u2} C G))) (ModuleCat.moduleCategory.{u1, u1} (CategoryTheory.End.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1)) (Opposite.op.{succ u2} C G)) (CategoryTheory.Preadditive.instRingEndToCategoryStruct.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.instPreadditiveOppositeOpposite.{u2, u1} C _inst_1 _inst_2) (Opposite.op.{succ u2} C G))) (CategoryTheory.preadditiveCoyonedaObj.{u1, u2} C _inst_1 _inst_2 (Opposite.op.{succ u2} C G)))
Case conversion may be inaccurate. Consider using '#align category_theory.is_separator_iff_faithful_preadditive_coyoneda_obj CategoryTheory.isSeparator_iff_faithful_preadditiveCoyonedaObjₓ'. -/
theorem isSeparator_iff_faithful_preadditiveCoyonedaObj (G : C) :
    IsSeparator G ↔ Faithful (preadditiveCoyonedaObj (op G)) :=
  by
  rw [is_separator_iff_faithful_preadditive_coyoneda, preadditive_coyoneda_obj_2]
  exact ⟨fun h => faithful.of_comp _ (forget₂ _ AddCommGroupCat.{v}), fun h => faithful.comp _ _⟩
#align category_theory.is_separator_iff_faithful_preadditive_coyoneda_obj CategoryTheory.isSeparator_iff_faithful_preadditiveCoyonedaObj

/- warning: category_theory.is_coseparator_iff_faithful_preadditive_yoneda -> CategoryTheory.isCoseparator_iff_faithful_preadditiveYoneda is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} C _inst_1] (G : C), Iff (CategoryTheory.IsCoseparator.{u1, u2} C _inst_1 G) (CategoryTheory.Faithful.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1} (CategoryTheory.Functor.obj.{u1, max u2 u1, u2, max u1 u2 (succ u1)} C _inst_1 (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1}) (CategoryTheory.preadditiveYoneda.{u1, u2} C _inst_1 _inst_2) G))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} C _inst_1] (G : C), Iff (CategoryTheory.IsCoseparator.{u1, u2} C _inst_1 G) (CategoryTheory.Faithful.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1} (Prefunctor.obj.{succ u1, max (succ u1) (succ u2), u2, max (succ u1) u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1}))) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u2, max u2 (succ u1)} C _inst_1 (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1}) (CategoryTheory.preadditiveYoneda.{u1, u2} C _inst_1 _inst_2)) G))
Case conversion may be inaccurate. Consider using '#align category_theory.is_coseparator_iff_faithful_preadditive_yoneda CategoryTheory.isCoseparator_iff_faithful_preadditiveYonedaₓ'. -/
theorem isCoseparator_iff_faithful_preadditiveYoneda (G : C) :
    IsCoseparator G ↔ Faithful (preadditiveYoneda.obj G) :=
  by
  rw [is_coseparator_iff_faithful_yoneda_obj, ← whiskering_preadditive_yoneda, functor.comp_obj,
    whiskering_right_obj_obj]
  exact ⟨fun h => faithful.of_comp _ (forget AddCommGroupCat), fun h => faithful.comp _ _⟩
#align category_theory.is_coseparator_iff_faithful_preadditive_yoneda CategoryTheory.isCoseparator_iff_faithful_preadditiveYoneda

/- warning: category_theory.is_coseparator_iff_faithful_preadditive_yoneda_obj -> CategoryTheory.isCoseparator_iff_faithful_preadditiveYonedaObj is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} C _inst_1] (G : C), Iff (CategoryTheory.IsCoseparator.{u1, u2} C _inst_1 G) (CategoryTheory.Faithful.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (ModuleCat.{u1, u1} (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) G) (CategoryTheory.Preadditive.CategoryTheory.End.ring.{u1, u2} C _inst_1 _inst_2 G)) (ModuleCat.moduleCategory.{u1, u1} (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) G) (CategoryTheory.Preadditive.CategoryTheory.End.ring.{u1, u2} C _inst_1 _inst_2 G)) (CategoryTheory.preadditiveYonedaObj.{u1, u2} C _inst_1 _inst_2 G))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} C _inst_1] (G : C), Iff (CategoryTheory.IsCoseparator.{u1, u2} C _inst_1 G) (CategoryTheory.Faithful.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (ModuleCat.{u1, u1} (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) G) (CategoryTheory.Preadditive.instRingEndToCategoryStruct.{u1, u2} C _inst_1 _inst_2 G)) (ModuleCat.moduleCategory.{u1, u1} (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) G) (CategoryTheory.Preadditive.instRingEndToCategoryStruct.{u1, u2} C _inst_1 _inst_2 G)) (CategoryTheory.preadditiveYonedaObj.{u1, u2} C _inst_1 _inst_2 G))
Case conversion may be inaccurate. Consider using '#align category_theory.is_coseparator_iff_faithful_preadditive_yoneda_obj CategoryTheory.isCoseparator_iff_faithful_preadditiveYonedaObjₓ'. -/
theorem isCoseparator_iff_faithful_preadditiveYonedaObj (G : C) :
    IsCoseparator G ↔ Faithful (preadditiveYonedaObj G) :=
  by
  rw [is_coseparator_iff_faithful_preadditive_yoneda, preadditive_yoneda_obj_2]
  exact ⟨fun h => faithful.of_comp _ (forget₂ _ AddCommGroupCat.{v}), fun h => faithful.comp _ _⟩
#align category_theory.is_coseparator_iff_faithful_preadditive_yoneda_obj CategoryTheory.isCoseparator_iff_faithful_preadditiveYonedaObj

end CategoryTheory

