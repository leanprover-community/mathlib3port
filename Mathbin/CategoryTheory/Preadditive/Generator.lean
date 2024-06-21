/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import CategoryTheory.Generator
import CategoryTheory.Preadditive.Yoneda.Basic

#align_import category_theory.preadditive.generator from "leanprover-community/mathlib"@"9d2f0748e6c50d7a2657c564b1ff2c695b39148d"

/-!
# Separators in preadditive categories

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

#print CategoryTheory.isSeparator_iff_faithful_preadditiveCoyoneda /-
theorem isSeparator_iff_faithful_preadditiveCoyoneda (G : C) :
    IsSeparator G ↔ CategoryTheory.Functor.Faithful (preadditiveCoyoneda.obj (op G)) :=
  by
  rw [is_separator_iff_faithful_coyoneda_obj, ← whiskering_preadditive_coyoneda, functor.comp_obj,
    whiskering_right_obj_obj]
  exact ⟨fun h => faithful.of_comp _ (forget AddCommGrp), fun h => faithful.comp _ _⟩
#align category_theory.is_separator_iff_faithful_preadditive_coyoneda CategoryTheory.isSeparator_iff_faithful_preadditiveCoyoneda
-/

#print CategoryTheory.isSeparator_iff_faithful_preadditiveCoyonedaObj /-
theorem isSeparator_iff_faithful_preadditiveCoyonedaObj (G : C) :
    IsSeparator G ↔ CategoryTheory.Functor.Faithful (preadditiveCoyonedaObj (op G)) :=
  by
  rw [is_separator_iff_faithful_preadditive_coyoneda, preadditive_coyoneda_obj_2]
  exact ⟨fun h => faithful.of_comp _ (forget₂ _ AddCommGrp.{v}), fun h => faithful.comp _ _⟩
#align category_theory.is_separator_iff_faithful_preadditive_coyoneda_obj CategoryTheory.isSeparator_iff_faithful_preadditiveCoyonedaObj
-/

#print CategoryTheory.isCoseparator_iff_faithful_preadditiveYoneda /-
theorem isCoseparator_iff_faithful_preadditiveYoneda (G : C) :
    IsCoseparator G ↔ CategoryTheory.Functor.Faithful (preadditiveYoneda.obj G) :=
  by
  rw [is_coseparator_iff_faithful_yoneda_obj, ← whiskering_preadditive_yoneda, functor.comp_obj,
    whiskering_right_obj_obj]
  exact ⟨fun h => faithful.of_comp _ (forget AddCommGrp), fun h => faithful.comp _ _⟩
#align category_theory.is_coseparator_iff_faithful_preadditive_yoneda CategoryTheory.isCoseparator_iff_faithful_preadditiveYoneda
-/

#print CategoryTheory.isCoseparator_iff_faithful_preadditiveYonedaObj /-
theorem isCoseparator_iff_faithful_preadditiveYonedaObj (G : C) :
    IsCoseparator G ↔ CategoryTheory.Functor.Faithful (preadditiveYonedaObj G) :=
  by
  rw [is_coseparator_iff_faithful_preadditive_yoneda, preadditive_yoneda_obj_2]
  exact ⟨fun h => faithful.of_comp _ (forget₂ _ AddCommGrp.{v}), fun h => faithful.comp _ _⟩
#align category_theory.is_coseparator_iff_faithful_preadditive_yoneda_obj CategoryTheory.isCoseparator_iff_faithful_preadditiveYonedaObj
-/

end CategoryTheory

