/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel

! This file was ported from Lean 3 source module category_theory.preadditive.generator
! leanprover-community/mathlib commit 09597669f02422ed388036273d8848119699c22f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Generator
import Mathbin.CategoryTheory.Preadditive.Yoneda

/-!
# Separators in preadditive categories

This file contains characterizations of separating sets and objects that are valid in all
preadditive categories.

-/


universe v u

open CategoryTheory Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]

theorem Preadditive.is_separating_iff (𝒢 : Set C) :
    IsSeparating 𝒢 ↔ ∀ ⦃X Y : C⦄ (f : X ⟶ Y), (∀ G ∈ 𝒢, ∀ (h : G ⟶ X), h ≫ f = 0) → f = 0 :=
  ⟨fun h𝒢 X Y f hf => h𝒢 _ _ (by simpa only [limits.comp_zero] using hf), fun h𝒢 X Y f g hfg =>
    sub_eq_zero.1 <| h𝒢 _ (by simpa only [preadditive.comp_sub, sub_eq_zero] using hfg)⟩
#align category_theory.preadditive.is_separating_iff CategoryTheory.Preadditive.is_separating_iff

theorem Preadditive.is_coseparating_iff (𝒢 : Set C) :
    IsCoseparating 𝒢 ↔ ∀ ⦃X Y : C⦄ (f : X ⟶ Y), (∀ G ∈ 𝒢, ∀ (h : Y ⟶ G), f ≫ h = 0) → f = 0 :=
  ⟨fun h𝒢 X Y f hf => h𝒢 _ _ (by simpa only [limits.zero_comp] using hf), fun h𝒢 X Y f g hfg =>
    sub_eq_zero.1 <| h𝒢 _ (by simpa only [preadditive.sub_comp, sub_eq_zero] using hfg)⟩
#align
  category_theory.preadditive.is_coseparating_iff CategoryTheory.Preadditive.is_coseparating_iff

theorem Preadditive.is_separator_iff (G : C) :
    IsSeparator G ↔ ∀ ⦃X Y : C⦄ (f : X ⟶ Y), (∀ h : G ⟶ X, h ≫ f = 0) → f = 0 :=
  ⟨fun hG X Y f hf => hG.def _ _ (by simpa only [limits.comp_zero] using hf), fun hG =>
    (is_separator_def _).2 fun X Y f g hfg =>
      sub_eq_zero.1 <| hG _ (by simpa only [preadditive.comp_sub, sub_eq_zero] using hfg)⟩
#align category_theory.preadditive.is_separator_iff CategoryTheory.Preadditive.is_separator_iff

theorem Preadditive.is_coseparator_iff (G : C) :
    IsCoseparator G ↔ ∀ ⦃X Y : C⦄ (f : X ⟶ Y), (∀ h : Y ⟶ G, f ≫ h = 0) → f = 0 :=
  ⟨fun hG X Y f hf => hG.def _ _ (by simpa only [limits.zero_comp] using hf), fun hG =>
    (is_coseparator_def _).2 fun X Y f g hfg =>
      sub_eq_zero.1 <| hG _ (by simpa only [preadditive.sub_comp, sub_eq_zero] using hfg)⟩
#align category_theory.preadditive.is_coseparator_iff CategoryTheory.Preadditive.is_coseparator_iff

theorem is_separator_iff_faithful_preadditive_coyoneda (G : C) :
    IsSeparator G ↔ Faithful (preadditiveCoyoneda.obj (op G)) :=
  by
  rw [is_separator_iff_faithful_coyoneda_obj, ← whiskering_preadditive_coyoneda, functor.comp_obj,
    whiskering_right_obj_obj]
  exact ⟨fun h => faithful.of_comp _ (forget AddCommGroupCat), fun h => faithful.comp _ _⟩
#align
  category_theory.is_separator_iff_faithful_preadditive_coyoneda CategoryTheory.is_separator_iff_faithful_preadditive_coyoneda

theorem is_separator_iff_faithful_preadditive_coyoneda_obj (G : C) :
    IsSeparator G ↔ Faithful (preadditiveCoyonedaObj (op G)) :=
  by
  rw [is_separator_iff_faithful_preadditive_coyoneda, preadditive_coyoneda_obj_2]
  exact ⟨fun h => faithful.of_comp _ (forget₂ _ AddCommGroupCat.{v}), fun h => faithful.comp _ _⟩
#align
  category_theory.is_separator_iff_faithful_preadditive_coyoneda_obj CategoryTheory.is_separator_iff_faithful_preadditive_coyoneda_obj

theorem is_coseparator_iff_faithful_preadditive_yoneda (G : C) :
    IsCoseparator G ↔ Faithful (preadditiveYoneda.obj G) :=
  by
  rw [is_coseparator_iff_faithful_yoneda_obj, ← whiskering_preadditive_yoneda, functor.comp_obj,
    whiskering_right_obj_obj]
  exact ⟨fun h => faithful.of_comp _ (forget AddCommGroupCat), fun h => faithful.comp _ _⟩
#align
  category_theory.is_coseparator_iff_faithful_preadditive_yoneda CategoryTheory.is_coseparator_iff_faithful_preadditive_yoneda

theorem is_coseparator_iff_faithful_preadditive_yoneda_obj (G : C) :
    IsCoseparator G ↔ Faithful (preadditiveYonedaObj G) :=
  by
  rw [is_coseparator_iff_faithful_preadditive_yoneda, preadditive_yoneda_obj_2]
  exact ⟨fun h => faithful.of_comp _ (forget₂ _ AddCommGroupCat.{v}), fun h => faithful.comp _ _⟩
#align
  category_theory.is_coseparator_iff_faithful_preadditive_yoneda_obj CategoryTheory.is_coseparator_iff_faithful_preadditive_yoneda_obj

end CategoryTheory

