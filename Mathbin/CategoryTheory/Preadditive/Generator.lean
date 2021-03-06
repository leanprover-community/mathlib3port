/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
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

theorem Preadditive.is_separating_iff (ð¢ : Set C) :
    IsSeparating ð¢ â â â¦X Y : Câ¦ (f : X â¶ Y), (â, â G â ð¢, â (h : G â¶ X), h â« f = 0) â f = 0 :=
  â¨fun hð¢ X Y f hf =>
    hð¢ _ _
      (by
        simpa only [â limits.comp_zero] using hf),
    fun hð¢ X Y f g hfg =>
    sub_eq_zero.1 <|
      hð¢ _
        (by
          simpa only [â preadditive.comp_sub, â sub_eq_zero] using hfg)â©

theorem Preadditive.is_coseparating_iff (ð¢ : Set C) :
    IsCoseparating ð¢ â â â¦X Y : Câ¦ (f : X â¶ Y), (â, â G â ð¢, â (h : Y â¶ G), f â« h = 0) â f = 0 :=
  â¨fun hð¢ X Y f hf =>
    hð¢ _ _
      (by
        simpa only [â limits.zero_comp] using hf),
    fun hð¢ X Y f g hfg =>
    sub_eq_zero.1 <|
      hð¢ _
        (by
          simpa only [â preadditive.sub_comp, â sub_eq_zero] using hfg)â©

theorem Preadditive.is_separator_iff (G : C) :
    IsSeparator G â â â¦X Y : Câ¦ (f : X â¶ Y), (â h : G â¶ X, h â« f = 0) â f = 0 :=
  â¨fun hG X Y f hf =>
    hG.def _ _
      (by
        simpa only [â limits.comp_zero] using hf),
    fun hG =>
    (is_separator_def _).2 fun X Y f g hfg =>
      sub_eq_zero.1 <|
        hG _
          (by
            simpa only [â preadditive.comp_sub, â sub_eq_zero] using hfg)â©

theorem Preadditive.is_coseparator_iff (G : C) :
    IsCoseparator G â â â¦X Y : Câ¦ (f : X â¶ Y), (â h : Y â¶ G, f â« h = 0) â f = 0 :=
  â¨fun hG X Y f hf =>
    hG.def _ _
      (by
        simpa only [â limits.zero_comp] using hf),
    fun hG =>
    (is_coseparator_def _).2 fun X Y f g hfg =>
      sub_eq_zero.1 <|
        hG _
          (by
            simpa only [â preadditive.sub_comp, â sub_eq_zero] using hfg)â©

theorem is_separator_iff_faithful_preadditive_coyoneda (G : C) :
    IsSeparator G â Faithful (preadditiveCoyoneda.obj (op G)) := by
  rw [is_separator_iff_faithful_coyoneda_obj, â whiskering_preadditive_coyoneda, functor.comp_obj,
    whiskering_right_obj_obj]
  exact â¨fun h => faithful.of_comp _ (forget AddCommGroupââ), fun h => faithful.comp _ _â©

theorem is_separator_iff_faithful_preadditive_coyoneda_obj (G : C) :
    IsSeparator G â Faithful (preadditiveCoyonedaObj (op G)) := by
  rw [is_separator_iff_faithful_preadditive_coyoneda, preadditive_coyoneda_obj_2]
  exact â¨fun h => faithful.of_comp _ (forgetâ _ AddCommGroupââ.{v}), fun h => faithful.comp _ _â©

theorem is_coseparator_iff_faithful_preadditive_yoneda (G : C) : IsCoseparator G â Faithful (preadditiveYoneda.obj G) :=
  by
  rw [is_coseparator_iff_faithful_yoneda_obj, â whiskering_preadditive_yoneda, functor.comp_obj,
    whiskering_right_obj_obj]
  exact â¨fun h => faithful.of_comp _ (forget AddCommGroupââ), fun h => faithful.comp _ _â©

theorem is_coseparator_iff_faithful_preadditive_yoneda_obj (G : C) :
    IsCoseparator G â Faithful (preadditiveYonedaObj G) := by
  rw [is_coseparator_iff_faithful_preadditive_yoneda, preadditive_yoneda_obj_2]
  exact â¨fun h => faithful.of_comp _ (forgetâ _ AddCommGroupââ.{v}), fun h => faithful.comp _ _â©

end CategoryTheory

