/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Scott Morrison

! This file was ported from Lean 3 source module category_theory.products.bifunctor
! leanprover-community/mathlib commit 1ead22342e1a078bd44744ace999f85756555d35
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Products.Basic

/-!
# Lemmas about functors out of product categories.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


open CategoryTheory

namespace CategoryTheory.Bifunctor

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} {D : Type u₂} {E : Type u₃}

variable [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]

/- warning: category_theory.bifunctor.map_id -> CategoryTheory.Bifunctor.map_id is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u4}} {D : Type.{u5}} {E : Type.{u6}} [_inst_1 : CategoryTheory.Category.{u1, u4} C] [_inst_2 : CategoryTheory.Category.{u2, u5} D] [_inst_3 : CategoryTheory.Category.{u3, u6} E] (F : CategoryTheory.Functor.{max u1 u2, u3, max u4 u5, u6} (Prod.{u4, u5} C D) (CategoryTheory.prod.{u1, u2, u4, u5} C _inst_1 D _inst_2) E _inst_3) (X : C) (Y : D), Eq.{succ u3} (Quiver.Hom.{succ u3, u6} E (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} E (CategoryTheory.Category.toCategoryStruct.{u3, u6} E _inst_3)) (CategoryTheory.Functor.obj.{max u1 u2, u3, max u4 u5, u6} (Prod.{u4, u5} C D) (CategoryTheory.prod.{u1, u2, u4, u5} C _inst_1 D _inst_2) E _inst_3 F (Prod.mk.{u4, u5} C D X Y)) (CategoryTheory.Functor.obj.{max u1 u2, u3, max u4 u5, u6} (Prod.{u4, u5} C D) (CategoryTheory.prod.{u1, u2, u4, u5} C _inst_1 D _inst_2) E _inst_3 F (Prod.mk.{u4, u5} C D X Y))) (CategoryTheory.Functor.map.{max u1 u2, u3, max u4 u5, u6} (Prod.{u4, u5} C D) (CategoryTheory.prod.{u1, u2, u4, u5} C _inst_1 D _inst_2) E _inst_3 F (Prod.mk.{u4, u5} C D X Y) (Prod.mk.{u4, u5} C D X Y) (Prod.mk.{u1, u2} (Quiver.Hom.{succ u1, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} C (CategoryTheory.Category.toCategoryStruct.{u1, u4} C _inst_1)) (Prod.fst.{u4, u5} C D (Prod.mk.{u4, u5} C D X Y)) (Prod.fst.{u4, u5} C D (Prod.mk.{u4, u5} C D X Y))) (Quiver.Hom.{succ u2, u5} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u5} D (CategoryTheory.Category.toCategoryStruct.{u2, u5} D _inst_2)) (Prod.snd.{u4, u5} C D (Prod.mk.{u4, u5} C D X Y)) (Prod.snd.{u4, u5} C D (Prod.mk.{u4, u5} C D X Y))) (CategoryTheory.CategoryStruct.id.{u1, u4} C (CategoryTheory.Category.toCategoryStruct.{u1, u4} C _inst_1) X) (CategoryTheory.CategoryStruct.id.{u2, u5} D (CategoryTheory.Category.toCategoryStruct.{u2, u5} D _inst_2) Y))) (CategoryTheory.CategoryStruct.id.{u3, u6} E (CategoryTheory.Category.toCategoryStruct.{u3, u6} E _inst_3) (CategoryTheory.Functor.obj.{max u1 u2, u3, max u4 u5, u6} (Prod.{u4, u5} C D) (CategoryTheory.prod.{u1, u2, u4, u5} C _inst_1 D _inst_2) E _inst_3 F (Prod.mk.{u4, u5} C D X Y)))
but is expected to have type
  forall {C : Type.{u4}} {D : Type.{u5}} {E : Type.{u6}} [_inst_1 : CategoryTheory.Category.{u1, u4} C] [_inst_2 : CategoryTheory.Category.{u2, u5} D] [_inst_3 : CategoryTheory.Category.{u3, u6} E] (F : CategoryTheory.Functor.{max u1 u2, u3, max u5 u4, u6} (Prod.{u4, u5} C D) (CategoryTheory.prod.{u1, u2, u4, u5} C _inst_1 D _inst_2) E _inst_3) (X : C) (Y : D), Eq.{succ u3} (Quiver.Hom.{succ u3, u6} E (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} E (CategoryTheory.Category.toCategoryStruct.{u3, u6} E _inst_3)) (Prefunctor.obj.{max (succ u1) (succ u2), succ u3, max u4 u5, u6} (Prod.{u4, u5} C D) (CategoryTheory.CategoryStruct.toQuiver.{max u1 u2, max u4 u5} (Prod.{u4, u5} C D) (CategoryTheory.Category.toCategoryStruct.{max u1 u2, max u4 u5} (Prod.{u4, u5} C D) (CategoryTheory.prod.{u1, u2, u4, u5} C _inst_1 D _inst_2))) E (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} E (CategoryTheory.Category.toCategoryStruct.{u3, u6} E _inst_3)) (CategoryTheory.Functor.toPrefunctor.{max u1 u2, u3, max u4 u5, u6} (Prod.{u4, u5} C D) (CategoryTheory.prod.{u1, u2, u4, u5} C _inst_1 D _inst_2) E _inst_3 F) (Prod.mk.{u4, u5} C D X Y)) (Prefunctor.obj.{max (succ u1) (succ u2), succ u3, max u4 u5, u6} (Prod.{u4, u5} C D) (CategoryTheory.CategoryStruct.toQuiver.{max u1 u2, max u4 u5} (Prod.{u4, u5} C D) (CategoryTheory.Category.toCategoryStruct.{max u1 u2, max u4 u5} (Prod.{u4, u5} C D) (CategoryTheory.prod.{u1, u2, u4, u5} C _inst_1 D _inst_2))) E (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} E (CategoryTheory.Category.toCategoryStruct.{u3, u6} E _inst_3)) (CategoryTheory.Functor.toPrefunctor.{max u1 u2, u3, max u4 u5, u6} (Prod.{u4, u5} C D) (CategoryTheory.prod.{u1, u2, u4, u5} C _inst_1 D _inst_2) E _inst_3 F) (Prod.mk.{u4, u5} C D X Y))) (Prefunctor.map.{max (succ u1) (succ u2), succ u3, max u4 u5, u6} (Prod.{u4, u5} C D) (CategoryTheory.CategoryStruct.toQuiver.{max u1 u2, max u4 u5} (Prod.{u4, u5} C D) (CategoryTheory.Category.toCategoryStruct.{max u1 u2, max u4 u5} (Prod.{u4, u5} C D) (CategoryTheory.prod.{u1, u2, u4, u5} C _inst_1 D _inst_2))) E (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} E (CategoryTheory.Category.toCategoryStruct.{u3, u6} E _inst_3)) (CategoryTheory.Functor.toPrefunctor.{max u1 u2, u3, max u4 u5, u6} (Prod.{u4, u5} C D) (CategoryTheory.prod.{u1, u2, u4, u5} C _inst_1 D _inst_2) E _inst_3 F) (Prod.mk.{u4, u5} C D X Y) (Prod.mk.{u4, u5} C D X Y) (Prod.mk.{u1, u2} (Quiver.Hom.{succ u1, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} C (CategoryTheory.Category.toCategoryStruct.{u1, u4} C _inst_1)) (Prod.fst.{u4, u5} C D (Prod.mk.{u4, u5} C D X Y)) (Prod.fst.{u4, u5} C D (Prod.mk.{u4, u5} C D X Y))) (Quiver.Hom.{succ u2, u5} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u5} D (CategoryTheory.Category.toCategoryStruct.{u2, u5} D _inst_2)) (Prod.snd.{u4, u5} C D (Prod.mk.{u4, u5} C D X Y)) (Prod.snd.{u4, u5} C D (Prod.mk.{u4, u5} C D X Y))) (CategoryTheory.CategoryStruct.id.{u1, u4} C (CategoryTheory.Category.toCategoryStruct.{u1, u4} C _inst_1) X) (CategoryTheory.CategoryStruct.id.{u2, u5} D (CategoryTheory.Category.toCategoryStruct.{u2, u5} D _inst_2) Y))) (CategoryTheory.CategoryStruct.id.{u3, u6} E (CategoryTheory.Category.toCategoryStruct.{u3, u6} E _inst_3) (Prefunctor.obj.{max (succ u1) (succ u2), succ u3, max u4 u5, u6} (Prod.{u4, u5} C D) (CategoryTheory.CategoryStruct.toQuiver.{max u1 u2, max u4 u5} (Prod.{u4, u5} C D) (CategoryTheory.Category.toCategoryStruct.{max u1 u2, max u4 u5} (Prod.{u4, u5} C D) (CategoryTheory.prod.{u1, u2, u4, u5} C _inst_1 D _inst_2))) E (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} E (CategoryTheory.Category.toCategoryStruct.{u3, u6} E _inst_3)) (CategoryTheory.Functor.toPrefunctor.{max u1 u2, u3, max u4 u5, u6} (Prod.{u4, u5} C D) (CategoryTheory.prod.{u1, u2, u4, u5} C _inst_1 D _inst_2) E _inst_3 F) (Prod.mk.{u4, u5} C D X Y)))
Case conversion may be inaccurate. Consider using '#align category_theory.bifunctor.map_id CategoryTheory.Bifunctor.map_idₓ'. -/
@[simp]
theorem map_id (F : C × D ⥤ E) (X : C) (Y : D) :
    F.map ((𝟙 X, 𝟙 Y) : (X, Y) ⟶ (X, Y)) = 𝟙 (F.obj (X, Y)) :=
  F.map_id (X, Y)
#align category_theory.bifunctor.map_id CategoryTheory.Bifunctor.map_id

/- warning: category_theory.bifunctor.map_id_comp -> CategoryTheory.Bifunctor.map_id_comp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.bifunctor.map_id_comp CategoryTheory.Bifunctor.map_id_compₓ'. -/
@[simp]
theorem map_id_comp (F : C × D ⥤ E) (W : C) {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z) :
    F.map ((𝟙 W, f ≫ g) : (W, X) ⟶ (W, Z)) =
      F.map ((𝟙 W, f) : (W, X) ⟶ (W, Y)) ≫ F.map ((𝟙 W, g) : (W, Y) ⟶ (W, Z)) :=
  by rw [← functor.map_comp, prod_comp, category.comp_id]
#align category_theory.bifunctor.map_id_comp CategoryTheory.Bifunctor.map_id_comp

/- warning: category_theory.bifunctor.map_comp_id -> CategoryTheory.Bifunctor.map_comp_id is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.bifunctor.map_comp_id CategoryTheory.Bifunctor.map_comp_idₓ'. -/
@[simp]
theorem map_comp_id (F : C × D ⥤ E) (X Y Z : C) (W : D) (f : X ⟶ Y) (g : Y ⟶ Z) :
    F.map ((f ≫ g, 𝟙 W) : (X, W) ⟶ (Z, W)) =
      F.map ((f, 𝟙 W) : (X, W) ⟶ (Y, W)) ≫ F.map ((g, 𝟙 W) : (Y, W) ⟶ (Z, W)) :=
  by rw [← functor.map_comp, prod_comp, category.comp_id]
#align category_theory.bifunctor.map_comp_id CategoryTheory.Bifunctor.map_comp_id

/- warning: category_theory.bifunctor.diagonal -> CategoryTheory.Bifunctor.diagonal is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.bifunctor.diagonal CategoryTheory.Bifunctor.diagonalₓ'. -/
@[simp]
theorem diagonal (F : C × D ⥤ E) (X X' : C) (f : X ⟶ X') (Y Y' : D) (g : Y ⟶ Y') :
    F.map ((𝟙 X, g) : (X, Y) ⟶ (X, Y')) ≫ F.map ((f, 𝟙 Y') : (X, Y') ⟶ (X', Y')) =
      F.map ((f, g) : (X, Y) ⟶ (X', Y')) :=
  by rw [← functor.map_comp, prod_comp, category.id_comp, category.comp_id]
#align category_theory.bifunctor.diagonal CategoryTheory.Bifunctor.diagonal

/- warning: category_theory.bifunctor.diagonal' -> CategoryTheory.Bifunctor.diagonal' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.bifunctor.diagonal' CategoryTheory.Bifunctor.diagonal'ₓ'. -/
@[simp]
theorem diagonal' (F : C × D ⥤ E) (X X' : C) (f : X ⟶ X') (Y Y' : D) (g : Y ⟶ Y') :
    F.map ((f, 𝟙 Y) : (X, Y) ⟶ (X', Y)) ≫ F.map ((𝟙 X', g) : (X', Y) ⟶ (X', Y')) =
      F.map ((f, g) : (X, Y) ⟶ (X', Y')) :=
  by rw [← functor.map_comp, prod_comp, category.id_comp, category.comp_id]
#align category_theory.bifunctor.diagonal' CategoryTheory.Bifunctor.diagonal'

end CategoryTheory.Bifunctor

