/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz

! This file was ported from Lean 3 source module category_theory.sites.adjunction
! leanprover-community/mathlib commit f2b757fc5c341d88741b9c4630b1e8ba973c5726
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Adjunction.Whiskering
import Mathbin.CategoryTheory.Sites.Sheafification
import Mathbin.CategoryTheory.Sites.Whiskering

/-!
> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.


In this file, we show that an adjunction `F ⊣ G` induces an adjunction between
categories of sheaves, under certain hypotheses on `F` and `G`.

-/


namespace CategoryTheory

open CategoryTheory.GrothendieckTopology

open CategoryTheory

open CategoryTheory.Limits

open Opposite

universe w₁ w₂ v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

variable {D : Type w₁} [Category.{max v u} D]

variable {E : Type w₂} [Category.{max v u} E]

variable {F : D ⥤ E} {G : E ⥤ D}

variable [∀ (X : C) (S : J.cover X) (P : Cᵒᵖ ⥤ D), PreservesLimit (S.index P).multicospan F]

variable [ConcreteCategory.{max v u} D] [PreservesLimits (forget D)]

#print CategoryTheory.sheafForget /-
/-- The forgetful functor from `Sheaf J D` to sheaves of types, for a concrete category `D`
whose forgetful functor preserves the correct limits. -/
abbrev sheafForget : Sheaf J D ⥤ SheafOfTypes J :=
  sheafCompose J (forget D) ⋙ (sheafEquivSheafOfTypes J).Functor
#align category_theory.Sheaf_forget CategoryTheory.sheafForget
-/

-- We need to sheafify...
variable [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.cover X), HasMultiequalizer (S.index P)]
  [∀ X : C, HasColimitsOfShape (J.cover X)ᵒᵖ D]
  [∀ X : C, PreservesColimitsOfShape (J.cover X)ᵒᵖ (forget D)] [ReflectsIsomorphisms (forget D)]

namespace Sheaf

noncomputable section

/- warning: category_theory.Sheaf.compose_and_sheafify -> CategoryTheory.Sheaf.composeAndSheafify is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u3, u4} C] (J : CategoryTheory.GrothendieckTopology.{u3, u4} C _inst_1) {D : Type.{u1}} [_inst_2 : CategoryTheory.Category.{max u3 u4, u1} D] {E : Type.{u2}} [_inst_3 : CategoryTheory.Category.{max u3 u4, u2} E] [_inst_5 : CategoryTheory.ConcreteCategory.{max u3 u4, max u3 u4, u1} D _inst_2] [_inst_6 : CategoryTheory.Limits.PreservesLimits.{max u3 u4, max u3 u4, u1, succ (max u3 u4)} D _inst_2 Type.{max u3 u4} CategoryTheory.types.{max u3 u4} (CategoryTheory.forget.{u1, max u3 u4, max u3 u4} D _inst_2 _inst_5)] [_inst_7 : forall (P : CategoryTheory.Functor.{u3, max u3 u4, u4, u1} (Opposite.{succ u4} C) (CategoryTheory.Category.opposite.{u3, u4} C _inst_1) D _inst_2) (X : C) (S : CategoryTheory.GrothendieckTopology.Cover.{u3, u4} C _inst_1 J X), CategoryTheory.Limits.HasMultiequalizer.{max u3 u4, u1, max u4 u3} D _inst_2 (CategoryTheory.GrothendieckTopology.Cover.index.{u1, u3, u4} C _inst_1 X J D _inst_2 S P)] [_inst_8 : forall (X : C), CategoryTheory.Limits.HasColimitsOfShape.{max u4 u3, max u4 u3, max u3 u4, u1} (Opposite.{succ (max u4 u3)} (CategoryTheory.GrothendieckTopology.Cover.{u3, u4} C _inst_1 J X)) (CategoryTheory.Category.opposite.{max u4 u3, max u4 u3} (CategoryTheory.GrothendieckTopology.Cover.{u3, u4} C _inst_1 J X) (Preorder.smallCategory.{max u4 u3} (CategoryTheory.GrothendieckTopology.Cover.{u3, u4} C _inst_1 J X) (CategoryTheory.GrothendieckTopology.Cover.preorder.{u3, u4} C _inst_1 J X))) D _inst_2] [_inst_9 : forall (X : C), CategoryTheory.Limits.PreservesColimitsOfShape.{max u4 u3, max u4 u3, max u3 u4, max u3 u4, u1, succ (max u3 u4)} D _inst_2 Type.{max u3 u4} CategoryTheory.types.{max u3 u4} (Opposite.{succ (max u4 u3)} (CategoryTheory.GrothendieckTopology.Cover.{u3, u4} C _inst_1 J X)) (CategoryTheory.Category.opposite.{max u4 u3, max u4 u3} (CategoryTheory.GrothendieckTopology.Cover.{u3, u4} C _inst_1 J X) (Preorder.smallCategory.{max u4 u3} (CategoryTheory.GrothendieckTopology.Cover.{u3, u4} C _inst_1 J X) (CategoryTheory.GrothendieckTopology.Cover.preorder.{u3, u4} C _inst_1 J X))) (CategoryTheory.forget.{u1, max u3 u4, max u3 u4} D _inst_2 _inst_5)] [_inst_10 : CategoryTheory.ReflectsIsomorphisms.{max u3 u4, max u3 u4, u1, succ (max u3 u4)} D _inst_2 Type.{max u3 u4} CategoryTheory.types.{max u3 u4} (CategoryTheory.forget.{u1, max u3 u4, max u3 u4} D _inst_2 _inst_5)], (CategoryTheory.Functor.{max u3 u4, max u3 u4, u2, u1} E _inst_3 D _inst_2) -> (CategoryTheory.Functor.{max u3 u4, max u3 u4, max u4 u2 u3 u4, max u4 u1 u3 u4} (CategoryTheory.Sheaf.{u3, max u3 u4, u4, u2} C _inst_1 J E _inst_3) (CategoryTheory.Sheaf.CategoryTheory.category.{u3, max u3 u4, u4, u2} C _inst_1 J E _inst_3) (CategoryTheory.Sheaf.{u3, max u3 u4, u4, u1} C _inst_1 J D _inst_2) (CategoryTheory.Sheaf.CategoryTheory.category.{u3, max u3 u4, u4, u1} C _inst_1 J D _inst_2))
but is expected to have type
  forall {C : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u3, u4} C] (J : CategoryTheory.GrothendieckTopology.{u3, u4} C _inst_1) {D : Type.{u1}} [_inst_2 : CategoryTheory.Category.{max u3 u4, u1} D] {E : Type.{u2}} [_inst_3 : CategoryTheory.Category.{max u3 u4, u2} E] [_inst_5 : CategoryTheory.ConcreteCategory.{max u3 u4, max u4 u3, u1} D _inst_2] [_inst_6 : CategoryTheory.Limits.PreservesLimits.{max u4 u3, max u4 u3, u1, max (succ u4) (succ u3)} D _inst_2 Type.{max u4 u3} CategoryTheory.types.{max u4 u3} (CategoryTheory.forget.{u1, max u4 u3, max u4 u3} D _inst_2 _inst_5)] [_inst_7 : forall (P : CategoryTheory.Functor.{u3, max u4 u3, u4, u1} (Opposite.{succ u4} C) (CategoryTheory.Category.opposite.{u3, u4} C _inst_1) D _inst_2) (X : C) (S : CategoryTheory.GrothendieckTopology.Cover.{u3, u4} C _inst_1 J X), CategoryTheory.Limits.HasMultiequalizer.{max u4 u3, u1, max u4 u3} D _inst_2 (CategoryTheory.GrothendieckTopology.Cover.index.{u1, u3, u4} C _inst_1 X J D _inst_2 S P)] [_inst_8 : forall (X : C), CategoryTheory.Limits.HasColimitsOfShape.{max u4 u3, max u4 u3, max u4 u3, u1} (Opposite.{max (succ u4) (succ u3)} (CategoryTheory.GrothendieckTopology.Cover.{u3, u4} C _inst_1 J X)) (CategoryTheory.Category.opposite.{max u4 u3, max u4 u3} (CategoryTheory.GrothendieckTopology.Cover.{u3, u4} C _inst_1 J X) (Preorder.smallCategory.{max u4 u3} (CategoryTheory.GrothendieckTopology.Cover.{u3, u4} C _inst_1 J X) (CategoryTheory.GrothendieckTopology.instPreorderCover.{u3, u4} C _inst_1 J X))) D _inst_2] [_inst_9 : forall (X : C), CategoryTheory.Limits.PreservesColimitsOfShape.{max u4 u3, max u4 u3, max u4 u3, max u4 u3, u1, max (succ u4) (succ u3)} D _inst_2 Type.{max u4 u3} CategoryTheory.types.{max u4 u3} (Opposite.{max (succ u4) (succ u3)} (CategoryTheory.GrothendieckTopology.Cover.{u3, u4} C _inst_1 J X)) (CategoryTheory.Category.opposite.{max u4 u3, max u4 u3} (CategoryTheory.GrothendieckTopology.Cover.{u3, u4} C _inst_1 J X) (Preorder.smallCategory.{max u4 u3} (CategoryTheory.GrothendieckTopology.Cover.{u3, u4} C _inst_1 J X) (CategoryTheory.GrothendieckTopology.instPreorderCover.{u3, u4} C _inst_1 J X))) (CategoryTheory.forget.{u1, max u4 u3, max u4 u3} D _inst_2 _inst_5)] [_inst_10 : CategoryTheory.ReflectsIsomorphisms.{max u4 u3, max u4 u3, u1, max (succ u4) (succ u3)} D _inst_2 Type.{max u4 u3} CategoryTheory.types.{max u4 u3} (CategoryTheory.forget.{u1, max u4 u3, max u4 u3} D _inst_2 _inst_5)], (CategoryTheory.Functor.{max u4 u3, max u4 u3, u2, u1} E _inst_3 D _inst_2) -> (CategoryTheory.Functor.{max u4 u3, max u4 u3, max (max (max u2 u4) u4 u3) u3, max (max (max u1 u4) u4 u3) u3} (CategoryTheory.Sheaf.{u3, max u4 u3, u4, u2} C _inst_1 J E _inst_3) (CategoryTheory.Sheaf.instCategorySheaf.{u3, max u4 u3, u4, u2} C _inst_1 J E _inst_3) (CategoryTheory.Sheaf.{u3, max u4 u3, u4, u1} C _inst_1 J D _inst_2) (CategoryTheory.Sheaf.instCategorySheaf.{u3, max u4 u3, u4, u1} C _inst_1 J D _inst_2))
Case conversion may be inaccurate. Consider using '#align category_theory.Sheaf.compose_and_sheafify CategoryTheory.Sheaf.composeAndSheafifyₓ'. -/
/-- This is the functor sending a sheaf `X : Sheaf J E` to the sheafification
of `X ⋙ G`. -/
abbrev composeAndSheafify (G : E ⥤ D) : Sheaf J E ⥤ Sheaf J D :=
  sheafToPresheaf J E ⋙ (whiskeringRight _ _ _).obj G ⋙ presheafToSheaf J D
#align category_theory.Sheaf.compose_and_sheafify CategoryTheory.Sheaf.composeAndSheafify

/- warning: category_theory.Sheaf.compose_equiv -> CategoryTheory.Sheaf.composeEquiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.Sheaf.compose_equiv CategoryTheory.Sheaf.composeEquivₓ'. -/
/-- An auxiliary definition to be used in defining `category_theory.Sheaf.adjunction` below. -/
@[simps]
def composeEquiv (adj : G ⊣ F) (X : Sheaf J E) (Y : Sheaf J D) :
    ((composeAndSheafify J G).obj X ⟶ Y) ≃ (X ⟶ (sheafCompose J F).obj Y) :=
  let A := adj.whiskerRight Cᵒᵖ
  { toFun := fun η => ⟨A.homEquiv _ _ (J.toSheafify _ ≫ η.val)⟩
    invFun := fun γ => ⟨J.sheafifyLift ((A.homEquiv _ _).symm ((sheafToPresheaf _ _).map γ)) Y.2⟩
    left_inv := by
      intro η
      ext1
      dsimp
      symm
      apply J.sheafify_lift_unique
      rw [Equiv.symm_apply_apply]
    right_inv := by
      intro γ
      ext1
      dsimp
      rw [J.to_sheafify_sheafify_lift, Equiv.apply_symm_apply] }
#align category_theory.Sheaf.compose_equiv CategoryTheory.Sheaf.composeEquiv

/- warning: category_theory.Sheaf.adjunction -> CategoryTheory.Sheaf.adjunction is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.Sheaf.adjunction CategoryTheory.Sheaf.adjunctionₓ'. -/
/-- An adjunction `adj : G ⊣ F` with `F : D ⥤ E` and `G : E ⥤ D` induces an adjunction
between `Sheaf J D` and `Sheaf J E`, in contexts where one can sheafify `D`-valued presheaves,
and `F` preserves the correct limits. -/
@[simps unit_app_val counit_app_val]
def adjunction (adj : G ⊣ F) : composeAndSheafify J G ⊣ sheafCompose J F :=
  Adjunction.mkOfHomEquiv
    { homEquiv := composeEquiv J adj
      homEquiv_naturality_left_symm := fun X' X Y f g => by ext1; dsimp; simp
      homEquiv_naturality_right := fun X Y Y' f g => by ext1; dsimp; simp }
#align category_theory.Sheaf.adjunction CategoryTheory.Sheaf.adjunction

instance [IsRightAdjoint F] : IsRightAdjoint (sheafCompose J F) :=
  ⟨_, adjunction J (Adjunction.ofRightAdjoint F)⟩

section ForgetToType

/- warning: category_theory.Sheaf.compose_and_sheafify_from_types -> CategoryTheory.Sheaf.composeAndSheafifyFromTypes is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] (J : CategoryTheory.GrothendieckTopology.{u2, u3} C _inst_1) {D : Type.{u1}} [_inst_2 : CategoryTheory.Category.{max u2 u3, u1} D] [_inst_5 : CategoryTheory.ConcreteCategory.{max u2 u3, max u2 u3, u1} D _inst_2] [_inst_6 : CategoryTheory.Limits.PreservesLimits.{max u2 u3, max u2 u3, u1, succ (max u2 u3)} D _inst_2 Type.{max u2 u3} CategoryTheory.types.{max u2 u3} (CategoryTheory.forget.{u1, max u2 u3, max u2 u3} D _inst_2 _inst_5)] [_inst_7 : forall (P : CategoryTheory.Functor.{u2, max u2 u3, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) (X : C) (S : CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X), CategoryTheory.Limits.HasMultiequalizer.{max u2 u3, u1, max u3 u2} D _inst_2 (CategoryTheory.GrothendieckTopology.Cover.index.{u1, u2, u3} C _inst_1 X J D _inst_2 S P)] [_inst_8 : forall (X : C), CategoryTheory.Limits.HasColimitsOfShape.{max u3 u2, max u3 u2, max u2 u3, u1} (Opposite.{succ (max u3 u2)} (CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X)) (CategoryTheory.Category.opposite.{max u3 u2, max u3 u2} (CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X) (Preorder.smallCategory.{max u3 u2} (CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X) (CategoryTheory.GrothendieckTopology.Cover.preorder.{u2, u3} C _inst_1 J X))) D _inst_2] [_inst_9 : forall (X : C), CategoryTheory.Limits.PreservesColimitsOfShape.{max u3 u2, max u3 u2, max u2 u3, max u2 u3, u1, succ (max u2 u3)} D _inst_2 Type.{max u2 u3} CategoryTheory.types.{max u2 u3} (Opposite.{succ (max u3 u2)} (CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X)) (CategoryTheory.Category.opposite.{max u3 u2, max u3 u2} (CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X) (Preorder.smallCategory.{max u3 u2} (CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X) (CategoryTheory.GrothendieckTopology.Cover.preorder.{u2, u3} C _inst_1 J X))) (CategoryTheory.forget.{u1, max u2 u3, max u2 u3} D _inst_2 _inst_5)] [_inst_10 : CategoryTheory.ReflectsIsomorphisms.{max u2 u3, max u2 u3, u1, succ (max u2 u3)} D _inst_2 Type.{max u2 u3} CategoryTheory.types.{max u2 u3} (CategoryTheory.forget.{u1, max u2 u3, max u2 u3} D _inst_2 _inst_5)], (CategoryTheory.Functor.{max u2 u3, max u2 u3, succ (max u2 u3), u1} Type.{max u2 u3} CategoryTheory.types.{max u2 u3} D _inst_2) -> (CategoryTheory.Functor.{max u2 u3, max u2 u3, max u3 u2 (succ (max u2 u3)), max u3 u1 u2 u3} (CategoryTheory.SheafOfTypes.{max u2 u3, u2, u3} C _inst_1 J) (CategoryTheory.SheafOfTypes.CategoryTheory.category.{u2, u3, max u2 u3} C _inst_1 J) (CategoryTheory.Sheaf.{u2, max u2 u3, u3, u1} C _inst_1 J D _inst_2) (CategoryTheory.Sheaf.CategoryTheory.category.{u2, max u2 u3, u3, u1} C _inst_1 J D _inst_2))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] (J : CategoryTheory.GrothendieckTopology.{u2, u3} C _inst_1) {D : Type.{u1}} [_inst_2 : CategoryTheory.Category.{max u2 u3, u1} D] [_inst_5 : CategoryTheory.ConcreteCategory.{max u2 u3, max u3 u2, u1} D _inst_2] [_inst_6 : CategoryTheory.Limits.PreservesLimits.{max u3 u2, max u3 u2, u1, max (succ u3) (succ u2)} D _inst_2 Type.{max u3 u2} CategoryTheory.types.{max u3 u2} (CategoryTheory.forget.{u1, max u3 u2, max u3 u2} D _inst_2 _inst_5)] [_inst_7 : forall (P : CategoryTheory.Functor.{u2, max u3 u2, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) (X : C) (S : CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X), CategoryTheory.Limits.HasMultiequalizer.{max u3 u2, u1, max u3 u2} D _inst_2 (CategoryTheory.GrothendieckTopology.Cover.index.{u1, u2, u3} C _inst_1 X J D _inst_2 S P)] [_inst_8 : forall (X : C), CategoryTheory.Limits.HasColimitsOfShape.{max u3 u2, max u3 u2, max u3 u2, u1} (Opposite.{max (succ u3) (succ u2)} (CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X)) (CategoryTheory.Category.opposite.{max u3 u2, max u3 u2} (CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X) (Preorder.smallCategory.{max u3 u2} (CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X) (CategoryTheory.GrothendieckTopology.instPreorderCover.{u2, u3} C _inst_1 J X))) D _inst_2] [_inst_9 : forall (X : C), CategoryTheory.Limits.PreservesColimitsOfShape.{max u3 u2, max u3 u2, max u3 u2, max u3 u2, u1, max (succ u3) (succ u2)} D _inst_2 Type.{max u3 u2} CategoryTheory.types.{max u3 u2} (Opposite.{max (succ u3) (succ u2)} (CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X)) (CategoryTheory.Category.opposite.{max u3 u2, max u3 u2} (CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X) (Preorder.smallCategory.{max u3 u2} (CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X) (CategoryTheory.GrothendieckTopology.instPreorderCover.{u2, u3} C _inst_1 J X))) (CategoryTheory.forget.{u1, max u3 u2, max u3 u2} D _inst_2 _inst_5)] [_inst_10 : CategoryTheory.ReflectsIsomorphisms.{max u3 u2, max u3 u2, u1, max (succ u3) (succ u2)} D _inst_2 Type.{max u3 u2} CategoryTheory.types.{max u3 u2} (CategoryTheory.forget.{u1, max u3 u2, max u3 u2} D _inst_2 _inst_5)], (CategoryTheory.Functor.{max u3 u2, max u3 u2, max (succ u3) (succ u2), u1} Type.{max u2 u3} CategoryTheory.types.{max u3 u2} D _inst_2) -> (CategoryTheory.Functor.{max u3 u2, max u3 u2, succ (max u3 u2), max (max (max u1 u3) u3 u2) u2} (CategoryTheory.SheafOfTypes.{max u3 u2, u2, u3} C _inst_1 J) (CategoryTheory.SheafOfTypes.instCategorySheafOfTypes.{u2, u3, max u3 u2} C _inst_1 J) (CategoryTheory.Sheaf.{u2, max u3 u2, u3, u1} C _inst_1 J D _inst_2) (CategoryTheory.Sheaf.instCategorySheaf.{u2, max u3 u2, u3, u1} C _inst_1 J D _inst_2))
Case conversion may be inaccurate. Consider using '#align category_theory.Sheaf.compose_and_sheafify_from_types CategoryTheory.Sheaf.composeAndSheafifyFromTypesₓ'. -/
/-- This is the functor sending a sheaf of types `X` to the sheafification of `X ⋙ G`. -/
abbrev composeAndSheafifyFromTypes (G : Type max v u ⥤ D) : SheafOfTypes J ⥤ Sheaf J D :=
  (sheafEquivSheafOfTypes J).inverse ⋙ composeAndSheafify _ G
#align category_theory.Sheaf.compose_and_sheafify_from_types CategoryTheory.Sheaf.composeAndSheafifyFromTypes

/- warning: category_theory.Sheaf.adjunction_to_types -> CategoryTheory.Sheaf.adjunctionToTypes is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] (J : CategoryTheory.GrothendieckTopology.{u2, u3} C _inst_1) {D : Type.{u1}} [_inst_2 : CategoryTheory.Category.{max u2 u3, u1} D] [_inst_5 : CategoryTheory.ConcreteCategory.{max u2 u3, max u2 u3, u1} D _inst_2] [_inst_6 : CategoryTheory.Limits.PreservesLimits.{max u2 u3, max u2 u3, u1, succ (max u2 u3)} D _inst_2 Type.{max u2 u3} CategoryTheory.types.{max u2 u3} (CategoryTheory.forget.{u1, max u2 u3, max u2 u3} D _inst_2 _inst_5)] [_inst_7 : forall (P : CategoryTheory.Functor.{u2, max u2 u3, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) (X : C) (S : CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X), CategoryTheory.Limits.HasMultiequalizer.{max u2 u3, u1, max u3 u2} D _inst_2 (CategoryTheory.GrothendieckTopology.Cover.index.{u1, u2, u3} C _inst_1 X J D _inst_2 S P)] [_inst_8 : forall (X : C), CategoryTheory.Limits.HasColimitsOfShape.{max u3 u2, max u3 u2, max u2 u3, u1} (Opposite.{succ (max u3 u2)} (CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X)) (CategoryTheory.Category.opposite.{max u3 u2, max u3 u2} (CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X) (Preorder.smallCategory.{max u3 u2} (CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X) (CategoryTheory.GrothendieckTopology.Cover.preorder.{u2, u3} C _inst_1 J X))) D _inst_2] [_inst_9 : forall (X : C), CategoryTheory.Limits.PreservesColimitsOfShape.{max u3 u2, max u3 u2, max u2 u3, max u2 u3, u1, succ (max u2 u3)} D _inst_2 Type.{max u2 u3} CategoryTheory.types.{max u2 u3} (Opposite.{succ (max u3 u2)} (CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X)) (CategoryTheory.Category.opposite.{max u3 u2, max u3 u2} (CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X) (Preorder.smallCategory.{max u3 u2} (CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X) (CategoryTheory.GrothendieckTopology.Cover.preorder.{u2, u3} C _inst_1 J X))) (CategoryTheory.forget.{u1, max u2 u3, max u2 u3} D _inst_2 _inst_5)] [_inst_10 : CategoryTheory.ReflectsIsomorphisms.{max u2 u3, max u2 u3, u1, succ (max u2 u3)} D _inst_2 Type.{max u2 u3} CategoryTheory.types.{max u2 u3} (CategoryTheory.forget.{u1, max u2 u3, max u2 u3} D _inst_2 _inst_5)] {G : CategoryTheory.Functor.{max u2 u3, max u2 u3, succ (max u2 u3), u1} Type.{max u2 u3} CategoryTheory.types.{max u2 u3} D _inst_2}, (CategoryTheory.Adjunction.{max u2 u3, max u2 u3, succ (max u2 u3), u1} Type.{max u2 u3} CategoryTheory.types.{max u2 u3} D _inst_2 G (CategoryTheory.forget.{u1, max u2 u3, max u2 u3} D _inst_2 _inst_5)) -> (CategoryTheory.Adjunction.{max u2 u3, max u2 u3, max u3 u2 (succ (max u2 u3)), max u3 u1 u2 u3} (CategoryTheory.SheafOfTypes.{max u2 u3, u2, u3} C _inst_1 J) (CategoryTheory.SheafOfTypes.CategoryTheory.category.{u2, u3, max u2 u3} C _inst_1 J) (CategoryTheory.Sheaf.{u2, max u2 u3, u3, u1} C _inst_1 J D _inst_2) (CategoryTheory.Sheaf.CategoryTheory.category.{u2, max u2 u3, u3, u1} C _inst_1 J D _inst_2) (CategoryTheory.Sheaf.composeAndSheafifyFromTypes.{u1, u2, u3} C _inst_1 J D _inst_2 _inst_5 _inst_6 (CategoryTheory.Sheaf.adjunctionToTypes._proof_1.{u3, u2, u1} C _inst_1 J D _inst_2 _inst_7) (CategoryTheory.Sheaf.adjunctionToTypes._proof_2.{u3, u2, u1} C _inst_1 J D _inst_2 _inst_8) (fun (X : C) => _inst_9 X) _inst_10 G) (CategoryTheory.sheafForget.{u1, u2, u3} C _inst_1 J D _inst_2 _inst_5 _inst_6))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] (J : CategoryTheory.GrothendieckTopology.{u2, u3} C _inst_1) {D : Type.{u1}} [_inst_2 : CategoryTheory.Category.{max u2 u3, u1} D] [_inst_5 : CategoryTheory.ConcreteCategory.{max u2 u3, max u3 u2, u1} D _inst_2] [_inst_6 : CategoryTheory.Limits.PreservesLimits.{max u3 u2, max u3 u2, u1, max (succ u3) (succ u2)} D _inst_2 Type.{max u3 u2} CategoryTheory.types.{max u3 u2} (CategoryTheory.forget.{u1, max u3 u2, max u3 u2} D _inst_2 _inst_5)] [_inst_7 : forall (P : CategoryTheory.Functor.{u2, max u3 u2, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) (X : C) (S : CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X), CategoryTheory.Limits.HasMultiequalizer.{max u3 u2, u1, max u3 u2} D _inst_2 (CategoryTheory.GrothendieckTopology.Cover.index.{u1, u2, u3} C _inst_1 X J D _inst_2 S P)] [_inst_8 : forall (X : C), CategoryTheory.Limits.HasColimitsOfShape.{max u3 u2, max u3 u2, max u3 u2, u1} (Opposite.{max (succ u3) (succ u2)} (CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X)) (CategoryTheory.Category.opposite.{max u3 u2, max u3 u2} (CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X) (Preorder.smallCategory.{max u3 u2} (CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X) (CategoryTheory.GrothendieckTopology.instPreorderCover.{u2, u3} C _inst_1 J X))) D _inst_2] [_inst_9 : forall (X : C), CategoryTheory.Limits.PreservesColimitsOfShape.{max u3 u2, max u3 u2, max u3 u2, max u3 u2, u1, max (succ u3) (succ u2)} D _inst_2 Type.{max u3 u2} CategoryTheory.types.{max u3 u2} (Opposite.{max (succ u3) (succ u2)} (CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X)) (CategoryTheory.Category.opposite.{max u3 u2, max u3 u2} (CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X) (Preorder.smallCategory.{max u3 u2} (CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X) (CategoryTheory.GrothendieckTopology.instPreorderCover.{u2, u3} C _inst_1 J X))) (CategoryTheory.forget.{u1, max u3 u2, max u3 u2} D _inst_2 _inst_5)] [_inst_10 : CategoryTheory.ReflectsIsomorphisms.{max u3 u2, max u3 u2, u1, max (succ u3) (succ u2)} D _inst_2 Type.{max u3 u2} CategoryTheory.types.{max u3 u2} (CategoryTheory.forget.{u1, max u3 u2, max u3 u2} D _inst_2 _inst_5)] {G : CategoryTheory.Functor.{max u3 u2, max u3 u2, max (succ u3) (succ u2), u1} Type.{max u2 u3} CategoryTheory.types.{max u3 u2} D _inst_2}, (CategoryTheory.Adjunction.{max u3 u2, max u3 u2, max (succ u3) (succ u2), u1} Type.{max u2 u3} CategoryTheory.types.{max u3 u2} D _inst_2 G (CategoryTheory.forget.{u1, max u3 u2, max u3 u2} D _inst_2 _inst_5)) -> (CategoryTheory.Adjunction.{max u3 u2, max u3 u2, max (succ u3) (succ u2), max (max u3 u2) u1} (CategoryTheory.SheafOfTypes.{max u3 u2, u2, u3} C _inst_1 J) (CategoryTheory.SheafOfTypes.instCategorySheafOfTypes.{u2, u3, max u3 u2} C _inst_1 J) (CategoryTheory.Sheaf.{u2, max u3 u2, u3, u1} C _inst_1 J D _inst_2) (CategoryTheory.Sheaf.instCategorySheaf.{u2, max u3 u2, u3, u1} C _inst_1 J D _inst_2) (CategoryTheory.Sheaf.composeAndSheafifyFromTypes.{u1, u2, u3} C _inst_1 J D _inst_2 _inst_5 _inst_6 (fun (P : CategoryTheory.Functor.{u2, max u3 u2, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) (X : C) (S : CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X) => _inst_7 P X S) (fun (X : C) => _inst_8 X) (fun (X : C) => _inst_9 X) _inst_10 G) (CategoryTheory.sheafForget.{u1, u2, u3} C _inst_1 J D _inst_2 _inst_5 _inst_6))
Case conversion may be inaccurate. Consider using '#align category_theory.Sheaf.adjunction_to_types CategoryTheory.Sheaf.adjunctionToTypesₓ'. -/
/-- A variant of the adjunction between sheaf categories, in the case where the right adjoint
is the forgetful functor to sheaves of types. -/
def adjunctionToTypes {G : Type max v u ⥤ D} (adj : G ⊣ forget D) :
    composeAndSheafifyFromTypes J G ⊣ sheafForget J :=
  (sheafEquivSheafOfTypes J).symm.toAdjunction.comp (adjunction J adj)
#align category_theory.Sheaf.adjunction_to_types CategoryTheory.Sheaf.adjunctionToTypes

/- warning: category_theory.Sheaf.adjunction_to_types_unit_app_val -> CategoryTheory.Sheaf.adjunctionToTypes_unit_app_val is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.Sheaf.adjunction_to_types_unit_app_val CategoryTheory.Sheaf.adjunctionToTypes_unit_app_valₓ'. -/
@[simp]
theorem adjunctionToTypes_unit_app_val {G : Type max v u ⥤ D} (adj : G ⊣ forget D)
    (Y : SheafOfTypes J) :
    ((adjunctionToTypes J adj).Unit.app Y).val =
      (adj.whiskerRight _).Unit.app ((sheafOfTypesToPresheaf J).obj Y) ≫
        whiskerRight (J.toSheafify _) (forget D) :=
  by
  dsimp [adjunction_to_types, adjunction.comp]
  simpa
#align category_theory.Sheaf.adjunction_to_types_unit_app_val CategoryTheory.Sheaf.adjunctionToTypes_unit_app_val

/- warning: category_theory.Sheaf.adjunction_to_types_counit_app_val -> CategoryTheory.Sheaf.adjunctionToTypes_counit_app_val is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.Sheaf.adjunction_to_types_counit_app_val CategoryTheory.Sheaf.adjunctionToTypes_counit_app_valₓ'. -/
@[simp]
theorem adjunctionToTypes_counit_app_val {G : Type max v u ⥤ D} (adj : G ⊣ forget D)
    (X : Sheaf J D) :
    ((adjunctionToTypes J adj).counit.app X).val =
      J.sheafifyLift ((Functor.associator _ _ _).Hom ≫ (adj.whiskerRight _).counit.app _) X.2 :=
  by
  dsimp [adjunction_to_types, adjunction.comp, adjunction.whisker_right]
  rw [category.id_comp]
  apply J.sheafify_lift_unique
  rw [adjunction_counit_app_val, J.sheafify_map_sheafify_lift, J.to_sheafify_sheafify_lift]
  ext
  dsimp [Sheaf_equiv_SheafOfTypes, equivalence.symm, equivalence.to_adjunction,
    nat_iso.of_components]
  simp
#align category_theory.Sheaf.adjunction_to_types_counit_app_val CategoryTheory.Sheaf.adjunctionToTypes_counit_app_val

instance [IsRightAdjoint (forget D)] : IsRightAdjoint (sheafForget J) :=
  ⟨_, adjunctionToTypes J (Adjunction.ofRightAdjoint (forget D))⟩

end ForgetToType

end Sheaf

end CategoryTheory

