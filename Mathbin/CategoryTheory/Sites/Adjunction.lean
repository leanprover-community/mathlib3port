/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import CategoryTheory.Adjunction.Whiskering
import CategoryTheory.Sites.ConcreteSheafification
import CategoryTheory.Sites.Whiskering

#align_import category_theory.sites.adjunction from "leanprover-community/mathlib"@"f2b757fc5c341d88741b9c4630b1e8ba973c5726"

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
  [∀ X : C, PreservesColimitsOfShape (J.cover X)ᵒᵖ (forget D)]
  [CategoryTheory.Functor.ReflectsIsomorphisms (forget D)]

namespace Sheaf

noncomputable section

#print CategoryTheory.Sheaf.composeAndSheafify /-
/-- This is the functor sending a sheaf `X : Sheaf J E` to the sheafification
of `X ⋙ G`. -/
abbrev composeAndSheafify (G : E ⥤ D) : Sheaf J E ⥤ Sheaf J D :=
  sheafToPresheaf J E ⋙ (whiskeringRight _ _ _).obj G ⋙ plusPlusSheaf J D
#align category_theory.Sheaf.compose_and_sheafify CategoryTheory.Sheaf.composeAndSheafify
-/

#print CategoryTheory.Sheaf.composeEquiv /-
/-- An auxiliary definition to be used in defining `category_theory.Sheaf.adjunction` below. -/
@[simps]
def composeEquiv (adj : G ⊣ F) (X : Sheaf J E) (Y : Sheaf J D) :
    ((composeAndSheafify J G).obj X ⟶ Y) ≃ (X ⟶ (sheafCompose J F).obj Y) :=
  let A := MonCat.adj.whiskerRight Cᵒᵖ
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
-/

#print CategoryTheory.Sheaf.adjunction /-
/-- An adjunction `adj : G ⊣ F` with `F : D ⥤ E` and `G : E ⥤ D` induces an adjunction
between `Sheaf J D` and `Sheaf J E`, in contexts where one can sheafify `D`-valued presheaves,
and `F` preserves the correct limits. -/
@[simps unit_app_val counit_app_val]
def adjunction (adj : G ⊣ F) : composeAndSheafify J G ⊣ sheafCompose J F :=
  Adjunction.mkOfHomEquiv
    { homEquiv := composeEquiv J MonCat.adj
      homEquiv_naturality_left_symm := fun X' X Y f g => by ext1; dsimp; simp
      homEquiv_naturality_right := fun X Y Y' f g => by ext1; dsimp; simp }
#align category_theory.Sheaf.adjunction CategoryTheory.Sheaf.adjunction
-/

instance [CategoryTheory.Functor.IsRightAdjoint F] :
    CategoryTheory.Functor.IsRightAdjoint (sheafCompose J F) :=
  ⟨_, adjunction J (Adjunction.ofIsRightAdjoint F)⟩

section ForgetToType

#print CategoryTheory.Sheaf.composeAndSheafifyFromTypes /-
/-- This is the functor sending a sheaf of types `X` to the sheafification of `X ⋙ G`. -/
abbrev composeAndSheafifyFromTypes (G : Type max v u ⥤ D) : SheafOfTypes J ⥤ Sheaf J D :=
  (sheafEquivSheafOfTypes J).inverse ⋙ composeAndSheafify _ G
#align category_theory.Sheaf.compose_and_sheafify_from_types CategoryTheory.Sheaf.composeAndSheafifyFromTypes
-/

#print CategoryTheory.Sheaf.adjunctionToTypes /-
/-- A variant of the adjunction between sheaf categories, in the case where the right adjoint
is the forgetful functor to sheaves of types. -/
def adjunctionToTypes {G : Type max v u ⥤ D} (adj : G ⊣ forget D) :
    composeAndSheafifyFromTypes J G ⊣ sheafForget J :=
  (sheafEquivSheafOfTypes J).symm.toAdjunction.comp (adjunction J MonCat.adj)
#align category_theory.Sheaf.adjunction_to_types CategoryTheory.Sheaf.adjunctionToTypes
-/

#print CategoryTheory.Sheaf.adjunctionToTypes_unit_app_val /-
@[simp]
theorem adjunctionToTypes_unit_app_val {G : Type max v u ⥤ D} (adj : G ⊣ forget D)
    (Y : SheafOfTypes J) :
    ((adjunctionToTypes J MonCat.adj).Unit.app Y).val =
      (MonCat.adj.whiskerRight _).Unit.app ((sheafOfTypesToPresheaf J).obj Y) ≫
        whiskerRight (J.toSheafify _) (forget D) :=
  by
  dsimp [adjunction_to_types, adjunction.comp]
  simpa
#align category_theory.Sheaf.adjunction_to_types_unit_app_val CategoryTheory.Sheaf.adjunctionToTypes_unit_app_val
-/

#print CategoryTheory.Sheaf.adjunctionToTypes_counit_app_val /-
@[simp]
theorem adjunctionToTypes_counit_app_val {G : Type max v u ⥤ D} (adj : G ⊣ forget D)
    (X : Sheaf J D) :
    ((adjunctionToTypes J MonCat.adj).counit.app X).val =
      J.sheafifyLift ((Functor.associator _ _ _).Hom ≫ (MonCat.adj.whiskerRight _).counit.app _)
        X.2 :=
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
-/

instance [CategoryTheory.Functor.IsRightAdjoint (forget D)] :
    CategoryTheory.Functor.IsRightAdjoint (sheafForget J) :=
  ⟨_, adjunctionToTypes J (Adjunction.ofIsRightAdjoint (forget D))⟩

end ForgetToType

end Sheaf

end CategoryTheory

