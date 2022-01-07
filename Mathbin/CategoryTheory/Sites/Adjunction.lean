import Mathbin.CategoryTheory.Sites.CompatibleSheafification
import Mathbin.CategoryTheory.Adjunction.Whiskering

/-!

In this file, we show that an adjunction `F ⊣ G` induces an adjunction between
categories of sheaves, under certain hypotheses on `F` and `G`.

-/


namespace CategoryTheory

open CategoryTheory.GrothendieckTopology

open CategoryTheory

open CategoryTheory.Limits

open Opposite

universe w₁ w₂ v u

variable {C : Type u} [category.{v} C] (J : grothendieck_topology C)

variable {D : Type w₁} [category.{max v u} D]

variable {E : Type w₂} [category.{max v u} E]

variable {F : D ⥤ E} {G : E ⥤ D}

variable [∀ X : C S : J.cover X P : Cᵒᵖ ⥤ D, preserves_limit (S.index P).multicospan F]

variable [concrete_category.{max v u} D] [preserves_limits (forget D)]

/-- The forgetful functor from `Sheaf J D` to sheaves of types, for a concrete category `D`
whose forgetful functor preserves the correct limits. -/
abbrev Sheaf_forget : Sheaf J D ⥤ SheafOfTypes J :=
  Sheaf_compose J (forget D) ⋙ (Sheaf_equiv_SheafOfTypes J).Functor

variable [∀ P : Cᵒᵖ ⥤ D X : C S : J.cover X, has_multiequalizer (S.index P)]
  [∀ X : C, has_colimits_of_shape (J.cover Xᵒᵖ) D] [∀ X : C, preserves_colimits_of_shape (J.cover Xᵒᵖ) (forget D)]
  [reflects_isomorphisms (forget D)]

namespace Sheaf

noncomputable section

/-- This is the functor sending a sheaf `X : Sheaf J E` to the sheafification
of `X ⋙ G`. -/
abbrev compose_and_sheafify (G : E ⥤ D) : Sheaf J E ⥤ Sheaf J D :=
  Sheaf_to_presheaf J E ⋙ (whiskering_right _ _ _).obj G ⋙ presheaf_to_Sheaf J D

/-- An auxiliary definition to be used in defining `category_theory.Sheaf.adjunction` below. -/
@[simps]
def compose_equiv (adj : G ⊣ F) (X : Sheaf J E) (Y : Sheaf J D) :
    ((compose_and_sheafify J G).obj X ⟶ Y) ≃ (X ⟶ (Sheaf_compose J F).obj Y) :=
  let A := adj.whisker_right (Cᵒᵖ)
  { toFun := fun η => ⟨A.hom_equiv _ _ (J.to_sheafify _ ≫ η.val)⟩,
    invFun := fun γ => ⟨J.sheafify_lift ((A.hom_equiv _ _).symm ((Sheaf_to_presheaf _ _).map γ)) Y.2⟩,
    left_inv := by
      intro η
      ext1
      dsimp
      symm
      apply J.sheafify_lift_unique
      rw [Equivₓ.symm_apply_apply],
    right_inv := by
      intro γ
      ext1
      dsimp
      rw [J.to_sheafify_sheafify_lift, Equivₓ.apply_symm_apply] }

/-- An adjunction `adj : G ⊣ F` with `F : D ⥤ E` and `G : E ⥤ D` induces an adjunction
between `Sheaf J D` and `Sheaf J E`, in contexts where one can sheafify `D`-valued presheaves,
and `F` preserves the correct limits. -/
@[simps unit_app_val counit_app_val]
def adjunction (adj : G ⊣ F) : compose_and_sheafify J G ⊣ Sheaf_compose J F :=
  adjunction.mk_of_hom_equiv
    { homEquiv := compose_equiv J adj,
      hom_equiv_naturality_left_symm' := fun X' X Y f g => by
        ext1
        dsimp
        simp ,
      hom_equiv_naturality_right' := fun X Y Y' f g => by
        ext1
        dsimp
        simp }

instance [is_right_adjoint F] : is_right_adjoint (Sheaf_compose J F) :=
  ⟨_, adjunction J (adjunction.of_right_adjoint F)⟩

section ForgetToType

/-- This is the functor sending a sheaf of types `X` to the sheafification of `X ⋙ G`. -/
abbrev compose_and_sheafify_from_types (G : Type max v u ⥤ D) : SheafOfTypes J ⥤ Sheaf J D :=
  (Sheaf_equiv_SheafOfTypes J).inverse ⋙ compose_and_sheafify _ G

/-- A variant of the adjunction between sheaf categories, in the case where the right adjoint
is the forgetful functor to sheaves of types. -/
def adjunction_to_types {G : Type max v u ⥤ D} (adj : G ⊣ forget D) :
    compose_and_sheafify_from_types J G ⊣ Sheaf_forget J :=
  adjunction.comp _ _ (Sheaf_equiv_SheafOfTypes J).symm.toAdjunction (adjunction J adj)

@[simp]
theorem adjunction_to_types_unit_app_val {G : Type max v u ⥤ D} (adj : G ⊣ forget D) (Y : SheafOfTypes J) :
    ((adjunction_to_types J adj).Unit.app Y).val =
      (adj.whisker_right _).Unit.app ((SheafOfTypes_to_presheaf J).obj Y) ≫
        whisker_right (J.to_sheafify _) (forget D) :=
  by
  dsimp [adjunction_to_types, adjunction.comp]
  simpa

@[simp]
theorem adjunction_to_types_counit_app_val {G : Type max v u ⥤ D} (adj : G ⊣ forget D) (X : Sheaf J D) :
    ((adjunction_to_types J adj).counit.app X).val =
      J.sheafify_lift ((functor.associator _ _ _).Hom ≫ (adj.whisker_right _).counit.app _) X.2 :=
  by
  dsimp [adjunction_to_types, adjunction.comp, adjunction.whisker_right]
  rw [category.id_comp]
  apply J.sheafify_lift_unique
  rw [adjunction_counit_app_val, J.sheafify_map_sheafify_lift, J.to_sheafify_sheafify_lift]
  ext
  dsimp [Sheaf_equiv_SheafOfTypes, equivalence.symm, equivalence.to_adjunction, nat_iso.of_components]
  simp

instance [is_right_adjoint (forget D)] : is_right_adjoint (Sheaf_forget J) :=
  ⟨_, adjunction_to_types J (adjunction.of_right_adjoint (forget D))⟩

end ForgetToType

end Sheaf

end CategoryTheory

