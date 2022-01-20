import Mathbin.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!

# Limits and the category of (co)cones

This files contains results that stem from the limit API. For the definition and the category
instance of `cone`, please refer to `category_theory/limits/cones.lean`.

A cone is limiting iff it is terminal in the category of cones. As a corollary, an equivalence of
categories of cones preserves limiting properties. We also provide the dual.

-/


namespace CategoryTheory.Limits

open CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {J : Type u₁} [category.{v₁} J] {K : Type u₂} [category.{v₂} K]

variable {C : Type u₃} [category.{v₃} C] {D : Type u₄} [category.{v₄} D]

/-- A cone is a limit cone iff it is terminal. -/
def cone.is_limit_equiv_is_terminal {F : J ⥤ C} (c : cone F) : is_limit c ≃ is_terminal c :=
  is_limit.iso_unique_cone_morphism.toEquiv.trans
    { toFun := fun h => is_terminal.of_unique _,
      invFun := fun h s => ⟨⟨is_terminal.from h s⟩, fun a => is_terminal.hom_ext h a _⟩,
      left_inv := by
        tidy,
      right_inv := by
        tidy }

theorem is_limit.lift_cone_morphism_eq_is_terminal_from {F : J ⥤ C} {c : cone F} (hc : is_limit c) (s : cone F) :
    hc.lift_cone_morphism s = is_terminal.from (cone.is_limit_equiv_is_terminal _ hc) _ :=
  rfl

theorem is_terminal.from_eq_lift_cone_morphism {F : J ⥤ C} {c : cone F} (hc : is_terminal c) (s : cone F) :
    is_terminal.from hc s = ((cone.is_limit_equiv_is_terminal _).symm hc).liftConeMorphism s := by
  convert (is_limit.lift_cone_morphism_eq_is_terminal_from _ s).symm

/-- If `G : cone F ⥤ cone F'` preserves terminal objects, it preserves limit cones. -/
def is_limit.of_preserves_cone_terminal {F : J ⥤ C} {F' : K ⥤ D} (G : cone F ⥤ cone F')
    [preserves_limit (functor.empty.{v₃} _) G] {c : cone F} (hc : is_limit c) : is_limit (G.obj c) :=
  (cone.is_limit_equiv_is_terminal _).symm $ (cone.is_limit_equiv_is_terminal _ hc).isTerminalObj _ _

/-- If `G : cone F ⥤ cone F'` reflects terminal objects, it reflects limit cones. -/
def is_limit.of_reflects_cone_terminal {F : J ⥤ C} {F' : K ⥤ D} (G : cone F ⥤ cone F')
    [reflects_limit (functor.empty.{v₃} _) G] {c : cone F} (hc : is_limit (G.obj c)) : is_limit c :=
  (cone.is_limit_equiv_is_terminal _).symm $ (cone.is_limit_equiv_is_terminal _ hc).isTerminalOfObj _ _

/-- A cocone is a colimit cocone iff it is initial. -/
def cocone.is_colimit_equiv_is_initial {F : J ⥤ C} (c : cocone F) : is_colimit c ≃ is_initial c :=
  is_colimit.iso_unique_cocone_morphism.toEquiv.trans
    { toFun := fun h => is_initial.of_unique _,
      invFun := fun h s => ⟨⟨is_initial.to h s⟩, fun a => is_initial.hom_ext h a _⟩,
      left_inv := by
        tidy,
      right_inv := by
        tidy }

theorem is_colimit.desc_cocone_morphism_eq_is_initial_to {F : J ⥤ C} {c : cocone F} (hc : is_colimit c) (s : cocone F) :
    hc.desc_cocone_morphism s = is_initial.to (cocone.is_colimit_equiv_is_initial _ hc) _ :=
  rfl

theorem is_initial.to_eq_desc_cocone_morphism {F : J ⥤ C} {c : cocone F} (hc : is_initial c) (s : cocone F) :
    is_initial.to hc s = ((cocone.is_colimit_equiv_is_initial _).symm hc).descCoconeMorphism s := by
  convert (is_colimit.desc_cocone_morphism_eq_is_initial_to _ s).symm

/-- If `G : cocone F ⥤ cocone F'` preserves initial objects, it preserves colimit cocones. -/
def is_colimit.of_preserves_cocone_initial {F : J ⥤ C} {F' : K ⥤ D} (G : cocone F ⥤ cocone F')
    [preserves_colimit (functor.empty.{v₃} _) G] {c : cocone F} (hc : is_colimit c) : is_colimit (G.obj c) :=
  (cocone.is_colimit_equiv_is_initial _).symm $ (cocone.is_colimit_equiv_is_initial _ hc).isInitialObj _ _

/-- If `G : cocone F ⥤ cocone F'` reflects initial objects, it reflects colimit cocones. -/
def is_colimit.of_reflects_cocone_initial {F : J ⥤ C} {F' : K ⥤ D} (G : cocone F ⥤ cocone F')
    [reflects_colimit (functor.empty.{v₃} _) G] {c : cocone F} (hc : is_colimit (G.obj c)) : is_colimit c :=
  (cocone.is_colimit_equiv_is_initial _).symm $ (cocone.is_colimit_equiv_is_initial _ hc).isInitialOfObj _ _

end CategoryTheory.Limits

