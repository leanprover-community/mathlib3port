import Mathbin.CategoryTheory.Sites.Sheaf

/-!

In this file we construct the functor `Sheaf J A ⥤ Sheaf J B` between sheaf categories
obtained by composition with a functor `F : A ⥤ B`.

In order for the sheaf condition to be preserved, `F` must preserve the correct limits.
The lemma `presheaf.is_sheaf.comp` says that composition with such an `F` indeed preserves the
sheaf condition.

The functor between sheaf categories is called `Sheaf_compose J F`.
Given a natural transformation `η : F ⟶ G`, we obtain a natural transformation
`Sheaf_compose J F ⟶ Sheaf_compose J G`, which we call `Sheaf_compose_map J η`.

-/


namespace CategoryTheory

open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂ u₃

variable {C : Type u₁} [category.{v₁} C]

variable {A : Type u₂} [category.{max v₁ u₁} A]

variable {B : Type u₃} [category.{max v₁ u₁} B]

variable {J : grothendieck_topology C}

variable {U : C} (R : presieve U)

variable (F : A ⥤ B)

namespace GrothendieckTopology.Cover

variable (P : «expr ᵒᵖ» C ⥤ A) {X : C} (S : J.cover X)

/-- The multicospan associated to a cover `S : J.cover X` and a presheaf of the form `P ⋙ F`
is isomorphic to the composition of the multicospan associated to `S` and `P`,
composed with `F`. -/
def multicospan_comp : (S.index (P ⋙ F)).multicospan ≅ (S.index P).multicospan ⋙ F :=
  nat_iso.of_components
    (fun t =>
      match t with 
      | walking_multicospan.left a => eq_to_iso rfl
      | walking_multicospan.right b => eq_to_iso rfl)
    (by 
      rintro (a | b) (a | b) (f | f | f)
      any_goals 
        dsimp 
        erw [Functor.map_id, Functor.map_id, category.id_comp]
      any_goals 
        dsimp 
        erw [category.comp_id, category.id_comp]
        rfl)

@[simp]
theorem multicospan_comp_app_left a : (S.multicospan_comp F P).app (walking_multicospan.left a) = eq_to_iso rfl :=
  rfl

@[simp]
theorem multicospan_comp_app_right b : (S.multicospan_comp F P).app (walking_multicospan.right b) = eq_to_iso rfl :=
  rfl

@[simp]
theorem multicospan_comp_hom_app_left a :
  (S.multicospan_comp F P).Hom.app (walking_multicospan.left a) = eq_to_hom rfl :=
  rfl

@[simp]
theorem multicospan_comp_hom_app_right b :
  (S.multicospan_comp F P).Hom.app (walking_multicospan.right b) = eq_to_hom rfl :=
  rfl

/-- Mapping the multifork associated to a cover `S : J.cover X` and a presheaf `P` with
respect to a functor `F` is isomorphic (upto a natural isomorphism of the underlying functors)
to the multifork associated to `S` and `P ⋙ F`. -/
def map_multifork :
  F.map_cone (S.multifork P) ≅ (limits.cones.postcompose (S.multicospan_comp F P).Hom).obj (S.multifork (P ⋙ F)) :=
  cones.ext (eq_to_iso rfl)
    (by 
      rintro (a | b)
      ·
        dsimp 
        simpa
      ·
        dsimp 
        simp 
        dsimp [multifork.of_ι]
        simpa)

end GrothendieckTopology.Cover

variable [∀ X : C S : J.cover X P : «expr ᵒᵖ» C ⥤ A, preserves_limit (S.index P).multicospan F]

theorem presheaf.is_sheaf.comp {P : «expr ᵒᵖ» C ⥤ A} (hP : presheaf.is_sheaf J P) : presheaf.is_sheaf J (P ⋙ F) :=
  by 
    rw [presheaf.is_sheaf_iff_multifork] at hP⊢
    intro X S 
    obtain ⟨h⟩ := hP X S 
    replace h := is_limit_of_preserves F h 
    replace h := limits.is_limit.of_iso_limit h (S.map_multifork F P)
    exact ⟨limits.is_limit.postcompose_hom_equiv (S.multicospan_comp F P) _ h⟩

variable (J)

/-- Composing a sheaf with a functor preserving the appropriate limits yields a functor
between sheaf categories. -/
def Sheaf_compose : Sheaf J A ⥤ Sheaf J B :=
  { obj := fun G => ⟨G.1 ⋙ F, presheaf.is_sheaf.comp _ G.2⟩, map := fun G H η => whisker_right η _,
    map_id' := fun G => whisker_right_id _, map_comp' := fun G H W f g => whisker_right_comp _ _ _ }

@[simp]
theorem Sheaf_compose_obj_to_presheaf (G : Sheaf J A) :
  (Sheaf_to_presheaf J B).obj ((Sheaf_compose J F).obj G) = (Sheaf_to_presheaf J A).obj G ⋙ F :=
  rfl

@[simp]
theorem Sheaf_compose_map_to_presheaf {G H : Sheaf J A} (η : G ⟶ H) :
  (Sheaf_to_presheaf J B).map ((Sheaf_compose J F).map η) = whisker_right ((Sheaf_to_presheaf J A).map η) F :=
  rfl

@[simp]
theorem Sheaf_compose_map_app {G H : Sheaf J A} (η : G ⟶ H) X :
  ((Sheaf_compose J F).map η).app X = F.map (((Sheaf_to_presheaf J A).map η).app X) :=
  rfl

/-- A natural transformation induces a natural transformation between the associated
functors between sheaf categories. -/
def Sheaf_compose_map {F G : A ⥤ B}
  [∀ X : C S : J.cover X P : «expr ᵒᵖ» C ⥤ A, preserves_limit (S.index P).multicospan F]
  [∀ X : C S : J.cover X P : «expr ᵒᵖ» C ⥤ A, preserves_limit (S.index P).multicospan G] (η : F ⟶ G) :
  Sheaf_compose J F ⟶ Sheaf_compose J G :=
  { app := fun X => whisker_left _ η,
    naturality' :=
      fun X Y f =>
        by 
          ext 
          apply η.naturality }

@[simp]
theorem Sheaf_compose_map_app_app {F G : A ⥤ B}
  [∀ X : C S : J.cover X P : «expr ᵒᵖ» C ⥤ A, preserves_limit (S.index P).multicospan F]
  [∀ X : C S : J.cover X P : «expr ᵒᵖ» C ⥤ A, preserves_limit (S.index P).multicospan G] (η : F ⟶ G) X Y :
  ((Sheaf_compose_map J η).app X).app Y = η.app (((Sheaf_to_presheaf J A).obj X).obj Y) :=
  rfl

@[simp]
theorem Sheaf_compose_map_id {F : A ⥤ B}
  [∀ X : C S : J.cover X P : «expr ᵒᵖ» C ⥤ A, preserves_limit (S.index P).multicospan F] :
  Sheaf_compose_map J (𝟙 F) = 𝟙 (Sheaf_compose J F) :=
  rfl

@[simp]
theorem Sheaf_compose_map_comp {F G H : A ⥤ B}
  [∀ X : C S : J.cover X P : «expr ᵒᵖ» C ⥤ A, preserves_limit (S.index P).multicospan F]
  [∀ X : C S : J.cover X P : «expr ᵒᵖ» C ⥤ A, preserves_limit (S.index P).multicospan G]
  [∀ X : C S : J.cover X P : «expr ᵒᵖ» C ⥤ A, preserves_limit (S.index P).multicospan H] (η : F ⟶ G) (γ : G ⟶ H) :
  Sheaf_compose_map J (η ≫ γ) = Sheaf_compose_map J η ≫ Sheaf_compose_map J γ :=
  rfl

end CategoryTheory

