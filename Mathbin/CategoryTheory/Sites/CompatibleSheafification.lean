import Mathbin.CategoryTheory.Sites.CompatiblePlus

/-!

In this file, we prove that sheafification is compatible with functors which
preserve the correct limits and colimits.

-/


namespace CategoryTheory.GrothendieckTopology

open CategoryTheory

open CategoryTheory.Limits

open Opposite

universe w₁ w₂ v u

variable {C : Type u} [category.{v} C] (J : grothendieck_topology C)

variable {D : Type w₁} [category.{max v u} D]

variable {E : Type w₂} [category.{max v u} E]

variable (F : D ⥤ E)

noncomputable section

variable [∀ α β : Type max v u fst snd : β → α, has_limits_of_shape (walking_multicospan fst snd) D]

variable [∀ α β : Type max v u fst snd : β → α, has_limits_of_shape (walking_multicospan fst snd) E]

variable [∀ X : C, has_colimits_of_shape (J.cover Xᵒᵖ) D]

variable [∀ X : C, has_colimits_of_shape (J.cover Xᵒᵖ) E]

variable [∀ X : C, preserves_colimits_of_shape (J.cover Xᵒᵖ) F]

variable [∀ X : C W : J.cover X P : Cᵒᵖ ⥤ D, preserves_limit (W.index P).multicospan F]

variable (P : Cᵒᵖ ⥤ D)

/-- The isomorphism between the sheafification of `P` composed with `F` and
the sheafification of `P ⋙ F`.

Use the lemmas `whisker_right_to_sheafify_sheafify_comp_iso_hom`,
`to_sheafify_comp_sheafify_comp_iso_inv` and `sheafify_comp_iso_inv_eq_sheafify_lift` to reduce
the components of this isomorphisms to a state that can be handled using the universal property
of sheafification. -/
def sheafify_comp_iso : J.sheafify P ⋙ F ≅ J.sheafify (P ⋙ F) :=
  J.plus_comp_iso _ _ ≪≫ (J.plus_functor _).mapIso (J.plus_comp_iso _ _)

/-- The isomorphism between the sheafification of `P` composed with `F` and
the sheafification of `P ⋙ F`, functorially in `F`. -/
def sheafification_whisker_left_iso (P : Cᵒᵖ ⥤ D) [∀ F : D ⥤ E X : C, preserves_colimits_of_shape (J.cover Xᵒᵖ) F]
    [∀ F : D ⥤ E X : C W : J.cover X P : Cᵒᵖ ⥤ D, preserves_limit (W.index P).multicospan F] :
    (whiskering_left _ _ E).obj (J.sheafify P) ≅ (whiskering_left _ _ _).obj P ⋙ J.sheafification E := by
  refine' J.plus_functor_whisker_left_iso _ ≪≫ _ ≪≫ functor.associator _ _ _
  refine' iso_whisker_right _ _
  refine' J.plus_functor_whisker_left_iso _

@[simp]
theorem sheafification_whisker_left_iso_hom_app (P : Cᵒᵖ ⥤ D) (F : D ⥤ E)
    [∀ F : D ⥤ E X : C, preserves_colimits_of_shape (J.cover Xᵒᵖ) F]
    [∀ F : D ⥤ E X : C W : J.cover X P : Cᵒᵖ ⥤ D, preserves_limit (W.index P).multicospan F] :
    (sheafification_whisker_left_iso J P).Hom.app F = (J.sheafify_comp_iso F P).Hom := by
  dsimp [sheafification_whisker_left_iso, sheafify_comp_iso]
  rw [category.comp_id]

@[simp]
theorem sheafification_whisker_left_iso_inv_app (P : Cᵒᵖ ⥤ D) (F : D ⥤ E)
    [∀ F : D ⥤ E X : C, preserves_colimits_of_shape (J.cover Xᵒᵖ) F]
    [∀ F : D ⥤ E X : C W : J.cover X P : Cᵒᵖ ⥤ D, preserves_limit (W.index P).multicospan F] :
    (sheafification_whisker_left_iso J P).inv.app F = (J.sheafify_comp_iso F P).inv := by
  dsimp [sheafification_whisker_left_iso, sheafify_comp_iso]
  erw [category.id_comp]

/-- The isomorphism between the sheafification of `P` composed with `F` and
the sheafification of `P ⋙ F`, functorially in `P`. -/
def sheafification_whisker_right_iso :
    J.sheafification D ⋙ (whiskering_right _ _ _).obj F ≅ (whiskering_right _ _ _).obj F ⋙ J.sheafification E := by
  refine' functor.associator _ _ _ ≪≫ _
  refine' iso_whisker_left (J.plus_functor D) (J.plus_functor_whisker_right_iso _) ≪≫ _
  refine' _ ≪≫ functor.associator _ _ _
  refine' (functor.associator _ _ _).symm ≪≫ _
  exact iso_whisker_right (J.plus_functor_whisker_right_iso _) (J.plus_functor E)

@[simp]
theorem sheafification_whisker_right_iso_hom_app :
    (J.sheafification_whisker_right_iso F).Hom.app P = (J.sheafify_comp_iso F P).Hom := by
  dsimp [sheafification_whisker_right_iso, sheafify_comp_iso]
  simp only [category.id_comp, category.comp_id]
  erw [category.id_comp]

@[simp]
theorem sheafification_whisker_right_iso_inv_app :
    (J.sheafification_whisker_right_iso F).inv.app P = (J.sheafify_comp_iso F P).inv := by
  dsimp [sheafification_whisker_right_iso, sheafify_comp_iso]
  simp only [category.id_comp, category.comp_id]
  erw [category.id_comp]

@[simp, reassoc]
theorem whisker_right_to_sheafify_sheafify_comp_iso_hom :
    whisker_right (J.to_sheafify _) _ ≫ (J.sheafify_comp_iso F P).Hom = J.to_sheafify _ := by
  dsimp [sheafify_comp_iso]
  erw [whisker_right_comp, category.assoc]
  slice_lhs 2 3 => rw [plus_comp_iso_whisker_right]
  rw [category.assoc, ← J.plus_map_comp, whisker_right_to_plus_comp_plus_comp_iso_hom, ← category.assoc,
    whisker_right_to_plus_comp_plus_comp_iso_hom]
  rfl

@[simp, reassoc]
theorem to_sheafify_comp_sheafify_comp_iso_inv :
    J.to_sheafify _ ≫ (J.sheafify_comp_iso F P).inv = whisker_right (J.to_sheafify _) _ := by
  rw [iso.comp_inv_eq]
  simp

section

variable [concrete_category.{max v u} D] [preserves_limits (forget D)]
  [∀ X : C, preserves_colimits_of_shape (J.cover Xᵒᵖ) (forget D)] [reflects_isomorphisms (forget D)]

@[simp]
theorem sheafify_comp_iso_inv_eq_sheafify_lift :
    (J.sheafify_comp_iso F P).inv =
      J.sheafify_lift (whisker_right (J.to_sheafify _) _) ((J.sheafify_is_sheaf _).comp _) :=
  by
  apply J.sheafify_lift_unique
  rw [iso.comp_inv_eq]
  simp

end

end CategoryTheory.GrothendieckTopology

