/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathbin.CategoryTheory.Limits.Shapes.Pullbacks
import Mathbin.CategoryTheory.Arrow

/-!
# Properties of morphisms

We provide the basic framework for talking about properties of morphisms.
The following meta-properties are defined

* `respects_iso`: `P` respects isomorphisms if `P f → P (e ≫ f)` and `P f → P (f ≫ e)`, where
  `e` is an isomorphism.
* `stable_under_composition`: `P` is stable under composition if `P f → P g → P (f ≫ g)`.
* `stable_under_base_change`: `P` is stable under base change if `P (Y ⟶ S) → P (X ×[S] Y ⟶ X)`.

-/


universe v u

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] {D : Type _} [Category D]

/-- A `morphism_property C` is a class of morphisms between objects in `C`. -/
def MorphismProperty :=
  ∀ ⦃X Y : C⦄ (f : X ⟶ Y), Prop deriving CompleteLattice

instance : Inhabited (MorphismProperty C) :=
  ⟨⊤⟩

variable {C}

namespace MorphismProperty

/-- A morphism property `respects_iso` if it still holds when composed with an isomorphism -/
def RespectsIso (P : MorphismProperty C) : Prop :=
  (∀ {X Y Z} (e : X ≅ Y) (f : Y ⟶ Z), P f → P (e.Hom ≫ f)) ∧ ∀ {X Y Z} (e : Y ≅ Z) (f : X ⟶ Y), P f → P (f ≫ e.Hom)

/-- A morphism property is `stable_under_composition` if the composition of two such morphisms
still falls in the class. -/
def StableUnderComposition (P : MorphismProperty C) : Prop :=
  ∀ ⦃X Y Z⦄ (f : X ⟶ Y) (g : Y ⟶ Z), P f → P g → P (f ≫ g)

/-- A morphism property is `stable_under_inverse` if the inverse of a morphism satisfying
the property still falls in the class. -/
def StableUnderInverse (P : MorphismProperty C) : Prop :=
  ∀ ⦃X Y⦄ (e : X ≅ Y), P e.Hom → P e.inv

/-- A morphism property is `stable_under_base_change` if the base change of such a morphism
still falls in the class. -/
def StableUnderBaseChange [HasPullbacks C] (P : MorphismProperty C) : Prop :=
  ∀ ⦃X Y S : C⦄ (f : X ⟶ S) (g : Y ⟶ S), P g → P (pullback.fst : pullback f g ⟶ X)

theorem StableUnderComposition.respects_iso {P : MorphismProperty C} (hP : StableUnderComposition P)
    (hP' : ∀ {X Y} (e : X ≅ Y), P e.Hom) : RespectsIso P :=
  ⟨fun X Y Z e f hf => hP _ _ (hP' e) hf, fun X Y Z e f hf => hP _ _ hf (hP' e)⟩

theorem RespectsIso.cancel_left_is_iso {P : MorphismProperty C} (hP : RespectsIso P) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsIso f] : P (f ≫ g) ↔ P g :=
  ⟨fun h => by
    simpa using hP.1 (as_iso f).symm (f ≫ g) h, hP.1 (asIso f) g⟩

theorem RespectsIso.cancel_right_is_iso {P : MorphismProperty C} (hP : RespectsIso P) {X Y Z : C} (f : X ⟶ Y)
    (g : Y ⟶ Z) [IsIso g] : P (f ≫ g) ↔ P f :=
  ⟨fun h => by
    simpa using hP.2 (as_iso g).symm (f ≫ g) h, hP.2 (asIso g) f⟩

theorem RespectsIso.arrow_iso_iff {P : MorphismProperty C} (hP : RespectsIso P) {f g : Arrow C} (e : f ≅ g) :
    P f.Hom ↔ P g.Hom := by
  rw [← arrow.inv_left_hom_right e.hom, hP.cancel_left_is_iso, hP.cancel_right_is_iso]
  rfl

theorem RespectsIso.arrow_mk_iso_iff {P : MorphismProperty C} (hP : RespectsIso P) {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z}
    (e : Arrow.mk f ≅ Arrow.mk g) : P f ↔ P g :=
  hP.arrow_iso_iff e

-- This is here to mirror `stable_under_base_change.snd`.
@[nolint unused_arguments]
theorem StableUnderBaseChange.fst [HasPullbacks C] {P : MorphismProperty C} (hP : StableUnderBaseChange P)
    (hP' : RespectsIso P) {X Y S : C} (f : X ⟶ S) (g : Y ⟶ S) (H : P g) : P (pullback.fst : pullback f g ⟶ X) :=
  hP f g H

theorem StableUnderBaseChange.snd [HasPullbacks C] {P : MorphismProperty C} (hP : StableUnderBaseChange P)
    (hP' : RespectsIso P) {X Y S : C} (f : X ⟶ S) (g : Y ⟶ S) (H : P f) : P (pullback.snd : pullback f g ⟶ Y) := by
  rw [← pullback_symmetry_hom_comp_fst, hP'.cancel_left_is_iso]
  exact hP g f H

theorem StableUnderBaseChange.base_change_obj [HasPullbacks C] {P : MorphismProperty C} (hP : StableUnderBaseChange P)
    (hP' : RespectsIso P) {S S' : C} (f : S' ⟶ S) (X : Over S) (H : P X.Hom) : P ((baseChange f).obj X).Hom :=
  hP.snd hP' X.Hom f H

theorem StableUnderBaseChange.base_change_map [HasPullbacks C] {P : MorphismProperty C} (hP : StableUnderBaseChange P)
    (hP' : RespectsIso P) {S S' : C} (f : S' ⟶ S) {X Y : Over S} (g : X ⟶ Y) (H : P g.left) :
    P ((baseChange f).map g).left := by
  let e := pullback_right_pullback_fst_iso Y.hom f g.left ≪≫ pullback.congr_hom (g.w.trans (category.comp_id _)) rfl
  have : e.inv ≫ pullback.snd = ((base_change f).map g).left := by
    apply pullback.hom_ext <;> dsimp' <;> simp
  rw [← this, hP'.cancel_left_is_iso]
  apply hP.snd hP'
  exact H

theorem StableUnderBaseChange.pullback_map [HasPullbacks C] {P : MorphismProperty C} (hP : StableUnderBaseChange P)
    (hP' : RespectsIso P) (hP'' : StableUnderComposition P) {S X X' Y Y' : C} {f : X ⟶ S} {g : Y ⟶ S} {f' : X' ⟶ S}
    {g' : Y' ⟶ S} {i₁ : X ⟶ X'} {i₂ : Y ⟶ Y'} (h₁ : P i₁) (h₂ : P i₂) (e₁ : f = i₁ ≫ f') (e₂ : g = i₂ ≫ g') :
    P (pullback.map f g f' g' i₁ i₂ (𝟙 _) ((Category.comp_id _).trans e₁) ((Category.comp_id _).trans e₂)) := by
  have :
    pullback.map f g f' g' i₁ i₂ (𝟙 _) ((category.comp_id _).trans e₁) ((category.comp_id _).trans e₂) =
      ((pullback_symmetry _ _).Hom ≫ ((base_change _).map (over.hom_mk _ e₂.symm : over.mk g ⟶ over.mk g')).left) ≫
        (pullback_symmetry _ _).Hom ≫ ((base_change g').map (over.hom_mk _ e₁.symm : over.mk f ⟶ over.mk f')).left :=
    by
    apply pullback.hom_ext <;> dsimp' <;> simp
  rw [this]
  apply hP'' <;> rw [hP'.cancel_left_is_iso]
  exacts[hP.base_change_map hP' _ (over.hom_mk _ e₂.symm : over.mk g ⟶ over.mk g') h₂,
    hP.base_change_map hP' _ (over.hom_mk _ e₁.symm : over.mk f ⟶ over.mk f') h₁]

/-- If `P : morphism_property C` and `F : C ⥤ D`, then
`P.is_inverted_by F` means that all morphisms in `P` are mapped by `F`
to isomorphisms in `D`. -/
def IsInvertedBy (P : MorphismProperty C) (F : C ⥤ D) : Prop :=
  ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (hf : P f), IsIso (F.map f)

/-- Given `app : Π X, F₁.obj X ⟶ F₂.obj X` where `F₁` and `F₂` are two functors,
this is the `morphism_property C` satisfied by the morphisms in `C` with respect
to whom `app` is natural. -/
@[simp]
def NaturalityProperty {F₁ F₂ : C ⥤ D} (app : ∀ X, F₁.obj X ⟶ F₂.obj X) : MorphismProperty C := fun X Y f =>
  F₁.map f ≫ app Y = app X ≫ F₂.map f

namespace NaturalityProperty

theorem is_stable_under_composition {F₁ F₂ : C ⥤ D} (app : ∀ X, F₁.obj X ⟶ F₂.obj X) :
    (NaturalityProperty app).StableUnderComposition := fun X Y Z f g hf hg => by
  simp only [← naturality_property] at hf hg⊢
  simp only [← functor.map_comp, ← category.assoc, ← hg]
  slice_lhs 1 2 => rw [hf]
  rw [category.assoc]

theorem is_stable_under_inverse {F₁ F₂ : C ⥤ D} (app : ∀ X, F₁.obj X ⟶ F₂.obj X) :
    (NaturalityProperty app).StableUnderInverse := fun X Y e he => by
  simp only [← naturality_property] at he⊢
  rw [← cancel_epi (F₁.map e.hom)]
  slice_rhs 1 2 => rw [he]
  simp only [← category.assoc, F₁.map_comp_assoc, F₂.map_comp, ← e.hom_inv_id, ← Functor.map_id, ← category.id_comp, ←
    category.comp_id]

end NaturalityProperty

end MorphismProperty

end CategoryTheory

