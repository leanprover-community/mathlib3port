/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathbin.CategoryTheory.Limits.Shapes.Diagonal
import Mathbin.CategoryTheory.Arrow
import Mathbin.CategoryTheory.Limits.Shapes.CommSq

/-!
# Properties of morphisms

We provide the basic framework for talking about properties of morphisms.
The following meta-properties are defined

* `respects_iso`: `P` respects isomorphisms if `P f → P (e ≫ f)` and `P f → P (f ≫ e)`, where
  `e` is an isomorphism.
* `stable_under_composition`: `P` is stable under composition if `P f → P g → P (f ≫ g)`.
* `stable_under_base_change`: `P` is stable under base change if in all pullback
  squares, the left map satisfies `P` if the right map satisfies it.
* `stable_under_cobase_change`: `P` is stable under cobase change if in all pushout
  squares, the right map satisfies `P` if the left map satisfies it.

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

instance : Subset (MorphismProperty C) :=
  ⟨fun P₁ P₂ => ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (hf : P₁ f), P₂ f⟩

instance : Inter (MorphismProperty C) :=
  ⟨fun P₁ P₂ X Y f => P₁ f ∧ P₂ f⟩

/-- The morphism property in `Cᵒᵖ` associated to a morphism property in `C` -/
@[simp]
def Op (P : MorphismProperty C) : MorphismProperty Cᵒᵖ := fun X Y f => P f.unop

/-- The morphism property in `C` associated to a morphism property in `Cᵒᵖ` -/
@[simp]
def Unop (P : MorphismProperty Cᵒᵖ) : MorphismProperty C := fun X Y f => P f.op

theorem unop_op (P : MorphismProperty C) : P.op.unop = P :=
  rfl

theorem op_unop (P : MorphismProperty Cᵒᵖ) : P.unop.op = P :=
  rfl

/-- The inverse image of a `morphism_property D` by a functor `C ⥤ D` -/
def InverseImage (P : MorphismProperty D) (F : C ⥤ D) : MorphismProperty C := fun X Y f => P (F.map f)

/-- A morphism property `respects_iso` if it still holds when composed with an isomorphism -/
def RespectsIso (P : MorphismProperty C) : Prop :=
  (∀ {X Y Z} (e : X ≅ Y) (f : Y ⟶ Z), P f → P (e.Hom ≫ f)) ∧ ∀ {X Y Z} (e : Y ≅ Z) (f : X ⟶ Y), P f → P (f ≫ e.Hom)

theorem RespectsIso.op {P : MorphismProperty C} (h : RespectsIso P) : RespectsIso P.op :=
  ⟨fun X Y Z e f hf => h.2 e.unop f.unop hf, fun X Y Z e f hf => h.1 e.unop f.unop hf⟩

theorem RespectsIso.unop {P : MorphismProperty Cᵒᵖ} (h : RespectsIso P) : RespectsIso P.unop :=
  ⟨fun X Y Z e f hf => h.2 e.op f.op hf, fun X Y Z e f hf => h.1 e.op f.op hf⟩

/-- A morphism property is `stable_under_composition` if the composition of two such morphisms
still falls in the class. -/
def StableUnderComposition (P : MorphismProperty C) : Prop :=
  ∀ ⦃X Y Z⦄ (f : X ⟶ Y) (g : Y ⟶ Z), P f → P g → P (f ≫ g)

theorem StableUnderComposition.op {P : MorphismProperty C} (h : StableUnderComposition P) :
    StableUnderComposition P.op := fun X Y Z f g hf hg => h g.unop f.unop hg hf

theorem StableUnderComposition.unop {P : MorphismProperty Cᵒᵖ} (h : StableUnderComposition P) :
    StableUnderComposition P.unop := fun X Y Z f g hf hg => h g.op f.op hg hf

/-- A morphism property is `stable_under_inverse` if the inverse of a morphism satisfying
the property still falls in the class. -/
def StableUnderInverse (P : MorphismProperty C) : Prop :=
  ∀ ⦃X Y⦄ (e : X ≅ Y), P e.Hom → P e.inv

theorem StableUnderInverse.op {P : MorphismProperty C} (h : StableUnderInverse P) : StableUnderInverse P.op :=
  fun X Y e he => h e.unop he

theorem StableUnderInverse.unop {P : MorphismProperty Cᵒᵖ} (h : StableUnderInverse P) : StableUnderInverse P.unop :=
  fun X Y e he => h e.op he

/-- A morphism property is `stable_under_base_change` if the base change of such a morphism
still falls in the class. -/
def StableUnderBaseChange (P : MorphismProperty C) : Prop :=
  ∀ ⦃X Y Y' S : C⦄ ⦃f : X ⟶ S⦄ ⦃g : Y ⟶ S⦄ ⦃f' : Y' ⟶ Y⦄ ⦃g' : Y' ⟶ X⦄ (sq : IsPullback f' g' g f) (hg : P g), P g'

/-- A morphism property is `stable_under_cobase_change` if the cobase change of such a morphism
still falls in the class. -/
def StableUnderCobaseChange (P : MorphismProperty C) : Prop :=
  ∀ ⦃A A' B B' : C⦄ ⦃f : A ⟶ A'⦄ ⦃g : A ⟶ B⦄ ⦃f' : B ⟶ B'⦄ ⦃g' : A' ⟶ B'⦄ (sq : IsPushout g f f' g') (hf : P f), P f'

theorem StableUnderComposition.respects_iso {P : MorphismProperty C} (hP : StableUnderComposition P)
    (hP' : ∀ {X Y} (e : X ≅ Y), P e.Hom) : RespectsIso P :=
  ⟨fun X Y Z e f hf => hP _ _ (hP' e) hf, fun X Y Z e f hf => hP _ _ hf (hP' e)⟩

theorem RespectsIso.cancel_left_is_iso {P : MorphismProperty C} (hP : RespectsIso P) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsIso f] : P (f ≫ g) ↔ P g :=
  ⟨fun h => by simpa using hP.1 (as_iso f).symm (f ≫ g) h, hP.1 (asIso f) g⟩

theorem RespectsIso.cancel_right_is_iso {P : MorphismProperty C} (hP : RespectsIso P) {X Y Z : C} (f : X ⟶ Y)
    (g : Y ⟶ Z) [IsIso g] : P (f ≫ g) ↔ P f :=
  ⟨fun h => by simpa using hP.2 (as_iso g).symm (f ≫ g) h, hP.2 (asIso g) f⟩

theorem RespectsIso.arrow_iso_iff {P : MorphismProperty C} (hP : RespectsIso P) {f g : Arrow C} (e : f ≅ g) :
    P f.Hom ↔ P g.Hom := by
  rw [← arrow.inv_left_hom_right e.hom, hP.cancel_left_is_iso, hP.cancel_right_is_iso]
  rfl

theorem RespectsIso.arrow_mk_iso_iff {P : MorphismProperty C} (hP : RespectsIso P) {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z}
    (e : Arrow.mk f ≅ Arrow.mk g) : P f ↔ P g :=
  hP.arrow_iso_iff e

theorem RespectsIso.of_respects_arrow_iso (P : MorphismProperty C)
    (hP : ∀ (f g : Arrow C) (e : f ≅ g) (hf : P f.Hom), P g.Hom) : RespectsIso P := by
  constructor
  · intro X Y Z e f hf
    refine' hP (arrow.mk f) (arrow.mk (e.hom ≫ f)) (arrow.iso_mk e.symm (iso.refl _) _) hf
    dsimp
    simp only [iso.inv_hom_id_assoc, category.comp_id]
    
  · intro X Y Z e f hf
    refine' hP (arrow.mk f) (arrow.mk (f ≫ e.hom)) (arrow.iso_mk (iso.refl _) e _) hf
    dsimp
    simp only [category.id_comp]
    

theorem StableUnderBaseChange.mk {P : MorphismProperty C} [HasPullbacks C] (hP₁ : RespectsIso P)
    (hP₂ : ∀ (X Y S : C) (f : X ⟶ S) (g : Y ⟶ S) (hg : P g), P (pullback.fst : pullback f g ⟶ X)) :
    StableUnderBaseChange P := fun X Y Y' S f g f' g' sq hg => by
  let e := sq.flip.iso_pullback
  rw [← hP₁.cancel_left_is_iso e.inv, sq.flip.iso_pullback_inv_fst]
  exact hP₂ _ _ _ f g hg

theorem StableUnderBaseChange.respects_iso {P : MorphismProperty C} (hP : StableUnderBaseChange P) : RespectsIso P := by
  apply respects_iso.of_respects_arrow_iso
  intro f g e
  exact hP (is_pullback.of_horiz_is_iso (comm_sq.mk e.inv.w))

theorem StableUnderBaseChange.fst {P : MorphismProperty C} (hP : StableUnderBaseChange P) {X Y S : C} (f : X ⟶ S)
    (g : Y ⟶ S) [HasPullback f g] (H : P g) : P (pullback.fst : pullback f g ⟶ X) :=
  hP (IsPullback.of_has_pullback f g).flip H

theorem StableUnderBaseChange.snd {P : MorphismProperty C} (hP : StableUnderBaseChange P) {X Y S : C} (f : X ⟶ S)
    (g : Y ⟶ S) [HasPullback f g] (H : P f) : P (pullback.snd : pullback f g ⟶ Y) :=
  hP (IsPullback.of_has_pullback f g) H

theorem StableUnderBaseChange.base_change_obj [HasPullbacks C] {P : MorphismProperty C} (hP : StableUnderBaseChange P)
    {S S' : C} (f : S' ⟶ S) (X : Over S) (H : P X.Hom) : P ((baseChange f).obj X).Hom :=
  hP.snd X.Hom f H

theorem StableUnderBaseChange.base_change_map [HasPullbacks C] {P : MorphismProperty C} (hP : StableUnderBaseChange P)
    {S S' : C} (f : S' ⟶ S) {X Y : Over S} (g : X ⟶ Y) (H : P g.left) : P ((baseChange f).map g).left := by
  let e := pullback_right_pullback_fst_iso Y.hom f g.left ≪≫ pullback.congr_hom (g.w.trans (category.comp_id _)) rfl
  have : e.inv ≫ pullback.snd = ((base_change f).map g).left := by apply pullback.hom_ext <;> dsimp <;> simp
  rw [← this, hP.respects_iso.cancel_left_is_iso]
  exact hP.snd _ _ H

theorem StableUnderBaseChange.pullback_map [HasPullbacks C] {P : MorphismProperty C} (hP : StableUnderBaseChange P)
    (hP' : StableUnderComposition P) {S X X' Y Y' : C} {f : X ⟶ S} {g : Y ⟶ S} {f' : X' ⟶ S} {g' : Y' ⟶ S} {i₁ : X ⟶ X'}
    {i₂ : Y ⟶ Y'} (h₁ : P i₁) (h₂ : P i₂) (e₁ : f = i₁ ≫ f') (e₂ : g = i₂ ≫ g') :
    P (pullback.map f g f' g' i₁ i₂ (𝟙 _) ((Category.comp_id _).trans e₁) ((Category.comp_id _).trans e₂)) := by
  have :
    pullback.map f g f' g' i₁ i₂ (𝟙 _) ((category.comp_id _).trans e₁) ((category.comp_id _).trans e₂) =
      ((pullback_symmetry _ _).Hom ≫ ((base_change _).map (over.hom_mk _ e₂.symm : over.mk g ⟶ over.mk g')).left) ≫
        (pullback_symmetry _ _).Hom ≫ ((base_change g').map (over.hom_mk _ e₁.symm : over.mk f ⟶ over.mk f')).left :=
    by apply pullback.hom_ext <;> dsimp <;> simp
  rw [this]
  apply hP' <;> rw [hP.respects_iso.cancel_left_is_iso]
  exacts[hP.base_change_map _ (over.hom_mk _ e₂.symm : over.mk g ⟶ over.mk g') h₂,
    hP.base_change_map _ (over.hom_mk _ e₁.symm : over.mk f ⟶ over.mk f') h₁]

theorem StableUnderCobaseChange.mk {P : MorphismProperty C} [HasPushouts C] (hP₁ : RespectsIso P)
    (hP₂ : ∀ (A B A' : C) (f : A ⟶ A') (g : A ⟶ B) (hf : P f), P (pushout.inr : B ⟶ pushout f g)) :
    StableUnderCobaseChange P := fun A A' B B' f g f' g' sq hf => by
  let e := sq.flip.iso_pushout
  rw [← hP₁.cancel_right_is_iso _ e.hom, sq.flip.inr_iso_pushout_hom]
  exact hP₂ _ _ _ f g hf

theorem StableUnderCobaseChange.respects_iso {P : MorphismProperty C} (hP : StableUnderCobaseChange P) :
    RespectsIso P :=
  RespectsIso.of_respects_arrow_iso _ fun f g e => hP (IsPushout.of_horiz_is_iso (CommSq.mk e.Hom.w))

theorem StableUnderCobaseChange.inl {P : MorphismProperty C} (hP : StableUnderCobaseChange P) {A B A' : C} (f : A ⟶ A')
    (g : A ⟶ B) [HasPushout f g] (H : P g) : P (pushout.inl : A' ⟶ pushout f g) :=
  hP (IsPushout.of_has_pushout f g) H

theorem StableUnderCobaseChange.inr {P : MorphismProperty C} (hP : StableUnderCobaseChange P) {A B A' : C} (f : A ⟶ A')
    (g : A ⟶ B) [HasPushout f g] (H : P f) : P (pushout.inr : B ⟶ pushout f g) :=
  hP (IsPushout.of_has_pushout f g).flip H

theorem StableUnderCobaseChange.op {P : MorphismProperty C} (hP : StableUnderCobaseChange P) :
    StableUnderBaseChange P.op := fun X Y Y' S f g f' g' sq hg => hP sq.unop hg

theorem StableUnderCobaseChange.unop {P : MorphismProperty Cᵒᵖ} (hP : StableUnderCobaseChange P) :
    StableUnderBaseChange P.unop := fun X Y Y' S f g f' g' sq hg => hP sq.op hg

theorem StableUnderBaseChange.op {P : MorphismProperty C} (hP : StableUnderBaseChange P) :
    StableUnderCobaseChange P.op := fun A A' B B' f g f' g' sq hf => hP sq.unop hf

theorem StableUnderBaseChange.unop {P : MorphismProperty Cᵒᵖ} (hP : StableUnderBaseChange P) :
    StableUnderCobaseChange P.unop := fun A A' B B' f g f' g' sq hf => hP sq.op hf

/-- If `P : morphism_property C` and `F : C ⥤ D`, then
`P.is_inverted_by F` means that all morphisms in `P` are mapped by `F`
to isomorphisms in `D`. -/
def IsInvertedBy (P : MorphismProperty C) (F : C ⥤ D) : Prop :=
  ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (hf : P f), IsIso (F.map f)

theorem IsInvertedBy.of_comp {C₁ C₂ C₃ : Type _} [Category C₁] [Category C₂] [Category C₃] (W : MorphismProperty C₁)
    (F : C₁ ⥤ C₂) (hF : W.IsInvertedBy F) (G : C₂ ⥤ C₃) : W.IsInvertedBy (F ⋙ G) := fun X Y f hf => by
  haveI := hF f hf
  dsimp
  infer_instance

/-- Given `app : Π X, F₁.obj X ⟶ F₂.obj X` where `F₁` and `F₂` are two functors,
this is the `morphism_property C` satisfied by the morphisms in `C` with respect
to whom `app` is natural. -/
@[simp]
def NaturalityProperty {F₁ F₂ : C ⥤ D} (app : ∀ X, F₁.obj X ⟶ F₂.obj X) : MorphismProperty C := fun X Y f =>
  F₁.map f ≫ app Y = app X ≫ F₂.map f

namespace NaturalityProperty

theorem is_stable_under_composition {F₁ F₂ : C ⥤ D} (app : ∀ X, F₁.obj X ⟶ F₂.obj X) :
    (NaturalityProperty app).StableUnderComposition := fun X Y Z f g hf hg => by
  simp only [naturality_property] at hf hg⊢
  simp only [functor.map_comp, category.assoc, hg]
  slice_lhs 1 2 => rw [hf]
  rw [category.assoc]

theorem is_stable_under_inverse {F₁ F₂ : C ⥤ D} (app : ∀ X, F₁.obj X ⟶ F₂.obj X) :
    (NaturalityProperty app).StableUnderInverse := fun X Y e he => by
  simp only [naturality_property] at he⊢
  rw [← cancel_epi (F₁.map e.hom)]
  slice_rhs 1 2 => rw [he]
  simp only [category.assoc, ← F₁.map_comp_assoc, ← F₂.map_comp, e.hom_inv_id, Functor.map_id, category.id_comp,
    category.comp_id]

end NaturalityProperty

theorem RespectsIso.inverse_image {P : MorphismProperty D} (h : RespectsIso P) (F : C ⥤ D) :
    RespectsIso (P.InverseImage F) := by
  constructor
  all_goals
  intro X Y Z e f hf
  dsimp [inverse_image]
  rw [F.map_comp]
  exacts[h.1 (F.map_iso e) (F.map f) hf, h.2 (F.map_iso e) (F.map f) hf]

theorem StableUnderComposition.inverse_image {P : MorphismProperty D} (h : StableUnderComposition P) (F : C ⥤ D) :
    StableUnderComposition (P.InverseImage F) := fun X Y Z f g hf hg => by
  simpa only [← F.map_comp] using h (F.map f) (F.map g) hf hg

variable (C)

/-- The `morphism_property C` satisfied by isomorphisms in `C`. -/
def Isomorphisms : MorphismProperty C := fun X Y f => IsIso f

/-- The `morphism_property C` satisfied by monomorphisms in `C`. -/
def Monomorphisms : MorphismProperty C := fun X Y f => Mono f

/-- The `morphism_property C` satisfied by epimorphisms in `C`. -/
def Epimorphisms : MorphismProperty C := fun X Y f => Epi f

section

variable {C} {X Y : C} (f : X ⟶ Y)

@[simp]
theorem Isomorphisms.iff : (Isomorphisms C) f ↔ IsIso f := by rfl

@[simp]
theorem Monomorphisms.iff : (Monomorphisms C) f ↔ Mono f := by rfl

@[simp]
theorem Epimorphisms.iff : (Epimorphisms C) f ↔ Epi f := by rfl

theorem Isomorphisms.infer_property [hf : IsIso f] : (Isomorphisms C) f :=
  hf

theorem Monomorphisms.infer_property [hf : Mono f] : (Monomorphisms C) f :=
  hf

theorem Epimorphisms.infer_property [hf : Epi f] : (Epimorphisms C) f :=
  hf

end

theorem RespectsIso.monomorphisms : RespectsIso (Monomorphisms C) := by
  constructor <;>
    · intro X Y Z e f
      simp only [monomorphisms.iff]
      intro
      apply mono_comp
      

theorem RespectsIso.epimorphisms : RespectsIso (Epimorphisms C) := by
  constructor <;>
    · intro X Y Z e f
      simp only [epimorphisms.iff]
      intro
      apply epi_comp
      

theorem RespectsIso.isomorphisms : RespectsIso (Isomorphisms C) := by
  constructor <;>
    · intro X Y Z e f
      simp only [isomorphisms.iff]
      intro
      infer_instance
      

theorem StableUnderComposition.isomorphisms : StableUnderComposition (Isomorphisms C) := fun X Y Z f g hf hg => by
  rw [isomorphisms.iff] at hf hg⊢
  haveI := hf
  haveI := hg
  infer_instance

theorem StableUnderComposition.monomorphisms : StableUnderComposition (Monomorphisms C) := fun X Y Z f g hf hg => by
  rw [monomorphisms.iff] at hf hg⊢
  haveI := hf
  haveI := hg
  apply mono_comp

theorem StableUnderComposition.epimorphisms : StableUnderComposition (Epimorphisms C) := fun X Y Z f g hf hg => by
  rw [epimorphisms.iff] at hf hg⊢
  haveI := hf
  haveI := hg
  apply epi_comp

variable {C}

/-- The full subcategory of `C ⥤ D` consisting of functors inverting morphisms in `W` -/
@[nolint has_nonempty_instance]
def FunctorsInverting (W : MorphismProperty C) (D : Type _) [Category D] :=
  FullSubcategory fun F : C ⥤ D => W.IsInvertedBy F deriving Category

/-- A constructor for `W.functors_inverting D` -/
def FunctorsInverting.mk {W : MorphismProperty C} {D : Type _} [Category D] (F : C ⥤ D) (hF : W.IsInvertedBy F) :
    W.FunctorsInverting D :=
  ⟨F, hF⟩

section Diagonal

variable [HasPullbacks C] {P : MorphismProperty C}

/-- For `P : morphism_property C`, `P.diagonal` is a morphism property that holds for `f : X ⟶ Y`
whenever `P` holds for `X ⟶ Y xₓ Y`. -/
def Diagonal (P : MorphismProperty C) : MorphismProperty C := fun X Y f => P (pullback.diagonal f)

theorem diagonal_iff {X Y : C} {f : X ⟶ Y} : P.Diagonal f ↔ P (pullback.diagonal f) :=
  Iff.rfl

theorem RespectsIso.diagonal (hP : P.RespectsIso) : P.Diagonal.RespectsIso := by
  constructor
  · introv H
    rwa [diagonal_iff, pullback.diagonal_comp, hP.cancel_left_is_iso, hP.cancel_left_is_iso, ←
      hP.cancel_right_is_iso _ _, ← pullback.condition, hP.cancel_left_is_iso]
    infer_instance
    
  · introv H
    delta diagonal
    rwa [pullback.diagonal_comp, hP.cancel_right_is_iso]
    

theorem StableUnderComposition.diagonal (hP : StableUnderComposition P) (hP' : RespectsIso P)
    (hP'' : StableUnderBaseChange P) : P.Diagonal.StableUnderComposition := by
  introv X h₁ h₂
  rw [diagonal_iff, pullback.diagonal_comp]
  apply hP
  · assumption
    
  rw [hP'.cancel_left_is_iso]
  apply hP''.snd
  assumption

theorem StableUnderBaseChange.diagonal (hP : StableUnderBaseChange P) (hP' : RespectsIso P) :
    P.Diagonal.StableUnderBaseChange :=
  StableUnderBaseChange.mk hP'.Diagonal
    (by
      introv h
      rw [diagonal_iff, diagonal_pullback_fst, hP'.cancel_left_is_iso, hP'.cancel_right_is_iso]
      convert hP.base_change_map f _ _ <;> simp <;> assumption)

end Diagonal

end MorphismProperty

end CategoryTheory

