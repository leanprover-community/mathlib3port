/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou

! This file was ported from Lean 3 source module category_theory.localization.predicate
! leanprover-community/mathlib commit 31ca6f9cf5f90a6206092cd7f84b359dcb6d52e0
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Localization.Construction

/-!

# Predicate for localized categories

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file, a predicate `L.is_localization W` is introduced for a functor `L : C ⥤ D`
and `W : morphism_property C`: it expresses that `L` identifies `D` with the localized
category of `C` with respect to `W` (up to equivalence).

We introduce a universal property `strict_universal_property_fixed_target L W E` which
states that `L` inverts the morphisms in `W` and that all functors `C ⥤ E` inverting
`W` uniquely factors as a composition of `L ⋙ G` with `G : D ⥤ E`. Such universal
properties are inputs for the constructor `is_localization.mk'` for `L.is_localization W`.

When `L : C ⥤ D` is a localization functor for `W : morphism_property` (i.e. when
`[L.is_localization W]` holds), for any category `E`, there is
an equivalence `functor_equivalence L W E : (D ⥤ E) ≌ (W.functors_inverting E)`
that is induced by the composition with the functor `L`. When two functors
`F : C ⥤ E` and `F' : D ⥤ E` correspond via this equivalence, we shall say
that `F'` lifts `F`, and the associated isomorphism `L ⋙ F' ≅ F` is the
datum that is part of the class `lifting L W F F'`. The functions
`lift_nat_trans` and `lift_nat_iso` can be used to lift natural transformations
and natural isomorphisms between functors.

-/


noncomputable section

namespace CategoryTheory

open Category

variable {C D : Type _} [Category C] [Category D] (L : C ⥤ D) (W : MorphismProperty C) (E : Type _)
  [Category E]

namespace Functor

#print CategoryTheory.Functor.IsLocalization /-
/-- The predicate expressing that, up to equivalence, a functor `L : C ⥤ D`
identifies the category `D` with the localized category of `C` with respect
to `W : morphism_property C`. -/
class IsLocalization : Prop where
  inverts : W.IsInvertedBy L
  nonempty_isEquivalence : Nonempty (IsEquivalence (Localization.Construction.lift L inverts))
#align category_theory.functor.is_localization CategoryTheory.Functor.IsLocalization
-/

#print CategoryTheory.Functor.q_isLocalization /-
instance q_isLocalization : W.Q.IsLocalization W
    where
  inverts := W.Q_inverts
  nonempty_isEquivalence :=
    by
    suffices localization.construction.lift W.Q W.Q_inverts = 𝟭 _ by apply Nonempty.intro;
      rw [this]; infer_instance
    apply localization.construction.uniq
    simpa only [localization.construction.fac]
#align category_theory.functor.Q_is_localization CategoryTheory.Functor.q_isLocalization
-/

end Functor

namespace Localization

#print CategoryTheory.Localization.StrictUniversalPropertyFixedTarget /-
/-- This universal property states that a functor `L : C ⥤ D` inverts morphisms
in `W` and the all functors `D ⥤ E` (for a fixed category `E`) uniquely factors
through `L`. -/
structure StrictUniversalPropertyFixedTarget where
  inverts : W.IsInvertedBy L
  lift : ∀ (F : C ⥤ E) (hF : W.IsInvertedBy F), D ⥤ E
  fac : ∀ (F : C ⥤ E) (hF : W.IsInvertedBy F), L ⋙ lift F hF = F
  uniq : ∀ (F₁ F₂ : D ⥤ E) (h : L ⋙ F₁ = L ⋙ F₂), F₁ = F₂
#align category_theory.localization.strict_universal_property_fixed_target CategoryTheory.Localization.StrictUniversalPropertyFixedTarget
-/

#print CategoryTheory.Localization.strictUniversalPropertyFixedTargetQ /-
/-- The localized category `W.localization` that was constructed satisfies
the universal property of the localization. -/
@[simps]
def strictUniversalPropertyFixedTargetQ : StrictUniversalPropertyFixedTarget W.Q W E
    where
  inverts := W.Q_inverts
  lift := Construction.lift
  fac := Construction.fac
  uniq := Construction.uniq
#align category_theory.localization.strict_universal_property_fixed_target_Q CategoryTheory.Localization.strictUniversalPropertyFixedTargetQ
-/

instance : Inhabited (StrictUniversalPropertyFixedTarget W.Q W E) :=
  ⟨strictUniversalPropertyFixedTargetQ _ _⟩

#print CategoryTheory.Localization.strictUniversalPropertyFixedTargetId /-
/-- When `W` consists of isomorphisms, the identity satisfies the universal property
of the localization. -/
@[simps]
def strictUniversalPropertyFixedTargetId (hW : W ⊆ MorphismProperty.isomorphisms C) :
    StrictUniversalPropertyFixedTarget (𝟭 C) W E
    where
  inverts X Y f hf := hW f hf
  lift F hF := F
  fac F hF := by cases F; rfl
  uniq F₁ F₂ eq := by cases F₁; cases F₂; exact Eq
#align category_theory.localization.strict_universal_property_fixed_target_id CategoryTheory.Localization.strictUniversalPropertyFixedTargetId
-/

end Localization

namespace Functor

/- warning: category_theory.functor.is_localization.mk' -> CategoryTheory.Functor.IsLocalization.mk' is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} {D : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u1} C] [_inst_2 : CategoryTheory.Category.{u4, u2} D] (L : CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2) (W : CategoryTheory.MorphismProperty.{u3, u1} C _inst_1), (CategoryTheory.Localization.StrictUniversalPropertyFixedTarget.{u1, u2, u3, u4, u2, u4} C D _inst_1 _inst_2 L W D _inst_2) -> (CategoryTheory.Localization.StrictUniversalPropertyFixedTarget.{u1, u2, u3, u4, u1, max u1 u3} C D _inst_1 _inst_2 L W (CategoryTheory.MorphismProperty.Localization.{u1, u3} C _inst_1 W) (CategoryTheory.MorphismProperty.Localization.category.{u1, u3} C _inst_1 W)) -> (CategoryTheory.Functor.IsLocalization.{u1, u2, u3, u4} C D _inst_1 _inst_2 L W)
but is expected to have type
  forall {C : Type.{u4}} {D : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u4} C] [_inst_2 : CategoryTheory.Category.{u1, u3} D] (L : CategoryTheory.Functor.{u2, u1, u4, u3} C _inst_1 D _inst_2) (W : CategoryTheory.MorphismProperty.{u2, u4} C _inst_1), (CategoryTheory.Localization.StrictUniversalPropertyFixedTarget.{u4, u3, u2, u1, u3, u1} C D _inst_1 _inst_2 L W D _inst_2) -> (CategoryTheory.Localization.StrictUniversalPropertyFixedTarget.{u4, u3, u2, u1, u4, max u4 u2} C D _inst_1 _inst_2 L W (CategoryTheory.MorphismProperty.Localization.{u4, u2} C _inst_1 W) (CategoryTheory.MorphismProperty.instCategoryLocalization.{u4, u2} C _inst_1 W)) -> (CategoryTheory.Functor.IsLocalization.{u4, u3, u2, u1} C D _inst_1 _inst_2 L W)
Case conversion may be inaccurate. Consider using '#align category_theory.functor.is_localization.mk' CategoryTheory.Functor.IsLocalization.mk'ₓ'. -/
theorem IsLocalization.mk' (h₁ : Localization.StrictUniversalPropertyFixedTarget L W D)
    (h₂ : Localization.StrictUniversalPropertyFixedTarget L W W.Localization) :
    IsLocalization L W :=
  { inverts := h₁.inverts
    nonempty_isEquivalence :=
      Nonempty.intro
        { inverse := h₂.lift W.Q W.Q_inverts
          unitIso :=
            eqToIso
              (Localization.Construction.uniq _ _
                (by
                  simp only [← functor.assoc, localization.construction.fac, h₂.fac,
                    functor.comp_id]))
          counitIso :=
            eqToIso
              (h₁.uniq _ _
                (by
                  simp only [← functor.assoc, h₂.fac, localization.construction.fac,
                    functor.comp_id]))
          functor_unitIso_comp' := fun X => by
            simpa only [eq_to_iso.hom, eq_to_hom_app, eq_to_hom_map, eq_to_hom_trans,
              eq_to_hom_refl] } }
#align category_theory.functor.is_localization.mk' CategoryTheory.Functor.IsLocalization.mk'

/- warning: category_theory.functor.is_localization.for_id -> CategoryTheory.Functor.IsLocalization.for_id is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C] (W : CategoryTheory.MorphismProperty.{u2, u1} C _inst_1), (HasSubset.Subset.{max u1 u2} (CategoryTheory.MorphismProperty.{u2, u1} C _inst_1) (CategoryTheory.MorphismProperty.hasSubset.{u2, u1} C _inst_1) W (CategoryTheory.MorphismProperty.isomorphisms.{u2, u1} C _inst_1)) -> (CategoryTheory.Functor.IsLocalization.{u1, u1, u2, u2} C C _inst_1 _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) W)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (W : CategoryTheory.MorphismProperty.{u1, u2} C _inst_1), (HasSubset.Subset.{max u2 u1} (CategoryTheory.MorphismProperty.{u1, u2} C _inst_1) (CategoryTheory.MorphismProperty.instHasSubsetMorphismProperty.{u1, u2} C _inst_1) W (CategoryTheory.MorphismProperty.isomorphisms.{u1, u2} C _inst_1)) -> (CategoryTheory.Functor.IsLocalization.{u2, u2, u1, u1} C C _inst_1 _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) W)
Case conversion may be inaccurate. Consider using '#align category_theory.functor.is_localization.for_id CategoryTheory.Functor.IsLocalization.for_idₓ'. -/
theorem IsLocalization.for_id (hW : W ⊆ MorphismProperty.isomorphisms C) : (𝟭 C).IsLocalization W :=
  IsLocalization.mk' _ _ (Localization.strictUniversalPropertyFixedTargetId W _ hW)
    (Localization.strictUniversalPropertyFixedTargetId W _ hW)
#align category_theory.functor.is_localization.for_id CategoryTheory.Functor.IsLocalization.for_id

end Functor

namespace Localization

variable [L.IsLocalization W]

/- warning: category_theory.localization.inverts -> CategoryTheory.Localization.inverts is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} {D : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u1} C] [_inst_2 : CategoryTheory.Category.{u4, u2} D] (L : CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2) (W : CategoryTheory.MorphismProperty.{u3, u1} C _inst_1) [_inst_4 : CategoryTheory.Functor.IsLocalization.{u1, u2, u3, u4} C D _inst_1 _inst_2 L W], CategoryTheory.MorphismProperty.IsInvertedBy.{u3, u1, u2, u4} C _inst_1 D _inst_2 W L
but is expected to have type
  forall {C : Type.{u3}} {D : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u4, u3} C] [_inst_2 : CategoryTheory.Category.{u1, u2} D] (L : CategoryTheory.Functor.{u4, u1, u3, u2} C _inst_1 D _inst_2) (W : CategoryTheory.MorphismProperty.{u4, u3} C _inst_1) [_inst_4 : CategoryTheory.Functor.IsLocalization.{u3, u2, u4, u1} C D _inst_1 _inst_2 L W], CategoryTheory.MorphismProperty.IsInvertedBy.{u4, u3, u2, u1} C _inst_1 D _inst_2 W L
Case conversion may be inaccurate. Consider using '#align category_theory.localization.inverts CategoryTheory.Localization.invertsₓ'. -/
theorem inverts : W.IsInvertedBy L :=
  (inferInstance : L.IsLocalization W).inverts
#align category_theory.localization.inverts CategoryTheory.Localization.inverts

/- warning: category_theory.localization.iso_of_hom -> CategoryTheory.Localization.isoOfHom is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} {D : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u1} C] [_inst_2 : CategoryTheory.Category.{u4, u2} D] (L : CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2) (W : CategoryTheory.MorphismProperty.{u3, u1} C _inst_1) [_inst_4 : CategoryTheory.Functor.IsLocalization.{u1, u2, u3, u4} C D _inst_1 _inst_2 L W] {X : C} {Y : C} (f : Quiver.Hom.{succ u3, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} C (CategoryTheory.Category.toCategoryStruct.{u3, u1} C _inst_1)) X Y), (W X Y f) -> (CategoryTheory.Iso.{u4, u2} D _inst_2 (CategoryTheory.Functor.obj.{u3, u4, u1, u2} C _inst_1 D _inst_2 L X) (CategoryTheory.Functor.obj.{u3, u4, u1, u2} C _inst_1 D _inst_2 L Y))
but is expected to have type
  forall {C : Type.{u1}} {D : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u1} C] [_inst_2 : CategoryTheory.Category.{u4, u2} D] (L : CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2) (W : CategoryTheory.MorphismProperty.{u3, u1} C _inst_1) [_inst_4 : CategoryTheory.Functor.IsLocalization.{u1, u2, u3, u4} C D _inst_1 _inst_2 L W] {X : C} {Y : C} (f : Quiver.Hom.{succ u3, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} C (CategoryTheory.Category.toCategoryStruct.{u3, u1} C _inst_1)) X Y), (W X Y f) -> (CategoryTheory.Iso.{u4, u2} D _inst_2 (Prefunctor.obj.{succ u3, succ u4, u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} C (CategoryTheory.Category.toCategoryStruct.{u3, u1} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} D (CategoryTheory.Category.toCategoryStruct.{u4, u2} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u3, u4, u1, u2} C _inst_1 D _inst_2 L) X) (Prefunctor.obj.{succ u3, succ u4, u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} C (CategoryTheory.Category.toCategoryStruct.{u3, u1} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} D (CategoryTheory.Category.toCategoryStruct.{u4, u2} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u3, u4, u1, u2} C _inst_1 D _inst_2 L) Y))
Case conversion may be inaccurate. Consider using '#align category_theory.localization.iso_of_hom CategoryTheory.Localization.isoOfHomₓ'. -/
/-- The isomorphism `L.obj X ≅ L.obj Y` that is deduced from a morphism `f : X ⟶ Y` which
belongs to `W`, when `L.is_localization W`. -/
@[simps]
def isoOfHom {X Y : C} (f : X ⟶ Y) (hf : W f) : L.obj X ≅ L.obj Y :=
  haveI : is_iso (L.map f) := inverts L W f hf
  as_iso (L.map f)
#align category_theory.localization.iso_of_hom CategoryTheory.Localization.isoOfHom

instance : IsEquivalence (Localization.Construction.lift L (inverts L W)) :=
  (inferInstance : L.IsLocalization W).nonempty_isEquivalence.some

/- warning: category_theory.localization.equivalence_from_model -> CategoryTheory.Localization.equivalenceFromModel is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} {D : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u1} C] [_inst_2 : CategoryTheory.Category.{u4, u2} D] (L : CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2) (W : CategoryTheory.MorphismProperty.{u3, u1} C _inst_1) [_inst_4 : CategoryTheory.Functor.IsLocalization.{u1, u2, u3, u4} C D _inst_1 _inst_2 L W], CategoryTheory.Equivalence.{max u1 u3, u4, u1, u2} (CategoryTheory.MorphismProperty.Localization.{u1, u3} C _inst_1 W) (CategoryTheory.MorphismProperty.Localization.category.{u1, u3} C _inst_1 W) D _inst_2
but is expected to have type
  forall {C : Type.{u1}} {D : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u1} C] [_inst_2 : CategoryTheory.Category.{u4, u2} D] (L : CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2) (W : CategoryTheory.MorphismProperty.{u3, u1} C _inst_1) [_inst_4 : CategoryTheory.Functor.IsLocalization.{u1, u2, u3, u4} C D _inst_1 _inst_2 L W], CategoryTheory.Equivalence.{max u1 u3, u4, u1, u2} (CategoryTheory.MorphismProperty.Localization.{u1, u3} C _inst_1 W) D (CategoryTheory.MorphismProperty.instCategoryLocalization.{u1, u3} C _inst_1 W) _inst_2
Case conversion may be inaccurate. Consider using '#align category_theory.localization.equivalence_from_model CategoryTheory.Localization.equivalenceFromModelₓ'. -/
/-- A chosen equivalence of categories `W.localization ≅ D` for a functor
`L : C ⥤ D` which satisfies `L.is_localization W`. This shall be used in
order to deduce properties of `L` from properties of `W.Q`. -/
def equivalenceFromModel : W.Localization ≌ D :=
  (Localization.Construction.lift L (inverts L W)).asEquivalence
#align category_theory.localization.equivalence_from_model CategoryTheory.Localization.equivalenceFromModel

#print CategoryTheory.Localization.qCompEquivalenceFromModelFunctorIso /-
/-- Via the equivalence of categories `equivalence_from_model L W : W.localization ≌ D`,
one may identify the functors `W.Q` and `L`. -/
def qCompEquivalenceFromModelFunctorIso : W.Q ⋙ (equivalenceFromModel L W).Functor ≅ L :=
  eqToIso (Construction.fac _ _)
#align category_theory.localization.Q_comp_equivalence_from_model_functor_iso CategoryTheory.Localization.qCompEquivalenceFromModelFunctorIso
-/

#print CategoryTheory.Localization.compEquivalenceFromModelInverseIso /-
/-- Via the equivalence of categories `equivalence_from_model L W : W.localization ≌ D`,
one may identify the functors `L` and `W.Q`. -/
def compEquivalenceFromModelInverseIso : L ⋙ (equivalenceFromModel L W).inverse ≅ W.Q :=
  calc
    L ⋙ (equivalenceFromModel L W).inverse ≅ _ :=
      isoWhiskerRight (qCompEquivalenceFromModelFunctorIso L W).symm _
    _ ≅ W.Q ⋙ (equivalenceFromModel L W).Functor ⋙ (equivalenceFromModel L W).inverse :=
      (Functor.associator _ _ _)
    _ ≅ W.Q ⋙ 𝟭 _ := (isoWhiskerLeft _ (equivalenceFromModel L W).unitIso.symm)
    _ ≅ W.Q := Functor.rightUnitor _
    
#align category_theory.localization.comp_equivalence_from_model_inverse_iso CategoryTheory.Localization.compEquivalenceFromModelInverseIso
-/

/- warning: category_theory.localization.ess_surj -> CategoryTheory.Localization.essSurj is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} {D : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u1} C] [_inst_2 : CategoryTheory.Category.{u4, u2} D] (L : CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2) (W : CategoryTheory.MorphismProperty.{u3, u1} C _inst_1) [_inst_4 : CategoryTheory.Functor.IsLocalization.{u1, u2, u3, u4} C D _inst_1 _inst_2 L W], CategoryTheory.EssSurj.{u3, u4, u1, u2} C D _inst_1 _inst_2 L
but is expected to have type
  forall {C : Type.{u2}} {D : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u4, u2} C] [_inst_2 : CategoryTheory.Category.{u3, u1} D] (L : CategoryTheory.Functor.{u4, u3, u2, u1} C _inst_1 D _inst_2) (W : CategoryTheory.MorphismProperty.{u4, u2} C _inst_1) [_inst_4 : CategoryTheory.Functor.IsLocalization.{u2, u1, u4, u3} C D _inst_1 _inst_2 L W], CategoryTheory.EssSurj.{u4, u3, u2, u1} C D _inst_1 _inst_2 L
Case conversion may be inaccurate. Consider using '#align category_theory.localization.ess_surj CategoryTheory.Localization.essSurjₓ'. -/
theorem essSurj : EssSurj L :=
  ⟨fun X =>
    ⟨(Construction.objEquiv W).invFun ((equivalenceFromModel L W).inverse.obj X),
      Nonempty.intro
        ((qCompEquivalenceFromModelFunctorIso L W).symm.app _ ≪≫
          (equivalenceFromModel L W).counitIso.app X)⟩⟩
#align category_theory.localization.ess_surj CategoryTheory.Localization.essSurj

#print CategoryTheory.Localization.whiskeringLeftFunctor /-
/-- The functor `(D ⥤ E) ⥤ W.functors_inverting E` induced by the composition
with a localization functor `L : C ⥤ D` with respect to `W : morphism_property C`. -/
def whiskeringLeftFunctor : (D ⥤ E) ⥤ W.FunctorsInverting E :=
  FullSubcategory.lift _ ((whiskeringLeft _ _ E).obj L)
    (MorphismProperty.IsInvertedBy.of_comp W L (inverts L W))
#align category_theory.localization.whiskering_left_functor CategoryTheory.Localization.whiskeringLeftFunctor
-/

instance : IsEquivalence (whiskeringLeftFunctor L W E) :=
  by
  refine'
    is_equivalence.of_iso _
      (is_equivalence.of_equivalence
        ((equivalence.congr_left (equivalence_from_model L W).symm).trans
          (construction.whiskering_left_equivalence W E)))
  refine'
    nat_iso.of_components
      (fun F =>
        eq_to_iso
          (by
            ext
            change (W.Q ⋙ localization.construction.lift L (inverts L W)) ⋙ F = L ⋙ F
            rw [construction.fac]))
      fun F₁ F₂ τ => by
      ext X
      dsimp [equivalence_from_model, whisker_left, construction.whiskering_left_equivalence,
        construction.whiskering_left_equivalence.functor, whiskering_left_functor,
        morphism_property.Q]
      erw [nat_trans.comp_app, nat_trans.comp_app, eq_to_hom_app, eq_to_hom_app, eq_to_hom_refl,
        eq_to_hom_refl, comp_id, id_comp]
      all_goals
        change (W.Q ⋙ localization.construction.lift L (inverts L W)) ⋙ _ = L ⋙ _
        rw [construction.fac]

/- warning: category_theory.localization.functor_equivalence -> CategoryTheory.Localization.functorEquivalence is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} {D : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u1} C] [_inst_2 : CategoryTheory.Category.{u4, u2} D] (L : CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2) (W : CategoryTheory.MorphismProperty.{u3, u1} C _inst_1) (E : Type.{u5}) [_inst_3 : CategoryTheory.Category.{u6, u5} E] [_inst_4 : CategoryTheory.Functor.IsLocalization.{u1, u2, u3, u4} C D _inst_1 _inst_2 L W], CategoryTheory.Equivalence.{max u2 u6, max u1 u6, max u4 u6 u2 u5, max u3 u6 u1 u5} (CategoryTheory.Functor.{u4, u6, u2, u5} D _inst_2 E _inst_3) (CategoryTheory.Functor.category.{u4, u6, u2, u5} D _inst_2 E _inst_3) (CategoryTheory.MorphismProperty.FunctorsInverting.{u3, u1, u5, u6} C _inst_1 W E _inst_3) (CategoryTheory.MorphismProperty.FunctorsInverting.category.{u3, u5, u1, u6} C _inst_1 W E _inst_3)
but is expected to have type
  forall {C : Type.{u1}} {D : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u1} C] [_inst_2 : CategoryTheory.Category.{u4, u2} D] (L : CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2) (W : CategoryTheory.MorphismProperty.{u3, u1} C _inst_1) (E : Type.{u5}) [_inst_3 : CategoryTheory.Category.{u6, u5} E] [_inst_4 : CategoryTheory.Functor.IsLocalization.{u1, u2, u3, u4} C D _inst_1 _inst_2 L W], CategoryTheory.Equivalence.{max u2 u6, max u1 u6, max (max (max u5 u2) u6) u4, max (max (max u1 u3) u6) u5} (CategoryTheory.Functor.{u4, u6, u2, u5} D _inst_2 E _inst_3) (CategoryTheory.MorphismProperty.FunctorsInverting.{u3, u1, u5, u6} C _inst_1 W E _inst_3) (CategoryTheory.Functor.category.{u4, u6, u2, u5} D _inst_2 E _inst_3) (CategoryTheory.MorphismProperty.instCategoryFunctorsInverting.{u3, u1, u5, u6} C _inst_1 W E _inst_3)
Case conversion may be inaccurate. Consider using '#align category_theory.localization.functor_equivalence CategoryTheory.Localization.functorEquivalenceₓ'. -/
/-- The equivalence of categories `(D ⥤ E) ≌ (W.functors_inverting E)` induced by
the composition with a localization functor `L : C ⥤ D` with respect to
`W : morphism_property C`. -/
def functorEquivalence : D ⥤ E ≌ W.FunctorsInverting E :=
  (whiskeringLeftFunctor L W E).asEquivalence
#align category_theory.localization.functor_equivalence CategoryTheory.Localization.functorEquivalence

include W

/- warning: category_theory.localization.whiskering_left_functor' -> CategoryTheory.Localization.whiskeringLeftFunctor' is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} {D : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u1} C] [_inst_2 : CategoryTheory.Category.{u4, u2} D] (L : CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2) (W : CategoryTheory.MorphismProperty.{u3, u1} C _inst_1) (E : Type.{u5}) [_inst_3 : CategoryTheory.Category.{u6, u5} E] [_inst_4 : CategoryTheory.Functor.IsLocalization.{u1, u2, u3, u4} C D _inst_1 _inst_2 L W], CategoryTheory.Functor.{max u2 u6, max u1 u6, max u4 u6 u2 u5, max u3 u6 u1 u5} (CategoryTheory.Functor.{u4, u6, u2, u5} D _inst_2 E _inst_3) (CategoryTheory.Functor.category.{u4, u6, u2, u5} D _inst_2 E _inst_3) (CategoryTheory.Functor.{u3, u6, u1, u5} C _inst_1 E _inst_3) (CategoryTheory.Functor.category.{u3, u6, u1, u5} C _inst_1 E _inst_3)
but is expected to have type
  forall {C : Type.{u1}} {D : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u1} C] [_inst_2 : CategoryTheory.Category.{u4, u2} D], (CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2) -> (CategoryTheory.MorphismProperty.{u3, u1} C _inst_1) -> (forall (E : Type.{u5}) [_inst_3 : CategoryTheory.Category.{u6, u5} E], CategoryTheory.Functor.{max u2 u6, max u1 u6, max (max (max u5 u2) u6) u4, max (max (max u5 u1) u6) u3} (CategoryTheory.Functor.{u4, u6, u2, u5} D _inst_2 E _inst_3) (CategoryTheory.Functor.category.{u4, u6, u2, u5} D _inst_2 E _inst_3) (CategoryTheory.Functor.{u3, u6, u1, u5} C _inst_1 E _inst_3) (CategoryTheory.Functor.category.{u3, u6, u1, u5} C _inst_1 E _inst_3))
Case conversion may be inaccurate. Consider using '#align category_theory.localization.whiskering_left_functor' CategoryTheory.Localization.whiskeringLeftFunctor'ₓ'. -/
/-- The functor `(D ⥤ E) ⥤ (C ⥤ E)` given by the composition with a localization
functor `L : C ⥤ D` with respect to `W : morphism_property C`. -/
@[nolint unused_arguments]
def whiskeringLeftFunctor' : (D ⥤ E) ⥤ C ⥤ E :=
  (whiskeringLeft C D E).obj L
#align category_theory.localization.whiskering_left_functor' CategoryTheory.Localization.whiskeringLeftFunctor'

/- warning: category_theory.localization.whiskering_left_functor'_eq -> CategoryTheory.Localization.whiskeringLeftFunctor'_eq is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} {D : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u1} C] [_inst_2 : CategoryTheory.Category.{u4, u2} D] (L : CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2) (W : CategoryTheory.MorphismProperty.{u3, u1} C _inst_1) (E : Type.{u5}) [_inst_3 : CategoryTheory.Category.{u6, u5} E] [_inst_4 : CategoryTheory.Functor.IsLocalization.{u1, u2, u3, u4} C D _inst_1 _inst_2 L W], Eq.{succ (max (max u2 u6) (max u1 u6) (max u4 u6 u2 u5) u3 u6 u1 u5)} (CategoryTheory.Functor.{max u2 u6, max u1 u6, max u4 u6 u2 u5, max u3 u6 u1 u5} (CategoryTheory.Functor.{u4, u6, u2, u5} D _inst_2 E _inst_3) (CategoryTheory.Functor.category.{u4, u6, u2, u5} D _inst_2 E _inst_3) (CategoryTheory.Functor.{u3, u6, u1, u5} C _inst_1 E _inst_3) (CategoryTheory.Functor.category.{u3, u6, u1, u5} C _inst_1 E _inst_3)) (CategoryTheory.Localization.whiskeringLeftFunctor'.{u1, u2, u3, u4, u5, u6} C D _inst_1 _inst_2 L W E _inst_3 _inst_4) (CategoryTheory.Functor.comp.{max u2 u6, max u1 u6, max u1 u6, max u4 u6 u2 u5, max u3 u6 u1 u5, max u3 u6 u1 u5} (CategoryTheory.Functor.{u4, u6, u2, u5} D _inst_2 E _inst_3) (CategoryTheory.Functor.category.{u4, u6, u2, u5} D _inst_2 E _inst_3) (CategoryTheory.MorphismProperty.FunctorsInverting.{u3, u1, u5, u6} C _inst_1 W E _inst_3) (CategoryTheory.MorphismProperty.FunctorsInverting.category.{u3, u5, u1, u6} C _inst_1 W E _inst_3) (CategoryTheory.Functor.{u3, u6, u1, u5} C _inst_1 E _inst_3) (CategoryTheory.Functor.category.{u3, u6, u1, u5} C _inst_1 E _inst_3) (CategoryTheory.Localization.whiskeringLeftFunctor.{u1, u2, u3, u4, u5, u6} C D _inst_1 _inst_2 L W E _inst_3 _inst_4) (CategoryTheory.inducedFunctor.{max u1 u6, max u3 u6 u1 u5, max u3 u6 u1 u5} (CategoryTheory.FullSubcategoryₓ.{max u1 u6, max u3 u6 u1 u5} (CategoryTheory.Functor.{u3, u6, u1, u5} C _inst_1 E _inst_3) (CategoryTheory.Functor.category.{u3, u6, u1, u5} C _inst_1 E _inst_3) (fun (F : CategoryTheory.Functor.{u3, u6, u1, u5} C _inst_1 E _inst_3) => CategoryTheory.MorphismProperty.IsInvertedBy.{u3, u1, u5, u6} C _inst_1 E _inst_3 W F)) (CategoryTheory.Functor.{u3, u6, u1, u5} C _inst_1 E _inst_3) (CategoryTheory.Functor.category.{u3, u6, u1, u5} C _inst_1 E _inst_3) (CategoryTheory.FullSubcategoryₓ.obj.{max u1 u6, max u3 u6 u1 u5} (CategoryTheory.Functor.{u3, u6, u1, u5} C _inst_1 E _inst_3) (CategoryTheory.Functor.category.{u3, u6, u1, u5} C _inst_1 E _inst_3) (CategoryTheory.MorphismProperty.IsInvertedBy.{u3, u1, u5, u6} C _inst_1 E _inst_3 W))))
but is expected to have type
  forall {C : Type.{u6}} {D : Type.{u5}} [_inst_1 : CategoryTheory.Category.{u4, u6} C] [_inst_2 : CategoryTheory.Category.{u3, u5} D] (L : CategoryTheory.Functor.{u4, u3, u6, u5} C _inst_1 D _inst_2) (W : CategoryTheory.MorphismProperty.{u4, u6} C _inst_1) (E : Type.{u2}) [_inst_3 : CategoryTheory.Category.{u1, u2} E] [_inst_4 : CategoryTheory.Functor.IsLocalization.{u6, u5, u4, u3} C D _inst_1 _inst_2 L W], Eq.{max (max (max (max (max (succ u6) (succ u5)) (succ u4)) (succ u3)) (succ u2)) (succ u1)} (CategoryTheory.Functor.{max u5 u1, max u6 u1, max (max (max u2 u5) u1) u3, max (max (max u2 u6) u1) u4} (CategoryTheory.Functor.{u3, u1, u5, u2} D _inst_2 E _inst_3) (CategoryTheory.Functor.category.{u3, u1, u5, u2} D _inst_2 E _inst_3) (CategoryTheory.Functor.{u4, u1, u6, u2} C _inst_1 E _inst_3) (CategoryTheory.Functor.category.{u4, u1, u6, u2} C _inst_1 E _inst_3)) (CategoryTheory.Localization.whiskeringLeftFunctor'.{u6, u5, u4, u3, u2, u1} C D _inst_1 _inst_2 L W E _inst_3) (CategoryTheory.Functor.comp.{max u5 u1, max u6 u1, max u6 u1, max (max (max u5 u3) u2) u1, max (max (max u6 u4) u2) u1, max (max (max u6 u4) u2) u1} (CategoryTheory.Functor.{u3, u1, u5, u2} D _inst_2 E _inst_3) (CategoryTheory.Functor.category.{u3, u1, u5, u2} D _inst_2 E _inst_3) (CategoryTheory.MorphismProperty.FunctorsInverting.{u4, u6, u2, u1} C _inst_1 W E _inst_3) (CategoryTheory.MorphismProperty.instCategoryFunctorsInverting.{u4, u6, u2, u1} C _inst_1 W E _inst_3) (CategoryTheory.Functor.{u4, u1, u6, u2} C _inst_1 E _inst_3) (CategoryTheory.Functor.category.{u4, u1, u6, u2} C _inst_1 E _inst_3) (CategoryTheory.Localization.whiskeringLeftFunctor.{u6, u5, u4, u3, u2, u1} C D _inst_1 _inst_2 L W E _inst_3 _inst_4) (CategoryTheory.inducedFunctor.{max u6 u1, max (max (max u6 u4) u2) u1, max (max (max u6 u4) u2) u1} (CategoryTheory.FullSubcategory.{max (max (max u6 u4) u2) u1} (CategoryTheory.Functor.{u4, u1, u6, u2} C _inst_1 E _inst_3) (fun (F : CategoryTheory.Functor.{u4, u1, u6, u2} C _inst_1 E _inst_3) => CategoryTheory.MorphismProperty.IsInvertedBy.{u4, u6, u2, u1} C _inst_1 E _inst_3 W F)) (CategoryTheory.Functor.{u4, u1, u6, u2} C _inst_1 E _inst_3) (CategoryTheory.Functor.category.{u4, u1, u6, u2} C _inst_1 E _inst_3) (CategoryTheory.FullSubcategory.obj.{max (max (max u6 u4) u2) u1} (CategoryTheory.Functor.{u4, u1, u6, u2} C _inst_1 E _inst_3) (fun (F : CategoryTheory.Functor.{u4, u1, u6, u2} C _inst_1 E _inst_3) => CategoryTheory.MorphismProperty.IsInvertedBy.{u4, u6, u2, u1} C _inst_1 E _inst_3 W F))))
Case conversion may be inaccurate. Consider using '#align category_theory.localization.whiskering_left_functor'_eq CategoryTheory.Localization.whiskeringLeftFunctor'_eqₓ'. -/
theorem whiskeringLeftFunctor'_eq :
    whiskeringLeftFunctor' L W E = Localization.whiskeringLeftFunctor L W E ⋙ inducedFunctor _ :=
  rfl
#align category_theory.localization.whiskering_left_functor'_eq CategoryTheory.Localization.whiskeringLeftFunctor'_eq

variable {E}

/- warning: category_theory.localization.whiskering_left_functor'_obj -> CategoryTheory.Localization.whiskeringLeftFunctor'_obj is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} {D : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u1} C] [_inst_2 : CategoryTheory.Category.{u4, u2} D] (L : CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2) (W : CategoryTheory.MorphismProperty.{u3, u1} C _inst_1) {E : Type.{u5}} [_inst_3 : CategoryTheory.Category.{u6, u5} E] [_inst_4 : CategoryTheory.Functor.IsLocalization.{u1, u2, u3, u4} C D _inst_1 _inst_2 L W] (F : CategoryTheory.Functor.{u4, u6, u2, u5} D _inst_2 E _inst_3), Eq.{succ (max u3 u6 u1 u5)} (CategoryTheory.Functor.{u3, u6, u1, u5} C _inst_1 E _inst_3) (CategoryTheory.Functor.obj.{max u2 u6, max u1 u6, max u4 u6 u2 u5, max u3 u6 u1 u5} (CategoryTheory.Functor.{u4, u6, u2, u5} D _inst_2 E _inst_3) (CategoryTheory.Functor.category.{u4, u6, u2, u5} D _inst_2 E _inst_3) (CategoryTheory.Functor.{u3, u6, u1, u5} C _inst_1 E _inst_3) (CategoryTheory.Functor.category.{u3, u6, u1, u5} C _inst_1 E _inst_3) (CategoryTheory.Localization.whiskeringLeftFunctor'.{u1, u2, u3, u4, u5, u6} C D _inst_1 _inst_2 L W E _inst_3 _inst_4) F) (CategoryTheory.Functor.comp.{u3, u4, u6, u1, u2, u5} C _inst_1 D _inst_2 E _inst_3 L F)
but is expected to have type
  forall {C : Type.{u2}} {D : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Category.{u6, u4} D] (L : CategoryTheory.Functor.{u1, u6, u2, u4} C _inst_1 D _inst_2) (W : CategoryTheory.MorphismProperty.{u1, u2} C _inst_1) {E : Type.{u3}} [_inst_3 : CategoryTheory.Category.{u5, u3} E] (_inst_4 : CategoryTheory.Functor.{u6, u5, u4, u3} D _inst_2 E _inst_3), Eq.{max (max (max (succ u2) (succ u1)) (succ u3)) (succ u5)} (CategoryTheory.Functor.{u1, u5, u2, u3} C _inst_1 E _inst_3) (Prefunctor.obj.{max (succ u4) (succ u5), max (succ u2) (succ u5), max (max (max u4 u6) u3) u5, max (max (max u2 u1) u3) u5} (CategoryTheory.Functor.{u6, u5, u4, u3} D _inst_2 E _inst_3) (CategoryTheory.CategoryStruct.toQuiver.{max u4 u5, max (max (max u4 u6) u3) u5} (CategoryTheory.Functor.{u6, u5, u4, u3} D _inst_2 E _inst_3) (CategoryTheory.Category.toCategoryStruct.{max u4 u5, max (max (max u4 u6) u3) u5} (CategoryTheory.Functor.{u6, u5, u4, u3} D _inst_2 E _inst_3) (CategoryTheory.Functor.category.{u6, u5, u4, u3} D _inst_2 E _inst_3))) (CategoryTheory.Functor.{u1, u5, u2, u3} C _inst_1 E _inst_3) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u5, max (max (max u2 u1) u3) u5} (CategoryTheory.Functor.{u1, u5, u2, u3} C _inst_1 E _inst_3) (CategoryTheory.Category.toCategoryStruct.{max u2 u5, max (max (max u2 u1) u3) u5} (CategoryTheory.Functor.{u1, u5, u2, u3} C _inst_1 E _inst_3) (CategoryTheory.Functor.category.{u1, u5, u2, u3} C _inst_1 E _inst_3))) (CategoryTheory.Functor.toPrefunctor.{max u4 u5, max u2 u5, max (max (max u4 u6) u3) u5, max (max (max u2 u1) u3) u5} (CategoryTheory.Functor.{u6, u5, u4, u3} D _inst_2 E _inst_3) (CategoryTheory.Functor.category.{u6, u5, u4, u3} D _inst_2 E _inst_3) (CategoryTheory.Functor.{u1, u5, u2, u3} C _inst_1 E _inst_3) (CategoryTheory.Functor.category.{u1, u5, u2, u3} C _inst_1 E _inst_3) (CategoryTheory.Localization.whiskeringLeftFunctor'.{u2, u4, u1, u6, u3, u5} C D _inst_1 _inst_2 L W E _inst_3)) _inst_4) (CategoryTheory.Functor.comp.{u1, u6, u5, u2, u4, u3} C _inst_1 D _inst_2 E _inst_3 L _inst_4)
Case conversion may be inaccurate. Consider using '#align category_theory.localization.whiskering_left_functor'_obj CategoryTheory.Localization.whiskeringLeftFunctor'_objₓ'. -/
@[simp]
theorem whiskeringLeftFunctor'_obj (F : D ⥤ E) : (whiskeringLeftFunctor' L W E).obj F = L ⋙ F :=
  rfl
#align category_theory.localization.whiskering_left_functor'_obj CategoryTheory.Localization.whiskeringLeftFunctor'_obj

instance : Full (whiskeringLeftFunctor' L W E) := by rw [whiskering_left_functor'_eq];
  infer_instance

instance : Faithful (whiskeringLeftFunctor' L W E) := by rw [whiskering_left_functor'_eq];
  infer_instance

/- warning: category_theory.localization.nat_trans_ext -> CategoryTheory.Localization.natTrans_ext is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} {D : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u1} C] [_inst_2 : CategoryTheory.Category.{u4, u2} D] (L : CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2) (W : CategoryTheory.MorphismProperty.{u3, u1} C _inst_1) {E : Type.{u5}} [_inst_3 : CategoryTheory.Category.{u6, u5} E] [_inst_4 : CategoryTheory.Functor.IsLocalization.{u1, u2, u3, u4} C D _inst_1 _inst_2 L W] {F₁ : CategoryTheory.Functor.{u4, u6, u2, u5} D _inst_2 E _inst_3} {F₂ : CategoryTheory.Functor.{u4, u6, u2, u5} D _inst_2 E _inst_3} (τ : Quiver.Hom.{succ (max u2 u6), max u4 u6 u2 u5} (CategoryTheory.Functor.{u4, u6, u2, u5} D _inst_2 E _inst_3) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u6, max u4 u6 u2 u5} (CategoryTheory.Functor.{u4, u6, u2, u5} D _inst_2 E _inst_3) (CategoryTheory.Category.toCategoryStruct.{max u2 u6, max u4 u6 u2 u5} (CategoryTheory.Functor.{u4, u6, u2, u5} D _inst_2 E _inst_3) (CategoryTheory.Functor.category.{u4, u6, u2, u5} D _inst_2 E _inst_3))) F₁ F₂) (τ' : Quiver.Hom.{succ (max u2 u6), max u4 u6 u2 u5} (CategoryTheory.Functor.{u4, u6, u2, u5} D _inst_2 E _inst_3) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u6, max u4 u6 u2 u5} (CategoryTheory.Functor.{u4, u6, u2, u5} D _inst_2 E _inst_3) (CategoryTheory.Category.toCategoryStruct.{max u2 u6, max u4 u6 u2 u5} (CategoryTheory.Functor.{u4, u6, u2, u5} D _inst_2 E _inst_3) (CategoryTheory.Functor.category.{u4, u6, u2, u5} D _inst_2 E _inst_3))) F₁ F₂), (forall (X : C), Eq.{succ u6} (Quiver.Hom.{succ u6, u5} E (CategoryTheory.CategoryStruct.toQuiver.{u6, u5} E (CategoryTheory.Category.toCategoryStruct.{u6, u5} E _inst_3)) (CategoryTheory.Functor.obj.{u4, u6, u2, u5} D _inst_2 E _inst_3 F₁ (CategoryTheory.Functor.obj.{u3, u4, u1, u2} C _inst_1 D _inst_2 L X)) (CategoryTheory.Functor.obj.{u4, u6, u2, u5} D _inst_2 E _inst_3 F₂ (CategoryTheory.Functor.obj.{u3, u4, u1, u2} C _inst_1 D _inst_2 L X))) (CategoryTheory.NatTrans.app.{u4, u6, u2, u5} D _inst_2 E _inst_3 F₁ F₂ τ (CategoryTheory.Functor.obj.{u3, u4, u1, u2} C _inst_1 D _inst_2 L X)) (CategoryTheory.NatTrans.app.{u4, u6, u2, u5} D _inst_2 E _inst_3 F₁ F₂ τ' (CategoryTheory.Functor.obj.{u3, u4, u1, u2} C _inst_1 D _inst_2 L X))) -> (Eq.{succ (max u2 u6)} (Quiver.Hom.{succ (max u2 u6), max u4 u6 u2 u5} (CategoryTheory.Functor.{u4, u6, u2, u5} D _inst_2 E _inst_3) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u6, max u4 u6 u2 u5} (CategoryTheory.Functor.{u4, u6, u2, u5} D _inst_2 E _inst_3) (CategoryTheory.Category.toCategoryStruct.{max u2 u6, max u4 u6 u2 u5} (CategoryTheory.Functor.{u4, u6, u2, u5} D _inst_2 E _inst_3) (CategoryTheory.Functor.category.{u4, u6, u2, u5} D _inst_2 E _inst_3))) F₁ F₂) τ τ')
but is expected to have type
  forall {C : Type.{u1}} {D : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u2, u1} C] [_inst_2 : CategoryTheory.Category.{u6, u4} D] (L : CategoryTheory.Functor.{u2, u6, u1, u4} C _inst_1 D _inst_2) (W : CategoryTheory.MorphismProperty.{u2, u1} C _inst_1) {E : Type.{u3}} [_inst_3 : CategoryTheory.Category.{u5, u3} E] [_inst_4 : CategoryTheory.Functor.IsLocalization.{u1, u4, u2, u6} C D _inst_1 _inst_2 L W] {F₁ : CategoryTheory.Functor.{u6, u5, u4, u3} D _inst_2 E _inst_3} {F₂ : CategoryTheory.Functor.{u6, u5, u4, u3} D _inst_2 E _inst_3} (τ : Quiver.Hom.{max (succ u4) (succ u5), max (max (max u4 u6) u3) u5} (CategoryTheory.Functor.{u6, u5, u4, u3} D _inst_2 E _inst_3) (CategoryTheory.CategoryStruct.toQuiver.{max u4 u5, max (max (max u4 u6) u3) u5} (CategoryTheory.Functor.{u6, u5, u4, u3} D _inst_2 E _inst_3) (CategoryTheory.Category.toCategoryStruct.{max u4 u5, max (max (max u4 u6) u3) u5} (CategoryTheory.Functor.{u6, u5, u4, u3} D _inst_2 E _inst_3) (CategoryTheory.Functor.category.{u6, u5, u4, u3} D _inst_2 E _inst_3))) F₁ F₂) (τ' : Quiver.Hom.{max (succ u4) (succ u5), max (max (max u4 u6) u3) u5} (CategoryTheory.Functor.{u6, u5, u4, u3} D _inst_2 E _inst_3) (CategoryTheory.CategoryStruct.toQuiver.{max u4 u5, max (max (max u4 u6) u3) u5} (CategoryTheory.Functor.{u6, u5, u4, u3} D _inst_2 E _inst_3) (CategoryTheory.Category.toCategoryStruct.{max u4 u5, max (max (max u4 u6) u3) u5} (CategoryTheory.Functor.{u6, u5, u4, u3} D _inst_2 E _inst_3) (CategoryTheory.Functor.category.{u6, u5, u4, u3} D _inst_2 E _inst_3))) F₁ F₂), (forall (X : C), Eq.{succ u5} (Quiver.Hom.{succ u5, u3} E (CategoryTheory.CategoryStruct.toQuiver.{u5, u3} E (CategoryTheory.Category.toCategoryStruct.{u5, u3} E _inst_3)) (Prefunctor.obj.{succ u6, succ u5, u4, u3} D (CategoryTheory.CategoryStruct.toQuiver.{u6, u4} D (CategoryTheory.Category.toCategoryStruct.{u6, u4} D _inst_2)) E (CategoryTheory.CategoryStruct.toQuiver.{u5, u3} E (CategoryTheory.Category.toCategoryStruct.{u5, u3} E _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u6, u5, u4, u3} D _inst_2 E _inst_3 F₁) (Prefunctor.obj.{succ u2, succ u6, u1, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u6, u4} D (CategoryTheory.Category.toCategoryStruct.{u6, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u2, u6, u1, u4} C _inst_1 D _inst_2 L) X)) (Prefunctor.obj.{succ u6, succ u5, u4, u3} D (CategoryTheory.CategoryStruct.toQuiver.{u6, u4} D (CategoryTheory.Category.toCategoryStruct.{u6, u4} D _inst_2)) E (CategoryTheory.CategoryStruct.toQuiver.{u5, u3} E (CategoryTheory.Category.toCategoryStruct.{u5, u3} E _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u6, u5, u4, u3} D _inst_2 E _inst_3 F₂) (Prefunctor.obj.{succ u2, succ u6, u1, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u6, u4} D (CategoryTheory.Category.toCategoryStruct.{u6, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u2, u6, u1, u4} C _inst_1 D _inst_2 L) X))) (CategoryTheory.NatTrans.app.{u6, u5, u4, u3} D _inst_2 E _inst_3 F₁ F₂ τ (Prefunctor.obj.{succ u2, succ u6, u1, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u6, u4} D (CategoryTheory.Category.toCategoryStruct.{u6, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u2, u6, u1, u4} C _inst_1 D _inst_2 L) X)) (CategoryTheory.NatTrans.app.{u6, u5, u4, u3} D _inst_2 E _inst_3 F₁ F₂ τ' (Prefunctor.obj.{succ u2, succ u6, u1, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u6, u4} D (CategoryTheory.Category.toCategoryStruct.{u6, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u2, u6, u1, u4} C _inst_1 D _inst_2 L) X))) -> (Eq.{max (succ u4) (succ u5)} (Quiver.Hom.{max (succ u4) (succ u5), max (max (max u4 u6) u3) u5} (CategoryTheory.Functor.{u6, u5, u4, u3} D _inst_2 E _inst_3) (CategoryTheory.CategoryStruct.toQuiver.{max u4 u5, max (max (max u4 u6) u3) u5} (CategoryTheory.Functor.{u6, u5, u4, u3} D _inst_2 E _inst_3) (CategoryTheory.Category.toCategoryStruct.{max u4 u5, max (max (max u4 u6) u3) u5} (CategoryTheory.Functor.{u6, u5, u4, u3} D _inst_2 E _inst_3) (CategoryTheory.Functor.category.{u6, u5, u4, u3} D _inst_2 E _inst_3))) F₁ F₂) τ τ')
Case conversion may be inaccurate. Consider using '#align category_theory.localization.nat_trans_ext CategoryTheory.Localization.natTrans_extₓ'. -/
theorem natTrans_ext {F₁ F₂ : D ⥤ E} (τ τ' : F₁ ⟶ F₂)
    (h : ∀ X : C, τ.app (L.obj X) = τ'.app (L.obj X)) : τ = τ' :=
  by
  haveI : CategoryTheory.EssSurj L := ess_surj L W
  ext Y
  rw [← cancel_epi (F₁.map (L.obj_obj_preimage_iso Y).Hom), τ.naturality, τ'.naturality, h]
#align category_theory.localization.nat_trans_ext CategoryTheory.Localization.natTrans_ext

/- warning: category_theory.localization.lifting -> CategoryTheory.Localization.Lifting is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} {D : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u1} C] [_inst_2 : CategoryTheory.Category.{u4, u2} D] (L : CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2) (W : CategoryTheory.MorphismProperty.{u3, u1} C _inst_1) {E : Type.{u5}} [_inst_3 : CategoryTheory.Category.{u6, u5} E] [_inst_4 : CategoryTheory.Functor.IsLocalization.{u1, u2, u3, u4} C D _inst_1 _inst_2 L W], (CategoryTheory.Functor.{u3, u6, u1, u5} C _inst_1 E _inst_3) -> (CategoryTheory.Functor.{u4, u6, u2, u5} D _inst_2 E _inst_3) -> Sort.{max (succ u1) (succ u6)}
but is expected to have type
  forall {C : Type.{u1}} {D : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u1} C] [_inst_2 : CategoryTheory.Category.{u4, u2} D], (CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2) -> (forall {W : Type.{u5}} [E : CategoryTheory.Category.{u6, u5} W], (CategoryTheory.MorphismProperty.{u3, u1} C _inst_1) -> (CategoryTheory.Functor.{u3, u6, u1, u5} C _inst_1 W E) -> (CategoryTheory.Functor.{u4, u6, u2, u5} D _inst_2 W E) -> Sort.{max (succ u1) (succ u6)})
Case conversion may be inaccurate. Consider using '#align category_theory.localization.lifting CategoryTheory.Localization.Liftingₓ'. -/
/- ./././Mathport/Syntax/Translate/Command.lean:393:30: infer kinds are unsupported in Lean 4: #[`Iso] [] -/
/-- When `L : C ⥤ D` is a localization functor for `W : morphism_property C` and
`F : C ⥤ E` is a functor, we shall say that `F' : D ⥤ E` lifts `F` if the obvious diagram
is commutative up to an isomorphism. -/
class Lifting (F : C ⥤ E) (F' : D ⥤ E) where
  Iso : L ⋙ F' ≅ F
#align category_theory.localization.lifting CategoryTheory.Localization.Lifting

variable {W}

#print CategoryTheory.Localization.lift /-
/-- Given a localization functor `L : C ⥤ D` for `W : morphism_property C` and
a functor `F : C ⥤ E` which inverts `W`, this is a choice of functor
`D ⥤ E` which lifts `F`. -/
def lift (F : C ⥤ E) (hF : W.IsInvertedBy F) (L : C ⥤ D) [hL : L.IsLocalization W] : D ⥤ E :=
  (functorEquivalence L W E).inverse.obj ⟨F, hF⟩
#align category_theory.localization.lift CategoryTheory.Localization.lift
-/

#print CategoryTheory.Localization.liftingLift /-
instance liftingLift (F : C ⥤ E) (hF : W.IsInvertedBy F) (L : C ⥤ D) [hL : L.IsLocalization W] :
    Lifting L W F (lift F hF L) :=
  ⟨(inducedFunctor _).mapIso ((functorEquivalence L W E).counitIso.app ⟨F, hF⟩)⟩
#align category_theory.localization.lifting_lift CategoryTheory.Localization.liftingLift
-/

#print CategoryTheory.Localization.fac /-
/-- The canonical isomorphism `L ⋙ lift F hF L ≅ F` for any functor `F : C ⥤ E`
which inverts `W`, when `L : C ⥤ D` is a localization functor for `W`. -/
@[simps]
def fac (F : C ⥤ E) (hF : W.IsInvertedBy F) (L : C ⥤ D) [hL : L.IsLocalization W] :
    L ⋙ lift F hF L ≅ F :=
  Lifting.iso _ W _ _
#align category_theory.localization.fac CategoryTheory.Localization.fac
-/

#print CategoryTheory.Localization.liftingConstructionLift /-
instance liftingConstructionLift (F : C ⥤ D) (hF : W.IsInvertedBy F) :
    Lifting W.Q W F (Construction.lift F hF) :=
  ⟨eqToIso (Construction.fac F hF)⟩
#align category_theory.localization.lifting_construction_lift CategoryTheory.Localization.liftingConstructionLift
-/

variable (W)

#print CategoryTheory.Localization.liftNatTrans /-
/-- Given a localization functor `L : C ⥤ D` for `W : morphism_property C`,
if `(F₁' F₂' : D ⥤ E)` are functors which lifts functors `(F₁ F₂ : C ⥤ E)`,
a natural transformation `τ : F₁ ⟶ F₂` uniquely lifts to a natural transformation `F₁' ⟶ F₂'`. -/
def liftNatTrans (F₁ F₂ : C ⥤ E) (F₁' F₂' : D ⥤ E) [Lifting L W F₁ F₁'] [h₂ : Lifting L W F₂ F₂']
    (τ : F₁ ⟶ F₂) : F₁' ⟶ F₂' :=
  (whiskeringLeftFunctor' L W E).preimage
    ((Lifting.iso L W F₁ F₁').Hom ≫ τ ≫ (Lifting.iso L W F₂ F₂').inv)
#align category_theory.localization.lift_nat_trans CategoryTheory.Localization.liftNatTrans
-/

/- warning: category_theory.localization.lift_nat_trans_app -> CategoryTheory.Localization.liftNatTrans_app is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.localization.lift_nat_trans_app CategoryTheory.Localization.liftNatTrans_appₓ'. -/
@[simp]
theorem liftNatTrans_app (F₁ F₂ : C ⥤ E) (F₁' F₂' : D ⥤ E) [Lifting L W F₁ F₁'] [Lifting L W F₂ F₂']
    (τ : F₁ ⟶ F₂) (X : C) :
    (liftNatTrans L W F₁ F₂ F₁' F₂' τ).app (L.obj X) =
      (Lifting.iso L W F₁ F₁').Hom.app X ≫ τ.app X ≫ (Lifting.iso L W F₂ F₂').inv.app X :=
  congr_app (Functor.image_preimage (whiskeringLeftFunctor' L W E) _) X
#align category_theory.localization.lift_nat_trans_app CategoryTheory.Localization.liftNatTrans_app

/- warning: category_theory.localization.comp_lift_nat_trans -> CategoryTheory.Localization.comp_liftNatTrans is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.localization.comp_lift_nat_trans CategoryTheory.Localization.comp_liftNatTransₓ'. -/
@[simp, reassoc]
theorem comp_liftNatTrans (F₁ F₂ F₃ : C ⥤ E) (F₁' F₂' F₃' : D ⥤ E) [h₁ : Lifting L W F₁ F₁']
    [h₂ : Lifting L W F₂ F₂'] [h₃ : Lifting L W F₃ F₃'] (τ : F₁ ⟶ F₂) (τ' : F₂ ⟶ F₃) :
    liftNatTrans L W F₁ F₂ F₁' F₂' τ ≫ liftNatTrans L W F₂ F₃ F₂' F₃' τ' =
      liftNatTrans L W F₁ F₃ F₁' F₃' (τ ≫ τ') :=
  natTrans_ext L W _ _ fun X => by
    simp only [nat_trans.comp_app, lift_nat_trans_app, assoc, iso.inv_hom_id_app_assoc]
#align category_theory.localization.comp_lift_nat_trans CategoryTheory.Localization.comp_liftNatTrans

/- warning: category_theory.localization.lift_nat_trans_id -> CategoryTheory.Localization.liftNatTrans_id is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} {D : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u1} C] [_inst_2 : CategoryTheory.Category.{u4, u2} D] (L : CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2) (W : CategoryTheory.MorphismProperty.{u3, u1} C _inst_1) {E : Type.{u5}} [_inst_3 : CategoryTheory.Category.{u6, u5} E] [_inst_4 : CategoryTheory.Functor.IsLocalization.{u1, u2, u3, u4} C D _inst_1 _inst_2 L W] (F : CategoryTheory.Functor.{u3, u6, u1, u5} C _inst_1 E _inst_3) (F' : CategoryTheory.Functor.{u4, u6, u2, u5} D _inst_2 E _inst_3) [h : CategoryTheory.Localization.Lifting.{u1, u2, u3, u4, u5, u6} C D _inst_1 _inst_2 L W E _inst_3 _inst_4 F F'], Eq.{succ (max u2 u6)} (Quiver.Hom.{succ (max u2 u6), max u4 u6 u2 u5} (CategoryTheory.Functor.{u4, u6, u2, u5} D _inst_2 E _inst_3) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u6, max u4 u6 u2 u5} (CategoryTheory.Functor.{u4, u6, u2, u5} D _inst_2 E _inst_3) (CategoryTheory.Category.toCategoryStruct.{max u2 u6, max u4 u6 u2 u5} (CategoryTheory.Functor.{u4, u6, u2, u5} D _inst_2 E _inst_3) (CategoryTheory.Functor.category.{u4, u6, u2, u5} D _inst_2 E _inst_3))) F' F') (CategoryTheory.Localization.liftNatTrans.{u1, u2, u3, u4, u5, u6} C D _inst_1 _inst_2 L W E _inst_3 _inst_4 F F F' F' h h (CategoryTheory.CategoryStruct.id.{max u1 u6, max u3 u6 u1 u5} (CategoryTheory.Functor.{u3, u6, u1, u5} C _inst_1 E _inst_3) (CategoryTheory.Category.toCategoryStruct.{max u1 u6, max u3 u6 u1 u5} (CategoryTheory.Functor.{u3, u6, u1, u5} C _inst_1 E _inst_3) (CategoryTheory.Functor.category.{u3, u6, u1, u5} C _inst_1 E _inst_3)) F)) (CategoryTheory.CategoryStruct.id.{max u2 u6, max u4 u6 u2 u5} (CategoryTheory.Functor.{u4, u6, u2, u5} D _inst_2 E _inst_3) (CategoryTheory.Category.toCategoryStruct.{max u2 u6, max u4 u6 u2 u5} (CategoryTheory.Functor.{u4, u6, u2, u5} D _inst_2 E _inst_3) (CategoryTheory.Functor.category.{u4, u6, u2, u5} D _inst_2 E _inst_3)) F')
but is expected to have type
  forall {C : Type.{u4}} {D : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u6, u4} C] [_inst_2 : CategoryTheory.Category.{u2, u1} D] (L : CategoryTheory.Functor.{u6, u2, u4, u1} C _inst_1 D _inst_2) (W : CategoryTheory.MorphismProperty.{u6, u4} C _inst_1) {E : Type.{u3}} [_inst_3 : CategoryTheory.Category.{u5, u3} E] [_inst_4 : CategoryTheory.Functor.IsLocalization.{u4, u1, u6, u2} C D _inst_1 _inst_2 L W] (F : CategoryTheory.Functor.{u6, u5, u4, u3} C _inst_1 E _inst_3) (F' : CategoryTheory.Functor.{u2, u5, u1, u3} D _inst_2 E _inst_3) [h : CategoryTheory.Localization.Lifting.{u4, u1, u6, u2, u3, u5} C D _inst_1 _inst_2 L E _inst_3 W F F'], Eq.{max (succ u1) (succ u5)} (Quiver.Hom.{max (succ u1) (succ u5), max (max (max u1 u2) u3) u5} (CategoryTheory.Functor.{u2, u5, u1, u3} D _inst_2 E _inst_3) (CategoryTheory.CategoryStruct.toQuiver.{max u1 u5, max (max (max u1 u2) u3) u5} (CategoryTheory.Functor.{u2, u5, u1, u3} D _inst_2 E _inst_3) (CategoryTheory.Category.toCategoryStruct.{max u1 u5, max (max (max u1 u2) u3) u5} (CategoryTheory.Functor.{u2, u5, u1, u3} D _inst_2 E _inst_3) (CategoryTheory.Functor.category.{u2, u5, u1, u3} D _inst_2 E _inst_3))) F' F') (CategoryTheory.Localization.liftNatTrans.{u4, u1, u6, u2, u3, u5} C D _inst_1 _inst_2 L W E _inst_3 _inst_4 F F F' F' h h (CategoryTheory.CategoryStruct.id.{max u4 u5, max (max (max u4 u6) u3) u5} (CategoryTheory.Functor.{u6, u5, u4, u3} C _inst_1 E _inst_3) (CategoryTheory.Category.toCategoryStruct.{max u4 u5, max (max (max u4 u6) u3) u5} (CategoryTheory.Functor.{u6, u5, u4, u3} C _inst_1 E _inst_3) (CategoryTheory.Functor.category.{u6, u5, u4, u3} C _inst_1 E _inst_3)) F)) (CategoryTheory.CategoryStruct.id.{max u1 u5, max (max (max u1 u2) u3) u5} (CategoryTheory.Functor.{u2, u5, u1, u3} D _inst_2 E _inst_3) (CategoryTheory.Category.toCategoryStruct.{max u1 u5, max (max (max u1 u2) u3) u5} (CategoryTheory.Functor.{u2, u5, u1, u3} D _inst_2 E _inst_3) (CategoryTheory.Functor.category.{u2, u5, u1, u3} D _inst_2 E _inst_3)) F')
Case conversion may be inaccurate. Consider using '#align category_theory.localization.lift_nat_trans_id CategoryTheory.Localization.liftNatTrans_idₓ'. -/
@[simp]
theorem liftNatTrans_id (F : C ⥤ E) (F' : D ⥤ E) [h : Lifting L W F F'] :
    liftNatTrans L W F F F' F' (𝟙 F) = 𝟙 F' :=
  natTrans_ext L W _ _ fun X => by
    simpa only [lift_nat_trans_app, nat_trans.id_app, id_comp, iso.hom_inv_id_app]
#align category_theory.localization.lift_nat_trans_id CategoryTheory.Localization.liftNatTrans_id

#print CategoryTheory.Localization.liftNatIso /-
/-- Given a localization functor `L : C ⥤ D` for `W : morphism_property C`,
if `(F₁' F₂' : D ⥤ E)` are functors which lifts functors `(F₁ F₂ : C ⥤ E)`,
a natural isomorphism `τ : F₁ ⟶ F₂` lifts to a natural isomorphism `F₁' ⟶ F₂'`. -/
@[simps]
def liftNatIso (F₁ F₂ : C ⥤ E) (F₁' F₂' : D ⥤ E) [h₁ : Lifting L W F₁ F₁'] [h₂ : Lifting L W F₂ F₂']
    (e : F₁ ≅ F₂) : F₁' ≅ F₂'
    where
  Hom := liftNatTrans L W F₁ F₂ F₁' F₂' e.Hom
  inv := liftNatTrans L W F₂ F₁ F₂' F₁' e.inv
#align category_theory.localization.lift_nat_iso CategoryTheory.Localization.liftNatIso
-/

namespace Lifting

/- warning: category_theory.localization.lifting.comp_right -> CategoryTheory.Localization.Lifting.compRight is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} {D : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u1} C] [_inst_2 : CategoryTheory.Category.{u4, u2} D] (L : CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2) (W : CategoryTheory.MorphismProperty.{u3, u1} C _inst_1) {E : Type.{u5}} [_inst_3 : CategoryTheory.Category.{u6, u5} E] [_inst_4 : CategoryTheory.Functor.IsLocalization.{u1, u2, u3, u4} C D _inst_1 _inst_2 L W] {E' : Type.{u7}} [_inst_5 : CategoryTheory.Category.{u8, u7} E'] (F : CategoryTheory.Functor.{u3, u6, u1, u5} C _inst_1 E _inst_3) (F' : CategoryTheory.Functor.{u4, u6, u2, u5} D _inst_2 E _inst_3) [_inst_6 : CategoryTheory.Localization.Lifting.{u1, u2, u3, u4, u5, u6} C D _inst_1 _inst_2 L W E _inst_3 _inst_4 F F'] (G : CategoryTheory.Functor.{u6, u8, u5, u7} E _inst_3 E' _inst_5), CategoryTheory.Localization.Lifting.{u1, u2, u3, u4, u7, u8} C D _inst_1 _inst_2 L W E' _inst_5 _inst_4 (CategoryTheory.Functor.comp.{u3, u6, u8, u1, u5, u7} C _inst_1 E _inst_3 E' _inst_5 F G) (CategoryTheory.Functor.comp.{u4, u6, u8, u2, u5, u7} D _inst_2 E _inst_3 E' _inst_5 F' G)
but is expected to have type
  forall {C : Type.{u1}} {D : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u1} C] [_inst_2 : CategoryTheory.Category.{u4, u2} D] (L : CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2) (W : CategoryTheory.MorphismProperty.{u3, u1} C _inst_1) {E : Type.{u5}} [_inst_3 : CategoryTheory.Category.{u6, u5} E] {_inst_4 : Type.{u7}} [E' : CategoryTheory.Category.{u8, u7} _inst_4] (_inst_5 : CategoryTheory.Functor.{u3, u6, u1, u5} C _inst_1 E _inst_3) (F : CategoryTheory.Functor.{u4, u6, u2, u5} D _inst_2 E _inst_3) [F' : CategoryTheory.Localization.Lifting.{u1, u2, u3, u4, u5, u6} C D _inst_1 _inst_2 L E _inst_3 W _inst_5 F] (_inst_6 : CategoryTheory.Functor.{u6, u8, u5, u7} E _inst_3 _inst_4 E'), CategoryTheory.Localization.Lifting.{u1, u2, u3, u4, u7, u8} C D _inst_1 _inst_2 L _inst_4 E' W (CategoryTheory.Functor.comp.{u3, u6, u8, u1, u5, u7} C _inst_1 E _inst_3 _inst_4 E' _inst_5 _inst_6) (CategoryTheory.Functor.comp.{u4, u6, u8, u2, u5, u7} D _inst_2 E _inst_3 _inst_4 E' F _inst_6)
Case conversion may be inaccurate. Consider using '#align category_theory.localization.lifting.comp_right CategoryTheory.Localization.Lifting.compRightₓ'. -/
@[simps]
instance compRight {E' : Type _} [Category E'] (F : C ⥤ E) (F' : D ⥤ E) [Lifting L W F F']
    (G : E ⥤ E') : Lifting L W (F ⋙ G) (F' ⋙ G) :=
  ⟨isoWhiskerRight (iso L W F F') G⟩
#align category_theory.localization.lifting.comp_right CategoryTheory.Localization.Lifting.compRight

#print CategoryTheory.Localization.Lifting.id /-
@[simps]
instance id : Lifting L W L (𝟭 D) :=
  ⟨Functor.rightUnitor L⟩
#align category_theory.localization.lifting.id CategoryTheory.Localization.Lifting.id
-/

/- warning: category_theory.localization.lifting.of_isos -> CategoryTheory.Localization.Lifting.ofIsos is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} {D : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u1} C] [_inst_2 : CategoryTheory.Category.{u4, u2} D] (L : CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2) (W : CategoryTheory.MorphismProperty.{u3, u1} C _inst_1) {E : Type.{u5}} [_inst_3 : CategoryTheory.Category.{u6, u5} E] [_inst_4 : CategoryTheory.Functor.IsLocalization.{u1, u2, u3, u4} C D _inst_1 _inst_2 L W] {F₁ : CategoryTheory.Functor.{u3, u6, u1, u5} C _inst_1 E _inst_3} {F₂ : CategoryTheory.Functor.{u3, u6, u1, u5} C _inst_1 E _inst_3} {F₁' : CategoryTheory.Functor.{u4, u6, u2, u5} D _inst_2 E _inst_3} {F₂' : CategoryTheory.Functor.{u4, u6, u2, u5} D _inst_2 E _inst_3}, (CategoryTheory.Iso.{max u1 u6, max u3 u6 u1 u5} (CategoryTheory.Functor.{u3, u6, u1, u5} C _inst_1 E _inst_3) (CategoryTheory.Functor.category.{u3, u6, u1, u5} C _inst_1 E _inst_3) F₁ F₂) -> (CategoryTheory.Iso.{max u2 u6, max u4 u6 u2 u5} (CategoryTheory.Functor.{u4, u6, u2, u5} D _inst_2 E _inst_3) (CategoryTheory.Functor.category.{u4, u6, u2, u5} D _inst_2 E _inst_3) F₁' F₂') -> (forall [_inst_5 : CategoryTheory.Localization.Lifting.{u1, u2, u3, u4, u5, u6} C D _inst_1 _inst_2 L W E _inst_3 _inst_4 F₁ F₁'], CategoryTheory.Localization.Lifting.{u1, u2, u3, u4, u5, u6} C D _inst_1 _inst_2 L W E _inst_3 _inst_4 F₂ F₂')
but is expected to have type
  forall {C : Type.{u1}} {D : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u1} C] [_inst_2 : CategoryTheory.Category.{u4, u2} D] (L : CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2) (W : CategoryTheory.MorphismProperty.{u3, u1} C _inst_1) {E : Type.{u5}} [_inst_3 : CategoryTheory.Category.{u6, u5} E] {_inst_4 : CategoryTheory.Functor.{u3, u6, u1, u5} C _inst_1 E _inst_3} {F₁ : CategoryTheory.Functor.{u3, u6, u1, u5} C _inst_1 E _inst_3} {F₂ : CategoryTheory.Functor.{u4, u6, u2, u5} D _inst_2 E _inst_3} {F₁' : CategoryTheory.Functor.{u4, u6, u2, u5} D _inst_2 E _inst_3}, (CategoryTheory.Iso.{max u1 u6, max (max (max u1 u3) u5) u6} (CategoryTheory.Functor.{u3, u6, u1, u5} C _inst_1 E _inst_3) (CategoryTheory.Functor.category.{u3, u6, u1, u5} C _inst_1 E _inst_3) _inst_4 F₁) -> (CategoryTheory.Iso.{max u2 u6, max (max (max u2 u4) u5) u6} (CategoryTheory.Functor.{u4, u6, u2, u5} D _inst_2 E _inst_3) (CategoryTheory.Functor.category.{u4, u6, u2, u5} D _inst_2 E _inst_3) F₂ F₁') -> (forall [e' : CategoryTheory.Localization.Lifting.{u1, u2, u3, u4, u5, u6} C D _inst_1 _inst_2 L E _inst_3 W _inst_4 F₂], CategoryTheory.Localization.Lifting.{u1, u2, u3, u4, u5, u6} C D _inst_1 _inst_2 L E _inst_3 W F₁ F₁')
Case conversion may be inaccurate. Consider using '#align category_theory.localization.lifting.of_isos CategoryTheory.Localization.Lifting.ofIsosₓ'. -/
/-- Given a localization functor `L : C ⥤ D` for `W : morphism_property C`,
if `F₁' : D ⥤ E` lifts a functor `F₁ : C ⥤ D`, then a functor `F₂'` which
is isomorphic to `F₁'` also lifts a functor `F₂` that is isomorphic to `F₁`.  -/
@[simps]
def ofIsos {F₁ F₂ : C ⥤ E} {F₁' F₂' : D ⥤ E} (e : F₁ ≅ F₂) (e' : F₁' ≅ F₂') [Lifting L W F₁ F₁'] :
    Lifting L W F₂ F₂' :=
  ⟨isoWhiskerLeft L e'.symm ≪≫ iso L W F₁ F₁' ≪≫ e⟩
#align category_theory.localization.lifting.of_isos CategoryTheory.Localization.Lifting.ofIsos

end Lifting

end Localization

namespace Functor

namespace IsLocalization

open Localization

/- warning: category_theory.functor.is_localization.of_iso -> CategoryTheory.Functor.IsLocalization.of_iso is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} {D : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u1} C] [_inst_2 : CategoryTheory.Category.{u4, u2} D] (W : CategoryTheory.MorphismProperty.{u3, u1} C _inst_1) {L₁ : CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2} {L₂ : CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2}, (CategoryTheory.Iso.{max u1 u4, max u3 u4 u1 u2} (CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u3, u4, u1, u2} C _inst_1 D _inst_2) L₁ L₂) -> (forall [_inst_4 : CategoryTheory.Functor.IsLocalization.{u1, u2, u3, u4} C D _inst_1 _inst_2 L₁ W], CategoryTheory.Functor.IsLocalization.{u1, u2, u3, u4} C D _inst_1 _inst_2 L₂ W)
but is expected to have type
  forall {C : Type.{u2}} {D : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u4, u2} C] [_inst_2 : CategoryTheory.Category.{u3, u1} D] (W : CategoryTheory.MorphismProperty.{u4, u2} C _inst_1) {L₁ : CategoryTheory.Functor.{u4, u3, u2, u1} C _inst_1 D _inst_2} {L₂ : CategoryTheory.Functor.{u4, u3, u2, u1} C _inst_1 D _inst_2}, (CategoryTheory.Iso.{max u2 u3, max (max (max u2 u1) u4) u3} (CategoryTheory.Functor.{u4, u3, u2, u1} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u4, u3, u2, u1} C _inst_1 D _inst_2) L₁ L₂) -> (forall [_inst_4 : CategoryTheory.Functor.IsLocalization.{u2, u1, u4, u3} C D _inst_1 _inst_2 L₁ W], CategoryTheory.Functor.IsLocalization.{u2, u1, u4, u3} C D _inst_1 _inst_2 L₂ W)
Case conversion may be inaccurate. Consider using '#align category_theory.functor.is_localization.of_iso CategoryTheory.Functor.IsLocalization.of_isoₓ'. -/
theorem of_iso {L₁ L₂ : C ⥤ D} (e : L₁ ≅ L₂) [L₁.IsLocalization W] : L₂.IsLocalization W :=
  by
  have h := localization.inverts L₁ W
  rw [morphism_property.is_inverted_by.iff_of_iso W e] at h
  let F₁ := localization.construction.lift L₁ (localization.inverts L₁ W)
  let F₂ := localization.construction.lift L₂ h
  exact
    { inverts := h
      nonempty_isEquivalence :=
        Nonempty.intro (is_equivalence.of_iso (lift_nat_iso W.Q W L₁ L₂ F₁ F₂ e) inferInstance) }
#align category_theory.functor.is_localization.of_iso CategoryTheory.Functor.IsLocalization.of_iso

/- warning: category_theory.functor.is_localization.of_equivalence_target -> CategoryTheory.Functor.IsLocalization.of_equivalence_target is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} {D : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u1} C] [_inst_2 : CategoryTheory.Category.{u4, u2} D] (L : CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2) (W : CategoryTheory.MorphismProperty.{u3, u1} C _inst_1) {E : Type.{u5}} [_inst_4 : CategoryTheory.Category.{u6, u5} E] (L' : CategoryTheory.Functor.{u3, u6, u1, u5} C _inst_1 E _inst_4) (eq : CategoryTheory.Equivalence.{u4, u6, u2, u5} D _inst_2 E _inst_4) [_inst_5 : CategoryTheory.Functor.IsLocalization.{u1, u2, u3, u4} C D _inst_1 _inst_2 L W], (CategoryTheory.Iso.{max u1 u6, max u3 u6 u1 u5} (CategoryTheory.Functor.{u3, u6, u1, u5} C _inst_1 E _inst_4) (CategoryTheory.Functor.category.{u3, u6, u1, u5} C _inst_1 E _inst_4) (CategoryTheory.Functor.comp.{u3, u4, u6, u1, u2, u5} C _inst_1 D _inst_2 E _inst_4 L (CategoryTheory.Equivalence.functor.{u4, u6, u2, u5} D _inst_2 E _inst_4 eq)) L') -> (CategoryTheory.Functor.IsLocalization.{u1, u5, u3, u6} C E _inst_1 _inst_4 L' W)
but is expected to have type
  forall {C : Type.{u3}} {D : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u4, u3} C] [_inst_2 : CategoryTheory.Category.{u2, u1} D] (L : CategoryTheory.Functor.{u4, u2, u3, u1} C _inst_1 D _inst_2) (W : CategoryTheory.MorphismProperty.{u4, u3} C _inst_1) {E : Type.{u6}} [_inst_4 : CategoryTheory.Category.{u5, u6} E] (L' : CategoryTheory.Functor.{u4, u5, u3, u6} C _inst_1 E _inst_4) (eq : CategoryTheory.Equivalence.{u2, u5, u1, u6} D E _inst_2 _inst_4) [_inst_5 : CategoryTheory.Functor.IsLocalization.{u3, u1, u4, u2} C D _inst_1 _inst_2 L W], (CategoryTheory.Iso.{max u3 u5, max (max (max u6 u3) u5) u4} (CategoryTheory.Functor.{u4, u5, u3, u6} C _inst_1 E _inst_4) (CategoryTheory.Functor.category.{u4, u5, u3, u6} C _inst_1 E _inst_4) (CategoryTheory.Functor.comp.{u4, u2, u5, u3, u1, u6} C _inst_1 D _inst_2 E _inst_4 L (CategoryTheory.Equivalence.functor.{u2, u5, u1, u6} D E _inst_2 _inst_4 eq)) L') -> (CategoryTheory.Functor.IsLocalization.{u3, u6, u4, u5} C E _inst_1 _inst_4 L' W)
Case conversion may be inaccurate. Consider using '#align category_theory.functor.is_localization.of_equivalence_target CategoryTheory.Functor.IsLocalization.of_equivalence_targetₓ'. -/
/-- If `L : C ⥤ D` is a localization for `W : morphism_property C`, then it is also
the case of a functor obtained by post-composing `L` with an equivalence of categories. -/
theorem of_equivalence_target {E : Type _} [Category E] (L' : C ⥤ E) (eq : D ≌ E)
    [L.IsLocalization W] (e : L ⋙ Eq.Functor ≅ L') : L'.IsLocalization W :=
  by
  have h : W.is_inverted_by L' :=
    by
    rw [← morphism_property.is_inverted_by.iff_of_iso W e]
    exact morphism_property.is_inverted_by.of_comp W L (localization.inverts L W) eq.functor
  let F₁ := localization.construction.lift L (localization.inverts L W)
  let F₂ := localization.construction.lift L' h
  let e' : F₁ ⋙ eq.functor ≅ F₂ := lift_nat_iso W.Q W (L ⋙ eq.functor) L' _ _ e
  exact
    { inverts := h
      nonempty_isEquivalence := Nonempty.intro (is_equivalence.of_iso e' inferInstance) }
#align category_theory.functor.is_localization.of_equivalence_target CategoryTheory.Functor.IsLocalization.of_equivalence_target

end IsLocalization

end Functor

end CategoryTheory

