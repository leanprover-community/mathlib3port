/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathbin.CategoryTheory.Localization.Construction

/-!

# Predicate for localized categories

In this file, a predicate `L.is_localization W` is introduced for a functor `L : C ⥤ D`
and `W : morphism_property C`: it expresses that `L` identifies `D` with the localized
category of `C` with respect to `W` (up to equivalence).

We introduce a universal property `strict_universal_property_fixed_target L W E` which
states that `L` inverts the morphisms in `W` and that all functors `C ⥤ E` inverting
`W` uniquely factors as a composition of `L ⋙ G` with `G : D ⥤ E`. Such universal
properties are inputs for the constructor `is_localization.mk'` for `L.is_localization W`.

-/


noncomputable section

namespace CategoryTheory

variable {C D : Type _} [Category C] [Category D] (L : C ⥤ D) (W : MorphismProperty C) (E : Type _) [Category E]

namespace Functor

/-- The predicate expressing that, up to equivalence, a functor `L : C ⥤ D`
identifies the category `D` with the localized category of `C` with respect
to `W : morphism_property C`. -/
class IsLocalization : Prop where
  inverts : W.IsInvertedBy L
  nonempty_is_equivalence : Nonempty (IsEquivalence (Localization.Construction.lift L inverts))

instance Q_is_localization : W.q.IsLocalization W where
  inverts := W.Q_inverts
  nonempty_is_equivalence := by
    suffices localization.construction.lift W.Q W.Q_inverts = 𝟭 _ by
      apply Nonempty.intro
      rw [this]
      infer_instance
    apply localization.construction.uniq
    simpa only [localization.construction.fac]

end Functor

namespace Localization

/-- This universal property states that a functor `L : C ⥤ D` inverts morphisms
in `W` and the all functors `D ⥤ E` (for a fixed category `E`) uniquely factors
through `L`. -/
structure StrictUniversalPropertyFixedTarget where
  inverts : W.IsInvertedBy L
  lift : ∀ (F : C ⥤ E) (hF : W.IsInvertedBy F), D ⥤ E
  fac : ∀ (F : C ⥤ E) (hF : W.IsInvertedBy F), L ⋙ lift F hF = F
  uniq : ∀ (F₁ F₂ : D ⥤ E) (h : L ⋙ F₁ = L ⋙ F₂), F₁ = F₂

/-- The localized category `W.localization` that was constructed satisfies
the universal property of the localization. -/
@[simps]
def strictUniversalPropertyFixedTargetQ : StrictUniversalPropertyFixedTarget W.q W E where
  inverts := W.Q_inverts
  lift := Construction.lift
  fac := Construction.fac
  uniq := Construction.uniq

instance : Inhabited (StrictUniversalPropertyFixedTarget W.q W E) :=
  ⟨strictUniversalPropertyFixedTargetQ _ _⟩

/-- When `W` consists of isomorphisms, the identity satisfies the universal property
of the localization. -/
@[simps]
def strictUniversalPropertyFixedTargetId (hW : W ⊆ MorphismProperty.Isomorphisms C) :
    StrictUniversalPropertyFixedTarget (𝟭 C) W E where
  inverts X Y f hf := hW f hf
  lift F hF := F
  fac F hF := by
    cases F
    rfl
  uniq F₁ F₂ eq := by
    cases F₁
    cases F₂
    exact Eq

end Localization

namespace Functor

theorem IsLocalization.mk' (h₁ : Localization.StrictUniversalPropertyFixedTarget L W D)
    (h₂ : Localization.StrictUniversalPropertyFixedTarget L W W.Localization) : IsLocalization L W :=
  { inverts := h₁.inverts,
    nonempty_is_equivalence :=
      Nonempty.intro
        { inverse := h₂.lift W.q W.Q_inverts,
          unitIso :=
            eqToIso
              (Localization.Construction.uniq _ _
                (by simp only [← functor.assoc, localization.construction.fac, h₂.fac, functor.comp_id])),
          counitIso :=
            eqToIso
              (h₁.uniq _ _ (by simp only [← functor.assoc, h₂.fac, localization.construction.fac, functor.comp_id])),
          functor_unit_iso_comp' := fun X => by
            simpa only [eq_to_iso.hom, eq_to_hom_app, eq_to_hom_map, eq_to_hom_trans, eq_to_hom_refl] } }

theorem IsLocalization.for_id (hW : W ⊆ MorphismProperty.Isomorphisms C) : (𝟭 C).IsLocalization W :=
  IsLocalization.mk' _ _ (Localization.strictUniversalPropertyFixedTargetId W _ hW)
    (Localization.strictUniversalPropertyFixedTargetId W _ hW)

end Functor

namespace Localization

variable [L.IsLocalization W]

include L W

theorem inverts : W.IsInvertedBy L :=
  (inferInstance : L.IsLocalization W).inverts

variable {W}

/-- The isomorphism `L.obj X ≅ L.obj Y` that is deduced from a morphism `f : X ⟶ Y` which
belongs to `W`, when `L.is_localization W`. -/
@[simps]
def isoOfHom {X Y : C} (f : X ⟶ Y) (hf : W f) : L.obj X ≅ L.obj Y :=
  haveI : is_iso (L.map f) := inverts L W f hf
  as_iso (L.map f)

variable (W)

instance : IsEquivalence (Localization.Construction.lift L (inverts L W)) :=
  (inferInstance : L.IsLocalization W).nonempty_is_equivalence.some

/-- A chosen equivalence of categories `W.localization ≅ D` for a functor
`L : C ⥤ D` which satisfies `L.is_localization W`. This shall be used in
order to deduce properties of `L` from properties of `W.Q`. -/
def equivalenceFromModel : W.Localization ≌ D :=
  (Localization.Construction.lift L (inverts L W)).asEquivalence

/-- Via the equivalence of categories `equivalence_from_model L W : W.localization ≌ D`,
one may identify the functors `W.Q` and `L`. -/
def qCompEquivalenceFromModelFunctorIso : W.q ⋙ (equivalenceFromModel L W).Functor ≅ L :=
  eqToIso (Construction.fac _ _)

/-- Via the equivalence of categories `equivalence_from_model L W : W.localization ≌ D`,
one may identify the functors `L` and `W.Q`. -/
def compEquivalenceFromModelInverseIso : L ⋙ (equivalenceFromModel L W).inverse ≅ W.q :=
  calc
    L ⋙ (equivalenceFromModel L W).inverse ≅ _ := isoWhiskerRight (qCompEquivalenceFromModelFunctorIso L W).symm _
    _ ≅ W.q ⋙ (equivalenceFromModel L W).Functor ⋙ (equivalenceFromModel L W).inverse := Functor.associator _ _ _
    _ ≅ W.q ⋙ 𝟭 _ := isoWhiskerLeft _ (equivalenceFromModel L W).unitIso.symm
    _ ≅ W.q := Functor.rightUnitor _
    

theorem ess_surj : EssSurj L :=
  ⟨fun X =>
    ⟨(Construction.objEquiv W).invFun ((equivalenceFromModel L W).inverse.obj X),
      Nonempty.intro
        ((qCompEquivalenceFromModelFunctorIso L W).symm.app _ ≪≫ (equivalenceFromModel L W).counitIso.app X)⟩⟩

end Localization

end CategoryTheory

