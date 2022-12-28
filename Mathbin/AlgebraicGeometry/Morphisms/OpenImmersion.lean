/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

! This file was ported from Lean 3 source module algebraic_geometry.morphisms.open_immersion
! leanprover-community/mathlib commit 46a64b5b4268c594af770c44d9e502afc6a515cb
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathbin.Topology.LocalAtTarget

/-!

# Open immersions

A morphism is an open immersions if the underlying map of spaces is an open embedding
`f : X ⟶ U ⊆ Y`, and the sheaf map `Y(V) ⟶ f _* X(V)` is an iso for each `V ⊆ U`.

Most of the theories are developed in `algebraic_geometry/open_immersion`, and we provide the
remaining theorems analogous to other lemmas in `algebraic_geometry/morphisms/*`.

-/


noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X Y Z : SchemeCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

theorem is_open_immersion_iff_stalk {f : X ⟶ Y} :
    IsOpenImmersion f ↔ OpenEmbedding f.1.base ∧ ∀ x, IsIso (PresheafedSpaceCat.stalkMap f.1 x) :=
  by
  constructor
  · intro h
    exact ⟨h.1, inferInstance⟩
  · rintro ⟨h₁, h₂⟩
    exact is_open_immersion.of_stalk_iso f h₁
#align algebraic_geometry.is_open_immersion_iff_stalk AlgebraicGeometry.is_open_immersion_iff_stalk

theorem is_open_immersion_stable_under_composition :
    MorphismProperty.StableUnderComposition @IsOpenImmersion := by intro X Y Z f g h₁ h₂;
  infer_instance
#align
  algebraic_geometry.is_open_immersion_stable_under_composition AlgebraicGeometry.is_open_immersion_stable_under_composition

theorem is_open_immersion_respects_iso : MorphismProperty.RespectsIso @IsOpenImmersion :=
  by
  apply is_open_immersion_stable_under_composition.respects_iso
  intro _ _ _; infer_instance
#align
  algebraic_geometry.is_open_immersion_respects_iso AlgebraicGeometry.is_open_immersion_respects_iso

theorem is_open_immersion_is_local_at_target : PropertyIsLocalAtTarget @IsOpenImmersion :=
  by
  constructor
  · exact is_open_immersion_respects_iso
  · intros
    infer_instance
  · intro X Y f 𝒰 H
    rw [is_open_immersion_iff_stalk]
    constructor
    · apply (open_embedding_iff_open_embedding_of_supr_eq_top 𝒰.supr_opens_range f.1.base.2).mpr
      intro i
      have :=
        ((is_open_immersion_respects_iso.arrow_iso_iff
                (morphism_restrict_opens_range f (𝒰.map i))).mpr
            (H i)).1
      rwa [arrow.mk_hom, morphism_restrict_val_base] at this
    · intro x
      have :=
        arrow.iso_w
          (morphism_restrict_stalk_map f (𝒰.map <| 𝒰.f <| f.1 x).opensRange ⟨x, 𝒰.covers _⟩)
      dsimp only [arrow.mk_hom] at this
      rw [this]
      haveI : is_open_immersion (f ∣_ (𝒰.map <| 𝒰.f <| f.1 x).opensRange) :=
        (is_open_immersion_respects_iso.arrow_iso_iff
              (morphism_restrict_opens_range f (𝒰.map _))).mpr
          (H _)
      infer_instance
#align
  algebraic_geometry.is_open_immersion_is_local_at_target AlgebraicGeometry.is_open_immersion_is_local_at_target

theorem IsOpenImmersion.open_cover_tfae {X Y : SchemeCat.{u}} (f : X ⟶ Y) :
    Tfae
      [IsOpenImmersion f,
        ∃ 𝒰 : SchemeCat.OpenCover.{u} Y,
          ∀ i : 𝒰.J, IsOpenImmersion (pullback.snd : (𝒰.pullbackCover f).obj i ⟶ 𝒰.obj i),
        ∀ (𝒰 : SchemeCat.OpenCover.{u} Y) (i : 𝒰.J),
          IsOpenImmersion (pullback.snd : (𝒰.pullbackCover f).obj i ⟶ 𝒰.obj i),
        ∀ U : Opens Y.carrier, IsOpenImmersion (f ∣_ U),
        ∀ {U : SchemeCat} (g : U ⟶ Y) [IsOpenImmersion g],
          IsOpenImmersion (pullback.snd : pullback f g ⟶ _),
        ∃ (ι : Type u)(U : ι → Opens Y.carrier)(hU : supᵢ U = ⊤),
          ∀ i, IsOpenImmersion (f ∣_ U i)] :=
  is_open_immersion_is_local_at_target.open_cover_tfae f
#align
  algebraic_geometry.is_open_immersion.open_cover_tfae AlgebraicGeometry.IsOpenImmersion.open_cover_tfae

theorem IsOpenImmersion.open_cover_iff {X Y : SchemeCat.{u}} (𝒰 : SchemeCat.OpenCover.{u} Y)
    (f : X ⟶ Y) :
    IsOpenImmersion f ↔ ∀ i, IsOpenImmersion (pullback.snd : pullback f (𝒰.map i) ⟶ _) :=
  is_open_immersion_is_local_at_target.open_cover_iff f 𝒰
#align
  algebraic_geometry.is_open_immersion.open_cover_iff AlgebraicGeometry.IsOpenImmersion.open_cover_iff

theorem is_open_immersion_stable_under_base_change :
    MorphismProperty.StableUnderBaseChange @IsOpenImmersion :=
  MorphismProperty.StableUnderBaseChange.mk is_open_immersion_respects_iso <|
    by
    intro X Y Z f g H
    infer_instance
#align
  algebraic_geometry.is_open_immersion_stable_under_base_change AlgebraicGeometry.is_open_immersion_stable_under_base_change

end AlgebraicGeometry

