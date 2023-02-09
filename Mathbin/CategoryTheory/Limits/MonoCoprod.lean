/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou

! This file was ported from Lean 3 source module category_theory.limits.mono_coprod
! leanprover-community/mathlib commit 0ebfdb71919ac6ca5d7fbc61a082fa2519556818
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.Shapes.RegularMono
import Mathbin.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!

# Categories where inclusions into coproducts are monomorphisms

If `C` is a category, the class `mono_coprod C` expresses that left
inclusions `A ⟶ A ⨿ B` are monomorphisms when `has_coproduct A B`
is satisfied. If it is so, it is shown that right inclusions are
also monomorphisms.

TODO @joelriou: show that if `X : I → C` and `ι : J → I` is an injective map,
then the canonical morphism `∐ (X ∘ ι) ⟶ ∐ X` is a monomorphism.

TODO: define distributive categories, and show that they satisfy `mono_coprod`, see
<https://ncatlab.org/toddtrimble/published/distributivity+implies+monicity+of+coproduct+inclusions>

-/


noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

universe u

namespace CategoryTheory

namespace Limits

variable (C : Type _) [Category C]

/-- This condition expresses that inclusion morphisms into coproducts are monomorphisms. -/
class MonoCoprod : Prop where
  binaryCofan_inl : ∀ ⦃A B : C⦄ (c : BinaryCofan A B) (hc : IsColimit c), Mono c.inl
#align category_theory.limits.mono_coprod CategoryTheory.Limits.MonoCoprod

variable {C}

instance (priority := 100) monoCoprodOfHasZeroMorphisms [HasZeroMorphisms C] : MonoCoprod C :=
  ⟨fun A B c hc =>
    by
    haveI : IsSplitMono c.inl :=
      IsSplitMono.mk' (SplitMono.mk (hc.desc (BinaryCofan.mk (𝟙 A) 0)) (IsColimit.fac _ _ _))
    infer_instance⟩
#align category_theory.limits.mono_coprod_of_has_zero_morphisms CategoryTheory.Limits.monoCoprodOfHasZeroMorphisms

namespace MonoCoprod

theorem binaryCofan_inr {A B : C} [MonoCoprod C] (c : BinaryCofan A B) (hc : IsColimit c) :
    Mono c.inr :=
  haveI hc' : IsColimit (BinaryCofan.mk c.inr c.inl) :=
    BinaryCofan.isColimitMk (fun s => hc.desc (BinaryCofan.mk s.inr s.inl)) (by tidy) (by tidy)
      fun s m h₁ h₂ =>
      BinaryCofan.IsColimit.hom_ext hc
        (by simp only [h₂, IsColimit.fac, BinaryCofan.ι_app_left, BinaryCofan.mk_inl])
        (by simp only [h₁, IsColimit.fac, BinaryCofan.ι_app_right, BinaryCofan.mk_inr])
  binaryCofan_inl _ hc'
#align category_theory.limits.mono_coprod.binary_cofan_inr CategoryTheory.Limits.MonoCoprod.binaryCofan_inr

instance {A B : C} [MonoCoprod C] [HasBinaryCoproduct A B] : Mono (coprod.inl : A ⟶ A ⨿ B) :=
  binaryCofan_inl _ (colimit.isColimit _)

instance {A B : C} [MonoCoprod C] [HasBinaryCoproduct A B] : Mono (coprod.inr : B ⟶ A ⨿ B) :=
  binaryCofan_inr _ (colimit.isColimit _)

theorem mono_inl_iff {A B : C} {c₁ c₂ : BinaryCofan A B} (hc₁ : IsColimit c₁) (hc₂ : IsColimit c₂) :
    Mono c₁.inl ↔ Mono c₂.inl :=
  by
  suffices
    ∀ (c₁ c₂ : BinaryCofan A B) (hc₁ : IsColimit c₁) (hc₂ : IsColimit c₂) (h : Mono c₁.inl),
      Mono c₂.inl
    by exact ⟨fun h₁ => this _ _ hc₁ hc₂ h₁, fun h₂ => this _ _ hc₂ hc₁ h₂⟩
  intro c₁ c₂ hc₁ hc₂
  intro
  simpa only [IsColimit.comp_coconePointUniqueUpToIso_hom] using
    mono_comp c₁.inl (hc₁.cocone_point_unique_up_to_iso hc₂).hom
#align category_theory.limits.mono_coprod.mono_inl_iff CategoryTheory.Limits.MonoCoprod.mono_inl_iff

theorem mk' (h : ∀ A B : C, ∃ (c : BinaryCofan A B)(hc : IsColimit c), Mono c.inl) : MonoCoprod C :=
  ⟨fun A B c' hc' => by
    obtain ⟨c, hc₁, hc₂⟩ := h A B
    simpa only [mono_inl_iff hc' hc₁] using hc₂⟩
#align category_theory.limits.mono_coprod.mk' CategoryTheory.Limits.MonoCoprod.mk'

instance monoCoprodType : MonoCoprod (Type u) :=
  MonoCoprod.mk' fun A B =>
    by
    refine' ⟨BinaryCofan.mk (Sum.inl : A ⟶ Sum A B) Sum.inr, _, _⟩
    · refine'
        BinaryCofan.IsColimit.mk _
          (fun Y f₁ f₂ x => by
            cases x
            exacts[f₁ x, f₂ x])
          (fun Y f₁ f₂ => rfl) (fun Y f₁ f₂ => rfl) _
      intro Y f₁ f₂ m h₁ h₂
      ext x
      cases x
      · dsimp
        exact congr_fun h₁ x
      · dsimp
        exact congr_fun h₂ x
    · rw [mono_iff_injective]
      intro a₁ a₂ h
      simp only [BinaryCofan.mk_inl] at h
      dsimp at h
      simpa only using h
#align category_theory.limits.mono_coprod.mono_coprod_type CategoryTheory.Limits.MonoCoprod.monoCoprodType

end MonoCoprod

end Limits

end CategoryTheory

