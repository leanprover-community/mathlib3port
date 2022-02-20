/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import Mathbin.CategoryTheory.Bicategory.NaturalTransformation

/-!
# The bicategory of oplax functors between two bicategories

Given bicategories `B` and `C`, we give a bicategory structure on `oplax_functor B C` whose
* objects are oplax functors,
* 1-morphisms are oplax natural transformations, and
* 2-morphisms are modifications.
-/


namespace CategoryTheory

open Category Bicategory

open_locale Bicategory

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]

variable {F G H I : OplaxFunctor B C}

namespace OplaxNatTrans

/-- Left whiskering of an oplax natural transformation and a modification. -/
@[simps]
def whiskerLeft (η : F ⟶ G) {θ ι : G ⟶ H} (Γ : θ ⟶ ι) : η ≫ θ ⟶ η ≫ ι where
  app := fun a => η.app a ◁ Γ.app a
  naturality' := fun a b f => by
    dsimp
    simp only [assoc]
    rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc, associator_naturality_right_assoc,
      Γ.whisker_left_naturality_assoc, associator_inv_naturality_middle]

/-- Right whiskering of an oplax natural transformation and a modification. -/
@[simps]
def whiskerRight {η θ : F ⟶ G} (Γ : η ⟶ θ) (ι : G ⟶ H) : η ≫ ι ⟶ θ ≫ ι where
  app := fun a => Γ.app a ▷ ι.app a
  naturality' := fun a b f => by
    dsimp
    simp only [assoc]
    rw [associator_inv_naturality_middle_assoc, Γ.whisker_right_naturality_assoc, associator_naturality_left_assoc, ←
      whisker_exchange_assoc, associator_inv_naturality_left]

/-- Associator for the vertical composition of oplax natural transformations. -/
@[simps]
def associator (η : F ⟶ G) (θ : G ⟶ H) (ι : H ⟶ I) : (η ≫ θ) ≫ ι ≅ η ≫ θ ≫ ι :=
  ModificationIso.ofComponents (fun a => α_ (η.app a) (θ.app a) (ι.app a))
    (by
      intro a b f
      dsimp
      simp only [whisker_right_comp, whisker_left_comp, assoc]
      rw [← pentagon_inv_inv_hom_hom_inv_assoc, ← associator_naturality_left_assoc, pentagon_hom_hom_inv_hom_hom_assoc,
        ← associator_naturality_middle_assoc, ← pentagon_inv_hom_hom_hom_hom_assoc, ← associator_naturality_right_assoc,
        pentagon_hom_inv_inv_inv_hom])

/-- Left unitor for the vertical composition of oplax natural transformations. -/
@[simps]
def leftUnitor (η : F ⟶ G) : 𝟙 F ≫ η ≅ η :=
  ModificationIso.ofComponents (fun a => λ_ (η.app a))
    (by
      intro a b f
      dsimp
      simp only [triangle_assoc_comp_right_assoc, whisker_right_comp, assoc, whisker_exchange_assoc]
      rw [← left_unitor_comp, left_unitor_naturality, left_unitor_comp]
      simp only [iso.hom_inv_id_assoc, inv_hom_whisker_right_assoc, assoc, whisker_exchange_assoc])

/-- Right unitor for the vertical composition of oplax natural transformations. -/
@[simps]
def rightUnitor (η : F ⟶ G) : η ≫ 𝟙 G ≅ η :=
  ModificationIso.ofComponents (fun a => ρ_ (η.app a))
    (by
      intro a b f
      dsimp
      simp only [triangle_assoc_comp_left_inv, inv_hom_whisker_right_assoc, whisker_exchange, assoc, whisker_left_comp]
      rw [← right_unitor_comp, right_unitor_naturality, right_unitor_comp]
      simp only [iso.inv_hom_id_assoc, assoc])

end OplaxNatTrans

variable (B C)

/-- A bicategory structure on the oplax functors between bicategories. -/
@[simps]
instance OplaxFunctor.bicategory : Bicategory (OplaxFunctor B C) where
  whiskerLeft := fun F G H η _ _ Γ => OplaxNatTrans.whiskerLeft η Γ
  whiskerRight := fun F G H _ _ Γ η => OplaxNatTrans.whiskerRight Γ η
  associator := fun F G H I => OplaxNatTrans.associator
  leftUnitor := fun F G => OplaxNatTrans.leftUnitor
  rightUnitor := fun F G => OplaxNatTrans.rightUnitor
  associator_naturality_left' := by
    intros
    ext
    apply associator_naturality_left
  associator_naturality_middle' := by
    intros
    ext
    apply associator_naturality_middle
  associator_naturality_right' := by
    intros
    ext
    apply associator_naturality_right
  left_unitor_naturality' := by
    intros
    ext
    apply left_unitor_naturality
  right_unitor_naturality' := by
    intros
    ext
    apply right_unitor_naturality
  pentagon' := by
    intros
    ext
    apply pentagon
  triangle' := by
    intros
    ext
    apply triangle

end CategoryTheory

