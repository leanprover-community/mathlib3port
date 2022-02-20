/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import Mathbin.CategoryTheory.Bicategory.Functor

/-!
# Oplax natural transformations

Just as there are natural transformations between functors, there are oplax natural transformations
between oplax functors. The equality in the naturality of natural transformations is replaced by a
specified 2-morphism `F.map f ≫ app b ⟶ app a ≫ G.map f` in the case of oplax natural
transformations.

## Main definitions

* `oplax_nat_trans F G` : oplax natural transformations between oplax functors `F` and `G`
* `oplax_nat_trans.vcomp η θ` : the vertical composition of oplax natural transformations `η`
  and `θ`
* `oplax_nat_trans.category F G` : the category structure on the oplax natural transformations
  between `F` and `G`
-/


namespace CategoryTheory

open Category Bicategory

open_locale Bicategory

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]

/-- If `η` is an oplax natural transformation between `F` and `G`, we have a 1-morphism
`η.app a : F.obj a ⟶ G.obj a` for each object `a : B`. We also have a 2-morphism
`η.naturality f : F.map f ≫ app b ⟶ app a ≫ G.map f` for each 1-morphism `f : a ⟶ b`.
These 2-morphisms satisfies the naturality condition, and preserve the identities and
the compositions modulo some adjustments of domains and codomains of 2-morphisms.
-/
structure OplaxNatTrans (F G : OplaxFunctor B C) where
  app (a : B) : F.obj a ⟶ G.obj a
  naturality {a b : B} (f : a ⟶ b) : F.map f ≫ app b ⟶ app a ≫ G.map f
  naturality_naturality' :
    ∀ {a b : B} {f g : a ⟶ b} η : f ⟶ g, (F.map₂ η ▷ app b) ≫ naturality g = naturality f ≫ (app a ◁ G.map₂ η) := by
    run_tac
      obviously
  naturality_id' :
    ∀ a : B, naturality (𝟙 a) ≫ (app a ◁ G.map_id a) = (F.map_id a ▷ app a) ≫ (λ_ (app a)).Hom ≫ (ρ_ (app a)).inv := by
    run_tac
      obviously
  naturality_comp' :
    ∀ {a b c : B} f : a ⟶ b g : b ⟶ c,
      naturality (f ≫ g) ≫ (app a ◁ G.map_comp f g) =
        (F.map_comp f g ▷ app c) ≫
          (α_ _ _ _).Hom ≫ (F.map f ◁ naturality g) ≫ (α_ _ _ _).inv ≫ (naturality f ▷ G.map g) ≫ (α_ _ _ _).Hom := by
    run_tac
      obviously

restate_axiom oplax_nat_trans.naturality_naturality'

restate_axiom oplax_nat_trans.naturality_id'

restate_axiom oplax_nat_trans.naturality_comp'

attribute [simp, reassoc]
  oplax_nat_trans.naturality_naturality oplax_nat_trans.naturality_id oplax_nat_trans.naturality_comp

namespace OplaxNatTrans

section

variable (F : OplaxFunctor B C)

/-- The identity oplax natural transformation. -/
@[simps]
def id : OplaxNatTrans F F where
  app := fun a => 𝟙 (F.obj a)
  naturality := fun a b f => (ρ_ (F.map f)).Hom ≫ (λ_ (F.map f)).inv
  naturality_naturality' := fun a b f f' η => by
    rw [assoc, ← left_unitor_inv_naturality, ← right_unitor_naturality_assoc]
  naturality_comp' := fun a b c f g => by
    rw [assoc, ← left_unitor_inv_naturality, ← right_unitor_naturality_assoc]
    simp only [triangle_assoc_comp_right_assoc, right_unitor_comp, left_unitor_comp_inv, whisker_right_comp,
      inv_hom_whisker_left_assoc, assoc, whisker_left_comp]
  naturality_id' := fun a => by
    rw [assoc, ← left_unitor_inv_naturality, ← right_unitor_naturality_assoc, unitors_equal, unitors_inv_equal]

instance : Inhabited (OplaxNatTrans F F) :=
  ⟨id F⟩

variable {F} {G H : OplaxFunctor B C} (η : OplaxNatTrans F G) (θ : OplaxNatTrans G H)

section

variable {a b c : B} {a' : C}

@[simp, reassoc]
theorem whisker_left_naturality_naturality (f : a' ⟶ G.obj a) {g h : a ⟶ b} (β : g ⟶ h) :
    (f ◁ G.map₂ β ▷ θ.app b) ≫ (f ◁ θ.naturality h) = (f ◁ θ.naturality g) ≫ (f ◁ θ.app a ◁ H.map₂ β) := by
  simp only [← whisker_left_comp, naturality_naturality]

@[simp, reassoc]
theorem whisker_right_naturality_naturality {f g : a ⟶ b} (β : f ⟶ g) (h : G.obj b ⟶ a') :
    ((F.map₂ β ▷ η.app b) ▷ h) ≫ (η.naturality g ▷ h) = (η.naturality f ▷ h) ≫ ((η.app a ◁ G.map₂ β) ▷ h) := by
  simp only [← whisker_right_comp, naturality_naturality]

@[simp, reassoc]
theorem whisker_left_naturality_comp (f : a' ⟶ G.obj a) (g : a ⟶ b) (h : b ⟶ c) :
    (f ◁ θ.naturality (g ≫ h)) ≫ (f ◁ θ.app a ◁ H.map_comp g h) =
      (f ◁ G.map_comp g h ▷ θ.app c) ≫
        (f ◁ (α_ _ _ _).Hom) ≫
          (f ◁ G.map g ◁ θ.naturality h) ≫
            (f ◁ (α_ _ _ _).inv) ≫ (f ◁ θ.naturality g ▷ H.map h) ≫ (f ◁ (α_ _ _ _).Hom) :=
  by
  simp only [← whisker_left_comp, naturality_comp]

@[simp, reassoc]
theorem whisker_right_naturality_comp (f : a ⟶ b) (g : b ⟶ c) (h : G.obj c ⟶ a') :
    (η.naturality (f ≫ g) ▷ h) ≫ ((η.app a ◁ G.map_comp f g) ▷ h) =
      ((F.map_comp f g ▷ η.app c) ▷ h) ≫
        ((α_ _ _ _).Hom ▷ h) ≫
          ((F.map f ◁ η.naturality g) ▷ h) ≫
            ((α_ _ _ _).inv ▷ h) ≫ ((η.naturality f ▷ G.map g) ▷ h) ≫ ((α_ _ _ _).Hom ▷ h) :=
  by
  simp only [← whisker_right_comp, naturality_comp]

@[simp, reassoc]
theorem whisker_left_naturality_id (f : a' ⟶ G.obj a) :
    (f ◁ θ.naturality (𝟙 a)) ≫ (f ◁ θ.app a ◁ H.map_id a) =
      (f ◁ G.map_id a ▷ θ.app a) ≫ (f ◁ (λ_ (θ.app a)).Hom) ≫ (f ◁ (ρ_ (θ.app a)).inv) :=
  by
  simp only [← whisker_left_comp, naturality_id]

@[simp, reassoc]
theorem whisker_right_naturality_id (f : G.obj a ⟶ a') :
    (η.naturality (𝟙 a) ▷ f) ≫ ((η.app a ◁ G.map_id a) ▷ f) =
      ((F.map_id a ▷ η.app a) ▷ f) ≫ ((λ_ (η.app a)).Hom ▷ f) ≫ ((ρ_ (η.app a)).inv ▷ f) :=
  by
  simp only [← whisker_right_comp, naturality_id]

end

/-- Vertical composition of oplax natural transformations. -/
@[simps]
def vcomp (η : OplaxNatTrans F G) (θ : OplaxNatTrans G H) : OplaxNatTrans F H where
  app := fun a => η.app a ≫ θ.app a
  naturality := fun a b f =>
    (α_ _ _ _).inv ≫ (η.naturality f ▷ θ.app b) ≫ (α_ _ _ _).Hom ≫ (η.app a ◁ θ.naturality f) ≫ (α_ _ _ _).inv
  naturality_naturality' := fun a b f g ι => by
    simp only [whisker_right_comp, assoc, whisker_left_comp]
    rw [← associator_inv_naturality_right, ← whisker_left_naturality_naturality_assoc, ←
      associator_naturality_middle_assoc, ← whisker_right_naturality_naturality_assoc, ←
      associator_inv_naturality_left_assoc]
  naturality_comp' := fun a b c f g => by
    simp only [whisker_right_comp, assoc, whisker_left_comp]
    rw [← associator_inv_naturality_right, whisker_left_naturality_comp_assoc, ← associator_naturality_middle_assoc,
      whisker_right_naturality_comp_assoc, ← associator_inv_naturality_left_assoc]
    rw [← pentagon_hom_hom_inv_inv_hom, associator_naturality_middle_assoc, ← pentagon_inv_hom_hom_hom_inv_assoc, ←
      associator_naturality_middle_assoc]
    slice_rhs 5 13 =>
      rw [← pentagon_inv_hom_hom_hom_hom_assoc, ← pentagon_hom_hom_inv_hom_hom, associator_naturality_left_assoc, ←
        associator_naturality_right_assoc, pentagon_inv_inv_hom_hom_inv_assoc, inv_hom_whisker_left_assoc,
        iso.hom_inv_id_assoc, whisker_exchange_assoc, associator_naturality_right_assoc, ←
        associator_naturality_left_assoc, ← pentagon_assoc]
    simp only [assoc]
  naturality_id' := fun a => by
    simp only [whisker_right_comp, assoc, whisker_left_comp]
    rw [← associator_inv_naturality_right, whisker_left_naturality_id_assoc, ← associator_naturality_middle_assoc,
      whisker_right_naturality_id_assoc, ← associator_inv_naturality_left_assoc]
    simp only [left_unitor_comp, triangle_assoc, inv_hom_whisker_right_assoc, assoc, right_unitor_comp_inv]

variable (B C)

@[simps]
instance : CategoryStruct (OplaxFunctor B C) where
  Hom := fun F G => OplaxNatTrans F G
  id := OplaxNatTrans.id
  comp := fun F G H => OplaxNatTrans.vcomp

end

section

variable {F G : OplaxFunctor B C}

/-- A modification `Γ` between oplax natural transformations `η` and `θ` consists of a family of
2-morphisms `Γ.app a : η.app a ⟶ θ.app a`, which satisfies the equation
`(F.map f ◁ app b) ≫ θ.naturality f = η.naturality f ≫ (app a ▷ G.map f)`
for each 1-morphism `f : a ⟶ b`.
-/
@[ext]
structure Modification (η θ : F ⟶ G) where
  app (a : B) : η.app a ⟶ θ.app a
  naturality' : ∀ {a b : B} f : a ⟶ b, (F.map f ◁ app b) ≫ θ.naturality f = η.naturality f ≫ (app a ▷ G.map f) := by
    run_tac
      obviously

restate_axiom modification.naturality'

attribute [simp, reassoc] modification.naturality

variable {η θ ι : F ⟶ G}

namespace Modification

variable (η)

/-- The identity modification. -/
@[simps]
def id : Modification η η where
  app := fun a => 𝟙 (η.app a)

instance : Inhabited (Modification η η) :=
  ⟨Modification.id η⟩

variable {η}

section

variable (Γ : Modification η θ) {a b c : B} {a' : C}

@[reassoc]
theorem whisker_left_naturality (f : a' ⟶ F.obj b) (g : b ⟶ c) :
    (f ◁ F.map g ◁ Γ.app c) ≫ (f ◁ θ.naturality g) = (f ◁ η.naturality g) ≫ (f ◁ Γ.app b ▷ G.map g) := by
  simp only [← bicategory.whisker_left_comp, naturality]

@[reassoc]
theorem whisker_right_naturality (f : a ⟶ b) (g : G.obj b ⟶ a') :
    ((F.map f ◁ Γ.app b) ▷ g) ≫ (θ.naturality f ▷ g) = (η.naturality f ▷ g) ≫ ((Γ.app a ▷ G.map f) ▷ g) := by
  simp only [← bicategory.whisker_right_comp, naturality]

end

/-- Vertical composition of modifications. -/
@[simps]
def vcomp (Γ : Modification η θ) (Δ : Modification θ ι) : Modification η ι where
  app := fun a => Γ.app a ≫ Δ.app a

end Modification

/-- Category structure on the oplax natural transformations between oplax_functors. -/
@[simps]
instance category (F G : OplaxFunctor B C) : Category (F ⟶ G) where
  Hom := Modification
  id := Modification.id
  comp := fun η θ ι => Modification.vcomp

/-- Construct a modification isomorphism between oplax natural transformations
by giving object level isomorphisms, and checking naturality only in the forward direction.
-/
@[simps]
def ModificationIso.ofComponents (app : ∀ a, η.app a ≅ θ.app a)
    (naturality :
      ∀ {a b} f : a ⟶ b, (F.map f ◁ (app b).Hom) ≫ θ.naturality f = η.naturality f ≫ ((app a).Hom ▷ G.map f)) :
    η ≅ θ where
  Hom := { app := fun a => (app a).Hom }
  inv :=
    { app := fun a => (app a).inv,
      naturality' := fun a b f => by
        simpa using congr_argₓ (fun f => (_ ◁ (app b).inv) ≫ f ≫ ((app a).inv ▷ _)) (naturality f).symm }

end

end OplaxNatTrans

end CategoryTheory

