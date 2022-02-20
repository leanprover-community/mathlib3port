/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import Mathbin.CategoryTheory.Bicategory.Basic

/-!
# Oplax functors

An oplax functor `F` between bicategories `B` and `C` consists of
* a function between objects `F.obj : B ⟶ C`,
* a family of functions between 1-morphisms `F.map : (a ⟶ b) → (obj a ⟶ obj b)`,
* a family of functions between 2-morphisms `F.map₂ : (f ⟶ g) → (map f ⟶ map g)`,
* a family of 2-morphisms `F.map_id a : F.map (𝟙 a) ⟶ 𝟙 (F.obj a)`,
* a family of 2-morphisms `F.map_comp f g : F.map (f ≫ g) ⟶ F.map f ≫ F.map g`, and
* certain consistency conditions on them.

## Main definitions

* `oplax_functor B C` : an oplax functor between bicategories `B` and `C`
* `oplax_functor.comp F G` : the composition of oplax functors

## Future work

There are two types of functors between bicategories, called lax and oplax functors, depending on
the directions of `map_id` and `map_comp`. We may need both in mathlib in the future, but for
now we only define oplax functors.

In addition, if we require `map_id` and `map_comp` to be isomorphisms, we obtain the definition
of pseudofunctors. There are several possible design choices to implement pseudofunctors,
but the choice is left to future development.
-/


namespace CategoryTheory

open Category Bicategory

open_locale Bicategory

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

section

variable (B : Type u₁) [Quiver.{v₁ + 1} B] [∀ a b : B, Quiver.{w₁ + 1} (a ⟶ b)]

variable (C : Type u₂) [Quiver.{v₂ + 1} C] [∀ a b : C, Quiver.{w₂ + 1} (a ⟶ b)]

/-- A prelax functor between bicategories consists of functions between objects,
1-morphisms, and 2-morphisms. This structure will be extended to define `oplax_functor`.
-/
structure PrelaxFunctor extends Prefunctor B C : Type max w₁ w₂ v₁ v₂ u₁ u₂ where
  map₂ {a b : B} {f g : a ⟶ b} : (f ⟶ g) → (map f ⟶ map g)

/-- The prefunctor between the underlying quivers. -/
add_decl_doc prelax_functor.to_prefunctor

namespace PrelaxFunctor

variable {B C} {D : Type u₃} [Quiver.{v₃ + 1} D] [∀ a b : D, Quiver.{w₃ + 1} (a ⟶ b)]

variable (F : PrelaxFunctor B C) (G : PrelaxFunctor C D)

@[simp]
theorem to_prefunctor_obj : F.toPrefunctor.obj = F.obj :=
  rfl

@[simp]
theorem to_prefunctor_map : F.toPrefunctor.map = F.map :=
  rfl

variable (B)

/-- The identity prelax functor. -/
@[simps]
def id : PrelaxFunctor B B :=
  { Prefunctor.id B with map₂ := fun a b f g η => η }

instance : Inhabited (PrelaxFunctor B B) :=
  ⟨PrelaxFunctor.id B⟩

variable {B}

/-- Composition of prelax functors. -/
@[simps]
def comp : PrelaxFunctor B D :=
  { F.toPrefunctor.comp G.toPrefunctor with map₂ := fun a b f g η => G.map₂ (F.map₂ η) }

end PrelaxFunctor

end

section

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]

/-- This auxiliary definition states that oplax functors preserve the associators
modulo some adjustments of domains and codomains of 2-morphisms.
-/
/-
We use this auxiliary definition instead of writing it directly in the definition
of oplax functors because doing so will cause a timeout.
-/
@[simp]
def OplaxFunctor.Map₂AssociatorAux (obj : B → C) (map : ∀ {X Y : B}, (X ⟶ Y) → (obj X ⟶ obj Y))
    (map₂ : ∀ {a b : B} {f g : a ⟶ b}, (f ⟶ g) → (map f ⟶ map g))
    (map_comp : ∀ {a b c : B} f : a ⟶ b g : b ⟶ c, map (f ≫ g) ⟶ map f ≫ map g) {a b c d : B} (f : a ⟶ b) (g : b ⟶ c)
    (h : c ⟶ d) : Prop :=
  map₂ (α_ f g h).Hom ≫ map_comp f (g ≫ h) ≫ (map f ◁ map_comp g h) =
    map_comp (f ≫ g) h ≫ (map_comp f g ▷ map h) ≫ (α_ (map f) (map g) (map h)).Hom

variable (B C)

/-- An oplax functor `F` between bicategories `B` and `C` consists of functions between objects,
1-morphisms, and 2-morphisms.

Unlike functors between categories, functions between 1-morphisms do not need to strictly commute
with compositions, and do not need to strictly preserve the identity. Instead, there are
specified 2-morphisms `F.map (𝟙 a) ⟶ 𝟙 (F.obj a)` and `F.map (f ≫ g) ⟶ F.map f ≫ F.map g`.

Functions between 2-morphisms strictly commute with compositions and preserve the identity.
They also preserve the associator, the left unitor, and the right unitor modulo some adjustments
of domains and codomains of 2-morphisms.
-/
structure OplaxFunctor extends PrelaxFunctor B C : Type max w₁ w₂ v₁ v₂ u₁ u₂ where
  map_id (a : B) : map (𝟙 a) ⟶ 𝟙 (obj a)
  map_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) : map (f ≫ g) ⟶ map f ≫ map g
  map_comp_naturality_left' :
    ∀ {a b c : B} {f f' : a ⟶ b} η : f ⟶ f' g : b ⟶ c,
      map₂ (η ▷ g) ≫ map_comp f' g = map_comp f g ≫ (map₂ η ▷ map g) := by
    run_tac
      obviously
  map_comp_naturality_right' :
    ∀ {a b c : B} f : a ⟶ b {g g' : b ⟶ c} η : g ⟶ g',
      map₂ (f ◁ η) ≫ map_comp f g' = map_comp f g ≫ (map f ◁ map₂ η) := by
    run_tac
      obviously
  map₂_id' : ∀ {a b : B} f : a ⟶ b, map₂ (𝟙 f) = 𝟙 (map f) := by
    run_tac
      obviously
  map₂_comp' : ∀ {a b : B} {f g h : a ⟶ b} η : f ⟶ g θ : g ⟶ h, map₂ (η ≫ θ) = map₂ η ≫ map₂ θ := by
    run_tac
      obviously
  map₂_associator' :
    ∀ {a b c d : B} f : a ⟶ b g : b ⟶ c h : c ⟶ d,
      OplaxFunctor.Map₂AssociatorAux obj (fun a b => map) (fun a b f g => map₂) (fun a b c => map_comp) f g h := by
    run_tac
      obviously
  map₂_left_unitor' :
    ∀ {a b : B} f : a ⟶ b, map₂ (λ_ f).Hom = map_comp (𝟙 a) f ≫ (map_id a ▷ map f) ≫ (λ_ (map f)).Hom := by
    run_tac
      obviously
  map₂_right_unitor' :
    ∀ {a b : B} f : a ⟶ b, map₂ (ρ_ f).Hom = map_comp f (𝟙 b) ≫ (map f ◁ map_id b) ≫ (ρ_ (map f)).Hom := by
    run_tac
      obviously

restate_axiom oplax_functor.map_comp_naturality_left'

restate_axiom oplax_functor.map_comp_naturality_right'

restate_axiom oplax_functor.map₂_id'

restate_axiom oplax_functor.map₂_comp'

restate_axiom oplax_functor.map₂_associator'

restate_axiom oplax_functor.map₂_left_unitor'

restate_axiom oplax_functor.map₂_right_unitor'

attribute [simp]
  oplax_functor.map_comp_naturality_left oplax_functor.map_comp_naturality_right oplax_functor.map₂_id oplax_functor.map₂_associator

attribute [reassoc]
  oplax_functor.map_comp_naturality_left oplax_functor.map_comp_naturality_right oplax_functor.map₂_comp oplax_functor.map₂_associator oplax_functor.map₂_left_unitor oplax_functor.map₂_right_unitor

attribute [simp] oplax_functor.map₂_comp oplax_functor.map₂_left_unitor oplax_functor.map₂_right_unitor

namespace OplaxFunctor

variable {B} {C} {D : Type u₃} [Bicategory.{w₃, v₃} D]

variable (F : OplaxFunctor B C) (G : OplaxFunctor C D)

/-- Function between 1-morphisms as a functor. -/
@[simps]
def mapFunctor (a b : B) : (a ⟶ b) ⥤ (F.obj a ⟶ F.obj b) where
  obj := fun f => F.map f
  map := fun f g η => F.map₂ η

/-- The prelax functor between the underlying quivers. -/
add_decl_doc oplax_functor.to_prelax_functor

@[simp]
theorem to_prelax_functor_obj : F.toPrelaxFunctor.obj = F.obj :=
  rfl

@[simp]
theorem to_prelax_functor_map : F.toPrelaxFunctor.map = F.map :=
  rfl

@[simp]
theorem to_prelax_functor_map₂ : F.toPrelaxFunctor.map₂ = F.map₂ :=
  rfl

variable (B)

/-- The identity oplax functor. -/
@[simps]
def id : OplaxFunctor B B :=
  { PrelaxFunctor.id B with map_id := fun a => 𝟙 (𝟙 a), map_comp := fun a b c f g => 𝟙 (f ≫ g) }

instance : Inhabited (OplaxFunctor B B) :=
  ⟨id B⟩

variable {B}

/-- Composition of oplax functors. -/
@[simps]
def comp : OplaxFunctor B D :=
  { F.toPrelaxFunctor.comp G.toPrelaxFunctor with
    map_id := fun a => (G.mapFunctor _ _).map (F.map_id a) ≫ G.map_id (F.obj a),
    map_comp := fun a b c f g => (G.mapFunctor _ _).map (F.map_comp f g) ≫ G.map_comp (F.map f) (F.map g),
    map_comp_naturality_left' := fun a b c f f' η g => by
      dsimp
      rw [← map₂_comp_assoc, map_comp_naturality_left, map₂_comp_assoc, map_comp_naturality_left, assoc],
    map_comp_naturality_right' := fun a b c f g g' η => by
      dsimp
      rw [← map₂_comp_assoc, map_comp_naturality_right, map₂_comp_assoc, map_comp_naturality_right, assoc],
    map₂_associator' := fun a b c d f g h => by
      dsimp
      simp only [map₂_associator, ← map₂_comp_assoc, ← map_comp_naturality_right_assoc, whisker_left_comp, assoc]
      simp only [map₂_associator, map₂_comp, map_comp_naturality_left_assoc, whisker_right_comp, assoc],
    map₂_left_unitor' := fun a b f => by
      dsimp
      simp only [map₂_left_unitor, map₂_comp, map_comp_naturality_left_assoc, whisker_right_comp, assoc],
    map₂_right_unitor' := fun a b f => by
      dsimp
      simp only [map₂_right_unitor, map₂_comp, map_comp_naturality_right_assoc, whisker_left_comp, assoc] }

end OplaxFunctor

end

end CategoryTheory

