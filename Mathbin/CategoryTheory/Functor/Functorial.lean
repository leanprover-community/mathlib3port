/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.CategoryTheory.Functor.Basic

/-!
# Unbundled functors, as a typeclass decorating the object-level function.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/822
> Any changes to this file require a corresponding PR to mathlib4.
-/


namespace CategoryTheory

-- declare the `v`'s first; see `category_theory.category` for an explanation
universe v v₁ v₂ v₃ u u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

-- Perhaps in the future we could redefine `functor` in terms of this, but that isn't the
-- immediate plan.
/-- A unbundled functor. -/
class Functorial (F : C → D) : Type max v₁ v₂ u₁ u₂ where
  map : ∀ {X Y : C}, (X ⟶ Y) → (F X ⟶ F Y)
  map_id' : ∀ X : C, map (𝟙 X) = 𝟙 (F X) := by obviously
  map_comp' : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), map (f ≫ g) = map f ≫ map g := by obviously
#align category_theory.functorial CategoryTheory.Functorial

/-- If `F : C → D` (just a function) has `[functorial F]`,
we can write `map F f : F X ⟶ F Y` for the action of `F` on a morphism `f : X ⟶ Y`.
-/
def map (F : C → D) [Functorial.{v₁, v₂} F] {X Y : C} (f : X ⟶ Y) : F X ⟶ F Y :=
  Functorial.map.{v₁, v₂} f
#align category_theory.map CategoryTheory.map

@[simp]
theorem map_as_map {F : C → D} [Functorial.{v₁, v₂} F] {X Y : C} {f : X ⟶ Y} :
    Functorial.map.{v₁, v₂} f = map F f :=
  rfl
#align category_theory.map_as_map CategoryTheory.map_as_map

@[simp]
theorem Functorial.map_id {F : C → D} [Functorial.{v₁, v₂} F] {X : C} : map F (𝟙 X) = 𝟙 (F X) :=
  Functorial.map_id' X
#align category_theory.functorial.map_id CategoryTheory.Functorial.map_id

@[simp]
theorem Functorial.map_comp {F : C → D} [Functorial.{v₁, v₂} F] {X Y Z : C} {f : X ⟶ Y}
    {g : Y ⟶ Z} : map F (f ≫ g) = map F f ≫ map F g :=
  Functorial.map_comp' f g
#align category_theory.functorial.map_comp CategoryTheory.Functorial.map_comp

namespace Functor

/-- Bundle a functorial function as a functor.
-/
def of (F : C → D) [I : Functorial.{v₁, v₂} F] : C ⥤ D :=
  { I with obj := F }
#align category_theory.functor.of CategoryTheory.Functor.of

end Functor

instance (F : C ⥤ D) : Functorial.{v₁, v₂} F.obj :=
  { F with }

@[simp]
theorem map_functorial_obj (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) : map F.obj f = F.map f :=
  rfl
#align category_theory.map_functorial_obj CategoryTheory.map_functorial_obj

instance functorialId : Functorial.{v₁, v₁} (id : C → C) where map X Y f := f
#align category_theory.functorial_id CategoryTheory.functorialId

section

variable {E : Type u₃} [Category.{v₃} E]

-- This is no longer viable as an instance in Lean 3.7,
-- #lint reports an instance loop
-- Will this be a problem?
/-- `G ∘ F` is a functorial if both `F` and `G` are.
-/
def functorialComp (F : C → D) [Functorial.{v₁, v₂} F] (G : D → E) [Functorial.{v₂, v₃} G] :
    Functorial.{v₁, v₃} (G ∘ F) :=
  { Functor.of F ⋙ Functor.of G with }
#align category_theory.functorial_comp CategoryTheory.functorialComp

end

end CategoryTheory

