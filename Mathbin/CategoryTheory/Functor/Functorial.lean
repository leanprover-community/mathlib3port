/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module category_theory.functor.functorial
! leanprover-community/mathlib commit 448144f7ae193a8990cb7473c9e9a01990f64ac7
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Functor.Basic

/-!
# Unbundled functors, as a typeclass decorating the object-level function.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


namespace CategoryTheory

-- declare the `v`'s first; see `category_theory.category` for an explanation
universe v v₁ v₂ v₃ u u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

#print CategoryTheory.Functorial /-
-- Perhaps in the future we could redefine `functor` in terms of this, but that isn't the
-- immediate plan.
/-- A unbundled functor. -/
class Functorial (F : C → D) : Type max v₁ v₂ u₁ u₂ where
  map : ∀ {X Y : C}, (X ⟶ Y) → (F X ⟶ F Y)
  map_id' : ∀ X : C, map (𝟙 X) = 𝟙 (F X) := by obviously
  map_comp' : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), map (f ≫ g) = map f ≫ map g := by obviously
#align category_theory.functorial CategoryTheory.Functorial
-/

#print CategoryTheory.map /-
/-- If `F : C → D` (just a function) has `[functorial F]`,
we can write `map F f : F X ⟶ F Y` for the action of `F` on a morphism `f : X ⟶ Y`.
-/
def map (F : C → D) [Functorial.{v₁, v₂} F] {X Y : C} (f : X ⟶ Y) : F X ⟶ F Y :=
  Functorial.map'.{v₁, v₂} f
#align category_theory.map CategoryTheory.map
-/

#print CategoryTheory.map'_as_map /-
@[simp]
theorem map'_as_map {F : C → D} [Functorial.{v₁, v₂} F] {X Y : C} {f : X ⟶ Y} :
    Functorial.map'.{v₁, v₂} f = map F f :=
  rfl
#align category_theory.map_as_map CategoryTheory.map'_as_map
-/

#print CategoryTheory.Functorial.map_id /-
@[simp]
theorem Functorial.map_id {F : C → D} [Functorial.{v₁, v₂} F] {X : C} : map F (𝟙 X) = 𝟙 (F X) :=
  Functorial.map'_id' X
#align category_theory.functorial.map_id CategoryTheory.Functorial.map_id
-/

#print CategoryTheory.Functorial.map_comp /-
@[simp]
theorem Functorial.map_comp {F : C → D} [Functorial.{v₁, v₂} F] {X Y Z : C} {f : X ⟶ Y}
    {g : Y ⟶ Z} : map F (f ≫ g) = map F f ≫ map F g :=
  Functorial.map'_comp' f g
#align category_theory.functorial.map_comp CategoryTheory.Functorial.map_comp
-/

namespace Functor

#print CategoryTheory.Functor.of /-
/-- Bundle a functorial function as a functor.
-/
def of (F : C → D) [I : Functorial.{v₁, v₂} F] : C ⥤ D :=
  { I with obj := F }
#align category_theory.functor.of CategoryTheory.Functor.of
-/

end Functor

instance (F : C ⥤ D) : Functorial.{v₁, v₂} F.obj :=
  { F with }

/- warning: category_theory.map_functorial_obj -> CategoryTheory.map_functorial_obj is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y), Eq.{succ u2} (Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F Y)) (CategoryTheory.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) (CategoryTheory.Functor.obj.functorial.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X Y f) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X Y f)
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y), Eq.{succ u2} (Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) Y)) (CategoryTheory.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F)) (CategoryTheory.instFunctorialObjToQuiverToCategoryStructToQuiverToCategoryStructToPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X Y f) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X Y f)
Case conversion may be inaccurate. Consider using '#align category_theory.map_functorial_obj CategoryTheory.map_functorial_objₓ'. -/
@[simp]
theorem map_functorial_obj (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) : map F.obj f = F.map f :=
  rfl
#align category_theory.map_functorial_obj CategoryTheory.map_functorial_obj

#print CategoryTheory.functorial_id /-
instance functorial_id : Functorial.{v₁, v₁} (id : C → C) where map X Y f := f
#align category_theory.functorial_id CategoryTheory.functorial_id
-/

section

variable {E : Type u₃} [Category.{v₃} E]

#print CategoryTheory.functorial_comp /-
-- This is no longer viable as an instance in Lean 3.7,
-- #lint reports an instance loop
-- Will this be a problem?
/-- `G ∘ F` is a functorial if both `F` and `G` are.
-/
def functorial_comp (F : C → D) [Functorial.{v₁, v₂} F] (G : D → E) [Functorial.{v₂, v₃} G] :
    Functorial.{v₁, v₃} (G ∘ F) :=
  { Functor.of F ⋙ Functor.of G with }
#align category_theory.functorial_comp CategoryTheory.functorial_comp
-/

end

end CategoryTheory

