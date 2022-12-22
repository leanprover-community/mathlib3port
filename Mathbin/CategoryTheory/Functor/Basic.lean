/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Baumann, Stephen Morgan, Scott Morrison

! This file was ported from Lean 3 source module category_theory.functor.basic
! leanprover-community/mathlib commit 207cfac9fcd06138865b5d04f7091e46d9320432
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.ReassocAxiom
import Mathbin.CategoryTheory.Category.Basic

/-!
# Functors

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/749
> Any changes to this file require a corresponding PR to mathlib4.

Defines a functor between categories, extending a `prefunctor` between quivers.

Introduces notation `C ⥤ D` for the type of all functors from `C` to `D`.
(Unfortunately the `⇒` arrow (`\functor`) is taken by core,
but in mathlib4 we should switch to this.)
-/


namespace CategoryTheory

-- declare the `v`'s first; see `category_theory.category` for an explanation
universe v v₁ v₂ v₃ u u₁ u₂ u₃

section

#print CategoryTheory.Functor /-
/-- `functor C D` represents a functor between categories `C` and `D`.

To apply a functor `F` to an object use `F.obj X`, and to a morphism use `F.map f`.

The axiom `map_id` expresses preservation of identities, and
`map_comp` expresses functoriality.

See <https://stacks.math.columbia.edu/tag/001B>.
-/
structure Functor (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D] extends
  Prefunctor C D : Type max v₁ v₂ u₁ u₂ where
  map_id' : ∀ X : C, map (𝟙 X) = 𝟙 (obj X) := by obviously
  map_comp' : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), map (f ≫ g) = map f ≫ map g := by obviously
#align category_theory.functor CategoryTheory.Functor
-/

/-- The prefunctor between the underlying quivers. -/
add_decl_doc functor.to_prefunctor

end

-- mathport name: «expr ⥤ »
infixr:26
  " ⥤ " =>-- A functor is basically a function, so give ⥤ a similar precedence to → (25).
  -- For example, `C × D ⥤ E` should parse as `(C × D) ⥤ E` not `C × (D ⥤ E)`.
  Functor

-- type as \func --
restate_axiom functor.map_id'

attribute [simp] Functor.map_id

restate_axiom functor.map_comp'

attribute [reassoc.1, simp] functor.map_comp

namespace Functor

section

variable (C : Type u₁) [Category.{v₁} C]

#print CategoryTheory.Functor.id /-
-- We don't use `@[simps]` here because we want `C` implicit for the simp lemmas.
/-- `𝟭 C` is the identity functor on a category `C`. -/
protected def id : C ⥤ C where 
  obj X := X
  map _ _ f := f
#align category_theory.functor.id CategoryTheory.Functor.id
-/

-- mathport name: «expr𝟭»
notation "𝟭" => Functor.id

-- Type this as `\sb1`
instance : Inhabited (C ⥤ C) :=
  ⟨Functor.id C⟩

variable {C}

/- warning: category_theory.functor.id_obj -> CategoryTheory.Functor.id_obj is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (X : C), Eq.{succ u2} C (CategoryTheory.Functor.obj.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) X) X
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (X : C), Eq.{succ u2} C (Prefunctor.obj.{succ u1, succ u1, u2, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1)) X) X
Case conversion may be inaccurate. Consider using '#align category_theory.functor.id_obj CategoryTheory.Functor.id_objₓ'. -/
@[simp]
theorem id_obj (X : C) : (𝟭 C).obj X = X :=
  rfl
#align category_theory.functor.id_obj CategoryTheory.Functor.id_obj

/- warning: category_theory.functor.id_map -> CategoryTheory.Functor.id_map is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.obj.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) X) (CategoryTheory.Functor.obj.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) Y)) (CategoryTheory.Functor.map.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) X Y f) f
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prefunctor.obj.{succ u1, succ u1, u2, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1)) X) (Prefunctor.obj.{succ u1, succ u1, u2, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1)) Y)) (Prefunctor.map.{succ u1, succ u1, u2, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1)) X Y f) f
Case conversion may be inaccurate. Consider using '#align category_theory.functor.id_map CategoryTheory.Functor.id_mapₓ'. -/
@[simp]
theorem id_map {X Y : C} (f : X ⟶ Y) : (𝟭 C).map f = f :=
  rfl
#align category_theory.functor.id_map CategoryTheory.Functor.id_map

end

section

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {E : Type u₃}
  [Category.{v₃} E]

#print CategoryTheory.Functor.comp /-
/-- `F ⋙ G` is the composition of a functor `F` and a functor `G` (`F` first, then `G`).
-/
@[simps obj]
def comp (F : C ⥤ D) (G : D ⥤ E) :
    C ⥤ E where 
  obj X := G.obj (F.obj X)
  map _ _ f := G.map (F.map f)
#align category_theory.functor.comp CategoryTheory.Functor.comp
-/

-- mathport name: «expr ⋙ »
infixr:80 " ⋙ " => comp

/- warning: category_theory.functor.comp_map -> CategoryTheory.Functor.comp_map is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u1, u4} C] {D : Type.{u5}} [_inst_2 : CategoryTheory.Category.{u2, u5} D] {E : Type.{u6}} [_inst_3 : CategoryTheory.Category.{u3, u6} E] (F : CategoryTheory.Functor.{u1, u2, u4, u5} C _inst_1 D _inst_2) (G : CategoryTheory.Functor.{u2, u3, u5, u6} D _inst_2 E _inst_3) {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} C (CategoryTheory.Category.toCategoryStruct.{u1, u4} C _inst_1)) X Y), Eq.{succ u3} (Quiver.Hom.{succ u3, u6} E (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} E (CategoryTheory.Category.toCategoryStruct.{u3, u6} E _inst_3)) (CategoryTheory.Functor.obj.{u1, u3, u4, u6} C _inst_1 E _inst_3 (CategoryTheory.Functor.comp.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 E _inst_3 F G) X) (CategoryTheory.Functor.obj.{u1, u3, u4, u6} C _inst_1 E _inst_3 (CategoryTheory.Functor.comp.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 E _inst_3 F G) Y)) (CategoryTheory.Functor.map.{u1, u3, u4, u6} C _inst_1 E _inst_3 (CategoryTheory.Functor.comp.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 E _inst_3 F G) X Y f) (CategoryTheory.Functor.map.{u2, u3, u5, u6} D _inst_2 E _inst_3 G (CategoryTheory.Functor.obj.{u1, u2, u4, u5} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u2, u4, u5} C _inst_1 D _inst_2 F Y) (CategoryTheory.Functor.map.{u1, u2, u4, u5} C _inst_1 D _inst_2 F X Y f))
but is expected to have type
  forall {C : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u1, u4} C] {D : Type.{u5}} [_inst_2 : CategoryTheory.Category.{u2, u5} D] {E : Type.{u6}} [_inst_3 : CategoryTheory.Category.{u3, u6} E] (F : CategoryTheory.Functor.{u1, u2, u4, u5} C _inst_1 D _inst_2) (G : CategoryTheory.Functor.{u2, u3, u5, u6} D _inst_2 E _inst_3) {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} C (CategoryTheory.Category.toCategoryStruct.{u1, u4} C _inst_1)) X Y), Eq.{succ u3} (Quiver.Hom.{succ u3, u6} E (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} E (CategoryTheory.Category.toCategoryStruct.{u3, u6} E _inst_3)) (Prefunctor.obj.{succ u1, succ u3, u4, u6} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} C (CategoryTheory.Category.toCategoryStruct.{u1, u4} C _inst_1)) E (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} E (CategoryTheory.Category.toCategoryStruct.{u3, u6} E _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u3, u4, u6} C _inst_1 E _inst_3 (CategoryTheory.Functor.comp.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 E _inst_3 F G)) X) (Prefunctor.obj.{succ u1, succ u3, u4, u6} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} C (CategoryTheory.Category.toCategoryStruct.{u1, u4} C _inst_1)) E (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} E (CategoryTheory.Category.toCategoryStruct.{u3, u6} E _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u3, u4, u6} C _inst_1 E _inst_3 (CategoryTheory.Functor.comp.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 E _inst_3 F G)) Y)) (Prefunctor.map.{succ u1, succ u3, u4, u6} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} C (CategoryTheory.Category.toCategoryStruct.{u1, u4} C _inst_1)) E (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} E (CategoryTheory.Category.toCategoryStruct.{u3, u6} E _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u3, u4, u6} C _inst_1 E _inst_3 (CategoryTheory.Functor.comp.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 E _inst_3 F G)) X Y f) (Prefunctor.map.{succ u2, succ u3, u5, u6} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u5} D (CategoryTheory.Category.toCategoryStruct.{u2, u5} D _inst_2)) E (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} E (CategoryTheory.Category.toCategoryStruct.{u3, u6} E _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u2, u3, u5, u6} D _inst_2 E _inst_3 G) (Prefunctor.obj.{succ u1, succ u2, u4, u5} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} C (CategoryTheory.Category.toCategoryStruct.{u1, u4} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u5} D (CategoryTheory.Category.toCategoryStruct.{u2, u5} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u4, u5} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u2, u4, u5} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} C (CategoryTheory.Category.toCategoryStruct.{u1, u4} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u5} D (CategoryTheory.Category.toCategoryStruct.{u2, u5} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u4, u5} C _inst_1 D _inst_2 F) Y) (Prefunctor.map.{succ u1, succ u2, u4, u5} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} C (CategoryTheory.Category.toCategoryStruct.{u1, u4} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u5} D (CategoryTheory.Category.toCategoryStruct.{u2, u5} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u4, u5} C _inst_1 D _inst_2 F) X Y f))
Case conversion may be inaccurate. Consider using '#align category_theory.functor.comp_map CategoryTheory.Functor.comp_mapₓ'. -/
@[simp]
theorem comp_map (F : C ⥤ D) (G : D ⥤ E) {X Y : C} (f : X ⟶ Y) : (F ⋙ G).map f = G.map (F.map f) :=
  rfl
#align category_theory.functor.comp_map CategoryTheory.Functor.comp_map

#print CategoryTheory.Functor.comp_id /-
-- These are not simp lemmas because rewriting along equalities between functors
-- is not necessarily a good idea.
-- Natural isomorphisms are also provided in `whiskering.lean`.
protected theorem comp_id (F : C ⥤ D) : F ⋙ 𝟭 D = F := by cases F <;> rfl
#align category_theory.functor.comp_id CategoryTheory.Functor.comp_id
-/

#print CategoryTheory.Functor.id_comp /-
protected theorem id_comp (F : C ⥤ D) : 𝟭 C ⋙ F = F := by cases F <;> rfl
#align category_theory.functor.id_comp CategoryTheory.Functor.id_comp
-/

/- warning: category_theory.functor.map_dite -> CategoryTheory.Functor.map_dite is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C} {Y : C} {P : Prop} [_inst_4 : Decidable P] (f : P -> (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y)) (g : (Not P) -> (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y)), Eq.{succ u2} (Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F Y)) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X Y (dite.{succ u1} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) P _inst_4 (fun (h : P) => f h) (fun (h : Not P) => g h))) (dite.{succ u2} (Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F Y)) P _inst_4 (fun (h : P) => CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X Y (f h)) (fun (h : Not P) => CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X Y (g h)))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C} {Y : C} {P : Prop} [_inst_4 : Decidable P] (f : P -> (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y)) (g : (Not P) -> (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y)), Eq.{succ u2} (Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) Y)) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X Y (dite.{succ u1} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) P _inst_4 (fun (h : P) => f h) (fun (h : Not P) => g h))) (dite.{succ u2} (Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) Y)) P _inst_4 (fun (h : P) => Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X Y (f h)) (fun (h : Not P) => Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X Y (g h)))
Case conversion may be inaccurate. Consider using '#align category_theory.functor.map_dite CategoryTheory.Functor.map_diteₓ'. -/
@[simp]
theorem map_dite (F : C ⥤ D) {X Y : C} {P : Prop} [Decidable P] (f : P → (X ⟶ Y))
    (g : ¬P → (X ⟶ Y)) :
    F.map (if h : P then f h else g h) = if h : P then F.map (f h) else F.map (g h) := by
  split_ifs <;> rfl
#align category_theory.functor.map_dite CategoryTheory.Functor.map_dite

@[simp]
theorem to_prefunctor_obj (F : C ⥤ D) (X : C) : F.toPrefunctor.obj X = F.obj X :=
  rfl
#align category_theory.functor.to_prefunctor_obj CategoryTheory.Functor.to_prefunctor_obj

@[simp]
theorem to_prefunctor_map (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) : F.toPrefunctor.map f = F.map f :=
  rfl
#align category_theory.functor.to_prefunctor_map CategoryTheory.Functor.to_prefunctor_map

#print CategoryTheory.Functor.toPrefunctor_comp /-
@[simp]
theorem toPrefunctor_comp (F : C ⥤ D) (G : D ⥤ E) :
    F.toPrefunctor.comp G.toPrefunctor = (F ⋙ G).toPrefunctor :=
  rfl
#align category_theory.functor.to_prefunctor_comp CategoryTheory.Functor.toPrefunctor_comp
-/

end

end Functor

end CategoryTheory

