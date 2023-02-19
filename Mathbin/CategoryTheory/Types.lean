/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Scott Morrison, Johannes Hölzl

! This file was ported from Lean 3 source module category_theory.types
! leanprover-community/mathlib commit e97cf15cd1aec9bd5c193b2ffac5a6dc9118912b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.EpiMono
import Mathbin.CategoryTheory.Functor.FullyFaithful
import Mathbin.Logic.Equiv.Basic

/-!
# The category `Type`.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this section we set up the theory so that Lean's types and functions between them
can be viewed as a `large_category` in our framework.

Lean can not transparently view a function as a morphism in this category, and needs a hint in
order to be able to type check. We provide the abbreviation `as_hom f` to guide type checking,
as well as a corresponding notation `↾ f`. (Entered as `\upr `.) The notation is enabled using
`open_locale category_theory.Type`.

We provide various simplification lemmas for functors and natural transformations valued in `Type`.

We define `ulift_functor`, from `Type u` to `Type (max u v)`, and show that it is fully faithful
(but not, of course, essentially surjective).

We prove some basic facts about the category `Type`:
*  epimorphisms are surjections and monomorphisms are injections,
* `iso` is both `iso` and `equiv` to `equiv` (at least within a fixed universe),
* every type level `is_lawful_functor` gives a categorical functor `Type ⥤ Type`
  (the corresponding fact about monads is in `src/category_theory/monad/types.lean`).
-/


namespace CategoryTheory

-- morphism levels before object levels. See note [category_theory universes].
universe v v' w u u'

#print CategoryTheory.types /-
/- The `@[to_additive]` attribute is just a hint that expressions involving this instance can
  still be additivized. -/
@[to_additive CategoryTheory.types]
instance types : LargeCategory (Type u)
    where
  Hom a b := a → b
  id a := id
  comp _ _ _ f g := g ∘ f
#align category_theory.types CategoryTheory.types
#align category_theory.types CategoryTheory.types
-/

#print CategoryTheory.types_hom /-
theorem types_hom {α β : Type u} : (α ⟶ β) = (α → β) :=
  rfl
#align category_theory.types_hom CategoryTheory.types_hom
-/

#print CategoryTheory.types_id /-
theorem types_id (X : Type u) : 𝟙 X = id :=
  rfl
#align category_theory.types_id CategoryTheory.types_id
-/

#print CategoryTheory.types_comp /-
theorem types_comp {X Y Z : Type u} (f : X ⟶ Y) (g : Y ⟶ Z) : f ≫ g = g ∘ f :=
  rfl
#align category_theory.types_comp CategoryTheory.types_comp
-/

#print CategoryTheory.types_id_apply /-
@[simp]
theorem types_id_apply (X : Type u) (x : X) : (𝟙 X : X → X) x = x :=
  rfl
#align category_theory.types_id_apply CategoryTheory.types_id_apply
-/

#print CategoryTheory.types_comp_apply /-
@[simp]
theorem types_comp_apply {X Y Z : Type u} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = g (f x) :=
  rfl
#align category_theory.types_comp_apply CategoryTheory.types_comp_apply
-/

#print CategoryTheory.hom_inv_id_apply /-
@[simp]
theorem hom_inv_id_apply {X Y : Type u} (f : X ≅ Y) (x : X) : f.inv (f.Hom x) = x :=
  congr_fun f.hom_inv_id x
#align category_theory.hom_inv_id_apply CategoryTheory.hom_inv_id_apply
-/

#print CategoryTheory.inv_hom_id_apply /-
@[simp]
theorem inv_hom_id_apply {X Y : Type u} (f : X ≅ Y) (y : Y) : f.Hom (f.inv y) = y :=
  congr_fun f.inv_hom_id y
#align category_theory.inv_hom_id_apply CategoryTheory.inv_hom_id_apply
-/

#print CategoryTheory.asHom /-
-- Unfortunately without this wrapper we can't use `category_theory` idioms, such as `is_iso f`.
/-- `as_hom f` helps Lean type check a function as a morphism in the category `Type`. -/
abbrev asHom {α β : Type u} (f : α → β) : α ⟶ β :=
  f
#align category_theory.as_hom CategoryTheory.asHom
-/

-- mathport name: category_theory.as_hom
-- If you don't mind some notation you can use fewer keystrokes:
scoped[CategoryTheory.Type] notation "↾" f:200 => CategoryTheory.asHom f

-- type as \upr in VScode
section

-- We verify the expected type checking behaviour of `as_hom`.
variable (α β γ : Type u) (f : α → β) (g : β → γ)

example : α → γ :=
  ↾f ≫ ↾g

example [IsIso (↾f)] : Mono (↾f) := by infer_instance

example [IsIso (↾f)] : ↾f ≫ inv (↾f) = 𝟙 α := by simp

end

namespace Functor

variable {J : Type u} [Category.{v} J]

/- warning: category_theory.functor.sections -> CategoryTheory.Functor.sections is a dubious translation:
lean 3 declaration is
  forall {J : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} J] (F : CategoryTheory.Functor.{u1, u2, u3, succ u2} J _inst_1 Type.{u2} CategoryTheory.types.{u2}), Set.{max u3 u2} (forall (j : J), CategoryTheory.Functor.obj.{u1, u2, u3, succ u2} J _inst_1 Type.{u2} CategoryTheory.types.{u2} F j)
but is expected to have type
  forall {J : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} J] (F : CategoryTheory.Functor.{u1, u2, u3, succ u2} J _inst_1 Type.{u2} CategoryTheory.types.{u2}), Set.{max u3 u2} (forall (j : J), Prefunctor.obj.{succ u1, succ u2, u3, succ u2} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} J (CategoryTheory.Category.toCategoryStruct.{u1, u3} J _inst_1)) Type.{u2} (CategoryTheory.CategoryStruct.toQuiver.{u2, succ u2} Type.{u2} (CategoryTheory.Category.toCategoryStruct.{u2, succ u2} Type.{u2} CategoryTheory.types.{u2})) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, succ u2} J _inst_1 Type.{u2} CategoryTheory.types.{u2} F) j)
Case conversion may be inaccurate. Consider using '#align category_theory.functor.sections CategoryTheory.Functor.sectionsₓ'. -/
/-- The sections of a functor `J ⥤ Type` are
the choices of a point `u j : F.obj j` for each `j`,
such that `F.map f (u j) = u j` for every morphism `f : j ⟶ j'`.

We later use these to define limits in `Type` and in many concrete categories.
-/
def sections (F : J ⥤ Type w) : Set (∀ j, F.obj j) :=
  { u | ∀ {j j'} (f : j ⟶ j'), F.map f (u j) = u j' }
#align category_theory.functor.sections CategoryTheory.Functor.sections

end Functor

namespace FunctorToTypes

variable {C : Type u} [Category.{v} C] (F G H : C ⥤ Type w) {X Y Z : C}

variable (σ : F ⟶ G) (τ : G ⟶ H)

/- warning: category_theory.functor_to_types.map_comp_apply -> CategoryTheory.FunctorToTypes.map_comp_apply is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] (F : CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) {X : C} {Y : C} {Z : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) (g : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) Y Z) (a : CategoryTheory.Functor.obj.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} F X), Eq.{succ u2} (CategoryTheory.Functor.obj.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} F Z) (CategoryTheory.Functor.map.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} F X Z (CategoryTheory.CategoryStruct.comp.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1) X Y Z f g) a) (CategoryTheory.Functor.map.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} F Y Z g (CategoryTheory.Functor.map.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} F X Y f a))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] (F : CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) {X : C} {Y : C} {Z : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) (g : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) Y Z) (a : Prefunctor.obj.{succ u1, succ u2, u3, succ u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) Type.{u2} (CategoryTheory.CategoryStruct.toQuiver.{u2, succ u2} Type.{u2} (CategoryTheory.Category.toCategoryStruct.{u2, succ u2} Type.{u2} CategoryTheory.types.{u2})) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} F) X), Eq.{succ u2} (Prefunctor.obj.{succ u1, succ u2, u3, succ u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) Type.{u2} (CategoryTheory.CategoryStruct.toQuiver.{u2, succ u2} Type.{u2} (CategoryTheory.Category.toCategoryStruct.{u2, succ u2} Type.{u2} CategoryTheory.types.{u2})) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} F) Z) (Prefunctor.map.{succ u1, succ u2, u3, succ u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) Type.{u2} (CategoryTheory.CategoryStruct.toQuiver.{u2, succ u2} Type.{u2} (CategoryTheory.Category.toCategoryStruct.{u2, succ u2} Type.{u2} CategoryTheory.types.{u2})) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} F) X Z (CategoryTheory.CategoryStruct.comp.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1) X Y Z f g) a) (Prefunctor.map.{succ u1, succ u2, u3, succ u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) Type.{u2} (CategoryTheory.CategoryStruct.toQuiver.{u2, succ u2} Type.{u2} (CategoryTheory.Category.toCategoryStruct.{u2, succ u2} Type.{u2} CategoryTheory.types.{u2})) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} F) Y Z g (Prefunctor.map.{succ u1, succ u2, u3, succ u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) Type.{u2} (CategoryTheory.CategoryStruct.toQuiver.{u2, succ u2} Type.{u2} (CategoryTheory.Category.toCategoryStruct.{u2, succ u2} Type.{u2} CategoryTheory.types.{u2})) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} F) X Y f a))
Case conversion may be inaccurate. Consider using '#align category_theory.functor_to_types.map_comp_apply CategoryTheory.FunctorToTypes.map_comp_applyₓ'. -/
@[simp]
theorem map_comp_apply (f : X ⟶ Y) (g : Y ⟶ Z) (a : F.obj X) :
    (F.map (f ≫ g)) a = (F.map g) ((F.map f) a) := by simp [types_comp]
#align category_theory.functor_to_types.map_comp_apply CategoryTheory.FunctorToTypes.map_comp_apply

/- warning: category_theory.functor_to_types.map_id_apply -> CategoryTheory.FunctorToTypes.map_id_apply is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] (F : CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) {X : C} (a : CategoryTheory.Functor.obj.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} F X), Eq.{succ u2} (CategoryTheory.Functor.obj.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} F X) (CategoryTheory.Functor.map.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} F X X (CategoryTheory.CategoryStruct.id.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1) X) a) a
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] (F : CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) {X : C} (a : Prefunctor.obj.{succ u1, succ u2, u3, succ u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) Type.{u2} (CategoryTheory.CategoryStruct.toQuiver.{u2, succ u2} Type.{u2} (CategoryTheory.Category.toCategoryStruct.{u2, succ u2} Type.{u2} CategoryTheory.types.{u2})) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} F) X), Eq.{succ u2} (Prefunctor.obj.{succ u1, succ u2, u3, succ u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) Type.{u2} (CategoryTheory.CategoryStruct.toQuiver.{u2, succ u2} Type.{u2} (CategoryTheory.Category.toCategoryStruct.{u2, succ u2} Type.{u2} CategoryTheory.types.{u2})) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} F) X) (Prefunctor.map.{succ u1, succ u2, u3, succ u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) Type.{u2} (CategoryTheory.CategoryStruct.toQuiver.{u2, succ u2} Type.{u2} (CategoryTheory.Category.toCategoryStruct.{u2, succ u2} Type.{u2} CategoryTheory.types.{u2})) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} F) X X (CategoryTheory.CategoryStruct.id.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1) X) a) a
Case conversion may be inaccurate. Consider using '#align category_theory.functor_to_types.map_id_apply CategoryTheory.FunctorToTypes.map_id_applyₓ'. -/
@[simp]
theorem map_id_apply (a : F.obj X) : (F.map (𝟙 X)) a = a := by simp [types_id]
#align category_theory.functor_to_types.map_id_apply CategoryTheory.FunctorToTypes.map_id_apply

/- warning: category_theory.functor_to_types.naturality -> CategoryTheory.FunctorToTypes.naturality is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] (F : CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (G : CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) {X : C} {Y : C} (σ : Quiver.Hom.{succ (max u3 u2), max u1 u2 u3 (succ u2)} (CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.CategoryStruct.toQuiver.{max u3 u2, max u1 u2 u3 (succ u2)} (CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.Category.toCategoryStruct.{max u3 u2, max u1 u2 u3 (succ u2)} (CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.Functor.category.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}))) F G) (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) (x : CategoryTheory.Functor.obj.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} F X), Eq.{succ u2} (CategoryTheory.Functor.obj.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} G Y) (CategoryTheory.NatTrans.app.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} F G σ Y (CategoryTheory.Functor.map.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} F X Y f x)) (CategoryTheory.Functor.map.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} G X Y f (CategoryTheory.NatTrans.app.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} F G σ X x))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] (F : CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (G : CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) {X : C} {Y : C} (σ : Quiver.Hom.{max (succ u3) (succ u2), max (max u3 u1) (succ u2)} (CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.CategoryStruct.toQuiver.{max u3 u2, max (max u3 u1) (succ u2)} (CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.Category.toCategoryStruct.{max u3 u2, max (max u3 u1) (succ u2)} (CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.Functor.category.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}))) F G) (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) (x : Prefunctor.obj.{succ u1, succ u2, u3, succ u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) Type.{u2} (CategoryTheory.CategoryStruct.toQuiver.{u2, succ u2} Type.{u2} (CategoryTheory.Category.toCategoryStruct.{u2, succ u2} Type.{u2} CategoryTheory.types.{u2})) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} F) X), Eq.{succ u2} (Prefunctor.obj.{succ u1, succ u2, u3, succ u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) Type.{u2} (CategoryTheory.CategoryStruct.toQuiver.{u2, succ u2} Type.{u2} (CategoryTheory.Category.toCategoryStruct.{u2, succ u2} Type.{u2} CategoryTheory.types.{u2})) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} G) Y) (CategoryTheory.NatTrans.app.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} F G σ Y (Prefunctor.map.{succ u1, succ u2, u3, succ u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) Type.{u2} (CategoryTheory.CategoryStruct.toQuiver.{u2, succ u2} Type.{u2} (CategoryTheory.Category.toCategoryStruct.{u2, succ u2} Type.{u2} CategoryTheory.types.{u2})) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} F) X Y f x)) (Prefunctor.map.{succ u1, succ u2, u3, succ u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) Type.{u2} (CategoryTheory.CategoryStruct.toQuiver.{u2, succ u2} Type.{u2} (CategoryTheory.Category.toCategoryStruct.{u2, succ u2} Type.{u2} CategoryTheory.types.{u2})) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} G) X Y f (CategoryTheory.NatTrans.app.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} F G σ X x))
Case conversion may be inaccurate. Consider using '#align category_theory.functor_to_types.naturality CategoryTheory.FunctorToTypes.naturalityₓ'. -/
theorem naturality (f : X ⟶ Y) (x : F.obj X) : σ.app Y ((F.map f) x) = (G.map f) (σ.app X x) :=
  congr_fun (σ.naturality f) x
#align category_theory.functor_to_types.naturality CategoryTheory.FunctorToTypes.naturality

/- warning: category_theory.functor_to_types.comp -> CategoryTheory.FunctorToTypes.comp is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] (F : CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (G : CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (H : CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) {X : C} (σ : Quiver.Hom.{succ (max u3 u2), max u1 u2 u3 (succ u2)} (CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.CategoryStruct.toQuiver.{max u3 u2, max u1 u2 u3 (succ u2)} (CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.Category.toCategoryStruct.{max u3 u2, max u1 u2 u3 (succ u2)} (CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.Functor.category.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}))) F G) (τ : Quiver.Hom.{succ (max u3 u2), max u1 u2 u3 (succ u2)} (CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.CategoryStruct.toQuiver.{max u3 u2, max u1 u2 u3 (succ u2)} (CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.Category.toCategoryStruct.{max u3 u2, max u1 u2 u3 (succ u2)} (CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.Functor.category.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}))) G H) (x : CategoryTheory.Functor.obj.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} F X), Eq.{succ u2} (CategoryTheory.Functor.obj.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} H X) (CategoryTheory.NatTrans.app.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} F H (CategoryTheory.CategoryStruct.comp.{max u3 u2, max u1 u2 u3 (succ u2)} (CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.Category.toCategoryStruct.{max u3 u2, max u1 u2 u3 (succ u2)} (CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.Functor.category.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2})) F G H σ τ) X x) (CategoryTheory.NatTrans.app.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} G H τ X (CategoryTheory.NatTrans.app.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} F G σ X x))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] (F : CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (G : CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (H : CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) {X : C} (σ : Quiver.Hom.{max (succ u3) (succ u2), max (max u3 u1) (succ u2)} (CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.CategoryStruct.toQuiver.{max u3 u2, max (max u3 u1) (succ u2)} (CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.Category.toCategoryStruct.{max u3 u2, max (max u3 u1) (succ u2)} (CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.Functor.category.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}))) F G) (τ : Quiver.Hom.{max (succ u3) (succ u2), max (max u3 u1) (succ u2)} (CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.CategoryStruct.toQuiver.{max u3 u2, max (max u3 u1) (succ u2)} (CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.Category.toCategoryStruct.{max u3 u2, max (max u3 u1) (succ u2)} (CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.Functor.category.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}))) G H) (x : Prefunctor.obj.{succ u1, succ u2, u3, succ u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) Type.{u2} (CategoryTheory.CategoryStruct.toQuiver.{u2, succ u2} Type.{u2} (CategoryTheory.Category.toCategoryStruct.{u2, succ u2} Type.{u2} CategoryTheory.types.{u2})) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} F) X), Eq.{succ u2} (Prefunctor.obj.{succ u1, succ u2, u3, succ u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) Type.{u2} (CategoryTheory.CategoryStruct.toQuiver.{u2, succ u2} Type.{u2} (CategoryTheory.Category.toCategoryStruct.{u2, succ u2} Type.{u2} CategoryTheory.types.{u2})) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} H) X) (CategoryTheory.NatTrans.app.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} F H (CategoryTheory.CategoryStruct.comp.{max u3 u2, max (max u3 u1) (succ u2)} (CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.Category.toCategoryStruct.{max u3 u2, max (max u3 u1) (succ u2)} (CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.Functor.category.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2})) F G H σ τ) X x) (CategoryTheory.NatTrans.app.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} G H τ X (CategoryTheory.NatTrans.app.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} F G σ X x))
Case conversion may be inaccurate. Consider using '#align category_theory.functor_to_types.comp CategoryTheory.FunctorToTypes.compₓ'. -/
@[simp]
theorem comp (x : F.obj X) : (σ ≫ τ).app X x = τ.app X (σ.app X x) :=
  rfl
#align category_theory.functor_to_types.comp CategoryTheory.FunctorToTypes.comp

variable {D : Type u'} [𝒟 : Category.{u'} D] (I J : D ⥤ C) (ρ : I ⟶ J) {W : D}

/- warning: category_theory.functor_to_types.hcomp -> CategoryTheory.FunctorToTypes.hcomp is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] (F : CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (G : CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (σ : Quiver.Hom.{succ (max u3 u2), max u1 u2 u3 (succ u2)} (CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.CategoryStruct.toQuiver.{max u3 u2, max u1 u2 u3 (succ u2)} (CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.Category.toCategoryStruct.{max u3 u2, max u1 u2 u3 (succ u2)} (CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.Functor.category.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}))) F G) {D : Type.{u4}} [𝒟 : CategoryTheory.Category.{u4, u4} D] (I : CategoryTheory.Functor.{u4, u1, u4, u3} D 𝒟 C _inst_1) (J : CategoryTheory.Functor.{u4, u1, u4, u3} D 𝒟 C _inst_1) (ρ : Quiver.Hom.{succ (max u4 u1), max u4 u1 u4 u3} (CategoryTheory.Functor.{u4, u1, u4, u3} D 𝒟 C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{max u4 u1, max u4 u1 u4 u3} (CategoryTheory.Functor.{u4, u1, u4, u3} D 𝒟 C _inst_1) (CategoryTheory.Category.toCategoryStruct.{max u4 u1, max u4 u1 u4 u3} (CategoryTheory.Functor.{u4, u1, u4, u3} D 𝒟 C _inst_1) (CategoryTheory.Functor.category.{u4, u1, u4, u3} D 𝒟 C _inst_1))) I J) {W : D} (x : CategoryTheory.Functor.obj.{u4, u2, u4, succ u2} D 𝒟 Type.{u2} CategoryTheory.types.{u2} (CategoryTheory.Functor.comp.{u4, u1, u2, u4, u3, succ u2} D 𝒟 C _inst_1 Type.{u2} CategoryTheory.types.{u2} I F) W), Eq.{succ u2} (CategoryTheory.Functor.obj.{u4, u2, u4, succ u2} D 𝒟 Type.{u2} CategoryTheory.types.{u2} (CategoryTheory.Functor.comp.{u4, u1, u2, u4, u3, succ u2} D 𝒟 C _inst_1 Type.{u2} CategoryTheory.types.{u2} J G) W) (CategoryTheory.NatTrans.app.{u4, u2, u4, succ u2} D 𝒟 Type.{u2} CategoryTheory.types.{u2} (CategoryTheory.Functor.comp.{u4, u1, u2, u4, u3, succ u2} D 𝒟 C _inst_1 Type.{u2} CategoryTheory.types.{u2} I F) (CategoryTheory.Functor.comp.{u4, u1, u2, u4, u3, succ u2} D 𝒟 C _inst_1 Type.{u2} CategoryTheory.types.{u2} J G) (CategoryTheory.NatTrans.hcomp.{u4, u1, u2, u4, u3, succ u2} D 𝒟 C _inst_1 Type.{u2} CategoryTheory.types.{u2} I J F G ρ σ) W x) (CategoryTheory.Functor.map.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} G (CategoryTheory.Functor.obj.{u4, u1, u4, u3} D 𝒟 C _inst_1 I W) (CategoryTheory.Functor.obj.{u4, u1, u4, u3} D 𝒟 C _inst_1 J W) (CategoryTheory.NatTrans.app.{u4, u1, u4, u3} D 𝒟 C _inst_1 I J ρ W) (CategoryTheory.NatTrans.app.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} F G σ (CategoryTheory.Functor.obj.{u4, u1, u4, u3} D 𝒟 C _inst_1 I W) x))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] (F : CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (G : CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (σ : Quiver.Hom.{max (succ u3) (succ u2), max (max u3 u1) (succ u2)} (CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.CategoryStruct.toQuiver.{max u3 u2, max (max u3 u1) (succ u2)} (CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.Category.toCategoryStruct.{max u3 u2, max (max u3 u1) (succ u2)} (CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.Functor.category.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}))) F G) {D : Type.{u4}} [𝒟 : CategoryTheory.Category.{u4, u4} D] (I : CategoryTheory.Functor.{u4, u1, u4, u3} D 𝒟 C _inst_1) (J : CategoryTheory.Functor.{u4, u1, u4, u3} D 𝒟 C _inst_1) (ρ : Quiver.Hom.{max (succ u4) (succ u1), max (max u3 u4) u1} (CategoryTheory.Functor.{u4, u1, u4, u3} D 𝒟 C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{max u4 u1, max (max u3 u4) u1} (CategoryTheory.Functor.{u4, u1, u4, u3} D 𝒟 C _inst_1) (CategoryTheory.Category.toCategoryStruct.{max u4 u1, max (max u3 u4) u1} (CategoryTheory.Functor.{u4, u1, u4, u3} D 𝒟 C _inst_1) (CategoryTheory.Functor.category.{u4, u1, u4, u3} D 𝒟 C _inst_1))) I J) {W : D} (x : Prefunctor.obj.{succ u4, succ u2, u4, succ u2} D (CategoryTheory.CategoryStruct.toQuiver.{u4, u4} D (CategoryTheory.Category.toCategoryStruct.{u4, u4} D 𝒟)) Type.{u2} (CategoryTheory.CategoryStruct.toQuiver.{u2, succ u2} Type.{u2} (CategoryTheory.Category.toCategoryStruct.{u2, succ u2} Type.{u2} CategoryTheory.types.{u2})) (CategoryTheory.Functor.toPrefunctor.{u4, u2, u4, succ u2} D 𝒟 Type.{u2} CategoryTheory.types.{u2} (CategoryTheory.Functor.comp.{u4, u1, u2, u4, u3, succ u2} D 𝒟 C _inst_1 Type.{u2} CategoryTheory.types.{u2} I F)) W), Eq.{succ u2} (Prefunctor.obj.{succ u4, succ u2, u4, succ u2} D (CategoryTheory.CategoryStruct.toQuiver.{u4, u4} D (CategoryTheory.Category.toCategoryStruct.{u4, u4} D 𝒟)) Type.{u2} (CategoryTheory.CategoryStruct.toQuiver.{u2, succ u2} Type.{u2} (CategoryTheory.Category.toCategoryStruct.{u2, succ u2} Type.{u2} CategoryTheory.types.{u2})) (CategoryTheory.Functor.toPrefunctor.{u4, u2, u4, succ u2} D 𝒟 Type.{u2} CategoryTheory.types.{u2} (CategoryTheory.Functor.comp.{u4, u1, u2, u4, u3, succ u2} D 𝒟 C _inst_1 Type.{u2} CategoryTheory.types.{u2} J G)) W) (CategoryTheory.NatTrans.app.{u4, u2, u4, succ u2} D 𝒟 Type.{u2} CategoryTheory.types.{u2} (CategoryTheory.Functor.comp.{u4, u1, u2, u4, u3, succ u2} D 𝒟 C _inst_1 Type.{u2} CategoryTheory.types.{u2} I F) (CategoryTheory.Functor.comp.{u4, u1, u2, u4, u3, succ u2} D 𝒟 C _inst_1 Type.{u2} CategoryTheory.types.{u2} J G) (CategoryTheory.NatTrans.hcomp.{u4, u1, u2, u4, u3, succ u2} D 𝒟 C _inst_1 Type.{u2} CategoryTheory.types.{u2} I J F G ρ σ) W x) (Prefunctor.map.{succ u1, succ u2, u3, succ u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) Type.{u2} (CategoryTheory.CategoryStruct.toQuiver.{u2, succ u2} Type.{u2} (CategoryTheory.Category.toCategoryStruct.{u2, succ u2} Type.{u2} CategoryTheory.types.{u2})) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} G) (Prefunctor.obj.{succ u4, succ u1, u4, u3} D (CategoryTheory.CategoryStruct.toQuiver.{u4, u4} D (CategoryTheory.Category.toCategoryStruct.{u4, u4} D 𝒟)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u4, u1, u4, u3} D 𝒟 C _inst_1 I) W) (Prefunctor.obj.{succ u4, succ u1, u4, u3} D (CategoryTheory.CategoryStruct.toQuiver.{u4, u4} D (CategoryTheory.Category.toCategoryStruct.{u4, u4} D 𝒟)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u4, u1, u4, u3} D 𝒟 C _inst_1 J) W) (CategoryTheory.NatTrans.app.{u4, u1, u4, u3} D 𝒟 C _inst_1 I J ρ W) (CategoryTheory.NatTrans.app.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} F G σ (Prefunctor.obj.{succ u4, succ u1, u4, u3} D (CategoryTheory.CategoryStruct.toQuiver.{u4, u4} D (CategoryTheory.Category.toCategoryStruct.{u4, u4} D 𝒟)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u4, u1, u4, u3} D 𝒟 C _inst_1 I) W) x))
Case conversion may be inaccurate. Consider using '#align category_theory.functor_to_types.hcomp CategoryTheory.FunctorToTypes.hcompₓ'. -/
@[simp]
theorem hcomp (x : (I ⋙ F).obj W) : (ρ ◫ σ).app W x = (G.map (ρ.app W)) (σ.app (I.obj W) x) :=
  rfl
#align category_theory.functor_to_types.hcomp CategoryTheory.FunctorToTypes.hcomp

/- warning: category_theory.functor_to_types.map_inv_map_hom_apply -> CategoryTheory.FunctorToTypes.map_inv_map_hom_apply is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] (F : CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) {X : C} {Y : C} (f : CategoryTheory.Iso.{u1, u3} C _inst_1 X Y) (x : CategoryTheory.Functor.obj.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} F X), Eq.{succ u2} (CategoryTheory.Functor.obj.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} F X) (CategoryTheory.Functor.map.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} F Y X (CategoryTheory.Iso.inv.{u1, u3} C _inst_1 X Y f) (CategoryTheory.Functor.map.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} F X Y (CategoryTheory.Iso.hom.{u1, u3} C _inst_1 X Y f) x)) x
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] (F : CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) {X : C} {Y : C} (f : CategoryTheory.Iso.{u1, u3} C _inst_1 X Y) (x : Prefunctor.obj.{succ u1, succ u2, u3, succ u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) Type.{u2} (CategoryTheory.CategoryStruct.toQuiver.{u2, succ u2} Type.{u2} (CategoryTheory.Category.toCategoryStruct.{u2, succ u2} Type.{u2} CategoryTheory.types.{u2})) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} F) X), Eq.{succ u2} (Prefunctor.obj.{succ u1, succ u2, u3, succ u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) Type.{u2} (CategoryTheory.CategoryStruct.toQuiver.{u2, succ u2} Type.{u2} (CategoryTheory.Category.toCategoryStruct.{u2, succ u2} Type.{u2} CategoryTheory.types.{u2})) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} F) X) (Prefunctor.map.{succ u1, succ u2, u3, succ u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) Type.{u2} (CategoryTheory.CategoryStruct.toQuiver.{u2, succ u2} Type.{u2} (CategoryTheory.Category.toCategoryStruct.{u2, succ u2} Type.{u2} CategoryTheory.types.{u2})) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} F) Y X (CategoryTheory.Iso.inv.{u1, u3} C _inst_1 X Y f) (Prefunctor.map.{succ u1, succ u2, u3, succ u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) Type.{u2} (CategoryTheory.CategoryStruct.toQuiver.{u2, succ u2} Type.{u2} (CategoryTheory.Category.toCategoryStruct.{u2, succ u2} Type.{u2} CategoryTheory.types.{u2})) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} F) X Y (CategoryTheory.Iso.hom.{u1, u3} C _inst_1 X Y f) x)) x
Case conversion may be inaccurate. Consider using '#align category_theory.functor_to_types.map_inv_map_hom_apply CategoryTheory.FunctorToTypes.map_inv_map_hom_applyₓ'. -/
@[simp]
theorem map_inv_map_hom_apply (f : X ≅ Y) (x : F.obj X) : F.map f.inv (F.map f.Hom x) = x :=
  congr_fun (F.mapIso f).hom_inv_id x
#align category_theory.functor_to_types.map_inv_map_hom_apply CategoryTheory.FunctorToTypes.map_inv_map_hom_apply

/- warning: category_theory.functor_to_types.map_hom_map_inv_apply -> CategoryTheory.FunctorToTypes.map_hom_map_inv_apply is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] (F : CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) {X : C} {Y : C} (f : CategoryTheory.Iso.{u1, u3} C _inst_1 X Y) (y : CategoryTheory.Functor.obj.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} F Y), Eq.{succ u2} (CategoryTheory.Functor.obj.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} F Y) (CategoryTheory.Functor.map.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} F X Y (CategoryTheory.Iso.hom.{u1, u3} C _inst_1 X Y f) (CategoryTheory.Functor.map.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} F Y X (CategoryTheory.Iso.inv.{u1, u3} C _inst_1 X Y f) y)) y
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] (F : CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) {X : C} {Y : C} (f : CategoryTheory.Iso.{u1, u3} C _inst_1 X Y) (y : Prefunctor.obj.{succ u1, succ u2, u3, succ u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) Type.{u2} (CategoryTheory.CategoryStruct.toQuiver.{u2, succ u2} Type.{u2} (CategoryTheory.Category.toCategoryStruct.{u2, succ u2} Type.{u2} CategoryTheory.types.{u2})) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} F) Y), Eq.{succ u2} (Prefunctor.obj.{succ u1, succ u2, u3, succ u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) Type.{u2} (CategoryTheory.CategoryStruct.toQuiver.{u2, succ u2} Type.{u2} (CategoryTheory.Category.toCategoryStruct.{u2, succ u2} Type.{u2} CategoryTheory.types.{u2})) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} F) Y) (Prefunctor.map.{succ u1, succ u2, u3, succ u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) Type.{u2} (CategoryTheory.CategoryStruct.toQuiver.{u2, succ u2} Type.{u2} (CategoryTheory.Category.toCategoryStruct.{u2, succ u2} Type.{u2} CategoryTheory.types.{u2})) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} F) X Y (CategoryTheory.Iso.hom.{u1, u3} C _inst_1 X Y f) (Prefunctor.map.{succ u1, succ u2, u3, succ u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) Type.{u2} (CategoryTheory.CategoryStruct.toQuiver.{u2, succ u2} Type.{u2} (CategoryTheory.Category.toCategoryStruct.{u2, succ u2} Type.{u2} CategoryTheory.types.{u2})) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} F) Y X (CategoryTheory.Iso.inv.{u1, u3} C _inst_1 X Y f) y)) y
Case conversion may be inaccurate. Consider using '#align category_theory.functor_to_types.map_hom_map_inv_apply CategoryTheory.FunctorToTypes.map_hom_map_inv_applyₓ'. -/
@[simp]
theorem map_hom_map_inv_apply (f : X ≅ Y) (y : F.obj Y) : F.map f.Hom (F.map f.inv y) = y :=
  congr_fun (F.mapIso f).inv_hom_id y
#align category_theory.functor_to_types.map_hom_map_inv_apply CategoryTheory.FunctorToTypes.map_hom_map_inv_apply

/- warning: category_theory.functor_to_types.hom_inv_id_app_apply -> CategoryTheory.FunctorToTypes.hom_inv_id_app_apply is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] (F : CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (G : CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (α : CategoryTheory.Iso.{max u3 u2, max u1 u2 u3 (succ u2)} (CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.Functor.category.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) F G) (X : C) (x : CategoryTheory.Functor.obj.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} F X), Eq.{succ u2} (CategoryTheory.Functor.obj.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} F X) (CategoryTheory.NatTrans.app.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} G F (CategoryTheory.Iso.inv.{max u3 u2, max u1 u2 u3 (succ u2)} (CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.Functor.category.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) F G α) X (CategoryTheory.NatTrans.app.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} F G (CategoryTheory.Iso.hom.{max u3 u2, max u1 u2 u3 (succ u2)} (CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.Functor.category.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) F G α) X x)) x
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] (F : CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (G : CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (α : CategoryTheory.Iso.{max u3 u2, max (max u3 u1) (succ u2)} (CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.Functor.category.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) F G) (X : C) (x : Prefunctor.obj.{succ u1, succ u2, u3, succ u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) Type.{u2} (CategoryTheory.CategoryStruct.toQuiver.{u2, succ u2} Type.{u2} (CategoryTheory.Category.toCategoryStruct.{u2, succ u2} Type.{u2} CategoryTheory.types.{u2})) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} F) X), Eq.{succ u2} (Prefunctor.obj.{succ u1, succ u2, u3, succ u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) Type.{u2} (CategoryTheory.CategoryStruct.toQuiver.{u2, succ u2} Type.{u2} (CategoryTheory.Category.toCategoryStruct.{u2, succ u2} Type.{u2} CategoryTheory.types.{u2})) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} F) X) (CategoryTheory.NatTrans.app.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} G F (CategoryTheory.Iso.inv.{max u3 u2, max (max u3 u1) (succ u2)} (CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.Functor.category.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) F G α) X (CategoryTheory.NatTrans.app.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} F G (CategoryTheory.Iso.hom.{max u3 u2, max (max u3 u1) (succ u2)} (CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.Functor.category.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) F G α) X x)) x
Case conversion may be inaccurate. Consider using '#align category_theory.functor_to_types.hom_inv_id_app_apply CategoryTheory.FunctorToTypes.hom_inv_id_app_applyₓ'. -/
@[simp]
theorem hom_inv_id_app_apply (α : F ≅ G) (X) (x) : α.inv.app X (α.Hom.app X x) = x :=
  congr_fun (α.hom_inv_id_app X) x
#align category_theory.functor_to_types.hom_inv_id_app_apply CategoryTheory.FunctorToTypes.hom_inv_id_app_apply

/- warning: category_theory.functor_to_types.inv_hom_id_app_apply -> CategoryTheory.FunctorToTypes.inv_hom_id_app_apply is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] (F : CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (G : CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (α : CategoryTheory.Iso.{max u3 u2, max u1 u2 u3 (succ u2)} (CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.Functor.category.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) F G) (X : C) (x : CategoryTheory.Functor.obj.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} G X), Eq.{succ u2} (CategoryTheory.Functor.obj.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} G X) (CategoryTheory.NatTrans.app.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} F G (CategoryTheory.Iso.hom.{max u3 u2, max u1 u2 u3 (succ u2)} (CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.Functor.category.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) F G α) X (CategoryTheory.NatTrans.app.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} G F (CategoryTheory.Iso.inv.{max u3 u2, max u1 u2 u3 (succ u2)} (CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.Functor.category.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) F G α) X x)) x
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] (F : CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (G : CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (α : CategoryTheory.Iso.{max u3 u2, max (max u3 u1) (succ u2)} (CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.Functor.category.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) F G) (X : C) (x : Prefunctor.obj.{succ u1, succ u2, u3, succ u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) Type.{u2} (CategoryTheory.CategoryStruct.toQuiver.{u2, succ u2} Type.{u2} (CategoryTheory.Category.toCategoryStruct.{u2, succ u2} Type.{u2} CategoryTheory.types.{u2})) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} G) X), Eq.{succ u2} (Prefunctor.obj.{succ u1, succ u2, u3, succ u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) Type.{u2} (CategoryTheory.CategoryStruct.toQuiver.{u2, succ u2} Type.{u2} (CategoryTheory.Category.toCategoryStruct.{u2, succ u2} Type.{u2} CategoryTheory.types.{u2})) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} G) X) (CategoryTheory.NatTrans.app.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} F G (CategoryTheory.Iso.hom.{max u3 u2, max (max u3 u1) (succ u2)} (CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.Functor.category.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) F G α) X (CategoryTheory.NatTrans.app.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2} G F (CategoryTheory.Iso.inv.{max u3 u2, max (max u3 u1) (succ u2)} (CategoryTheory.Functor.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.Functor.category.{u1, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) F G α) X x)) x
Case conversion may be inaccurate. Consider using '#align category_theory.functor_to_types.inv_hom_id_app_apply CategoryTheory.FunctorToTypes.inv_hom_id_app_applyₓ'. -/
@[simp]
theorem inv_hom_id_app_apply (α : F ≅ G) (X) (x) : α.Hom.app X (α.inv.app X x) = x :=
  congr_fun (α.inv_hom_id_app X) x
#align category_theory.functor_to_types.inv_hom_id_app_apply CategoryTheory.FunctorToTypes.inv_hom_id_app_apply

end FunctorToTypes

#print CategoryTheory.uliftTrivial /-
/-- The isomorphism between a `Type` which has been `ulift`ed to the same universe,
and the original type.
-/
def uliftTrivial (V : Type u) : ULift.{u} V ≅ V := by tidy
#align category_theory.ulift_trivial CategoryTheory.uliftTrivial
-/

#print CategoryTheory.uliftFunctor /-
/-- The functor embedding `Type u` into `Type (max u v)`.
Write this as `ulift_functor.{5 2}` to get `Type 2 ⥤ Type 5`.
-/
def uliftFunctor : Type u ⥤ Type max u v
    where
  obj X := ULift.{v} X
  map X Y f := fun x : ULift.{v} X => ULift.up (f x.down)
#align category_theory.ulift_functor CategoryTheory.uliftFunctor
-/

/- warning: category_theory.ulift_functor_map -> CategoryTheory.uliftFunctor_map is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u2}} {Y : Type.{u2}} (f : Quiver.Hom.{succ u2, succ u2} Type.{u2} (CategoryTheory.CategoryStruct.toQuiver.{u2, succ u2} Type.{u2} (CategoryTheory.Category.toCategoryStruct.{u2, succ u2} Type.{u2} CategoryTheory.types.{u2})) X Y) (x : ULift.{u1, u2} X), Eq.{succ (max u2 u1)} (CategoryTheory.Functor.obj.{u2, max u2 u1, succ u2, succ (max u2 u1)} Type.{u2} CategoryTheory.types.{u2} Type.{max u2 u1} CategoryTheory.types.{max u2 u1} CategoryTheory.uliftFunctor.{u1, u2} Y) (CategoryTheory.Functor.map.{u2, max u2 u1, succ u2, succ (max u2 u1)} Type.{u2} CategoryTheory.types.{u2} Type.{max u2 u1} CategoryTheory.types.{max u2 u1} CategoryTheory.uliftFunctor.{u1, u2} X Y f x) (ULift.up.{u1, u2} Y (f (ULift.down.{u1, u2} X x)))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u2}} (f : Quiver.Hom.{succ u2, succ u2} Type.{u2} (CategoryTheory.CategoryStruct.toQuiver.{u2, succ u2} Type.{u2} (CategoryTheory.Category.toCategoryStruct.{u2, succ u2} Type.{u2} CategoryTheory.types.{u2})) X Y) (x : ULift.{u1, u2} X), Eq.{max (succ u2) (succ u1)} (Prefunctor.obj.{succ u2, max (succ u2) (succ u1), succ u2, max (succ u2) (succ u1)} Type.{u2} (CategoryTheory.CategoryStruct.toQuiver.{u2, succ u2} Type.{u2} (CategoryTheory.Category.toCategoryStruct.{u2, succ u2} Type.{u2} CategoryTheory.types.{u2})) Type.{max u2 u1} (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max (succ u2) (succ u1)} Type.{max u2 u1} (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max (succ u2) (succ u1)} Type.{max u2 u1} CategoryTheory.types.{max u2 u1})) (CategoryTheory.Functor.toPrefunctor.{u2, max u2 u1, succ u2, max (succ u2) (succ u1)} Type.{u2} CategoryTheory.types.{u2} Type.{max u2 u1} CategoryTheory.types.{max u2 u1} CategoryTheory.uliftFunctor.{u1, u2}) Y) (Prefunctor.map.{succ u2, max (succ u2) (succ u1), succ u2, max (succ u2) (succ u1)} Type.{u2} (CategoryTheory.CategoryStruct.toQuiver.{u2, succ u2} Type.{u2} (CategoryTheory.Category.toCategoryStruct.{u2, succ u2} Type.{u2} CategoryTheory.types.{u2})) Type.{max u2 u1} (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max (succ u2) (succ u1)} Type.{max u2 u1} (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max (succ u2) (succ u1)} Type.{max u2 u1} CategoryTheory.types.{max u2 u1})) (CategoryTheory.Functor.toPrefunctor.{u2, max u2 u1, succ u2, max (succ u2) (succ u1)} Type.{u2} CategoryTheory.types.{u2} Type.{max u2 u1} CategoryTheory.types.{max u2 u1} CategoryTheory.uliftFunctor.{u1, u2}) X Y f x) (ULift.up.{u1, u2} Y (f (ULift.down.{u1, u2} X x)))
Case conversion may be inaccurate. Consider using '#align category_theory.ulift_functor_map CategoryTheory.uliftFunctor_mapₓ'. -/
@[simp]
theorem uliftFunctor_map {X Y : Type u} (f : X ⟶ Y) (x : ULift.{v} X) :
    uliftFunctor.map f x = ULift.up (f x.down) :=
  rfl
#align category_theory.ulift_functor_map CategoryTheory.uliftFunctor_map

#print CategoryTheory.uliftFunctorFull /-
instance uliftFunctorFull : Full.{u} uliftFunctor where preimage X Y f x := (f (ULift.up x)).down
#align category_theory.ulift_functor_full CategoryTheory.uliftFunctorFull
-/

#print CategoryTheory.uliftFunctor_faithful /-
instance uliftFunctor_faithful : Faithful uliftFunctor
    where map_injective' X Y f g p :=
    funext fun x =>
      congr_arg ULift.down (congr_fun p (ULift.up x) : ULift.up (f x) = ULift.up (g x))
#align category_theory.ulift_functor_faithful CategoryTheory.uliftFunctor_faithful
-/

#print CategoryTheory.uliftFunctorTrivial /-
/-- The functor embedding `Type u` into `Type u` via `ulift` is isomorphic to the identity functor.
 -/
def uliftFunctorTrivial : uliftFunctor.{u, u} ≅ 𝟭 _ :=
  NatIso.ofComponents uliftTrivial (by tidy)
#align category_theory.ulift_functor_trivial CategoryTheory.uliftFunctorTrivial
-/

#print CategoryTheory.homOfElement /-
-- TODO We should connect this to a general story about concrete categories
-- whose forgetful functor is representable.
/-- Any term `x` of a type `X` corresponds to a morphism `punit ⟶ X`. -/
def homOfElement {X : Type u} (x : X) : PUnit ⟶ X := fun _ => x
#align category_theory.hom_of_element CategoryTheory.homOfElement
-/

#print CategoryTheory.homOfElement_eq_iff /-
theorem homOfElement_eq_iff {X : Type u} (x y : X) : homOfElement x = homOfElement y ↔ x = y :=
  ⟨fun H => congr_fun H PUnit.unit, by cc⟩
#align category_theory.hom_of_element_eq_iff CategoryTheory.homOfElement_eq_iff
-/

#print CategoryTheory.mono_iff_injective /-
/-- A morphism in `Type` is a monomorphism if and only if it is injective.

See <https://stacks.math.columbia.edu/tag/003C>.
-/
theorem mono_iff_injective {X Y : Type u} (f : X ⟶ Y) : Mono f ↔ Function.Injective f :=
  by
  constructor
  · intro H x x' h
    skip
    rw [← hom_of_element_eq_iff] at h⊢
    exact (cancel_mono f).mp h
  · exact fun H => ⟨fun Z => H.compLeft⟩
#align category_theory.mono_iff_injective CategoryTheory.mono_iff_injective
-/

#print CategoryTheory.injective_of_mono /-
theorem injective_of_mono {X Y : Type u} (f : X ⟶ Y) [hf : Mono f] : Function.Injective f :=
  (mono_iff_injective f).1 hf
#align category_theory.injective_of_mono CategoryTheory.injective_of_mono
-/

#print CategoryTheory.epi_iff_surjective /-
/-- A morphism in `Type` is an epimorphism if and only if it is surjective.

See <https://stacks.math.columbia.edu/tag/003C>.
-/
theorem epi_iff_surjective {X Y : Type u} (f : X ⟶ Y) : Epi f ↔ Function.Surjective f :=
  by
  constructor
  · rintro ⟨H⟩
    refine' Function.surjective_of_right_cancellable_Prop fun g₁ g₂ hg => _
    rw [← equiv.ulift.symm.injective.comp_left.eq_iff]
    apply H
    change ULift.up ∘ g₁ ∘ f = ULift.up ∘ g₂ ∘ f
    rw [hg]
  · exact fun H => ⟨fun Z => H.injective_comp_right⟩
#align category_theory.epi_iff_surjective CategoryTheory.epi_iff_surjective
-/

#print CategoryTheory.surjective_of_epi /-
theorem surjective_of_epi {X Y : Type u} (f : X ⟶ Y) [hf : Epi f] : Function.Surjective f :=
  (epi_iff_surjective f).1 hf
#align category_theory.surjective_of_epi CategoryTheory.surjective_of_epi
-/

section

#print CategoryTheory.ofTypeFunctor /-
/-- `of_type_functor m` converts from Lean's `Type`-based `category` to `category_theory`. This
allows us to use these functors in category theory. -/
def ofTypeFunctor (m : Type u → Type v) [Functor m] [LawfulFunctor m] : Type u ⥤ Type v
    where
  obj := m
  map α β := Functor.map
  map_id' α := Functor.map_id
  map_comp' α β γ f g := funext fun a => LawfulFunctor.comp_map f g _
#align category_theory.of_type_functor CategoryTheory.ofTypeFunctor
-/

variable (m : Type u → Type v) [Functor m] [LawfulFunctor m]

/- warning: category_theory.of_type_functor_obj -> CategoryTheory.ofTypeFunctor_obj is a dubious translation:
lean 3 declaration is
  forall (m : Type.{u2} -> Type.{u1}) [_inst_1 : Functor.{u2, u1} m] [_inst_2 : LawfulFunctor.{u2, u1} m _inst_1], Eq.{max (succ (succ u2)) (succ (succ u1))} (Type.{u2} -> Type.{u1}) (CategoryTheory.Functor.obj.{u2, u1, succ u2, succ u1} Type.{u2} CategoryTheory.types.{u2} Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.ofTypeFunctor.{u1, u2} m _inst_1 _inst_2)) m
but is expected to have type
  forall (m : Type.{u2} -> Type.{u1}) [_inst_1 : Functor.{u2, u1} m] [_inst_2 : LawfulFunctor.{u2, u1} m _inst_1], Eq.{max (succ (succ u2)) (succ (succ u1))} (Type.{u2} -> Type.{u1}) (Prefunctor.obj.{succ u2, succ u1, succ u2, succ u1} Type.{u2} (CategoryTheory.CategoryStruct.toQuiver.{u2, succ u2} Type.{u2} (CategoryTheory.Category.toCategoryStruct.{u2, succ u2} Type.{u2} CategoryTheory.types.{u2})) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u2, u1, succ u2, succ u1} Type.{u2} CategoryTheory.types.{u2} Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.ofTypeFunctor.{u1, u2} m _inst_1 _inst_2))) m
Case conversion may be inaccurate. Consider using '#align category_theory.of_type_functor_obj CategoryTheory.ofTypeFunctor_objₓ'. -/
@[simp]
theorem ofTypeFunctor_obj : (ofTypeFunctor m).obj = m :=
  rfl
#align category_theory.of_type_functor_obj CategoryTheory.ofTypeFunctor_obj

/- warning: category_theory.of_type_functor_map -> CategoryTheory.ofTypeFunctor_map is a dubious translation:
lean 3 declaration is
  forall (m : Type.{u2} -> Type.{u1}) [_inst_1 : Functor.{u2, u1} m] [_inst_2 : LawfulFunctor.{u2, u1} m _inst_1] {α : Type.{u2}} {β : Type.{u2}} (f : α -> β), Eq.{succ u1} (Quiver.Hom.{succ u1, succ u1} Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.obj.{u2, u1, succ u2, succ u1} Type.{u2} CategoryTheory.types.{u2} Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.ofTypeFunctor.{u1, u2} m _inst_1 _inst_2) α) (CategoryTheory.Functor.obj.{u2, u1, succ u2, succ u1} Type.{u2} CategoryTheory.types.{u2} Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.ofTypeFunctor.{u1, u2} m _inst_1 _inst_2) β)) (CategoryTheory.Functor.map.{u2, u1, succ u2, succ u1} Type.{u2} CategoryTheory.types.{u2} Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.ofTypeFunctor.{u1, u2} m _inst_1 _inst_2) α β f) (Functor.map.{u2, u1} m _inst_1 α β f)
but is expected to have type
  forall (m : Type.{u2} -> Type.{u1}) [_inst_1 : Functor.{u2, u1} m] [_inst_2 : LawfulFunctor.{u2, u1} m _inst_1] {α : Type.{u2}} {β : Type.{u2}} (f : α -> β), Eq.{succ u1} (Quiver.Hom.{succ u1, succ u1} Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (Prefunctor.obj.{succ u2, succ u1, succ u2, succ u1} Type.{u2} (CategoryTheory.CategoryStruct.toQuiver.{u2, succ u2} Type.{u2} (CategoryTheory.Category.toCategoryStruct.{u2, succ u2} Type.{u2} CategoryTheory.types.{u2})) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u2, u1, succ u2, succ u1} Type.{u2} CategoryTheory.types.{u2} Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.ofTypeFunctor.{u1, u2} m _inst_1 _inst_2)) α) (Prefunctor.obj.{succ u2, succ u1, succ u2, succ u1} Type.{u2} (CategoryTheory.CategoryStruct.toQuiver.{u2, succ u2} Type.{u2} (CategoryTheory.Category.toCategoryStruct.{u2, succ u2} Type.{u2} CategoryTheory.types.{u2})) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u2, u1, succ u2, succ u1} Type.{u2} CategoryTheory.types.{u2} Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.ofTypeFunctor.{u1, u2} m _inst_1 _inst_2)) β)) (Prefunctor.map.{succ u2, succ u1, succ u2, succ u1} Type.{u2} (CategoryTheory.CategoryStruct.toQuiver.{u2, succ u2} Type.{u2} (CategoryTheory.Category.toCategoryStruct.{u2, succ u2} Type.{u2} CategoryTheory.types.{u2})) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u2, u1, succ u2, succ u1} Type.{u2} CategoryTheory.types.{u2} Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.ofTypeFunctor.{u1, u2} m _inst_1 _inst_2)) α β f) (Functor.map.{u2, u1} m _inst_1 α β f)
Case conversion may be inaccurate. Consider using '#align category_theory.of_type_functor_map CategoryTheory.ofTypeFunctor_mapₓ'. -/
@[simp]
theorem ofTypeFunctor_map {α β} (f : α → β) :
    (ofTypeFunctor m).map f = (Functor.map f : m α → m β) :=
  rfl
#align category_theory.of_type_functor_map CategoryTheory.ofTypeFunctor_map

end

end CategoryTheory

-- Isomorphisms in Type and equivalences.
namespace Equiv

universe u

variable {X Y : Type u}

#print Equiv.toIso /-
/-- Any equivalence between types in the same universe gives
a categorical isomorphism between those types.
-/
def toIso (e : X ≃ Y) : X ≅ Y where
  Hom := e.toFun
  inv := e.invFun
  hom_inv_id' := funext e.left_inv
  inv_hom_id' := funext e.right_inv
#align equiv.to_iso Equiv.toIso
-/

#print Equiv.toIso_hom /-
@[simp]
theorem toIso_hom {e : X ≃ Y} : e.toIso.Hom = e :=
  rfl
#align equiv.to_iso_hom Equiv.toIso_hom
-/

#print Equiv.toIso_inv /-
@[simp]
theorem toIso_inv {e : X ≃ Y} : e.toIso.inv = e.symm :=
  rfl
#align equiv.to_iso_inv Equiv.toIso_inv
-/

end Equiv

universe u

namespace CategoryTheory.Iso

open CategoryTheory

variable {X Y : Type u}

#print CategoryTheory.Iso.toEquiv /-
/-- Any isomorphism between types gives an equivalence.
-/
def toEquiv (i : X ≅ Y) : X ≃ Y where
  toFun := i.Hom
  invFun := i.inv
  left_inv x := congr_fun i.hom_inv_id x
  right_inv y := congr_fun i.inv_hom_id y
#align category_theory.iso.to_equiv CategoryTheory.Iso.toEquiv
-/

#print CategoryTheory.Iso.toEquiv_fun /-
@[simp]
theorem toEquiv_fun (i : X ≅ Y) : (i.toEquiv : X → Y) = i.Hom :=
  rfl
#align category_theory.iso.to_equiv_fun CategoryTheory.Iso.toEquiv_fun
-/

#print CategoryTheory.Iso.toEquiv_symm_fun /-
@[simp]
theorem toEquiv_symm_fun (i : X ≅ Y) : (i.toEquiv.symm : Y → X) = i.inv :=
  rfl
#align category_theory.iso.to_equiv_symm_fun CategoryTheory.Iso.toEquiv_symm_fun
-/

#print CategoryTheory.Iso.toEquiv_id /-
@[simp]
theorem toEquiv_id (X : Type u) : (Iso.refl X).toEquiv = Equiv.refl X :=
  rfl
#align category_theory.iso.to_equiv_id CategoryTheory.Iso.toEquiv_id
-/

#print CategoryTheory.Iso.toEquiv_comp /-
@[simp]
theorem toEquiv_comp {X Y Z : Type u} (f : X ≅ Y) (g : Y ≅ Z) :
    (f ≪≫ g).toEquiv = f.toEquiv.trans g.toEquiv :=
  rfl
#align category_theory.iso.to_equiv_comp CategoryTheory.Iso.toEquiv_comp
-/

end CategoryTheory.Iso

namespace CategoryTheory

#print CategoryTheory.isIso_iff_bijective /-
/-- A morphism in `Type u` is an isomorphism if and only if it is bijective. -/
theorem isIso_iff_bijective {X Y : Type u} (f : X ⟶ Y) : IsIso f ↔ Function.Bijective f :=
  Iff.intro (fun i => (as_iso f : X ≅ Y).toEquiv.Bijective) fun b =>
    IsIso.of_iso (Equiv.ofBijective f b).toIso
#align category_theory.is_iso_iff_bijective CategoryTheory.isIso_iff_bijective
-/

instance : SplitEpiCategory (Type u)
    where isSplitEpi_of_epi X Y f hf :=
    IsSplitEpi.mk'
      { section_ := Function.surjInv <| (epi_iff_surjective f).1 hf
        id' := funext <| Function.rightInverse_surjInv <| (epi_iff_surjective f).1 hf }

end CategoryTheory

#print equivIsoIso /-
-- We prove `equiv_iso_iso` and then use that to sneakily construct `equiv_equiv_iso`.
-- (In this order the proofs are handled by `obviously`.)
/-- Equivalences (between types in the same universe) are the same as (isomorphic to) isomorphisms
of types. -/
@[simps]
def equivIsoIso {X Y : Type u} : X ≃ Y ≅ X ≅ Y
    where
  Hom e := e.toIso
  inv i := i.toEquiv
#align equiv_iso_iso equivIsoIso
-/

#print equivEquivIso /-
/-- Equivalences (between types in the same universe) are the same as (equivalent to) isomorphisms
of types. -/
def equivEquivIso {X Y : Type u} : X ≃ Y ≃ (X ≅ Y) :=
  equivIsoIso.toEquiv
#align equiv_equiv_iso equivEquivIso
-/

#print equivEquivIso_hom /-
@[simp]
theorem equivEquivIso_hom {X Y : Type u} (e : X ≃ Y) : equivEquivIso e = e.toIso :=
  rfl
#align equiv_equiv_iso_hom equivEquivIso_hom
-/

#print equivEquivIso_inv /-
@[simp]
theorem equivEquivIso_inv {X Y : Type u} (e : X ≅ Y) : equivEquivIso.symm e = e.toEquiv :=
  rfl
#align equiv_equiv_iso_inv equivEquivIso_inv
-/

