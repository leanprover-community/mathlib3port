/-
Copyright (c) 2018 Reid Barton All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Scott Morrison, David Wärn
-/
import Mathbin.CategoryTheory.FullSubcategory
import Mathbin.CategoryTheory.Products.Basic
import Mathbin.CategoryTheory.Pi.Basic
import Mathbin.CategoryTheory.Category.Basic
import Mathbin.Combinatorics.Quiver.ConnectedComponent

#align_import category_theory.groupoid from "leanprover-community/mathlib"@"2efd2423f8d25fa57cf7a179f5d8652ab4d0df44"

/-!
# Groupoids

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define `groupoid` as a typeclass extending `category`,
asserting that all morphisms have inverses.

The instance `is_iso.of_groupoid (f : X ⟶ Y) : is_iso f` means that you can then write
`inv f` to access the inverse of any morphism `f`.

`groupoid.iso_equiv_hom : (X ≅ Y) ≃ (X ⟶ Y)` provides the equivalence between
isomorphisms and morphisms in a groupoid.

We provide a (non-instance) constructor `groupoid.of_is_iso` from an existing category
with `is_iso f` for every `f`.

## See also

See also `category_theory.core` for the groupoid of isomorphisms in a category.
-/


namespace CategoryTheory

universe v v₂ u u₂

#print CategoryTheory.Groupoid /-
-- morphism levels before object levels. See note [category_theory universes].
/-- A `groupoid` is a category such that all morphisms are isomorphisms. -/
class Groupoid (obj : Type u) extends Category.{v} obj : Type max u (v + 1) where
  inv : ∀ {X Y : obj}, (X ⟶ Y) → (Y ⟶ X)
  inv_comp' : ∀ {X Y : obj} (f : X ⟶ Y), comp (inv f) f = id Y := by obviously
  comp_inv' : ∀ {X Y : obj} (f : X ⟶ Y), comp f (inv f) = id X := by obviously
#align category_theory.groupoid CategoryTheory.Groupoid
-/

initialize_simps_projections Groupoid (-to_category_to_category_struct_to_quiver_hom,
  to_category_to_category_struct_comp → comp, to_category_to_category_struct_id → id,
  -to_category_to_category_struct, -toCategory)

#print CategoryTheory.LargeGroupoid /-
/-- A `large_groupoid` is a groupoid
where the objects live in `Type (u+1)` while the morphisms live in `Type u`.
-/
abbrev LargeGroupoid (C : Type (u + 1)) : Type (u + 1) :=
  Groupoid.{u} C
#align category_theory.large_groupoid CategoryTheory.LargeGroupoid
-/

#print CategoryTheory.SmallGroupoid /-
/-- A `small_groupoid` is a groupoid
where the objects and morphisms live in the same universe.
-/
abbrev SmallGroupoid (C : Type u) : Type (u + 1) :=
  Groupoid.{u} C
#align category_theory.small_groupoid CategoryTheory.SmallGroupoid
-/

section

variable {C : Type u} [Groupoid.{v} C] {X Y : C}

#print CategoryTheory.IsIso.of_groupoid /-
-- see Note [lower instance priority]
instance (priority := 100) IsIso.of_groupoid (f : X ⟶ Y) : IsIso f :=
  ⟨⟨Groupoid.inv f, Groupoid.comp_inv f, Groupoid.inv_comp f⟩⟩
#align category_theory.is_iso.of_groupoid CategoryTheory.IsIso.of_groupoid
-/

#print CategoryTheory.Groupoid.inv_eq_inv /-
@[simp]
theorem Groupoid.inv_eq_inv (f : X ⟶ Y) : Groupoid.inv f = inv f :=
  IsIso.eq_inv_of_hom_inv_id <| Groupoid.comp_inv f
#align category_theory.groupoid.inv_eq_inv CategoryTheory.Groupoid.inv_eq_inv
-/

#print CategoryTheory.Groupoid.invEquiv /-
/-- `groupoid.inv` is involutive. -/
@[simps]
def Groupoid.invEquiv : (X ⟶ Y) ≃ (Y ⟶ X) :=
  ⟨Groupoid.inv, Groupoid.inv, fun f => by simp, fun f => by simp⟩
#align category_theory.groupoid.inv_equiv CategoryTheory.Groupoid.invEquiv
-/

#print CategoryTheory.groupoidHasInvolutiveReverse /-
instance (priority := 100) groupoidHasInvolutiveReverse : Quiver.HasInvolutiveReverse C
    where
  reverse' X Y f := Groupoid.inv f
  inv' X Y f := by dsimp [Quiver.reverse]; simp
#align category_theory.groupoid_has_involutive_reverse CategoryTheory.groupoidHasInvolutiveReverse
-/

#print CategoryTheory.Groupoid.reverse_eq_inv /-
@[simp]
theorem Groupoid.reverse_eq_inv (f : X ⟶ Y) : Quiver.reverse f = Groupoid.inv f :=
  rfl
#align category_theory.groupoid.reverse_eq_inv CategoryTheory.Groupoid.reverse_eq_inv
-/

#print CategoryTheory.functorMapReverse /-
instance functorMapReverse {D : Type _} [Groupoid D] (F : C ⥤ D) : F.toPrefunctor.MapReverse
    where map_reverse' X Y f := by
    simp only [Quiver.reverse, Quiver.HasReverse.reverse', groupoid.inv_eq_inv,
      functor.to_prefunctor_map, functor.map_inv]
#align category_theory.functor_map_reverse CategoryTheory.functorMapReverse
-/

variable (X Y)

#print CategoryTheory.Groupoid.isoEquivHom /-
/-- In a groupoid, isomorphisms are equivalent to morphisms. -/
def Groupoid.isoEquivHom : (X ≅ Y) ≃ (X ⟶ Y)
    where
  toFun := Iso.hom
  invFun f := ⟨f, Groupoid.inv f⟩
  left_inv i := Iso.ext rfl
  right_inv f := rfl
#align category_theory.groupoid.iso_equiv_hom CategoryTheory.Groupoid.isoEquivHom
-/

variable (C)

#print CategoryTheory.Groupoid.invFunctor /-
/-- The functor from a groupoid `C` to its opposite sending every morphism to its inverse. -/
@[simps]
noncomputable def Groupoid.invFunctor : C ⥤ Cᵒᵖ
    where
  obj := Opposite.op
  map {X Y} f := (inv f).op
#align category_theory.groupoid.inv_functor CategoryTheory.Groupoid.invFunctor
-/

end

section

variable {C : Type u} [Category.{v} C]

#print CategoryTheory.Groupoid.ofIsIso /-
/-- A category where every morphism `is_iso` is a groupoid. -/
noncomputable def Groupoid.ofIsIso (all_is_iso : ∀ {X Y : C} (f : X ⟶ Y), IsIso f) : Groupoid.{v} C
    where inv X Y f := inv f
#align category_theory.groupoid.of_is_iso CategoryTheory.Groupoid.ofIsIso
-/

#print CategoryTheory.Groupoid.ofHomUnique /-
/-- A category with a unique morphism between any two objects is a groupoid -/
def Groupoid.ofHomUnique (all_unique : ∀ {X Y : C}, Unique (X ⟶ Y)) : Groupoid.{v} C
    where inv X Y f := all_unique.default
#align category_theory.groupoid.of_hom_unique CategoryTheory.Groupoid.ofHomUnique
-/

end

#print CategoryTheory.InducedCategory.groupoid /-
instance InducedCategory.groupoid {C : Type u} (D : Type u₂) [Groupoid.{v} D] (F : C → D) :
    Groupoid.{v} (InducedCategory D F) :=
  { InducedCategory.category F with
    inv := fun X Y f => Groupoid.inv f
    inv_comp' := fun X Y f => Groupoid.inv_comp f
    comp_inv' := fun X Y f => Groupoid.comp_inv f }
#align category_theory.induced_category.groupoid CategoryTheory.InducedCategory.groupoid
-/

section

#print CategoryTheory.groupoidPi /-
instance groupoidPi {I : Type u} {J : I → Type u₂} [∀ i, Groupoid.{v} (J i)] :
    Groupoid.{max u v} (∀ i : I, J i)
    where inv (x y : ∀ i, J i) (f : ∀ i, x i ⟶ y i) := fun i : I => Groupoid.inv (f i)
#align category_theory.groupoid_pi CategoryTheory.groupoidPi
-/

#print CategoryTheory.groupoidProd /-
instance groupoidProd {α : Type u} {β : Type v} [Groupoid.{u₂} α] [Groupoid.{v₂} β] :
    Groupoid.{max u₂ v₂} (α × β)
    where inv (x y : α × β) (f : x ⟶ y) := (Groupoid.inv f.1, Groupoid.inv f.2)
#align category_theory.groupoid_prod CategoryTheory.groupoidProd
-/

end

end CategoryTheory

