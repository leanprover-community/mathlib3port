/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import Mathbin.CategoryTheory.DiscreteCategory
import Mathbin.CategoryTheory.Bicategory.Functor
import Mathbin.CategoryTheory.Bicategory.Strict

/-!
# Locally discrete bicategories

A category `C` can be promoted to a strict bicategory `locally_discrete C`. The objects and the
1-morphisms in `locally_discrete C` are the same as the objects and the morphisms, respectively,
in `C`, and the 2-morphisms in `locally_discrete C` are the equalities between 1-morphisms. In
other words, the category consisting of the 1-morphisms between each pair of objects `X` and `Y`
in `locally_discrete C` is defined as the discrete category associated with the type `X ⟶ Y`.
-/


namespace CategoryTheory

open Bicategory Discrete

open_locale Bicategory

universe w₂ v v₁ v₂ u u₁ u₂

variable (C : Type u)

/-- A type alias for promoting any category to a bicategory,
with the only 2-morphisms being equalities.
-/
def LocallyDiscrete :=
  C

namespace LocallyDiscrete

instance : ∀ [Inhabited C], Inhabited (LocallyDiscrete C) :=
  id

instance : ∀ [CategoryStruct.{v} C], CategoryStruct (LocallyDiscrete C) :=
  id

variable {C} [CategoryStruct.{v} C]

instance (X Y : LocallyDiscrete C) : SmallCategory (X ⟶ Y) :=
  CategoryTheory.discreteCategory (X ⟶ Y)

end LocallyDiscrete

variable (C) [Category.{v} C]

/-- The locally discrete bicategory on a category is a bicategory in which the objects and the
1-morphisms are the same as those in the underlying category, and the 2-morphisms are the
equalities between 1-morphisms.
-/
instance locallyDiscreteBicategory : Bicategory (LocallyDiscrete C) where
  whiskerLeft := fun X Y Z f g h η => eqToHom (congr_arg2ₓ (· ≫ ·) rfl (eq_of_hom η))
  whiskerRight := fun X Y Z f g η h => eqToHom (congr_arg2ₓ (· ≫ ·) (eq_of_hom η) rfl)
  associator := fun W X Y Z f g h => eqToIso (Category.assoc f g h)
  leftUnitor := fun X Y f => eqToIso (Category.id_comp f)
  rightUnitor := fun X Y f => eqToIso (Category.comp_id f)

/-- A locally discrete bicategory is strict. -/
instance locallyDiscreteBicategory.strict : Strict (LocallyDiscrete C) :=
  {  }

variable {I : Type u₁} [Category.{v₁} I] {B : Type u₂} [Bicategory.{w₂, v₂} B] [Strict B]

/-- If `B` is a strict bicategory and `I` is a (1-)category, any functor (of 1-categories) `I ⥤ B` can
be promoted to an oplax functor from `locally_discrete I` to `B`.
-/
@[simps]
def Functor.toOplaxFunctor (F : I ⥤ B) : OplaxFunctor (LocallyDiscrete I) B :=
  { F with map₂ := fun i j f g η => eqToHom (congr_argₓ _ (eq_of_hom η)), map_id := fun i => eqToHom (F.map_id i),
    map_comp := fun i j k f g => eqToHom (F.map_comp f g) }

end CategoryTheory

