/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Reid Barton
-/
import Mathbin.CategoryTheory.Functor.FullyFaithful

/-!
# Induced categories and full subcategories

Given a category `D` and a function `F : C → D `from a type `C` to the
objects of `D`, there is an essentially unique way to give `C` a
category structure such that `F` becomes a fully faithful functor,
namely by taking $$ Hom_C(X, Y) = Hom_D(FX, FY) $$. We call this the
category induced from `D` along `F`.

As a special case, if `C` is a subtype of `D`,
this produces the full subcategory of `D` on the objects belonging to `C`.
In general the induced category is equivalent to the full subcategory of `D` on the
image of `F`.

## Implementation notes

It looks odd to make `D` an explicit argument of `induced_category`,
when it is determined by the argument `F` anyways. The reason to make `D`
explicit is in order to control its syntactic form, so that instances
like `induced_category.has_forget₂` (elsewhere) refer to the correct
form of D. This is used to set up several algebraic categories like

  def CommMon : Type (u+1) := induced_category Mon (bundled.map @comm_monoid.to_monoid)
  -- not `induced_category (bundled monoid) (bundled.map @comm_monoid.to_monoid)`,
  -- even though `Mon = bundled monoid`!
-/


namespace CategoryTheory

universe v u₁ u₂

-- morphism levels before object levels. See note [category_theory universes].
section Induced

variable {C : Type u₁} (D : Type u₂) [Category.{v} D]

variable (F : C → D)

include F

/-- `induced_category D F`, where `F : C → D`, is a typeclass synonym for `C`,
which provides a category structure so that the morphisms `X ⟶ Y` are the morphisms
in `D` from `F X` to `F Y`.
-/
@[nolint has_inhabited_instance unused_arguments]
def InducedCategory : Type u₁ :=
  C

variable {D}

instance InducedCategory.hasCoeToSort {α : Sort _} [CoeSort D α] : CoeSort (InducedCategory D F) α :=
  ⟨fun c => ↥(F c)⟩

instance InducedCategory.category : Category.{v} (InducedCategory D F) where
  Hom := fun X Y => F X ⟶ F Y
  id := fun X => 𝟙 (F X)
  comp := fun _ _ _ f g => f ≫ g

/-- The forgetful functor from an induced category to the original category,
forgetting the extra data.
-/
@[simps]
def inducedFunctor : InducedCategory D F ⥤ D where
  obj := F
  map := fun x y f => f

instance InducedCategory.full : Full (inducedFunctor F) where
  Preimage := fun x y f => f

instance InducedCategory.faithful : Faithful (inducedFunctor F) :=
  {  }

end Induced

section FullSubcategory

-- A full subcategory is the special case of an induced category with F = subtype.val.
variable {C : Type u₂} [Category.{v} C]

variable (Z : C → Prop)

/-- The category structure on a subtype; morphisms just ignore the property.

See https://stacks.math.columbia.edu/tag/001D. We do not define 'strictly full' subcategories.
-/
instance fullSubcategory : Category.{v} { X : C // Z X } :=
  InducedCategory.category Subtype.val

/-- The forgetful functor from a full subcategory into the original category
("forgetting" the condition).
-/
def fullSubcategoryInclusion : { X : C // Z X } ⥤ C :=
  inducedFunctor Subtype.val

@[simp]
theorem fullSubcategoryInclusion.obj {X} : (fullSubcategoryInclusion Z).obj X = X.val :=
  rfl

@[simp]
theorem fullSubcategoryInclusion.map {X Y} {f : X ⟶ Y} : (fullSubcategoryInclusion Z).map f = f :=
  rfl

instance fullSubcategory.full : Full (fullSubcategoryInclusion Z) :=
  InducedCategory.full Subtype.val

instance fullSubcategory.faithful : Faithful (fullSubcategoryInclusion Z) :=
  InducedCategory.faithful Subtype.val

end FullSubcategory

end CategoryTheory

