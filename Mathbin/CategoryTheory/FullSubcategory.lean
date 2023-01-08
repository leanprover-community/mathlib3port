/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Reid Barton

! This file was ported from Lean 3 source module category_theory.full_subcategory
! leanprover-community/mathlib commit 940d371319c6658e526349d2c3e1daeeabfae0fd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Functor.FullyFaithful

/-!
# Induced categories and full subcategories

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

universe v v₂ u₁ u₂

-- morphism levels before object levels. See note [category_theory universes].
section Induced

variable {C : Type u₁} (D : Type u₂) [Category.{v} D]

variable (F : C → D)

include F

/- warning: category_theory.induced_category clashes with category_theory.InducedCategory -> CategoryTheory.InducedCategory
warning: category_theory.induced_category -> CategoryTheory.InducedCategory is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u₁}} (D : Type.{u₂}) [_inst_1 : CategoryTheory.Category.{v, u₂} D], (C -> D) -> Type.{u₁}
but is expected to have type
  forall {C : Type.{u₁}} (D : Type.{u₂}), (C -> D) -> Type.{u₁}
Case conversion may be inaccurate. Consider using '#align category_theory.induced_category CategoryTheory.InducedCategoryₓ'. -/
/-- `induced_category D F`, where `F : C → D`, is a typeclass synonym for `C`,
which provides a category structure so that the morphisms `X ⟶ Y` are the morphisms
in `D` from `F X` to `F Y`.
-/
@[nolint has_nonempty_instance unused_arguments]
def InducedCategory : Type u₁ :=
  C
#align category_theory.induced_category CategoryTheory.InducedCategory

variable {D}

/- warning: category_theory.induced_category.has_coe_to_sort clashes with category_theory.InducedCategory.has_coe_to_sort -> CategoryTheory.InducedCategory.hasCoeToSort
warning: category_theory.induced_category.has_coe_to_sort -> CategoryTheory.InducedCategory.hasCoeToSort is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u₁}} {D : Type.{u₂}} [_inst_1 : CategoryTheory.Category.{v, u₂} D] (F : C -> D) {α : Sort.{u_1}} [_inst_2 : CoeSort.{succ u₂, u_1} D α], CoeSort.{succ u₁, u_1} (CategoryTheory.InducedCategory.{v, u₁, u₂} C D _inst_1 F) α
but is expected to have type
  forall {C : Type.{u₁}} {D : Type.{u₂}} (_inst_1 : C -> D) {F : Sort.{u_1}} [α : CoeSort.{succ u₂, u_1} D F], CoeSort.{succ u₁, u_1} (CategoryTheory.InducedCategory.{u₁, u₂} C D _inst_1) F
Case conversion may be inaccurate. Consider using '#align category_theory.induced_category.has_coe_to_sort CategoryTheory.InducedCategory.hasCoeToSortₓ'. -/
instance InducedCategory.hasCoeToSort {α : Sort _} [CoeSort D α] :
    CoeSort (InducedCategory D F) α :=
  ⟨fun c => ↥(F c)⟩
#align category_theory.induced_category.has_coe_to_sort CategoryTheory.InducedCategory.hasCoeToSort

/- warning: category_theory.induced_category.category clashes with category_theory.InducedCategory.category -> CategoryTheory.InducedCategory.category
Case conversion may be inaccurate. Consider using '#align category_theory.induced_category.category CategoryTheory.InducedCategory.categoryₓ'. -/
#print CategoryTheory.InducedCategory.category /-
instance InducedCategory.category : Category.{v} (InducedCategory D F)
    where
  Hom X Y := F X ⟶ F Y
  id X := 𝟙 (F X)
  comp _ _ _ f g := f ≫ g
#align category_theory.induced_category.category CategoryTheory.InducedCategory.category
-/

#print CategoryTheory.inducedFunctor /-
/-- The forgetful functor from an induced category to the original category,
forgetting the extra data.
-/
@[simps]
def inducedFunctor : InducedCategory D F ⥤ D
    where
  obj := F
  map x y f := f
#align category_theory.induced_functor CategoryTheory.inducedFunctor
-/

/- warning: category_theory.induced_category.full clashes with category_theory.InducedCategory.full -> CategoryTheory.InducedCategory.full
Case conversion may be inaccurate. Consider using '#align category_theory.induced_category.full CategoryTheory.InducedCategory.fullₓ'. -/
#print CategoryTheory.InducedCategory.full /-
instance InducedCategory.full : Full (inducedFunctor F) where preimage x y f := f
#align category_theory.induced_category.full CategoryTheory.InducedCategory.full
-/

/- warning: category_theory.induced_category.faithful clashes with category_theory.InducedCategory.faithful -> CategoryTheory.InducedCategory.faithful
Case conversion may be inaccurate. Consider using '#align category_theory.induced_category.faithful CategoryTheory.InducedCategory.faithfulₓ'. -/
#print CategoryTheory.InducedCategory.faithful /-
instance InducedCategory.faithful : Faithful (inducedFunctor F) where
#align category_theory.induced_category.faithful CategoryTheory.InducedCategory.faithful
-/

end Induced

section FullSubcategory

-- A full subcategory is the special case of an induced category with F = subtype.val.
variable {C : Type u₁} [Category.{v} C]

variable (Z : C → Prop)

/--
A subtype-like structure for full subcategories. Morphisms just ignore the property. We don't use
actual subtypes since the simp-normal form `↑X` of `X.val` does not work well for full
subcategories.

See <https://stacks.math.columbia.edu/tag/001D>. We do not define 'strictly full' subcategories.
-/
@[ext, nolint has_nonempty_instance]
structure FullSubcategory where
  obj : C
  property : Z obj
#align category_theory.full_subcategory CategoryTheory.FullSubcategoryₓ

/- warning: category_theory.full_subcategory.category -> CategoryTheory.FullSubcategory.category is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (Z : C -> Prop), CategoryTheory.Category.{u1, u2} (CategoryTheory.FullSubcategoryₓ.{u1, u2} C _inst_1 Z)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (Z : C -> Prop), CategoryTheory.Category.{u1, u2} (CategoryTheory.FullSubcategory.{u2} C Z)
Case conversion may be inaccurate. Consider using '#align category_theory.full_subcategory.category CategoryTheory.FullSubcategory.categoryₓ'. -/
instance FullSubcategory.category : Category.{v} (FullSubcategory Z) :=
  InducedCategory.category FullSubcategory.obj
#align category_theory.full_subcategory.category CategoryTheory.FullSubcategory.category

/- warning: category_theory.full_subcategory_inclusion -> CategoryTheory.fullSubcategoryInclusion is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (Z : C -> Prop), CategoryTheory.Functor.{u1, u1, u2, u2} (CategoryTheory.FullSubcategoryₓ.{u1, u2} C _inst_1 Z) (CategoryTheory.InducedCategory.category.{u1, u2, u2} (CategoryTheory.FullSubcategoryₓ.{u1, u2} C _inst_1 Z) C _inst_1 (CategoryTheory.FullSubcategoryₓ.obj.{u1, u2} C _inst_1 Z)) C _inst_1
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (Z : C -> Prop), CategoryTheory.Functor.{u1, u1, u2, u2} (CategoryTheory.FullSubcategory.{u2} C Z) (CategoryTheory.FullSubcategory.category.{u1, u2} C _inst_1 Z) C _inst_1
Case conversion may be inaccurate. Consider using '#align category_theory.full_subcategory_inclusion CategoryTheory.fullSubcategoryInclusionₓ'. -/
/-- The forgetful functor from a full subcategory into the original category
("forgetting" the condition).
-/
def fullSubcategoryInclusion : FullSubcategory Z ⥤ C :=
  inducedFunctor FullSubcategory.obj
#align category_theory.full_subcategory_inclusion CategoryTheory.fullSubcategoryInclusion

/- warning: category_theory.full_subcategory_inclusion.obj -> CategoryTheory.fullSubcategoryInclusion.obj is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (Z : C -> Prop) {X : CategoryTheory.FullSubcategoryₓ.{u1, u2} C _inst_1 Z}, Eq.{succ u2} C (CategoryTheory.Functor.obj.{u1, u1, u2, u2} (CategoryTheory.FullSubcategoryₓ.{u1, u2} C _inst_1 Z) (CategoryTheory.InducedCategory.category.{u1, u2, u2} (CategoryTheory.FullSubcategoryₓ.{u1, u2} C _inst_1 Z) C _inst_1 (CategoryTheory.FullSubcategoryₓ.obj.{u1, u2} C _inst_1 Z)) C _inst_1 (CategoryTheory.fullSubcategoryInclusion.{u1, u2} C _inst_1 Z) X) (CategoryTheory.FullSubcategoryₓ.obj.{u1, u2} C _inst_1 Z X)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (Z : C -> Prop) {X : CategoryTheory.FullSubcategory.{u2} C Z}, Eq.{succ u2} C (Prefunctor.obj.{succ u1, succ u1, u2, u2} (CategoryTheory.FullSubcategory.{u2} C Z) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (CategoryTheory.FullSubcategory.{u2} C Z) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (CategoryTheory.FullSubcategory.{u2} C Z) (CategoryTheory.FullSubcategory.category.{u1, u2} C _inst_1 Z))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} (CategoryTheory.FullSubcategory.{u2} C Z) (CategoryTheory.FullSubcategory.category.{u1, u2} C _inst_1 Z) C _inst_1 (CategoryTheory.fullSubcategoryInclusion.{u1, u2} C _inst_1 Z)) X) (CategoryTheory.FullSubcategory.obj.{u2} C Z X)
Case conversion may be inaccurate. Consider using '#align category_theory.full_subcategory_inclusion.obj CategoryTheory.fullSubcategoryInclusion.objₓ'. -/
@[simp]
theorem fullSubcategoryInclusion.obj {X} : (fullSubcategoryInclusion Z).obj X = X.obj :=
  rfl
#align category_theory.full_subcategory_inclusion.obj CategoryTheory.fullSubcategoryInclusion.obj

/- warning: category_theory.full_subcategory_inclusion.map -> CategoryTheory.fullSubcategoryInclusion.map is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (Z : C -> Prop) {X : CategoryTheory.FullSubcategoryₓ.{u1, u2} C _inst_1 Z} {Y : CategoryTheory.FullSubcategoryₓ.{u1, u2} C _inst_1 Z} {f : Quiver.Hom.{succ u1, u2} (CategoryTheory.FullSubcategoryₓ.{u1, u2} C _inst_1 Z) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (CategoryTheory.FullSubcategoryₓ.{u1, u2} C _inst_1 Z) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (CategoryTheory.FullSubcategoryₓ.{u1, u2} C _inst_1 Z) (CategoryTheory.InducedCategory.category.{u1, u2, u2} (CategoryTheory.FullSubcategoryₓ.{u1, u2} C _inst_1 Z) C _inst_1 (CategoryTheory.FullSubcategoryₓ.obj.{u1, u2} C _inst_1 Z)))) X Y}, Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.obj.{u1, u1, u2, u2} (CategoryTheory.FullSubcategoryₓ.{u1, u2} C _inst_1 Z) (CategoryTheory.InducedCategory.category.{u1, u2, u2} (CategoryTheory.FullSubcategoryₓ.{u1, u2} C _inst_1 Z) C _inst_1 (CategoryTheory.FullSubcategoryₓ.obj.{u1, u2} C _inst_1 Z)) C _inst_1 (CategoryTheory.fullSubcategoryInclusion.{u1, u2} C _inst_1 Z) X) (CategoryTheory.Functor.obj.{u1, u1, u2, u2} (CategoryTheory.FullSubcategoryₓ.{u1, u2} C _inst_1 Z) (CategoryTheory.InducedCategory.category.{u1, u2, u2} (CategoryTheory.FullSubcategoryₓ.{u1, u2} C _inst_1 Z) C _inst_1 (CategoryTheory.FullSubcategoryₓ.obj.{u1, u2} C _inst_1 Z)) C _inst_1 (CategoryTheory.fullSubcategoryInclusion.{u1, u2} C _inst_1 Z) Y)) (CategoryTheory.Functor.map.{u1, u1, u2, u2} (CategoryTheory.FullSubcategoryₓ.{u1, u2} C _inst_1 Z) (CategoryTheory.InducedCategory.category.{u1, u2, u2} (CategoryTheory.FullSubcategoryₓ.{u1, u2} C _inst_1 Z) C _inst_1 (CategoryTheory.FullSubcategoryₓ.obj.{u1, u2} C _inst_1 Z)) C _inst_1 (CategoryTheory.fullSubcategoryInclusion.{u1, u2} C _inst_1 Z) X Y f) f
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (Z : C -> Prop) {X : CategoryTheory.FullSubcategory.{u2} C Z} {Y : CategoryTheory.FullSubcategory.{u2} C Z} {f : Quiver.Hom.{succ u1, u2} (CategoryTheory.FullSubcategory.{u2} C Z) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (CategoryTheory.FullSubcategory.{u2} C Z) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (CategoryTheory.FullSubcategory.{u2} C Z) (CategoryTheory.FullSubcategory.category.{u1, u2} C _inst_1 Z))) X Y}, Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prefunctor.obj.{succ u1, succ u1, u2, u2} (CategoryTheory.FullSubcategory.{u2} C Z) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (CategoryTheory.FullSubcategory.{u2} C Z) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (CategoryTheory.FullSubcategory.{u2} C Z) (CategoryTheory.FullSubcategory.category.{u1, u2} C _inst_1 Z))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} (CategoryTheory.FullSubcategory.{u2} C Z) (CategoryTheory.FullSubcategory.category.{u1, u2} C _inst_1 Z) C _inst_1 (CategoryTheory.fullSubcategoryInclusion.{u1, u2} C _inst_1 Z)) X) (Prefunctor.obj.{succ u1, succ u1, u2, u2} (CategoryTheory.FullSubcategory.{u2} C Z) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (CategoryTheory.FullSubcategory.{u2} C Z) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (CategoryTheory.FullSubcategory.{u2} C Z) (CategoryTheory.FullSubcategory.category.{u1, u2} C _inst_1 Z))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} (CategoryTheory.FullSubcategory.{u2} C Z) (CategoryTheory.FullSubcategory.category.{u1, u2} C _inst_1 Z) C _inst_1 (CategoryTheory.fullSubcategoryInclusion.{u1, u2} C _inst_1 Z)) Y)) (Prefunctor.map.{succ u1, succ u1, u2, u2} (CategoryTheory.FullSubcategory.{u2} C Z) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (CategoryTheory.FullSubcategory.{u2} C Z) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (CategoryTheory.FullSubcategory.{u2} C Z) (CategoryTheory.FullSubcategory.category.{u1, u2} C _inst_1 Z))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} (CategoryTheory.FullSubcategory.{u2} C Z) (CategoryTheory.FullSubcategory.category.{u1, u2} C _inst_1 Z) C _inst_1 (CategoryTheory.fullSubcategoryInclusion.{u1, u2} C _inst_1 Z)) X Y f) f
Case conversion may be inaccurate. Consider using '#align category_theory.full_subcategory_inclusion.map CategoryTheory.fullSubcategoryInclusion.mapₓ'. -/
@[simp]
theorem fullSubcategoryInclusion.map {X Y} {f : X ⟶ Y} : (fullSubcategoryInclusion Z).map f = f :=
  rfl
#align category_theory.full_subcategory_inclusion.map CategoryTheory.fullSubcategoryInclusion.map

/- warning: category_theory.full_subcategory.full -> CategoryTheory.FullSubcategory.full is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (Z : C -> Prop), CategoryTheory.Full.{u1, u1, u2, u2} (CategoryTheory.FullSubcategoryₓ.{u1, u2} C _inst_1 Z) (CategoryTheory.InducedCategory.category.{u1, u2, u2} (CategoryTheory.FullSubcategoryₓ.{u1, u2} C _inst_1 Z) C _inst_1 (CategoryTheory.FullSubcategoryₓ.obj.{u1, u2} C _inst_1 Z)) C _inst_1 (CategoryTheory.fullSubcategoryInclusion.{u1, u2} C _inst_1 Z)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (Z : C -> Prop), CategoryTheory.Full.{u1, u1, u2, u2} (CategoryTheory.FullSubcategory.{u2} C Z) (CategoryTheory.FullSubcategory.category.{u1, u2} C _inst_1 Z) C _inst_1 (CategoryTheory.fullSubcategoryInclusion.{u1, u2} C _inst_1 Z)
Case conversion may be inaccurate. Consider using '#align category_theory.full_subcategory.full CategoryTheory.FullSubcategory.fullₓ'. -/
instance FullSubcategory.full : Full (fullSubcategoryInclusion Z) :=
  InducedCategory.full _
#align category_theory.full_subcategory.full CategoryTheory.FullSubcategory.full

/- warning: category_theory.full_subcategory.faithful -> CategoryTheory.FullSubcategory.faithful is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (Z : C -> Prop), CategoryTheory.Faithful.{u1, u1, u2, u2} (CategoryTheory.FullSubcategoryₓ.{u1, u2} C _inst_1 Z) (CategoryTheory.InducedCategory.category.{u1, u2, u2} (CategoryTheory.FullSubcategoryₓ.{u1, u2} C _inst_1 Z) C _inst_1 (CategoryTheory.FullSubcategoryₓ.obj.{u1, u2} C _inst_1 Z)) C _inst_1 (CategoryTheory.fullSubcategoryInclusion.{u1, u2} C _inst_1 Z)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (Z : C -> Prop), CategoryTheory.Faithful.{u1, u1, u2, u2} (CategoryTheory.FullSubcategory.{u2} C Z) (CategoryTheory.FullSubcategory.category.{u1, u2} C _inst_1 Z) C _inst_1 (CategoryTheory.fullSubcategoryInclusion.{u1, u2} C _inst_1 Z)
Case conversion may be inaccurate. Consider using '#align category_theory.full_subcategory.faithful CategoryTheory.FullSubcategory.faithfulₓ'. -/
instance FullSubcategory.faithful : Faithful (fullSubcategoryInclusion Z) :=
  InducedCategory.faithful _
#align category_theory.full_subcategory.faithful CategoryTheory.FullSubcategory.faithful

variable {Z} {Z' : C → Prop}

/- warning: category_theory.full_subcategory.map -> CategoryTheory.FullSubcategory.map is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {Z : C -> Prop} {Z' : C -> Prop}, (forall {{X : C}}, (Z X) -> (Z' X)) -> (CategoryTheory.Functor.{u1, u1, u2, u2} (CategoryTheory.FullSubcategoryₓ.{u1, u2} C _inst_1 Z) (CategoryTheory.FullSubcategory.category.{u1, u2} C _inst_1 Z) (CategoryTheory.FullSubcategoryₓ.{u1, u2} C _inst_1 Z') (CategoryTheory.FullSubcategory.category.{u1, u2} C _inst_1 Z'))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {Z : C -> Prop} {Z' : C -> Prop}, (forall {{X : C}}, (Z X) -> (Z' X)) -> (CategoryTheory.Functor.{u1, u1, u2, u2} (CategoryTheory.FullSubcategory.{u2} C Z) (CategoryTheory.FullSubcategory.category.{u1, u2} C _inst_1 Z) (CategoryTheory.FullSubcategory.{u2} C Z') (CategoryTheory.FullSubcategory.category.{u1, u2} C _inst_1 Z'))
Case conversion may be inaccurate. Consider using '#align category_theory.full_subcategory.map CategoryTheory.FullSubcategory.mapₓ'. -/
/-- An implication of predicates `Z → Z'` induces a functor between full subcategories. -/
@[simps]
def FullSubcategory.map (h : ∀ ⦃X⦄, Z X → Z' X) : FullSubcategory Z ⥤ FullSubcategory Z'
    where
  obj X := ⟨X.1, h X.2⟩
  map X Y f := f
#align category_theory.full_subcategory.map CategoryTheory.FullSubcategory.map

instance (h : ∀ ⦃X⦄, Z X → Z' X) : Full (FullSubcategory.map h) where preimage X Y f := f

instance (h : ∀ ⦃X⦄, Z X → Z' X) : Faithful (FullSubcategory.map h) where

/- warning: category_theory.full_subcategory.map_inclusion -> CategoryTheory.FullSubcategory.map_inclusion is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {Z : C -> Prop} {Z' : C -> Prop} (h : forall {{X : C}}, (Z X) -> (Z' X)), Eq.{succ (max u1 u2)} (CategoryTheory.Functor.{u1, u1, u2, u2} (CategoryTheory.FullSubcategoryₓ.{u1, u2} C _inst_1 (fun (X : C) => Z X)) (CategoryTheory.FullSubcategory.category.{u1, u2} C _inst_1 (fun (X : C) => Z X)) C _inst_1) (CategoryTheory.Functor.comp.{u1, u1, u1, u2, u2, u2} (CategoryTheory.FullSubcategoryₓ.{u1, u2} C _inst_1 (fun (X : C) => Z X)) (CategoryTheory.FullSubcategory.category.{u1, u2} C _inst_1 (fun (X : C) => Z X)) (CategoryTheory.FullSubcategoryₓ.{u1, u2} C _inst_1 (fun (X : C) => Z' X)) (CategoryTheory.FullSubcategory.category.{u1, u2} C _inst_1 (fun (X : C) => Z' X)) C _inst_1 (CategoryTheory.FullSubcategory.map.{u1, u2} C _inst_1 (fun (X : C) => Z X) (fun (X : C) => Z' X) h) (CategoryTheory.fullSubcategoryInclusion.{u1, u2} C _inst_1 Z')) (CategoryTheory.fullSubcategoryInclusion.{u1, u2} C _inst_1 Z)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {Z : C -> Prop} {Z' : C -> Prop} (h : forall {{X : C}}, (Z X) -> (Z' X)), Eq.{max (succ u2) (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, u2} (CategoryTheory.FullSubcategory.{u2} C (fun (X : C) => Z X)) (CategoryTheory.FullSubcategory.category.{u1, u2} C _inst_1 (fun (X : C) => Z X)) C _inst_1) (CategoryTheory.Functor.comp.{u1, u1, u1, u2, u2, u2} (CategoryTheory.FullSubcategory.{u2} C (fun (X : C) => Z X)) (CategoryTheory.FullSubcategory.category.{u1, u2} C _inst_1 (fun (X : C) => Z X)) (CategoryTheory.FullSubcategory.{u2} C (fun (X : C) => Z' X)) (CategoryTheory.FullSubcategory.category.{u1, u2} C _inst_1 (fun (X : C) => Z' X)) C _inst_1 (CategoryTheory.FullSubcategory.map.{u1, u2} C _inst_1 (fun (X : C) => Z X) (fun (X : C) => Z' X) h) (CategoryTheory.fullSubcategoryInclusion.{u1, u2} C _inst_1 Z')) (CategoryTheory.fullSubcategoryInclusion.{u1, u2} C _inst_1 Z)
Case conversion may be inaccurate. Consider using '#align category_theory.full_subcategory.map_inclusion CategoryTheory.FullSubcategory.map_inclusionₓ'. -/
@[simp]
theorem FullSubcategory.map_inclusion (h : ∀ ⦃X⦄, Z X → Z' X) :
    FullSubcategory.map h ⋙ fullSubcategoryInclusion Z' = fullSubcategoryInclusion Z :=
  rfl
#align category_theory.full_subcategory.map_inclusion CategoryTheory.FullSubcategory.map_inclusion

section lift

variable {D : Type u₂} [Category.{v₂} D] (P Q : D → Prop)

/- warning: category_theory.full_subcategory.lift -> CategoryTheory.FullSubcategory.lift is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (P : D -> Prop) (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2), (forall (X : C), P (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) -> (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 (CategoryTheory.FullSubcategoryₓ.{u2, u4} D _inst_2 P) (CategoryTheory.FullSubcategory.category.{u2, u4} D _inst_2 P))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (P : D -> Prop) (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2), (forall (X : C), P (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)) -> (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 (CategoryTheory.FullSubcategory.{u4} D P) (CategoryTheory.FullSubcategory.category.{u2, u4} D _inst_2 P))
Case conversion may be inaccurate. Consider using '#align category_theory.full_subcategory.lift CategoryTheory.FullSubcategory.liftₓ'. -/
/-- A functor which maps objects to objects satisfying a certain property induces a lift through
    the full subcategory of objects satisfying that property. -/
@[simps]
def FullSubcategory.lift (F : C ⥤ D) (hF : ∀ X, P (F.obj X)) : C ⥤ FullSubcategory P
    where
  obj X := ⟨F.obj X, hF X⟩
  map X Y f := F.map f
#align category_theory.full_subcategory.lift CategoryTheory.FullSubcategory.lift

/- warning: category_theory.full_subcategory.lift_comp_inclusion -> CategoryTheory.FullSubcategory.lift_comp_inclusion is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (P : D -> Prop) (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (hF : forall (X : C), P (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)), CategoryTheory.Iso.{max u3 u2, max u1 u2 u3 u4} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.comp.{u1, u2, u2, u3, u4, u4} C _inst_1 (CategoryTheory.FullSubcategoryₓ.{u2, u4} D _inst_2 P) (CategoryTheory.FullSubcategory.category.{u2, u4} D _inst_2 P) D _inst_2 (CategoryTheory.FullSubcategory.lift.{u1, u2, u3, u4} C _inst_1 D _inst_2 P F hF) (CategoryTheory.fullSubcategoryInclusion.{u2, u4} D _inst_2 P)) F
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (P : D -> Prop) (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (hF : forall (X : C), P (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)), CategoryTheory.Iso.{max u3 u2, max (max (max u4 u3) u2) u1} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.comp.{u1, u2, u2, u3, u4, u4} C _inst_1 (CategoryTheory.FullSubcategory.{u4} D P) (CategoryTheory.FullSubcategory.category.{u2, u4} D _inst_2 P) D _inst_2 (CategoryTheory.FullSubcategory.lift.{u1, u2, u3, u4} C _inst_1 D _inst_2 P F hF) (CategoryTheory.fullSubcategoryInclusion.{u2, u4} D _inst_2 P)) F
Case conversion may be inaccurate. Consider using '#align category_theory.full_subcategory.lift_comp_inclusion CategoryTheory.FullSubcategory.lift_comp_inclusionₓ'. -/
/-- Composing the lift of a functor through a full subcategory with the inclusion yields the
    original functor. Unfortunately, this is not true by definition, so we only get a natural
    isomorphism, but it is pointwise definitionally true, see
    `full_subcategory.inclusion_obj_lift_obj` and `full_subcategory.inclusion_map_lift_map`. -/
def FullSubcategory.lift_comp_inclusion (F : C ⥤ D) (hF : ∀ X, P (F.obj X)) :
    FullSubcategory.lift P F hF ⋙ fullSubcategoryInclusion P ≅ F :=
  NatIso.ofComponents (fun X => Iso.refl _) (by simp)
#align
  category_theory.full_subcategory.lift_comp_inclusion CategoryTheory.FullSubcategory.lift_comp_inclusion

/- warning: category_theory.full_subcategory.inclusion_obj_lift_obj -> CategoryTheory.fullSubcategoryInclusion_obj_lift_obj is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (P : D -> Prop) (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (hF : forall (X : C), P (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) {X : C}, Eq.{succ u4} D (CategoryTheory.Functor.obj.{u2, u2, u4, u4} (CategoryTheory.FullSubcategoryₓ.{u2, u4} D _inst_2 P) (CategoryTheory.InducedCategory.category.{u2, u4, u4} (CategoryTheory.FullSubcategoryₓ.{u2, u4} D _inst_2 P) D _inst_2 (CategoryTheory.FullSubcategoryₓ.obj.{u2, u4} D _inst_2 P)) D _inst_2 (CategoryTheory.fullSubcategoryInclusion.{u2, u4} D _inst_2 P) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 (CategoryTheory.FullSubcategoryₓ.{u2, u4} D _inst_2 P) (CategoryTheory.FullSubcategory.category.{u2, u4} D _inst_2 P) (CategoryTheory.FullSubcategory.lift.{u1, u2, u3, u4} C _inst_1 D _inst_2 P F hF) X)) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (P : D -> Prop) (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (hF : forall (X : C), P (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)) {X : C}, Eq.{succ u4} D (Prefunctor.obj.{succ u2, succ u2, u4, u4} (CategoryTheory.FullSubcategory.{u4} D P) (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} (CategoryTheory.FullSubcategory.{u4} D P) (CategoryTheory.Category.toCategoryStruct.{u2, u4} (CategoryTheory.FullSubcategory.{u4} D P) (CategoryTheory.FullSubcategory.category.{u2, u4} D _inst_2 P))) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u2, u2, u4, u4} (CategoryTheory.FullSubcategory.{u4} D P) (CategoryTheory.FullSubcategory.category.{u2, u4} D _inst_2 P) D _inst_2 (CategoryTheory.fullSubcategoryInclusion.{u2, u4} D _inst_2 P)) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) (CategoryTheory.FullSubcategory.{u4} D P) (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} (CategoryTheory.FullSubcategory.{u4} D P) (CategoryTheory.Category.toCategoryStruct.{u2, u4} (CategoryTheory.FullSubcategory.{u4} D P) (CategoryTheory.FullSubcategory.category.{u2, u4} D _inst_2 P))) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 (CategoryTheory.FullSubcategory.{u4} D P) (CategoryTheory.FullSubcategory.category.{u2, u4} D _inst_2 P) (CategoryTheory.FullSubcategory.lift.{u1, u2, u3, u4} C _inst_1 D _inst_2 P F hF)) X)) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)
Case conversion may be inaccurate. Consider using '#align category_theory.full_subcategory.inclusion_obj_lift_obj CategoryTheory.fullSubcategoryInclusion_obj_lift_objₓ'. -/
@[simp]
theorem CategoryTheory.fullSubcategoryInclusion_obj_lift_obj (F : C ⥤ D) (hF : ∀ X, P (F.obj X))
    {X : C} : (fullSubcategoryInclusion P).obj ((FullSubcategory.lift P F hF).obj X) = F.obj X :=
  rfl
#align
  category_theory.full_subcategory.inclusion_obj_lift_obj CategoryTheory.fullSubcategoryInclusion_obj_lift_obj

/- warning: category_theory.full_subcategory.inclusion_map_lift_map -> CategoryTheory.fullSubcategoryInclusion_map_lift_map is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (P : D -> Prop) (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (hF : forall (X : C), P (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y), Eq.{succ u2} (Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.obj.{u2, u2, u4, u4} (CategoryTheory.FullSubcategoryₓ.{u2, u4} D _inst_2 P) (CategoryTheory.InducedCategory.category.{u2, u4, u4} (CategoryTheory.FullSubcategoryₓ.{u2, u4} D _inst_2 P) D _inst_2 (CategoryTheory.FullSubcategoryₓ.obj.{u2, u4} D _inst_2 P)) D _inst_2 (CategoryTheory.fullSubcategoryInclusion.{u2, u4} D _inst_2 P) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 (CategoryTheory.FullSubcategoryₓ.{u2, u4} D _inst_2 P) (CategoryTheory.FullSubcategory.category.{u2, u4} D _inst_2 P) (CategoryTheory.FullSubcategory.lift.{u1, u2, u3, u4} C _inst_1 D _inst_2 P F hF) X)) (CategoryTheory.Functor.obj.{u2, u2, u4, u4} (CategoryTheory.FullSubcategoryₓ.{u2, u4} D _inst_2 P) (CategoryTheory.InducedCategory.category.{u2, u4, u4} (CategoryTheory.FullSubcategoryₓ.{u2, u4} D _inst_2 P) D _inst_2 (CategoryTheory.FullSubcategoryₓ.obj.{u2, u4} D _inst_2 P)) D _inst_2 (CategoryTheory.fullSubcategoryInclusion.{u2, u4} D _inst_2 P) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 (CategoryTheory.FullSubcategoryₓ.{u2, u4} D _inst_2 P) (CategoryTheory.FullSubcategory.category.{u2, u4} D _inst_2 P) (CategoryTheory.FullSubcategory.lift.{u1, u2, u3, u4} C _inst_1 D _inst_2 P F hF) Y))) (CategoryTheory.Functor.map.{u2, u2, u4, u4} (CategoryTheory.FullSubcategoryₓ.{u2, u4} D _inst_2 P) (CategoryTheory.InducedCategory.category.{u2, u4, u4} (CategoryTheory.FullSubcategoryₓ.{u2, u4} D _inst_2 P) D _inst_2 (CategoryTheory.FullSubcategoryₓ.obj.{u2, u4} D _inst_2 P)) D _inst_2 (CategoryTheory.fullSubcategoryInclusion.{u2, u4} D _inst_2 P) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 (CategoryTheory.FullSubcategoryₓ.{u2, u4} D _inst_2 P) (CategoryTheory.FullSubcategory.category.{u2, u4} D _inst_2 P) (CategoryTheory.FullSubcategory.lift.{u1, u2, u3, u4} C _inst_1 D _inst_2 P F hF) X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 (CategoryTheory.FullSubcategoryₓ.{u2, u4} D _inst_2 P) (CategoryTheory.FullSubcategory.category.{u2, u4} D _inst_2 P) (CategoryTheory.FullSubcategory.lift.{u1, u2, u3, u4} C _inst_1 D _inst_2 P F hF) Y) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 (CategoryTheory.FullSubcategoryₓ.{u2, u4} D _inst_2 P) (CategoryTheory.FullSubcategory.category.{u2, u4} D _inst_2 P) (CategoryTheory.FullSubcategory.lift.{u1, u2, u3, u4} C _inst_1 D _inst_2 P F hF) X Y f)) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X Y f)
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (P : D -> Prop) (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (hF : forall (X : C), P (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)) {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y), Eq.{succ u2} (Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (Prefunctor.obj.{succ u2, succ u2, u4, u4} (CategoryTheory.FullSubcategory.{u4} D P) (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} (CategoryTheory.FullSubcategory.{u4} D P) (CategoryTheory.Category.toCategoryStruct.{u2, u4} (CategoryTheory.FullSubcategory.{u4} D P) (CategoryTheory.FullSubcategory.category.{u2, u4} D _inst_2 P))) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u2, u2, u4, u4} (CategoryTheory.FullSubcategory.{u4} D P) (CategoryTheory.FullSubcategory.category.{u2, u4} D _inst_2 P) D _inst_2 (CategoryTheory.fullSubcategoryInclusion.{u2, u4} D _inst_2 P)) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) (CategoryTheory.FullSubcategory.{u4} D P) (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} (CategoryTheory.FullSubcategory.{u4} D P) (CategoryTheory.Category.toCategoryStruct.{u2, u4} (CategoryTheory.FullSubcategory.{u4} D P) (CategoryTheory.FullSubcategory.category.{u2, u4} D _inst_2 P))) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 (CategoryTheory.FullSubcategory.{u4} D P) (CategoryTheory.FullSubcategory.category.{u2, u4} D _inst_2 P) (CategoryTheory.FullSubcategory.lift.{u1, u2, u3, u4} C _inst_1 D _inst_2 P F hF)) X)) (Prefunctor.obj.{succ u2, succ u2, u4, u4} (CategoryTheory.FullSubcategory.{u4} D P) (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} (CategoryTheory.FullSubcategory.{u4} D P) (CategoryTheory.Category.toCategoryStruct.{u2, u4} (CategoryTheory.FullSubcategory.{u4} D P) (CategoryTheory.FullSubcategory.category.{u2, u4} D _inst_2 P))) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u2, u2, u4, u4} (CategoryTheory.FullSubcategory.{u4} D P) (CategoryTheory.FullSubcategory.category.{u2, u4} D _inst_2 P) D _inst_2 (CategoryTheory.fullSubcategoryInclusion.{u2, u4} D _inst_2 P)) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) (CategoryTheory.FullSubcategory.{u4} D P) (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} (CategoryTheory.FullSubcategory.{u4} D P) (CategoryTheory.Category.toCategoryStruct.{u2, u4} (CategoryTheory.FullSubcategory.{u4} D P) (CategoryTheory.FullSubcategory.category.{u2, u4} D _inst_2 P))) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 (CategoryTheory.FullSubcategory.{u4} D P) (CategoryTheory.FullSubcategory.category.{u2, u4} D _inst_2 P) (CategoryTheory.FullSubcategory.lift.{u1, u2, u3, u4} C _inst_1 D _inst_2 P F hF)) Y))) (Prefunctor.map.{succ u2, succ u2, u4, u4} (CategoryTheory.FullSubcategory.{u4} D P) (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} (CategoryTheory.FullSubcategory.{u4} D P) (CategoryTheory.Category.toCategoryStruct.{u2, u4} (CategoryTheory.FullSubcategory.{u4} D P) (CategoryTheory.FullSubcategory.category.{u2, u4} D _inst_2 P))) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u2, u2, u4, u4} (CategoryTheory.FullSubcategory.{u4} D P) (CategoryTheory.FullSubcategory.category.{u2, u4} D _inst_2 P) D _inst_2 (CategoryTheory.fullSubcategoryInclusion.{u2, u4} D _inst_2 P)) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) (CategoryTheory.FullSubcategory.{u4} D P) (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} (CategoryTheory.FullSubcategory.{u4} D P) (CategoryTheory.Category.toCategoryStruct.{u2, u4} (CategoryTheory.FullSubcategory.{u4} D P) (CategoryTheory.FullSubcategory.category.{u2, u4} D _inst_2 P))) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 (CategoryTheory.FullSubcategory.{u4} D P) (CategoryTheory.FullSubcategory.category.{u2, u4} D _inst_2 P) (CategoryTheory.FullSubcategory.lift.{u1, u2, u3, u4} C _inst_1 D _inst_2 P F hF)) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) (CategoryTheory.FullSubcategory.{u4} D P) (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} (CategoryTheory.FullSubcategory.{u4} D P) (CategoryTheory.Category.toCategoryStruct.{u2, u4} (CategoryTheory.FullSubcategory.{u4} D P) (CategoryTheory.FullSubcategory.category.{u2, u4} D _inst_2 P))) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 (CategoryTheory.FullSubcategory.{u4} D P) (CategoryTheory.FullSubcategory.category.{u2, u4} D _inst_2 P) (CategoryTheory.FullSubcategory.lift.{u1, u2, u3, u4} C _inst_1 D _inst_2 P F hF)) Y) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) (CategoryTheory.FullSubcategory.{u4} D P) (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} (CategoryTheory.FullSubcategory.{u4} D P) (CategoryTheory.Category.toCategoryStruct.{u2, u4} (CategoryTheory.FullSubcategory.{u4} D P) (CategoryTheory.FullSubcategory.category.{u2, u4} D _inst_2 P))) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 (CategoryTheory.FullSubcategory.{u4} D P) (CategoryTheory.FullSubcategory.category.{u2, u4} D _inst_2 P) (CategoryTheory.FullSubcategory.lift.{u1, u2, u3, u4} C _inst_1 D _inst_2 P F hF)) X Y f)) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X Y f)
Case conversion may be inaccurate. Consider using '#align category_theory.full_subcategory.inclusion_map_lift_map CategoryTheory.fullSubcategoryInclusion_map_lift_mapₓ'. -/
theorem CategoryTheory.fullSubcategoryInclusion_map_lift_map (F : C ⥤ D) (hF : ∀ X, P (F.obj X))
    {X Y : C} (f : X ⟶ Y) :
    (fullSubcategoryInclusion P).map ((FullSubcategory.lift P F hF).map f) = F.map f :=
  rfl
#align
  category_theory.full_subcategory.inclusion_map_lift_map CategoryTheory.fullSubcategoryInclusion_map_lift_map

instance (F : C ⥤ D) (hF : ∀ X, P (F.obj X)) [Faithful F] :
    Faithful (FullSubcategory.lift P F hF) :=
  Faithful.of_comp_iso (FullSubcategory.lift_comp_inclusion P F hF)

instance (F : C ⥤ D) (hF : ∀ X, P (F.obj X)) [Full F] : Full (FullSubcategory.lift P F hF) :=
  Full.ofCompFaithfulIso (FullSubcategory.lift_comp_inclusion P F hF)

/- warning: category_theory.full_subcategory.lift_comp_map -> CategoryTheory.FullSubcategory.lift_comp_map is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (P : D -> Prop) (Q : D -> Prop) (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (hF : forall (X : C), P (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) (h : forall {{X : D}}, (P X) -> (Q X)), Eq.{succ (max u1 u2 u3 u4)} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 (CategoryTheory.FullSubcategoryₓ.{u2, u4} D _inst_2 (fun (X : D) => Q X)) (CategoryTheory.FullSubcategory.category.{u2, u4} D _inst_2 (fun (X : D) => Q X))) (CategoryTheory.Functor.comp.{u1, u2, u2, u3, u4, u4} C _inst_1 (CategoryTheory.FullSubcategoryₓ.{u2, u4} D _inst_2 P) (CategoryTheory.FullSubcategory.category.{u2, u4} D _inst_2 P) (CategoryTheory.FullSubcategoryₓ.{u2, u4} D _inst_2 (fun (X : D) => Q X)) (CategoryTheory.FullSubcategory.category.{u2, u4} D _inst_2 (fun (X : D) => Q X)) (CategoryTheory.FullSubcategory.lift.{u1, u2, u3, u4} C _inst_1 D _inst_2 P F hF) (CategoryTheory.FullSubcategory.map.{u2, u4} D _inst_2 P (fun (X : D) => Q X) h)) (CategoryTheory.FullSubcategory.lift.{u1, u2, u3, u4} C _inst_1 D _inst_2 Q F (fun (X : C) => h (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) (hF X)))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (P : D -> Prop) (Q : D -> Prop) (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (hF : forall (X : C), P (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)) (h : forall {{X : D}}, (P X) -> (Q X)), Eq.{max (max (max (succ u3) (succ u4)) (succ u1)) (succ u2)} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 (CategoryTheory.FullSubcategory.{u4} D (fun (X : D) => Q X)) (CategoryTheory.FullSubcategory.category.{u2, u4} D _inst_2 (fun (X : D) => Q X))) (CategoryTheory.Functor.comp.{u1, u2, u2, u3, u4, u4} C _inst_1 (CategoryTheory.FullSubcategory.{u4} D P) (CategoryTheory.FullSubcategory.category.{u2, u4} D _inst_2 P) (CategoryTheory.FullSubcategory.{u4} D (fun (X : D) => Q X)) (CategoryTheory.FullSubcategory.category.{u2, u4} D _inst_2 (fun (X : D) => Q X)) (CategoryTheory.FullSubcategory.lift.{u1, u2, u3, u4} C _inst_1 D _inst_2 P F hF) (CategoryTheory.FullSubcategory.map.{u2, u4} D _inst_2 P (fun (X : D) => Q X) h)) (CategoryTheory.FullSubcategory.lift.{u1, u2, u3, u4} C _inst_1 D _inst_2 Q F (fun (X : C) => h (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X) (hF X)))
Case conversion may be inaccurate. Consider using '#align category_theory.full_subcategory.lift_comp_map CategoryTheory.FullSubcategory.lift_comp_mapₓ'. -/
@[simp]
theorem FullSubcategory.lift_comp_map (F : C ⥤ D) (hF : ∀ X, P (F.obj X)) (h : ∀ ⦃X⦄, P X → Q X) :
    FullSubcategory.lift P F hF ⋙ FullSubcategory.map h =
      FullSubcategory.lift Q F fun X => h (hF X) :=
  rfl
#align category_theory.full_subcategory.lift_comp_map CategoryTheory.FullSubcategory.lift_comp_map

end lift

end FullSubcategory

end CategoryTheory

