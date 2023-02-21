/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module category_theory.sums.basic
! leanprover-community/mathlib commit bd9851ca476957ea4549eb19b40e7b5ade9428cc
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.EqToHom

/-!
# Binary disjoint unions of categories

We define the category instance on `C ⊕ D` when `C` and `D` are categories.

We define:
* `inl_`      : the functor `C ⥤ C ⊕ D`
* `inr_`      : the functor `D ⥤ C ⊕ D`
* `swap`      : the functor `C ⊕ D ⥤ D ⊕ C`
    (and the fact this is an equivalence)

We further define sums of functors and natural transformations, written `F.sum G` and `α.sum β`.
-/


namespace CategoryTheory

universe v₁ u₁

-- morphism levels before object levels. See note [category_theory universes].
open Sum

section

variable (C : Type u₁) [Category.{v₁} C] (D : Type u₁) [Category.{v₁} D]

#print CategoryTheory.sum /-
/-- `sum C D` gives the direct sum of two categories.
-/
instance sum : Category.{v₁} (Sum C D)
    where
  Hom X Y :=
    match X, Y with
    | inl X, inl Y => X ⟶ Y
    | inl X, inr Y => PEmpty
    | inr X, inl Y => PEmpty
    | inr X, inr Y => X ⟶ Y
  id X :=
    match X with
    | inl X => 𝟙 X
    | inr X => 𝟙 X
  comp X Y Z f g :=
    match X, Y, Z, f, g with
    | inl X, inl Y, inl Z, f, g => f ≫ g
    | inr X, inr Y, inr Z, f, g => f ≫ g
#align category_theory.sum CategoryTheory.sum
-/

#print CategoryTheory.sum_comp_inl /-
@[simp]
theorem sum_comp_inl {P Q R : C} (f : (inl P : Sum C D) ⟶ inl Q) (g : (inl Q : Sum C D) ⟶ inl R) :
    @CategoryStruct.comp _ _ P Q R (f : P ⟶ Q) (g : Q ⟶ R) =
      @CategoryStruct.comp _ _ (inl P) (inl Q) (inl R) (f : P ⟶ Q) (g : Q ⟶ R) :=
  rfl
#align category_theory.sum_comp_inl CategoryTheory.sum_comp_inl
-/

#print CategoryTheory.sum_comp_inr /-
@[simp]
theorem sum_comp_inr {P Q R : D} (f : (inr P : Sum C D) ⟶ inr Q) (g : (inr Q : Sum C D) ⟶ inr R) :
    @CategoryStruct.comp _ _ P Q R (f : P ⟶ Q) (g : Q ⟶ R) =
      @CategoryStruct.comp _ _ (inr P) (inr Q) (inr R) (f : P ⟶ Q) (g : Q ⟶ R) :=
  rfl
#align category_theory.sum_comp_inr CategoryTheory.sum_comp_inr
-/

end

namespace Sum

variable (C : Type u₁) [Category.{v₁} C] (D : Type u₁) [Category.{v₁} D]

#print CategoryTheory.Sum.inl_ /-
-- Unfortunate naming here, suggestions welcome.
/-- `inl_` is the functor `X ↦ inl X`. -/
@[simps]
def inl_ : C ⥤ Sum C D where
  obj X := inl X
  map X Y f := f
#align category_theory.sum.inl_ CategoryTheory.Sum.inl_
-/

#print CategoryTheory.Sum.inr_ /-
/-- `inr_` is the functor `X ↦ inr X`. -/
@[simps]
def inr_ : D ⥤ Sum C D where
  obj X := inr X
  map X Y f := f
#align category_theory.sum.inr_ CategoryTheory.Sum.inr_
-/

#print CategoryTheory.Sum.swap /-
/-- The functor exchanging two direct summand categories. -/
def swap : Sum C D ⥤ Sum D C
    where
  obj X :=
    match X with
    | inl X => inr X
    | inr X => inl X
  map X Y f :=
    match X, Y, f with
    | inl X, inl Y, f => f
    | inr X, inr Y, f => f
#align category_theory.sum.swap CategoryTheory.Sum.swap
-/

/- warning: category_theory.sum.swap_obj_inl -> CategoryTheory.Sum.swap_obj_inl is a dubious translation:
lean 3 declaration is
  forall (C : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u1, u2} C] (D : Type.{u2}) [_inst_2 : CategoryTheory.Category.{u1, u2} D] (X : C), Eq.{succ u2} (Sum.{u2, u2} D C) (CategoryTheory.Functor.obj.{u1, u1, u2, u2} (Sum.{u2, u2} C D) (CategoryTheory.sum.{u1, u2} C _inst_1 D _inst_2) (Sum.{u2, u2} D C) (CategoryTheory.sum.{u1, u2} D _inst_2 C _inst_1) (CategoryTheory.Sum.swap.{u1, u2} C _inst_1 D _inst_2) (Sum.inl.{u2, u2} C D X)) (Sum.inr.{u2, u2} D C X)
but is expected to have type
  forall (C : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u1, u2} C] (D : Type.{u2}) [_inst_2 : CategoryTheory.Category.{u1, u2} D] (X : C), Eq.{succ u2} (Sum.{u2, u2} D C) (Prefunctor.obj.{succ u1, succ u1, u2, u2} (Sum.{u2, u2} C D) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Sum.{u2, u2} C D) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Sum.{u2, u2} C D) (CategoryTheory.sum.{u1, u2} C _inst_1 D _inst_2))) (Sum.{u2, u2} D C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Sum.{u2, u2} D C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Sum.{u2, u2} D C) (CategoryTheory.sum.{u1, u2} D _inst_2 C _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} (Sum.{u2, u2} C D) (CategoryTheory.sum.{u1, u2} C _inst_1 D _inst_2) (Sum.{u2, u2} D C) (CategoryTheory.sum.{u1, u2} D _inst_2 C _inst_1) (CategoryTheory.Sum.swap.{u1, u2} C _inst_1 D _inst_2)) (Sum.inl.{u2, u2} C D X)) (Sum.inr.{u2, u2} D C X)
Case conversion may be inaccurate. Consider using '#align category_theory.sum.swap_obj_inl CategoryTheory.Sum.swap_obj_inlₓ'. -/
@[simp]
theorem swap_obj_inl (X : C) : (swap C D).obj (inl X) = inr X :=
  rfl
#align category_theory.sum.swap_obj_inl CategoryTheory.Sum.swap_obj_inl

/- warning: category_theory.sum.swap_obj_inr -> CategoryTheory.Sum.swap_obj_inr is a dubious translation:
lean 3 declaration is
  forall (C : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u1, u2} C] (D : Type.{u2}) [_inst_2 : CategoryTheory.Category.{u1, u2} D] (X : D), Eq.{succ u2} (Sum.{u2, u2} D C) (CategoryTheory.Functor.obj.{u1, u1, u2, u2} (Sum.{u2, u2} C D) (CategoryTheory.sum.{u1, u2} C _inst_1 D _inst_2) (Sum.{u2, u2} D C) (CategoryTheory.sum.{u1, u2} D _inst_2 C _inst_1) (CategoryTheory.Sum.swap.{u1, u2} C _inst_1 D _inst_2) (Sum.inr.{u2, u2} C D X)) (Sum.inl.{u2, u2} D C X)
but is expected to have type
  forall (C : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u1, u2} C] (D : Type.{u2}) [_inst_2 : CategoryTheory.Category.{u1, u2} D] (X : D), Eq.{succ u2} (Sum.{u2, u2} D C) (Prefunctor.obj.{succ u1, succ u1, u2, u2} (Sum.{u2, u2} C D) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Sum.{u2, u2} C D) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Sum.{u2, u2} C D) (CategoryTheory.sum.{u1, u2} C _inst_1 D _inst_2))) (Sum.{u2, u2} D C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Sum.{u2, u2} D C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Sum.{u2, u2} D C) (CategoryTheory.sum.{u1, u2} D _inst_2 C _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} (Sum.{u2, u2} C D) (CategoryTheory.sum.{u1, u2} C _inst_1 D _inst_2) (Sum.{u2, u2} D C) (CategoryTheory.sum.{u1, u2} D _inst_2 C _inst_1) (CategoryTheory.Sum.swap.{u1, u2} C _inst_1 D _inst_2)) (Sum.inr.{u2, u2} C D X)) (Sum.inl.{u2, u2} D C X)
Case conversion may be inaccurate. Consider using '#align category_theory.sum.swap_obj_inr CategoryTheory.Sum.swap_obj_inrₓ'. -/
@[simp]
theorem swap_obj_inr (X : D) : (swap C D).obj (inr X) = inl X :=
  rfl
#align category_theory.sum.swap_obj_inr CategoryTheory.Sum.swap_obj_inr

/- warning: category_theory.sum.swap_map_inl -> CategoryTheory.Sum.swap_map_inl is a dubious translation:
lean 3 declaration is
  forall (C : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u1, u2} C] (D : Type.{u2}) [_inst_2 : CategoryTheory.Category.{u1, u2} D] {X : C} {Y : C} {f : Quiver.Hom.{succ u1, u2} (Sum.{u2, u2} C D) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Sum.{u2, u2} C D) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Sum.{u2, u2} C D) (CategoryTheory.sum.{u1, u2} C _inst_1 D _inst_2))) (Sum.inl.{u2, u2} C D X) (Sum.inl.{u2, u2} C D Y)}, Eq.{succ u1} (Quiver.Hom.{succ u1, u2} (Sum.{u2, u2} D C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Sum.{u2, u2} D C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Sum.{u2, u2} D C) (CategoryTheory.sum.{u1, u2} D _inst_2 C _inst_1))) (CategoryTheory.Functor.obj.{u1, u1, u2, u2} (Sum.{u2, u2} C D) (CategoryTheory.sum.{u1, u2} C _inst_1 D _inst_2) (Sum.{u2, u2} D C) (CategoryTheory.sum.{u1, u2} D _inst_2 C _inst_1) (CategoryTheory.Sum.swap.{u1, u2} C _inst_1 D _inst_2) (Sum.inl.{u2, u2} C D X)) (CategoryTheory.Functor.obj.{u1, u1, u2, u2} (Sum.{u2, u2} C D) (CategoryTheory.sum.{u1, u2} C _inst_1 D _inst_2) (Sum.{u2, u2} D C) (CategoryTheory.sum.{u1, u2} D _inst_2 C _inst_1) (CategoryTheory.Sum.swap.{u1, u2} C _inst_1 D _inst_2) (Sum.inl.{u2, u2} C D Y))) (CategoryTheory.Functor.map.{u1, u1, u2, u2} (Sum.{u2, u2} C D) (CategoryTheory.sum.{u1, u2} C _inst_1 D _inst_2) (Sum.{u2, u2} D C) (CategoryTheory.sum.{u1, u2} D _inst_2 C _inst_1) (CategoryTheory.Sum.swap.{u1, u2} C _inst_1 D _inst_2) (Sum.inl.{u2, u2} C D X) (Sum.inl.{u2, u2} C D Y) f) f
but is expected to have type
  forall (C : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u1, u2} C] (D : Type.{u2}) [_inst_2 : CategoryTheory.Category.{u1, u2} D] {X : C} {Y : C} {f : Quiver.Hom.{succ u1, u2} (Sum.{u2, u2} C D) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Sum.{u2, u2} C D) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Sum.{u2, u2} C D) (CategoryTheory.sum.{u1, u2} C _inst_1 D _inst_2))) (Sum.inl.{u2, u2} C D X) (Sum.inl.{u2, u2} C D Y)}, Eq.{succ u1} (Quiver.Hom.{succ u1, u2} (Sum.{u2, u2} D C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Sum.{u2, u2} D C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Sum.{u2, u2} D C) (CategoryTheory.sum.{u1, u2} D _inst_2 C _inst_1))) (Prefunctor.obj.{succ u1, succ u1, u2, u2} (Sum.{u2, u2} C D) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Sum.{u2, u2} C D) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Sum.{u2, u2} C D) (CategoryTheory.sum.{u1, u2} C _inst_1 D _inst_2))) (Sum.{u2, u2} D C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Sum.{u2, u2} D C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Sum.{u2, u2} D C) (CategoryTheory.sum.{u1, u2} D _inst_2 C _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} (Sum.{u2, u2} C D) (CategoryTheory.sum.{u1, u2} C _inst_1 D _inst_2) (Sum.{u2, u2} D C) (CategoryTheory.sum.{u1, u2} D _inst_2 C _inst_1) (CategoryTheory.Sum.swap.{u1, u2} C _inst_1 D _inst_2)) (Sum.inl.{u2, u2} C D X)) (Prefunctor.obj.{succ u1, succ u1, u2, u2} (Sum.{u2, u2} C D) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Sum.{u2, u2} C D) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Sum.{u2, u2} C D) (CategoryTheory.sum.{u1, u2} C _inst_1 D _inst_2))) (Sum.{u2, u2} D C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Sum.{u2, u2} D C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Sum.{u2, u2} D C) (CategoryTheory.sum.{u1, u2} D _inst_2 C _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} (Sum.{u2, u2} C D) (CategoryTheory.sum.{u1, u2} C _inst_1 D _inst_2) (Sum.{u2, u2} D C) (CategoryTheory.sum.{u1, u2} D _inst_2 C _inst_1) (CategoryTheory.Sum.swap.{u1, u2} C _inst_1 D _inst_2)) (Sum.inl.{u2, u2} C D Y))) (Prefunctor.map.{succ u1, succ u1, u2, u2} (Sum.{u2, u2} C D) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Sum.{u2, u2} C D) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Sum.{u2, u2} C D) (CategoryTheory.sum.{u1, u2} C _inst_1 D _inst_2))) (Sum.{u2, u2} D C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Sum.{u2, u2} D C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Sum.{u2, u2} D C) (CategoryTheory.sum.{u1, u2} D _inst_2 C _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} (Sum.{u2, u2} C D) (CategoryTheory.sum.{u1, u2} C _inst_1 D _inst_2) (Sum.{u2, u2} D C) (CategoryTheory.sum.{u1, u2} D _inst_2 C _inst_1) (CategoryTheory.Sum.swap.{u1, u2} C _inst_1 D _inst_2)) (Sum.inl.{u2, u2} C D X) (Sum.inl.{u2, u2} C D Y) f) f
Case conversion may be inaccurate. Consider using '#align category_theory.sum.swap_map_inl CategoryTheory.Sum.swap_map_inlₓ'. -/
@[simp]
theorem swap_map_inl {X Y : C} {f : inl X ⟶ inl Y} : (swap C D).map f = f :=
  rfl
#align category_theory.sum.swap_map_inl CategoryTheory.Sum.swap_map_inl

/- warning: category_theory.sum.swap_map_inr -> CategoryTheory.Sum.swap_map_inr is a dubious translation:
lean 3 declaration is
  forall (C : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u1, u2} C] (D : Type.{u2}) [_inst_2 : CategoryTheory.Category.{u1, u2} D] {X : D} {Y : D} {f : Quiver.Hom.{succ u1, u2} (Sum.{u2, u2} C D) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Sum.{u2, u2} C D) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Sum.{u2, u2} C D) (CategoryTheory.sum.{u1, u2} C _inst_1 D _inst_2))) (Sum.inr.{u2, u2} C D X) (Sum.inr.{u2, u2} C D Y)}, Eq.{succ u1} (Quiver.Hom.{succ u1, u2} (Sum.{u2, u2} D C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Sum.{u2, u2} D C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Sum.{u2, u2} D C) (CategoryTheory.sum.{u1, u2} D _inst_2 C _inst_1))) (CategoryTheory.Functor.obj.{u1, u1, u2, u2} (Sum.{u2, u2} C D) (CategoryTheory.sum.{u1, u2} C _inst_1 D _inst_2) (Sum.{u2, u2} D C) (CategoryTheory.sum.{u1, u2} D _inst_2 C _inst_1) (CategoryTheory.Sum.swap.{u1, u2} C _inst_1 D _inst_2) (Sum.inr.{u2, u2} C D X)) (CategoryTheory.Functor.obj.{u1, u1, u2, u2} (Sum.{u2, u2} C D) (CategoryTheory.sum.{u1, u2} C _inst_1 D _inst_2) (Sum.{u2, u2} D C) (CategoryTheory.sum.{u1, u2} D _inst_2 C _inst_1) (CategoryTheory.Sum.swap.{u1, u2} C _inst_1 D _inst_2) (Sum.inr.{u2, u2} C D Y))) (CategoryTheory.Functor.map.{u1, u1, u2, u2} (Sum.{u2, u2} C D) (CategoryTheory.sum.{u1, u2} C _inst_1 D _inst_2) (Sum.{u2, u2} D C) (CategoryTheory.sum.{u1, u2} D _inst_2 C _inst_1) (CategoryTheory.Sum.swap.{u1, u2} C _inst_1 D _inst_2) (Sum.inr.{u2, u2} C D X) (Sum.inr.{u2, u2} C D Y) f) f
but is expected to have type
  forall (C : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u1, u2} C] (D : Type.{u2}) [_inst_2 : CategoryTheory.Category.{u1, u2} D] {X : D} {Y : D} {f : Quiver.Hom.{succ u1, u2} (Sum.{u2, u2} C D) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Sum.{u2, u2} C D) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Sum.{u2, u2} C D) (CategoryTheory.sum.{u1, u2} C _inst_1 D _inst_2))) (Sum.inr.{u2, u2} C D X) (Sum.inr.{u2, u2} C D Y)}, Eq.{succ u1} (Quiver.Hom.{succ u1, u2} (Sum.{u2, u2} D C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Sum.{u2, u2} D C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Sum.{u2, u2} D C) (CategoryTheory.sum.{u1, u2} D _inst_2 C _inst_1))) (Prefunctor.obj.{succ u1, succ u1, u2, u2} (Sum.{u2, u2} C D) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Sum.{u2, u2} C D) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Sum.{u2, u2} C D) (CategoryTheory.sum.{u1, u2} C _inst_1 D _inst_2))) (Sum.{u2, u2} D C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Sum.{u2, u2} D C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Sum.{u2, u2} D C) (CategoryTheory.sum.{u1, u2} D _inst_2 C _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} (Sum.{u2, u2} C D) (CategoryTheory.sum.{u1, u2} C _inst_1 D _inst_2) (Sum.{u2, u2} D C) (CategoryTheory.sum.{u1, u2} D _inst_2 C _inst_1) (CategoryTheory.Sum.swap.{u1, u2} C _inst_1 D _inst_2)) (Sum.inr.{u2, u2} C D X)) (Prefunctor.obj.{succ u1, succ u1, u2, u2} (Sum.{u2, u2} C D) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Sum.{u2, u2} C D) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Sum.{u2, u2} C D) (CategoryTheory.sum.{u1, u2} C _inst_1 D _inst_2))) (Sum.{u2, u2} D C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Sum.{u2, u2} D C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Sum.{u2, u2} D C) (CategoryTheory.sum.{u1, u2} D _inst_2 C _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} (Sum.{u2, u2} C D) (CategoryTheory.sum.{u1, u2} C _inst_1 D _inst_2) (Sum.{u2, u2} D C) (CategoryTheory.sum.{u1, u2} D _inst_2 C _inst_1) (CategoryTheory.Sum.swap.{u1, u2} C _inst_1 D _inst_2)) (Sum.inr.{u2, u2} C D Y))) (Prefunctor.map.{succ u1, succ u1, u2, u2} (Sum.{u2, u2} C D) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Sum.{u2, u2} C D) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Sum.{u2, u2} C D) (CategoryTheory.sum.{u1, u2} C _inst_1 D _inst_2))) (Sum.{u2, u2} D C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Sum.{u2, u2} D C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Sum.{u2, u2} D C) (CategoryTheory.sum.{u1, u2} D _inst_2 C _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} (Sum.{u2, u2} C D) (CategoryTheory.sum.{u1, u2} C _inst_1 D _inst_2) (Sum.{u2, u2} D C) (CategoryTheory.sum.{u1, u2} D _inst_2 C _inst_1) (CategoryTheory.Sum.swap.{u1, u2} C _inst_1 D _inst_2)) (Sum.inr.{u2, u2} C D X) (Sum.inr.{u2, u2} C D Y) f) f
Case conversion may be inaccurate. Consider using '#align category_theory.sum.swap_map_inr CategoryTheory.Sum.swap_map_inrₓ'. -/
@[simp]
theorem swap_map_inr {X Y : D} {f : inr X ⟶ inr Y} : (swap C D).map f = f :=
  rfl
#align category_theory.sum.swap_map_inr CategoryTheory.Sum.swap_map_inr

namespace Swap

/- warning: category_theory.sum.swap.equivalence -> CategoryTheory.Sum.Swap.equivalence is a dubious translation:
lean 3 declaration is
  forall (C : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u1, u2} C] (D : Type.{u2}) [_inst_2 : CategoryTheory.Category.{u1, u2} D], CategoryTheory.Equivalence.{u1, u1, u2, u2} (Sum.{u2, u2} C D) (CategoryTheory.sum.{u1, u2} C _inst_1 D _inst_2) (Sum.{u2, u2} D C) (CategoryTheory.sum.{u1, u2} D _inst_2 C _inst_1)
but is expected to have type
  forall (C : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u1, u2} C] (D : Type.{u2}) [_inst_2 : CategoryTheory.Category.{u1, u2} D], CategoryTheory.Equivalence.{u1, u1, u2, u2} (Sum.{u2, u2} C D) (Sum.{u2, u2} D C) (CategoryTheory.sum.{u1, u2} C _inst_1 D _inst_2) (CategoryTheory.sum.{u1, u2} D _inst_2 C _inst_1)
Case conversion may be inaccurate. Consider using '#align category_theory.sum.swap.equivalence CategoryTheory.Sum.Swap.equivalenceₓ'. -/
/-- `swap` gives an equivalence between `C ⊕ D` and `D ⊕ C`. -/
def equivalence : Sum C D ≌ Sum D C :=
  Equivalence.mk (swap C D) (swap D C)
    (NatIso.ofComponents (fun X => eqToIso (by cases X <;> rfl)) (by tidy))
    (NatIso.ofComponents (fun X => eqToIso (by cases X <;> rfl)) (by tidy))
#align category_theory.sum.swap.equivalence CategoryTheory.Sum.Swap.equivalence

#print CategoryTheory.Sum.Swap.isEquivalence /-
instance isEquivalence : IsEquivalence (swap C D) :=
  (by infer_instance : IsEquivalence (equivalence C D).Functor)
#align category_theory.sum.swap.is_equivalence CategoryTheory.Sum.Swap.isEquivalence
-/

#print CategoryTheory.Sum.Swap.symmetry /-
/-- The double swap on `C ⊕ D` is naturally isomorphic to the identity functor. -/
def symmetry : swap C D ⋙ swap D C ≅ 𝟭 (Sum C D) :=
  (equivalence C D).unitIso.symm
#align category_theory.sum.swap.symmetry CategoryTheory.Sum.Swap.symmetry
-/

end Swap

end Sum

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₁} [Category.{v₁} B] {C : Type u₁}
  [Category.{v₁} C] {D : Type u₁} [Category.{v₁} D]

namespace Functor

#print CategoryTheory.Functor.sum /-
/-- The sum of two functors. -/
def sum (F : A ⥤ B) (G : C ⥤ D) : Sum A C ⥤ Sum B D
    where
  obj X :=
    match X with
    | inl X => inl (F.obj X)
    | inr X => inr (G.obj X)
  map X Y f :=
    match X, Y, f with
    | inl X, inl Y, f => F.map f
    | inr X, inr Y, f => G.map f
  map_id' X := by cases X <;> unfold_aux; erw [F.map_id]; rfl; erw [G.map_id]; rfl
  map_comp' X Y Z f g :=
    match X, Y, Z, f, g with
    | inl X, inl Y, inl Z, f, g => by
      unfold_aux
      erw [F.map_comp]
      rfl
    | inr X, inr Y, inr Z, f, g => by
      unfold_aux
      erw [G.map_comp]
      rfl
#align category_theory.functor.sum CategoryTheory.Functor.sum
-/

/- warning: category_theory.functor.sum_obj_inl -> CategoryTheory.Functor.sum_obj_inl is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} A] {B : Type.{u2}} [_inst_2 : CategoryTheory.Category.{u1, u2} B] {C : Type.{u2}} [_inst_3 : CategoryTheory.Category.{u1, u2} C] {D : Type.{u2}} [_inst_4 : CategoryTheory.Category.{u1, u2} D] (F : CategoryTheory.Functor.{u1, u1, u2, u2} A _inst_1 B _inst_2) (G : CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_3 D _inst_4) (a : A), Eq.{succ u2} (Sum.{u2, u2} B D) (CategoryTheory.Functor.obj.{u1, u1, u2, u2} (Sum.{u2, u2} A C) (CategoryTheory.sum.{u1, u2} A _inst_1 C _inst_3) (Sum.{u2, u2} B D) (CategoryTheory.sum.{u1, u2} B _inst_2 D _inst_4) (CategoryTheory.Functor.sum.{u1, u2} A _inst_1 B _inst_2 C _inst_3 D _inst_4 F G) (Sum.inl.{u2, u2} A C a)) (Sum.inl.{u2, u2} B D (CategoryTheory.Functor.obj.{u1, u1, u2, u2} A _inst_1 B _inst_2 F a))
but is expected to have type
  forall {A : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} A] {B : Type.{u2}} [_inst_2 : CategoryTheory.Category.{u1, u2} B] {C : Type.{u2}} [_inst_3 : CategoryTheory.Category.{u1, u2} C] {D : Type.{u2}} [_inst_4 : CategoryTheory.Category.{u1, u2} D] (F : CategoryTheory.Functor.{u1, u1, u2, u2} A _inst_1 B _inst_2) (G : CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_3 D _inst_4) (a : A), Eq.{succ u2} (Sum.{u2, u2} B D) (Prefunctor.obj.{succ u1, succ u1, u2, u2} (Sum.{u2, u2} A C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Sum.{u2, u2} A C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Sum.{u2, u2} A C) (CategoryTheory.sum.{u1, u2} A _inst_1 C _inst_3))) (Sum.{u2, u2} B D) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Sum.{u2, u2} B D) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Sum.{u2, u2} B D) (CategoryTheory.sum.{u1, u2} B _inst_2 D _inst_4))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} (Sum.{u2, u2} A C) (CategoryTheory.sum.{u1, u2} A _inst_1 C _inst_3) (Sum.{u2, u2} B D) (CategoryTheory.sum.{u1, u2} B _inst_2 D _inst_4) (CategoryTheory.Functor.sum.{u1, u2} A _inst_1 B _inst_2 C _inst_3 D _inst_4 F G)) (Sum.inl.{u2, u2} A C a)) (Sum.inl.{u2, u2} B D (Prefunctor.obj.{succ u1, succ u1, u2, u2} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} A (CategoryTheory.Category.toCategoryStruct.{u1, u2} A _inst_1)) B (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} B (CategoryTheory.Category.toCategoryStruct.{u1, u2} B _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} A _inst_1 B _inst_2 F) a))
Case conversion may be inaccurate. Consider using '#align category_theory.functor.sum_obj_inl CategoryTheory.Functor.sum_obj_inlₓ'. -/
@[simp]
theorem sum_obj_inl (F : A ⥤ B) (G : C ⥤ D) (a : A) : (F.Sum G).obj (inl a) = inl (F.obj a) :=
  rfl
#align category_theory.functor.sum_obj_inl CategoryTheory.Functor.sum_obj_inl

/- warning: category_theory.functor.sum_obj_inr -> CategoryTheory.Functor.sum_obj_inr is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} A] {B : Type.{u2}} [_inst_2 : CategoryTheory.Category.{u1, u2} B] {C : Type.{u2}} [_inst_3 : CategoryTheory.Category.{u1, u2} C] {D : Type.{u2}} [_inst_4 : CategoryTheory.Category.{u1, u2} D] (F : CategoryTheory.Functor.{u1, u1, u2, u2} A _inst_1 B _inst_2) (G : CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_3 D _inst_4) (c : C), Eq.{succ u2} (Sum.{u2, u2} B D) (CategoryTheory.Functor.obj.{u1, u1, u2, u2} (Sum.{u2, u2} A C) (CategoryTheory.sum.{u1, u2} A _inst_1 C _inst_3) (Sum.{u2, u2} B D) (CategoryTheory.sum.{u1, u2} B _inst_2 D _inst_4) (CategoryTheory.Functor.sum.{u1, u2} A _inst_1 B _inst_2 C _inst_3 D _inst_4 F G) (Sum.inr.{u2, u2} A C c)) (Sum.inr.{u2, u2} B D (CategoryTheory.Functor.obj.{u1, u1, u2, u2} C _inst_3 D _inst_4 G c))
but is expected to have type
  forall {A : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} A] {B : Type.{u2}} [_inst_2 : CategoryTheory.Category.{u1, u2} B] {C : Type.{u2}} [_inst_3 : CategoryTheory.Category.{u1, u2} C] {D : Type.{u2}} [_inst_4 : CategoryTheory.Category.{u1, u2} D] (F : CategoryTheory.Functor.{u1, u1, u2, u2} A _inst_1 B _inst_2) (G : CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_3 D _inst_4) (c : C), Eq.{succ u2} (Sum.{u2, u2} B D) (Prefunctor.obj.{succ u1, succ u1, u2, u2} (Sum.{u2, u2} A C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Sum.{u2, u2} A C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Sum.{u2, u2} A C) (CategoryTheory.sum.{u1, u2} A _inst_1 C _inst_3))) (Sum.{u2, u2} B D) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Sum.{u2, u2} B D) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Sum.{u2, u2} B D) (CategoryTheory.sum.{u1, u2} B _inst_2 D _inst_4))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} (Sum.{u2, u2} A C) (CategoryTheory.sum.{u1, u2} A _inst_1 C _inst_3) (Sum.{u2, u2} B D) (CategoryTheory.sum.{u1, u2} B _inst_2 D _inst_4) (CategoryTheory.Functor.sum.{u1, u2} A _inst_1 B _inst_2 C _inst_3 D _inst_4 F G)) (Sum.inr.{u2, u2} A C c)) (Sum.inr.{u2, u2} B D (Prefunctor.obj.{succ u1, succ u1, u2, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_3)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} D (CategoryTheory.Category.toCategoryStruct.{u1, u2} D _inst_4)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} C _inst_3 D _inst_4 G) c))
Case conversion may be inaccurate. Consider using '#align category_theory.functor.sum_obj_inr CategoryTheory.Functor.sum_obj_inrₓ'. -/
@[simp]
theorem sum_obj_inr (F : A ⥤ B) (G : C ⥤ D) (c : C) : (F.Sum G).obj (inr c) = inr (G.obj c) :=
  rfl
#align category_theory.functor.sum_obj_inr CategoryTheory.Functor.sum_obj_inr

/- warning: category_theory.functor.sum_map_inl -> CategoryTheory.Functor.sum_map_inl is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} A] {B : Type.{u2}} [_inst_2 : CategoryTheory.Category.{u1, u2} B] {C : Type.{u2}} [_inst_3 : CategoryTheory.Category.{u1, u2} C] {D : Type.{u2}} [_inst_4 : CategoryTheory.Category.{u1, u2} D] (F : CategoryTheory.Functor.{u1, u1, u2, u2} A _inst_1 B _inst_2) (G : CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_3 D _inst_4) {a : A} {a' : A} (f : Quiver.Hom.{succ u1, u2} (Sum.{u2, u2} A C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Sum.{u2, u2} A C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Sum.{u2, u2} A C) (CategoryTheory.sum.{u1, u2} A _inst_1 C _inst_3))) (Sum.inl.{u2, u2} A C a) (Sum.inl.{u2, u2} A C a')), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} (Sum.{u2, u2} B D) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Sum.{u2, u2} B D) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Sum.{u2, u2} B D) (CategoryTheory.sum.{u1, u2} B _inst_2 D _inst_4))) (CategoryTheory.Functor.obj.{u1, u1, u2, u2} (Sum.{u2, u2} A C) (CategoryTheory.sum.{u1, u2} A _inst_1 C _inst_3) (Sum.{u2, u2} B D) (CategoryTheory.sum.{u1, u2} B _inst_2 D _inst_4) (CategoryTheory.Functor.sum.{u1, u2} A _inst_1 B _inst_2 C _inst_3 D _inst_4 F G) (Sum.inl.{u2, u2} A C a)) (CategoryTheory.Functor.obj.{u1, u1, u2, u2} (Sum.{u2, u2} A C) (CategoryTheory.sum.{u1, u2} A _inst_1 C _inst_3) (Sum.{u2, u2} B D) (CategoryTheory.sum.{u1, u2} B _inst_2 D _inst_4) (CategoryTheory.Functor.sum.{u1, u2} A _inst_1 B _inst_2 C _inst_3 D _inst_4 F G) (Sum.inl.{u2, u2} A C a'))) (CategoryTheory.Functor.map.{u1, u1, u2, u2} (Sum.{u2, u2} A C) (CategoryTheory.sum.{u1, u2} A _inst_1 C _inst_3) (Sum.{u2, u2} B D) (CategoryTheory.sum.{u1, u2} B _inst_2 D _inst_4) (CategoryTheory.Functor.sum.{u1, u2} A _inst_1 B _inst_2 C _inst_3 D _inst_4 F G) (Sum.inl.{u2, u2} A C a) (Sum.inl.{u2, u2} A C a') f) (CategoryTheory.Functor.map.{u1, u1, u2, u2} A _inst_1 B _inst_2 F a a' f)
but is expected to have type
  forall {A : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} A] {B : Type.{u2}} [_inst_2 : CategoryTheory.Category.{u1, u2} B] {C : Type.{u2}} [_inst_3 : CategoryTheory.Category.{u1, u2} C] {D : Type.{u2}} [_inst_4 : CategoryTheory.Category.{u1, u2} D] (F : CategoryTheory.Functor.{u1, u1, u2, u2} A _inst_1 B _inst_2) (G : CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_3 D _inst_4) {a : A} {a' : A} (f : Quiver.Hom.{succ u1, u2} (Sum.{u2, u2} A C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Sum.{u2, u2} A C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Sum.{u2, u2} A C) (CategoryTheory.sum.{u1, u2} A _inst_1 C _inst_3))) (Sum.inl.{u2, u2} A C a) (Sum.inl.{u2, u2} A C a')), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} (Sum.{u2, u2} B D) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Sum.{u2, u2} B D) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Sum.{u2, u2} B D) (CategoryTheory.sum.{u1, u2} B _inst_2 D _inst_4))) (Prefunctor.obj.{succ u1, succ u1, u2, u2} (Sum.{u2, u2} A C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Sum.{u2, u2} A C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Sum.{u2, u2} A C) (CategoryTheory.sum.{u1, u2} A _inst_1 C _inst_3))) (Sum.{u2, u2} B D) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Sum.{u2, u2} B D) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Sum.{u2, u2} B D) (CategoryTheory.sum.{u1, u2} B _inst_2 D _inst_4))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} (Sum.{u2, u2} A C) (CategoryTheory.sum.{u1, u2} A _inst_1 C _inst_3) (Sum.{u2, u2} B D) (CategoryTheory.sum.{u1, u2} B _inst_2 D _inst_4) (CategoryTheory.Functor.sum.{u1, u2} A _inst_1 B _inst_2 C _inst_3 D _inst_4 F G)) (Sum.inl.{u2, u2} A C a)) (Prefunctor.obj.{succ u1, succ u1, u2, u2} (Sum.{u2, u2} A C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Sum.{u2, u2} A C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Sum.{u2, u2} A C) (CategoryTheory.sum.{u1, u2} A _inst_1 C _inst_3))) (Sum.{u2, u2} B D) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Sum.{u2, u2} B D) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Sum.{u2, u2} B D) (CategoryTheory.sum.{u1, u2} B _inst_2 D _inst_4))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} (Sum.{u2, u2} A C) (CategoryTheory.sum.{u1, u2} A _inst_1 C _inst_3) (Sum.{u2, u2} B D) (CategoryTheory.sum.{u1, u2} B _inst_2 D _inst_4) (CategoryTheory.Functor.sum.{u1, u2} A _inst_1 B _inst_2 C _inst_3 D _inst_4 F G)) (Sum.inl.{u2, u2} A C a'))) (Prefunctor.map.{succ u1, succ u1, u2, u2} (Sum.{u2, u2} A C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Sum.{u2, u2} A C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Sum.{u2, u2} A C) (CategoryTheory.sum.{u1, u2} A _inst_1 C _inst_3))) (Sum.{u2, u2} B D) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Sum.{u2, u2} B D) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Sum.{u2, u2} B D) (CategoryTheory.sum.{u1, u2} B _inst_2 D _inst_4))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} (Sum.{u2, u2} A C) (CategoryTheory.sum.{u1, u2} A _inst_1 C _inst_3) (Sum.{u2, u2} B D) (CategoryTheory.sum.{u1, u2} B _inst_2 D _inst_4) (CategoryTheory.Functor.sum.{u1, u2} A _inst_1 B _inst_2 C _inst_3 D _inst_4 F G)) (Sum.inl.{u2, u2} A C a) (Sum.inl.{u2, u2} A C a') f) (Prefunctor.map.{succ u1, succ u1, u2, u2} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} A (CategoryTheory.Category.toCategoryStruct.{u1, u2} A _inst_1)) B (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} B (CategoryTheory.Category.toCategoryStruct.{u1, u2} B _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} A _inst_1 B _inst_2 F) a a' f)
Case conversion may be inaccurate. Consider using '#align category_theory.functor.sum_map_inl CategoryTheory.Functor.sum_map_inlₓ'. -/
@[simp]
theorem sum_map_inl (F : A ⥤ B) (G : C ⥤ D) {a a' : A} (f : inl a ⟶ inl a') :
    (F.Sum G).map f = F.map f :=
  rfl
#align category_theory.functor.sum_map_inl CategoryTheory.Functor.sum_map_inl

/- warning: category_theory.functor.sum_map_inr -> CategoryTheory.Functor.sum_map_inr is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} A] {B : Type.{u2}} [_inst_2 : CategoryTheory.Category.{u1, u2} B] {C : Type.{u2}} [_inst_3 : CategoryTheory.Category.{u1, u2} C] {D : Type.{u2}} [_inst_4 : CategoryTheory.Category.{u1, u2} D] (F : CategoryTheory.Functor.{u1, u1, u2, u2} A _inst_1 B _inst_2) (G : CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_3 D _inst_4) {c : C} {c' : C} (f : Quiver.Hom.{succ u1, u2} (Sum.{u2, u2} A C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Sum.{u2, u2} A C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Sum.{u2, u2} A C) (CategoryTheory.sum.{u1, u2} A _inst_1 C _inst_3))) (Sum.inr.{u2, u2} A C c) (Sum.inr.{u2, u2} A C c')), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} (Sum.{u2, u2} B D) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Sum.{u2, u2} B D) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Sum.{u2, u2} B D) (CategoryTheory.sum.{u1, u2} B _inst_2 D _inst_4))) (CategoryTheory.Functor.obj.{u1, u1, u2, u2} (Sum.{u2, u2} A C) (CategoryTheory.sum.{u1, u2} A _inst_1 C _inst_3) (Sum.{u2, u2} B D) (CategoryTheory.sum.{u1, u2} B _inst_2 D _inst_4) (CategoryTheory.Functor.sum.{u1, u2} A _inst_1 B _inst_2 C _inst_3 D _inst_4 F G) (Sum.inr.{u2, u2} A C c)) (CategoryTheory.Functor.obj.{u1, u1, u2, u2} (Sum.{u2, u2} A C) (CategoryTheory.sum.{u1, u2} A _inst_1 C _inst_3) (Sum.{u2, u2} B D) (CategoryTheory.sum.{u1, u2} B _inst_2 D _inst_4) (CategoryTheory.Functor.sum.{u1, u2} A _inst_1 B _inst_2 C _inst_3 D _inst_4 F G) (Sum.inr.{u2, u2} A C c'))) (CategoryTheory.Functor.map.{u1, u1, u2, u2} (Sum.{u2, u2} A C) (CategoryTheory.sum.{u1, u2} A _inst_1 C _inst_3) (Sum.{u2, u2} B D) (CategoryTheory.sum.{u1, u2} B _inst_2 D _inst_4) (CategoryTheory.Functor.sum.{u1, u2} A _inst_1 B _inst_2 C _inst_3 D _inst_4 F G) (Sum.inr.{u2, u2} A C c) (Sum.inr.{u2, u2} A C c') f) (CategoryTheory.Functor.map.{u1, u1, u2, u2} C _inst_3 D _inst_4 G c c' f)
but is expected to have type
  forall {A : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} A] {B : Type.{u2}} [_inst_2 : CategoryTheory.Category.{u1, u2} B] {C : Type.{u2}} [_inst_3 : CategoryTheory.Category.{u1, u2} C] {D : Type.{u2}} [_inst_4 : CategoryTheory.Category.{u1, u2} D] (F : CategoryTheory.Functor.{u1, u1, u2, u2} A _inst_1 B _inst_2) (G : CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_3 D _inst_4) {c : C} {c' : C} (f : Quiver.Hom.{succ u1, u2} (Sum.{u2, u2} A C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Sum.{u2, u2} A C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Sum.{u2, u2} A C) (CategoryTheory.sum.{u1, u2} A _inst_1 C _inst_3))) (Sum.inr.{u2, u2} A C c) (Sum.inr.{u2, u2} A C c')), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} (Sum.{u2, u2} B D) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Sum.{u2, u2} B D) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Sum.{u2, u2} B D) (CategoryTheory.sum.{u1, u2} B _inst_2 D _inst_4))) (Prefunctor.obj.{succ u1, succ u1, u2, u2} (Sum.{u2, u2} A C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Sum.{u2, u2} A C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Sum.{u2, u2} A C) (CategoryTheory.sum.{u1, u2} A _inst_1 C _inst_3))) (Sum.{u2, u2} B D) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Sum.{u2, u2} B D) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Sum.{u2, u2} B D) (CategoryTheory.sum.{u1, u2} B _inst_2 D _inst_4))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} (Sum.{u2, u2} A C) (CategoryTheory.sum.{u1, u2} A _inst_1 C _inst_3) (Sum.{u2, u2} B D) (CategoryTheory.sum.{u1, u2} B _inst_2 D _inst_4) (CategoryTheory.Functor.sum.{u1, u2} A _inst_1 B _inst_2 C _inst_3 D _inst_4 F G)) (Sum.inr.{u2, u2} A C c)) (Prefunctor.obj.{succ u1, succ u1, u2, u2} (Sum.{u2, u2} A C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Sum.{u2, u2} A C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Sum.{u2, u2} A C) (CategoryTheory.sum.{u1, u2} A _inst_1 C _inst_3))) (Sum.{u2, u2} B D) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Sum.{u2, u2} B D) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Sum.{u2, u2} B D) (CategoryTheory.sum.{u1, u2} B _inst_2 D _inst_4))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} (Sum.{u2, u2} A C) (CategoryTheory.sum.{u1, u2} A _inst_1 C _inst_3) (Sum.{u2, u2} B D) (CategoryTheory.sum.{u1, u2} B _inst_2 D _inst_4) (CategoryTheory.Functor.sum.{u1, u2} A _inst_1 B _inst_2 C _inst_3 D _inst_4 F G)) (Sum.inr.{u2, u2} A C c'))) (Prefunctor.map.{succ u1, succ u1, u2, u2} (Sum.{u2, u2} A C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Sum.{u2, u2} A C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Sum.{u2, u2} A C) (CategoryTheory.sum.{u1, u2} A _inst_1 C _inst_3))) (Sum.{u2, u2} B D) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Sum.{u2, u2} B D) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Sum.{u2, u2} B D) (CategoryTheory.sum.{u1, u2} B _inst_2 D _inst_4))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} (Sum.{u2, u2} A C) (CategoryTheory.sum.{u1, u2} A _inst_1 C _inst_3) (Sum.{u2, u2} B D) (CategoryTheory.sum.{u1, u2} B _inst_2 D _inst_4) (CategoryTheory.Functor.sum.{u1, u2} A _inst_1 B _inst_2 C _inst_3 D _inst_4 F G)) (Sum.inr.{u2, u2} A C c) (Sum.inr.{u2, u2} A C c') f) (Prefunctor.map.{succ u1, succ u1, u2, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_3)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} D (CategoryTheory.Category.toCategoryStruct.{u1, u2} D _inst_4)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} C _inst_3 D _inst_4 G) c c' f)
Case conversion may be inaccurate. Consider using '#align category_theory.functor.sum_map_inr CategoryTheory.Functor.sum_map_inrₓ'. -/
@[simp]
theorem sum_map_inr (F : A ⥤ B) (G : C ⥤ D) {c c' : C} (f : inr c ⟶ inr c') :
    (F.Sum G).map f = G.map f :=
  rfl
#align category_theory.functor.sum_map_inr CategoryTheory.Functor.sum_map_inr

end Functor

namespace NatTrans

#print CategoryTheory.NatTrans.sum /-
/-- The sum of two natural transformations. -/
def sum {F G : A ⥤ B} {H I : C ⥤ D} (α : F ⟶ G) (β : H ⟶ I) : F.Sum H ⟶ G.Sum I
    where
  app X :=
    match X with
    | inl X => α.app X
    | inr X => β.app X
  naturality' X Y f :=
    match X, Y, f with
    | inl X, inl Y, f => by unfold_aux; erw [α.naturality]; rfl
    | inr X, inr Y, f => by unfold_aux; erw [β.naturality]; rfl
#align category_theory.nat_trans.sum CategoryTheory.NatTrans.sum
-/

/- warning: category_theory.nat_trans.sum_app_inl -> CategoryTheory.NatTrans.sum_app_inl is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} A] {B : Type.{u2}} [_inst_2 : CategoryTheory.Category.{u1, u2} B] {C : Type.{u2}} [_inst_3 : CategoryTheory.Category.{u1, u2} C] {D : Type.{u2}} [_inst_4 : CategoryTheory.Category.{u1, u2} D] {F : CategoryTheory.Functor.{u1, u1, u2, u2} A _inst_1 B _inst_2} {G : CategoryTheory.Functor.{u1, u1, u2, u2} A _inst_1 B _inst_2} {H : CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_3 D _inst_4} {I : CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_3 D _inst_4} (α : Quiver.Hom.{succ (max u2 u1), max u1 u2} (CategoryTheory.Functor.{u1, u1, u2, u2} A _inst_1 B _inst_2) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u1 u2} (CategoryTheory.Functor.{u1, u1, u2, u2} A _inst_1 B _inst_2) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u1 u2} (CategoryTheory.Functor.{u1, u1, u2, u2} A _inst_1 B _inst_2) (CategoryTheory.Functor.category.{u1, u1, u2, u2} A _inst_1 B _inst_2))) F G) (β : Quiver.Hom.{succ (max u2 u1), max u1 u2} (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_3 D _inst_4) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u1 u2} (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_3 D _inst_4) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u1 u2} (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_3 D _inst_4) (CategoryTheory.Functor.category.{u1, u1, u2, u2} C _inst_3 D _inst_4))) H I) (a : A), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} (Sum.{u2, u2} B D) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Sum.{u2, u2} B D) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Sum.{u2, u2} B D) (CategoryTheory.sum.{u1, u2} B _inst_2 D _inst_4))) (CategoryTheory.Functor.obj.{u1, u1, u2, u2} (Sum.{u2, u2} A C) (CategoryTheory.sum.{u1, u2} A _inst_1 C _inst_3) (Sum.{u2, u2} B D) (CategoryTheory.sum.{u1, u2} B _inst_2 D _inst_4) (CategoryTheory.Functor.sum.{u1, u2} A _inst_1 B _inst_2 C _inst_3 D _inst_4 F H) (Sum.inl.{u2, u2} A C a)) (CategoryTheory.Functor.obj.{u1, u1, u2, u2} (Sum.{u2, u2} A C) (CategoryTheory.sum.{u1, u2} A _inst_1 C _inst_3) (Sum.{u2, u2} B D) (CategoryTheory.sum.{u1, u2} B _inst_2 D _inst_4) (CategoryTheory.Functor.sum.{u1, u2} A _inst_1 B _inst_2 C _inst_3 D _inst_4 G I) (Sum.inl.{u2, u2} A C a))) (CategoryTheory.NatTrans.app.{u1, u1, u2, u2} (Sum.{u2, u2} A C) (CategoryTheory.sum.{u1, u2} A _inst_1 C _inst_3) (Sum.{u2, u2} B D) (CategoryTheory.sum.{u1, u2} B _inst_2 D _inst_4) (CategoryTheory.Functor.sum.{u1, u2} A _inst_1 B _inst_2 C _inst_3 D _inst_4 F H) (CategoryTheory.Functor.sum.{u1, u2} A _inst_1 B _inst_2 C _inst_3 D _inst_4 G I) (CategoryTheory.NatTrans.sum.{u1, u2} A _inst_1 B _inst_2 C _inst_3 D _inst_4 F G H I α β) (Sum.inl.{u2, u2} A C a)) (CategoryTheory.NatTrans.app.{u1, u1, u2, u2} A _inst_1 B _inst_2 F G α a)
but is expected to have type
  forall {A : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} A] {B : Type.{u2}} [_inst_2 : CategoryTheory.Category.{u1, u2} B] {C : Type.{u2}} [_inst_3 : CategoryTheory.Category.{u1, u2} C] {D : Type.{u2}} [_inst_4 : CategoryTheory.Category.{u1, u2} D] {F : CategoryTheory.Functor.{u1, u1, u2, u2} A _inst_1 B _inst_2} {G : CategoryTheory.Functor.{u1, u1, u2, u2} A _inst_1 B _inst_2} {H : CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_3 D _inst_4} {I : CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_3 D _inst_4} (α : Quiver.Hom.{max (succ u2) (succ u1), max u2 u1} (CategoryTheory.Functor.{u1, u1, u2, u2} A _inst_1 B _inst_2) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 u1} (CategoryTheory.Functor.{u1, u1, u2, u2} A _inst_1 B _inst_2) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 u1} (CategoryTheory.Functor.{u1, u1, u2, u2} A _inst_1 B _inst_2) (CategoryTheory.Functor.category.{u1, u1, u2, u2} A _inst_1 B _inst_2))) F G) (β : Quiver.Hom.{max (succ u2) (succ u1), max u2 u1} (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_3 D _inst_4) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 u1} (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_3 D _inst_4) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 u1} (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_3 D _inst_4) (CategoryTheory.Functor.category.{u1, u1, u2, u2} C _inst_3 D _inst_4))) H I) (a : A), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} (Sum.{u2, u2} B D) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Sum.{u2, u2} B D) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Sum.{u2, u2} B D) (CategoryTheory.sum.{u1, u2} B _inst_2 D _inst_4))) (Prefunctor.obj.{succ u1, succ u1, u2, u2} (Sum.{u2, u2} A C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Sum.{u2, u2} A C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Sum.{u2, u2} A C) (CategoryTheory.sum.{u1, u2} A _inst_1 C _inst_3))) (Sum.{u2, u2} B D) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Sum.{u2, u2} B D) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Sum.{u2, u2} B D) (CategoryTheory.sum.{u1, u2} B _inst_2 D _inst_4))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} (Sum.{u2, u2} A C) (CategoryTheory.sum.{u1, u2} A _inst_1 C _inst_3) (Sum.{u2, u2} B D) (CategoryTheory.sum.{u1, u2} B _inst_2 D _inst_4) (CategoryTheory.Functor.sum.{u1, u2} A _inst_1 B _inst_2 C _inst_3 D _inst_4 F H)) (Sum.inl.{u2, u2} A C a)) (Prefunctor.obj.{succ u1, succ u1, u2, u2} (Sum.{u2, u2} A C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Sum.{u2, u2} A C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Sum.{u2, u2} A C) (CategoryTheory.sum.{u1, u2} A _inst_1 C _inst_3))) (Sum.{u2, u2} B D) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Sum.{u2, u2} B D) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Sum.{u2, u2} B D) (CategoryTheory.sum.{u1, u2} B _inst_2 D _inst_4))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} (Sum.{u2, u2} A C) (CategoryTheory.sum.{u1, u2} A _inst_1 C _inst_3) (Sum.{u2, u2} B D) (CategoryTheory.sum.{u1, u2} B _inst_2 D _inst_4) (CategoryTheory.Functor.sum.{u1, u2} A _inst_1 B _inst_2 C _inst_3 D _inst_4 G I)) (Sum.inl.{u2, u2} A C a))) (CategoryTheory.NatTrans.app.{u1, u1, u2, u2} (Sum.{u2, u2} A C) (CategoryTheory.sum.{u1, u2} A _inst_1 C _inst_3) (Sum.{u2, u2} B D) (CategoryTheory.sum.{u1, u2} B _inst_2 D _inst_4) (CategoryTheory.Functor.sum.{u1, u2} A _inst_1 B _inst_2 C _inst_3 D _inst_4 F H) (CategoryTheory.Functor.sum.{u1, u2} A _inst_1 B _inst_2 C _inst_3 D _inst_4 G I) (CategoryTheory.NatTrans.sum.{u1, u2} A _inst_1 B _inst_2 C _inst_3 D _inst_4 F G H I α β) (Sum.inl.{u2, u2} A C a)) (CategoryTheory.NatTrans.app.{u1, u1, u2, u2} A _inst_1 B _inst_2 F G α a)
Case conversion may be inaccurate. Consider using '#align category_theory.nat_trans.sum_app_inl CategoryTheory.NatTrans.sum_app_inlₓ'. -/
@[simp]
theorem sum_app_inl {F G : A ⥤ B} {H I : C ⥤ D} (α : F ⟶ G) (β : H ⟶ I) (a : A) :
    (sum α β).app (inl a) = α.app a :=
  rfl
#align category_theory.nat_trans.sum_app_inl CategoryTheory.NatTrans.sum_app_inl

/- warning: category_theory.nat_trans.sum_app_inr -> CategoryTheory.NatTrans.sum_app_inr is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} A] {B : Type.{u2}} [_inst_2 : CategoryTheory.Category.{u1, u2} B] {C : Type.{u2}} [_inst_3 : CategoryTheory.Category.{u1, u2} C] {D : Type.{u2}} [_inst_4 : CategoryTheory.Category.{u1, u2} D] {F : CategoryTheory.Functor.{u1, u1, u2, u2} A _inst_1 B _inst_2} {G : CategoryTheory.Functor.{u1, u1, u2, u2} A _inst_1 B _inst_2} {H : CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_3 D _inst_4} {I : CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_3 D _inst_4} (α : Quiver.Hom.{succ (max u2 u1), max u1 u2} (CategoryTheory.Functor.{u1, u1, u2, u2} A _inst_1 B _inst_2) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u1 u2} (CategoryTheory.Functor.{u1, u1, u2, u2} A _inst_1 B _inst_2) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u1 u2} (CategoryTheory.Functor.{u1, u1, u2, u2} A _inst_1 B _inst_2) (CategoryTheory.Functor.category.{u1, u1, u2, u2} A _inst_1 B _inst_2))) F G) (β : Quiver.Hom.{succ (max u2 u1), max u1 u2} (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_3 D _inst_4) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u1 u2} (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_3 D _inst_4) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u1 u2} (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_3 D _inst_4) (CategoryTheory.Functor.category.{u1, u1, u2, u2} C _inst_3 D _inst_4))) H I) (c : C), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} (Sum.{u2, u2} B D) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Sum.{u2, u2} B D) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Sum.{u2, u2} B D) (CategoryTheory.sum.{u1, u2} B _inst_2 D _inst_4))) (CategoryTheory.Functor.obj.{u1, u1, u2, u2} (Sum.{u2, u2} A C) (CategoryTheory.sum.{u1, u2} A _inst_1 C _inst_3) (Sum.{u2, u2} B D) (CategoryTheory.sum.{u1, u2} B _inst_2 D _inst_4) (CategoryTheory.Functor.sum.{u1, u2} A _inst_1 B _inst_2 C _inst_3 D _inst_4 F H) (Sum.inr.{u2, u2} A C c)) (CategoryTheory.Functor.obj.{u1, u1, u2, u2} (Sum.{u2, u2} A C) (CategoryTheory.sum.{u1, u2} A _inst_1 C _inst_3) (Sum.{u2, u2} B D) (CategoryTheory.sum.{u1, u2} B _inst_2 D _inst_4) (CategoryTheory.Functor.sum.{u1, u2} A _inst_1 B _inst_2 C _inst_3 D _inst_4 G I) (Sum.inr.{u2, u2} A C c))) (CategoryTheory.NatTrans.app.{u1, u1, u2, u2} (Sum.{u2, u2} A C) (CategoryTheory.sum.{u1, u2} A _inst_1 C _inst_3) (Sum.{u2, u2} B D) (CategoryTheory.sum.{u1, u2} B _inst_2 D _inst_4) (CategoryTheory.Functor.sum.{u1, u2} A _inst_1 B _inst_2 C _inst_3 D _inst_4 F H) (CategoryTheory.Functor.sum.{u1, u2} A _inst_1 B _inst_2 C _inst_3 D _inst_4 G I) (CategoryTheory.NatTrans.sum.{u1, u2} A _inst_1 B _inst_2 C _inst_3 D _inst_4 F G H I α β) (Sum.inr.{u2, u2} A C c)) (CategoryTheory.NatTrans.app.{u1, u1, u2, u2} C _inst_3 D _inst_4 H I β c)
but is expected to have type
  forall {A : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} A] {B : Type.{u2}} [_inst_2 : CategoryTheory.Category.{u1, u2} B] {C : Type.{u2}} [_inst_3 : CategoryTheory.Category.{u1, u2} C] {D : Type.{u2}} [_inst_4 : CategoryTheory.Category.{u1, u2} D] {F : CategoryTheory.Functor.{u1, u1, u2, u2} A _inst_1 B _inst_2} {G : CategoryTheory.Functor.{u1, u1, u2, u2} A _inst_1 B _inst_2} {H : CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_3 D _inst_4} {I : CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_3 D _inst_4} (α : Quiver.Hom.{max (succ u2) (succ u1), max u2 u1} (CategoryTheory.Functor.{u1, u1, u2, u2} A _inst_1 B _inst_2) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 u1} (CategoryTheory.Functor.{u1, u1, u2, u2} A _inst_1 B _inst_2) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 u1} (CategoryTheory.Functor.{u1, u1, u2, u2} A _inst_1 B _inst_2) (CategoryTheory.Functor.category.{u1, u1, u2, u2} A _inst_1 B _inst_2))) F G) (β : Quiver.Hom.{max (succ u2) (succ u1), max u2 u1} (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_3 D _inst_4) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 u1} (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_3 D _inst_4) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 u1} (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_3 D _inst_4) (CategoryTheory.Functor.category.{u1, u1, u2, u2} C _inst_3 D _inst_4))) H I) (c : C), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} (Sum.{u2, u2} B D) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Sum.{u2, u2} B D) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Sum.{u2, u2} B D) (CategoryTheory.sum.{u1, u2} B _inst_2 D _inst_4))) (Prefunctor.obj.{succ u1, succ u1, u2, u2} (Sum.{u2, u2} A C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Sum.{u2, u2} A C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Sum.{u2, u2} A C) (CategoryTheory.sum.{u1, u2} A _inst_1 C _inst_3))) (Sum.{u2, u2} B D) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Sum.{u2, u2} B D) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Sum.{u2, u2} B D) (CategoryTheory.sum.{u1, u2} B _inst_2 D _inst_4))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} (Sum.{u2, u2} A C) (CategoryTheory.sum.{u1, u2} A _inst_1 C _inst_3) (Sum.{u2, u2} B D) (CategoryTheory.sum.{u1, u2} B _inst_2 D _inst_4) (CategoryTheory.Functor.sum.{u1, u2} A _inst_1 B _inst_2 C _inst_3 D _inst_4 F H)) (Sum.inr.{u2, u2} A C c)) (Prefunctor.obj.{succ u1, succ u1, u2, u2} (Sum.{u2, u2} A C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Sum.{u2, u2} A C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Sum.{u2, u2} A C) (CategoryTheory.sum.{u1, u2} A _inst_1 C _inst_3))) (Sum.{u2, u2} B D) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Sum.{u2, u2} B D) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Sum.{u2, u2} B D) (CategoryTheory.sum.{u1, u2} B _inst_2 D _inst_4))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} (Sum.{u2, u2} A C) (CategoryTheory.sum.{u1, u2} A _inst_1 C _inst_3) (Sum.{u2, u2} B D) (CategoryTheory.sum.{u1, u2} B _inst_2 D _inst_4) (CategoryTheory.Functor.sum.{u1, u2} A _inst_1 B _inst_2 C _inst_3 D _inst_4 G I)) (Sum.inr.{u2, u2} A C c))) (CategoryTheory.NatTrans.app.{u1, u1, u2, u2} (Sum.{u2, u2} A C) (CategoryTheory.sum.{u1, u2} A _inst_1 C _inst_3) (Sum.{u2, u2} B D) (CategoryTheory.sum.{u1, u2} B _inst_2 D _inst_4) (CategoryTheory.Functor.sum.{u1, u2} A _inst_1 B _inst_2 C _inst_3 D _inst_4 F H) (CategoryTheory.Functor.sum.{u1, u2} A _inst_1 B _inst_2 C _inst_3 D _inst_4 G I) (CategoryTheory.NatTrans.sum.{u1, u2} A _inst_1 B _inst_2 C _inst_3 D _inst_4 F G H I α β) (Sum.inr.{u2, u2} A C c)) (CategoryTheory.NatTrans.app.{u1, u1, u2, u2} C _inst_3 D _inst_4 H I β c)
Case conversion may be inaccurate. Consider using '#align category_theory.nat_trans.sum_app_inr CategoryTheory.NatTrans.sum_app_inrₓ'. -/
@[simp]
theorem sum_app_inr {F G : A ⥤ B} {H I : C ⥤ D} (α : F ⟶ G) (β : H ⟶ I) (c : C) :
    (sum α β).app (inr c) = β.app c :=
  rfl
#align category_theory.nat_trans.sum_app_inr CategoryTheory.NatTrans.sum_app_inr

end NatTrans

end CategoryTheory

