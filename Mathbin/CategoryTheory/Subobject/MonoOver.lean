/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Scott Morrison

! This file was ported from Lean 3 source module category_theory.subobject.mono_over
! leanprover-community/mathlib commit ce38d86c0b2d427ce208c3cee3159cb421d2b3c4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.Over
import Mathbin.CategoryTheory.Limits.Shapes.Images
import Mathbin.CategoryTheory.Adjunction.Reflective

/-!
# Monomorphisms over a fixed object

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

As preparation for defining `subobject X`, we set up the theory for
`mono_over X := {f : over X // mono f.hom}`.

Here `mono_over X` is a thin category (a pair of objects has at most one morphism between them),
so we can think of it as a preorder. However as it is not skeletal, it is not yet a partial order.

`subobject X` will be defined as the skeletalization of `mono_over X`.

We provide
* `def pullback [has_pullbacks C] (f : X ⟶ Y) : mono_over Y ⥤ mono_over X`
* `def map (f : X ⟶ Y) [mono f] : mono_over X ⥤ mono_over Y`
* `def «exists» [has_images C] (f : X ⟶ Y) : mono_over X ⥤ mono_over Y`
and prove their basic properties and relationships.

## Notes

This development originally appeared in Bhavik Mehta's "Topos theory for Lean" repository,
and was ported to mathlib by Scott Morrison.

-/


universe v₁ v₂ u₁ u₂

noncomputable section

namespace CategoryTheory

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] {X Y Z : C}

variable {D : Type u₂} [Category.{v₂} D]

#print CategoryTheory.MonoOver /-
/-- The category of monomorphisms into `X` as a full subcategory of the over category.
This isn't skeletal, so it's not a partial order.

Later we define `subobject X` as the quotient of this by isomorphisms.
-/
def MonoOver (X : C) :=
  FullSubcategory fun f : Over X => Mono f.Hom deriving Category
#align category_theory.mono_over CategoryTheory.MonoOver
-/

namespace MonoOver

#print CategoryTheory.MonoOver.mk' /-
/-- Construct a `mono_over X`. -/
@[simps]
def mk' {X A : C} (f : A ⟶ X) [hf : Mono f] : MonoOver X
    where
  obj := Over.mk f
  property := hf
#align category_theory.mono_over.mk' CategoryTheory.MonoOver.mk'
-/

/- warning: category_theory.mono_over.forget -> CategoryTheory.MonoOver.forget is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (X : C), CategoryTheory.Functor.{u1, u1, max u2 u1, max u2 u1} (CategoryTheory.MonoOver.{u1, u2} C _inst_1 X) (CategoryTheory.InducedCategory.category.{u1, max u2 u1, max u2 u1} (CategoryTheory.FullSubcategoryₓ.{u1, max u2 u1} (CategoryTheory.Over.{u1, u2} C _inst_1 X) (CategoryTheory.Over.category.{u2, u1} C _inst_1 X) (fun (f : CategoryTheory.Over.{u1, u2} C _inst_1 X) => CategoryTheory.Mono.{u1, u2} C _inst_1 (CategoryTheory.Functor.obj.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Comma.left.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f)) (CategoryTheory.Functor.obj.{u1, u1, u1, u2} (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) (CategoryTheory.Comma.right.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f)) (CategoryTheory.Comma.hom.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f))) (CategoryTheory.Over.{u1, u2} C _inst_1 X) (CategoryTheory.Over.category.{u2, u1} C _inst_1 X) (CategoryTheory.FullSubcategoryₓ.obj.{u1, max u2 u1} (CategoryTheory.Over.{u1, u2} C _inst_1 X) (CategoryTheory.Over.category.{u2, u1} C _inst_1 X) (fun (f : CategoryTheory.Over.{u1, u2} C _inst_1 X) => CategoryTheory.Mono.{u1, u2} C _inst_1 (CategoryTheory.Functor.obj.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Comma.left.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f)) (CategoryTheory.Functor.obj.{u1, u1, u1, u2} (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) (CategoryTheory.Comma.right.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f)) (CategoryTheory.Comma.hom.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f)))) (CategoryTheory.Over.{u1, u2} C _inst_1 X) (CategoryTheory.Over.category.{u2, u1} C _inst_1 X)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (X : C), CategoryTheory.Functor.{u1, u1, max u2 u1, max u2 u1} (CategoryTheory.MonoOver.{u1, u2} C _inst_1 X) (CategoryTheory.instCategoryMonoOver.{u1, u2} C _inst_1 X) (CategoryTheory.Over.{u1, u2} C _inst_1 X) (CategoryTheory.instCategoryOver.{u1, u2} C _inst_1 X)
Case conversion may be inaccurate. Consider using '#align category_theory.mono_over.forget CategoryTheory.MonoOver.forgetₓ'. -/
/-- The inclusion from monomorphisms over X to morphisms over X. -/
def forget (X : C) : MonoOver X ⥤ Over X :=
  fullSubcategoryInclusion _
#align category_theory.mono_over.forget CategoryTheory.MonoOver.forget

instance : Coe (MonoOver X) C where coe Y := Y.obj.left

/- warning: category_theory.mono_over.forget_obj_left -> CategoryTheory.MonoOver.forget_obj_left is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.mono_over.forget_obj_left CategoryTheory.MonoOver.forget_obj_leftₓ'. -/
@[simp]
theorem forget_obj_left {f} : ((forget X).obj f).left = (f : C) :=
  rfl
#align category_theory.mono_over.forget_obj_left CategoryTheory.MonoOver.forget_obj_left

/- warning: category_theory.mono_over.mk'_coe' -> CategoryTheory.MonoOver.mk'_coe' is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {A : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) A X) [hf : CategoryTheory.Mono.{u1, u2} C _inst_1 A X f], Eq.{succ u2} C ((fun (a : Type.{max u2 u1}) (b : Type.{u2}) [self : HasLiftT.{succ (max u2 u1), succ u2} a b] => self.0) (CategoryTheory.MonoOver.{u1, u2} C _inst_1 X) C (HasLiftT.mk.{succ (max u2 u1), succ u2} (CategoryTheory.MonoOver.{u1, u2} C _inst_1 X) C (CoeTCₓ.coe.{succ (max u2 u1), succ u2} (CategoryTheory.MonoOver.{u1, u2} C _inst_1 X) C (coeBase.{succ (max u2 u1), succ u2} (CategoryTheory.MonoOver.{u1, u2} C _inst_1 X) C (CategoryTheory.MonoOver.hasCoe.{u1, u2} C _inst_1 X)))) (CategoryTheory.MonoOver.mk'.{u1, u2} C _inst_1 X A f hf)) A
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {A : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) A X) [hf : CategoryTheory.Mono.{u1, u2} C _inst_1 A X f], Eq.{succ u2} C (CategoryTheory.Comma.left.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) (CategoryTheory.FullSubcategory.obj.{max u2 u1} (CategoryTheory.Over.{u1, u2} C _inst_1 X) (fun (f : CategoryTheory.Over.{u1, u2} C _inst_1 X) => CategoryTheory.Mono.{u1, u2} C _inst_1 (Prefunctor.obj.{succ u1, succ u1, u2, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1)) (CategoryTheory.Comma.left.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f)) (Prefunctor.obj.{succ u1, succ u1, u1, u2} (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.Category.toCategoryStruct.{u1, u1} (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u1, u2} (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X)) (CategoryTheory.Comma.right.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f)) (CategoryTheory.Comma.hom.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f)) (CategoryTheory.MonoOver.mk'.{u1, u2} C _inst_1 X A f hf))) A
Case conversion may be inaccurate. Consider using '#align category_theory.mono_over.mk'_coe' CategoryTheory.MonoOver.mk'_coe'ₓ'. -/
@[simp]
theorem mk'_coe' {X A : C} (f : A ⟶ X) [hf : Mono f] : (mk' f : C) = A :=
  rfl
#align category_theory.mono_over.mk'_coe' CategoryTheory.MonoOver.mk'_coe'

/- warning: category_theory.mono_over.arrow -> CategoryTheory.MonoOver.arrow is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} (f : CategoryTheory.MonoOver.{u1, u2} C _inst_1 X), Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) ((fun (a : Type.{max u2 u1}) (b : Type.{u2}) [self : HasLiftT.{succ (max u2 u1), succ u2} a b] => self.0) (CategoryTheory.MonoOver.{u1, u2} C _inst_1 X) C (HasLiftT.mk.{succ (max u2 u1), succ u2} (CategoryTheory.MonoOver.{u1, u2} C _inst_1 X) C (CoeTCₓ.coe.{succ (max u2 u1), succ u2} (CategoryTheory.MonoOver.{u1, u2} C _inst_1 X) C (coeBase.{succ (max u2 u1), succ u2} (CategoryTheory.MonoOver.{u1, u2} C _inst_1 X) C (CategoryTheory.MonoOver.hasCoe.{u1, u2} C _inst_1 X)))) f) X
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} (f : CategoryTheory.MonoOver.{u1, u2} C _inst_1 X), Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Comma.left.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) (CategoryTheory.FullSubcategory.obj.{max u2 u1} (CategoryTheory.Over.{u1, u2} C _inst_1 X) (fun (f : CategoryTheory.Over.{u1, u2} C _inst_1 X) => CategoryTheory.Mono.{u1, u2} C _inst_1 (Prefunctor.obj.{succ u1, succ u1, u2, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1)) (CategoryTheory.Comma.left.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f)) (Prefunctor.obj.{succ u1, succ u1, u1, u2} (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.Category.toCategoryStruct.{u1, u1} (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u1, u2} (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X)) (CategoryTheory.Comma.right.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f)) (CategoryTheory.Comma.hom.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f)) f)) X
Case conversion may be inaccurate. Consider using '#align category_theory.mono_over.arrow CategoryTheory.MonoOver.arrowₓ'. -/
/-- Convenience notation for the underlying arrow of a monomorphism over X. -/
abbrev arrow (f : MonoOver X) : (f : C) ⟶ X :=
  ((forget X).obj f).Hom
#align category_theory.mono_over.arrow CategoryTheory.MonoOver.arrow

/- warning: category_theory.mono_over.mk'_arrow -> CategoryTheory.MonoOver.mk'_arrow is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {A : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) A X) [hf : CategoryTheory.Mono.{u1, u2} C _inst_1 A X f], Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) ((fun (a : Type.{max u2 u1}) (b : Type.{u2}) [self : HasLiftT.{succ (max u2 u1), succ u2} a b] => self.0) (CategoryTheory.MonoOver.{u1, u2} C _inst_1 X) C (HasLiftT.mk.{succ (max u2 u1), succ u2} (CategoryTheory.MonoOver.{u1, u2} C _inst_1 X) C (CoeTCₓ.coe.{succ (max u2 u1), succ u2} (CategoryTheory.MonoOver.{u1, u2} C _inst_1 X) C (coeBase.{succ (max u2 u1), succ u2} (CategoryTheory.MonoOver.{u1, u2} C _inst_1 X) C (CategoryTheory.MonoOver.hasCoe.{u1, u2} C _inst_1 X)))) (CategoryTheory.MonoOver.mk'.{u1, u2} C _inst_1 X A f hf)) X) (CategoryTheory.MonoOver.arrow.{u1, u2} C _inst_1 X (CategoryTheory.MonoOver.mk'.{u1, u2} C _inst_1 X A f hf)) f
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {A : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) A X) [hf : CategoryTheory.Mono.{u1, u2} C _inst_1 A X f], Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Comma.left.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) (CategoryTheory.FullSubcategory.obj.{max u2 u1} (CategoryTheory.Over.{u1, u2} C _inst_1 X) (fun (f : CategoryTheory.Over.{u1, u2} C _inst_1 X) => CategoryTheory.Mono.{u1, u2} C _inst_1 (Prefunctor.obj.{succ u1, succ u1, u2, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1)) (CategoryTheory.Comma.left.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f)) (Prefunctor.obj.{succ u1, succ u1, u1, u2} (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.Category.toCategoryStruct.{u1, u1} (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u1, u2} (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X)) (CategoryTheory.Comma.right.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f)) (CategoryTheory.Comma.hom.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f)) (CategoryTheory.MonoOver.mk'.{u1, u2} C _inst_1 X A f hf))) X) (CategoryTheory.MonoOver.arrow.{u1, u2} C _inst_1 X (CategoryTheory.MonoOver.mk'.{u1, u2} C _inst_1 X A f hf)) f
Case conversion may be inaccurate. Consider using '#align category_theory.mono_over.mk'_arrow CategoryTheory.MonoOver.mk'_arrowₓ'. -/
@[simp]
theorem mk'_arrow {X A : C} (f : A ⟶ X) [hf : Mono f] : (mk' f).arrow = f :=
  rfl
#align category_theory.mono_over.mk'_arrow CategoryTheory.MonoOver.mk'_arrow

/- warning: category_theory.mono_over.forget_obj_hom -> CategoryTheory.MonoOver.forget_obj_hom is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.mono_over.forget_obj_hom CategoryTheory.MonoOver.forget_obj_homₓ'. -/
@[simp]
theorem forget_obj_hom {f} : ((forget X).obj f).Hom = f.arrow :=
  rfl
#align category_theory.mono_over.forget_obj_hom CategoryTheory.MonoOver.forget_obj_hom

instance : Full (forget X) :=
  FullSubcategory.full _

instance : Faithful (forget X) :=
  FullSubcategory.faithful _

/- warning: category_theory.mono_over.mono -> CategoryTheory.MonoOver.mono is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} (f : CategoryTheory.MonoOver.{u1, u2} C _inst_1 X), CategoryTheory.Mono.{u1, u2} C _inst_1 ((fun (a : Type.{max u2 u1}) (b : Type.{u2}) [self : HasLiftT.{succ (max u2 u1), succ u2} a b] => self.0) (CategoryTheory.MonoOver.{u1, u2} C _inst_1 X) C (HasLiftT.mk.{succ (max u2 u1), succ u2} (CategoryTheory.MonoOver.{u1, u2} C _inst_1 X) C (CoeTCₓ.coe.{succ (max u2 u1), succ u2} (CategoryTheory.MonoOver.{u1, u2} C _inst_1 X) C (coeBase.{succ (max u2 u1), succ u2} (CategoryTheory.MonoOver.{u1, u2} C _inst_1 X) C (CategoryTheory.MonoOver.hasCoe.{u1, u2} C _inst_1 X)))) f) X (CategoryTheory.MonoOver.arrow.{u1, u2} C _inst_1 X f)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} (f : CategoryTheory.MonoOver.{u1, u2} C _inst_1 X), CategoryTheory.Mono.{u1, u2} C _inst_1 (CategoryTheory.Comma.left.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) (CategoryTheory.FullSubcategory.obj.{max u2 u1} (CategoryTheory.Over.{u1, u2} C _inst_1 X) (fun (f : CategoryTheory.Over.{u1, u2} C _inst_1 X) => CategoryTheory.Mono.{u1, u2} C _inst_1 (Prefunctor.obj.{succ u1, succ u1, u2, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1)) (CategoryTheory.Comma.left.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f)) (Prefunctor.obj.{succ u1, succ u1, u1, u2} (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.Category.toCategoryStruct.{u1, u1} (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u1, u2} (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X)) (CategoryTheory.Comma.right.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f)) (CategoryTheory.Comma.hom.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f)) f)) X (CategoryTheory.MonoOver.arrow.{u1, u2} C _inst_1 X f)
Case conversion may be inaccurate. Consider using '#align category_theory.mono_over.mono CategoryTheory.MonoOver.monoₓ'. -/
instance mono (f : MonoOver X) : Mono f.arrow :=
  f.property
#align category_theory.mono_over.mono CategoryTheory.MonoOver.mono

#print CategoryTheory.MonoOver.isThin /-
/-- The category of monomorphisms over X is a thin category,
which makes defining its skeleton easy. -/
instance isThin {X : C} : Quiver.IsThin (MonoOver X) := fun f g =>
  ⟨by
    intro h₁ h₂
    ext1
    erw [← cancel_mono g.arrow, over.w h₁, over.w h₂]⟩
#align category_theory.mono_over.is_thin CategoryTheory.MonoOver.isThin
-/

#print CategoryTheory.MonoOver.w /-
@[reassoc]
theorem w {f g : MonoOver X} (k : f ⟶ g) : k.left ≫ g.arrow = f.arrow :=
  Over.w _
#align category_theory.mono_over.w CategoryTheory.MonoOver.w
-/

#print CategoryTheory.MonoOver.homMk /-
/-- Convenience constructor for a morphism in monomorphisms over `X`. -/
abbrev homMk {f g : MonoOver X} (h : f.obj.left ⟶ g.obj.left) (w : h ≫ g.arrow = f.arrow) : f ⟶ g :=
  Over.homMk h w
#align category_theory.mono_over.hom_mk CategoryTheory.MonoOver.homMk
-/

#print CategoryTheory.MonoOver.isoMk /-
/-- Convenience constructor for an isomorphism in monomorphisms over `X`. -/
@[simps]
def isoMk {f g : MonoOver X} (h : f.obj.left ≅ g.obj.left) (w : h.Hom ≫ g.arrow = f.arrow) : f ≅ g
    where
  Hom := homMk h.Hom w
  inv := homMk h.inv (by rw [h.inv_comp_eq, w])
#align category_theory.mono_over.iso_mk CategoryTheory.MonoOver.isoMk
-/

/- warning: category_theory.mono_over.mk'_arrow_iso -> CategoryTheory.MonoOver.mk'ArrowIso is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} (f : CategoryTheory.MonoOver.{u1, u2} C _inst_1 X), CategoryTheory.Iso.{u1, max u2 u1} (CategoryTheory.MonoOver.{u1, u2} C _inst_1 X) (CategoryTheory.MonoOver.category.{u2, u1} C _inst_1 X) (CategoryTheory.MonoOver.mk'.{u1, u2} C _inst_1 X ((fun (a : Type.{max u2 u1}) (b : Type.{u2}) [self : HasLiftT.{succ (max u2 u1), succ u2} a b] => self.0) (CategoryTheory.MonoOver.{u1, u2} C _inst_1 X) C (HasLiftT.mk.{succ (max u2 u1), succ u2} (CategoryTheory.MonoOver.{u1, u2} C _inst_1 X) C (CoeTCₓ.coe.{succ (max u2 u1), succ u2} (CategoryTheory.MonoOver.{u1, u2} C _inst_1 X) C (coeBase.{succ (max u2 u1), succ u2} (CategoryTheory.MonoOver.{u1, u2} C _inst_1 X) C (CategoryTheory.MonoOver.hasCoe.{u1, u2} C _inst_1 X)))) f) (CategoryTheory.MonoOver.arrow.{u1, u2} C _inst_1 X f) (CategoryTheory.MonoOver.mono.{u1, u2} C _inst_1 X f)) f
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} (f : CategoryTheory.MonoOver.{u1, u2} C _inst_1 X), CategoryTheory.Iso.{u1, max u2 u1} (CategoryTheory.MonoOver.{u1, u2} C _inst_1 X) (CategoryTheory.instCategoryMonoOver.{u1, u2} C _inst_1 X) (CategoryTheory.MonoOver.mk'.{u1, u2} C _inst_1 X (CategoryTheory.Comma.left.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) (CategoryTheory.FullSubcategory.obj.{max u2 u1} (CategoryTheory.Over.{u1, u2} C _inst_1 X) (fun (f : CategoryTheory.Over.{u1, u2} C _inst_1 X) => CategoryTheory.Mono.{u1, u2} C _inst_1 (Prefunctor.obj.{succ u1, succ u1, u2, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1)) (CategoryTheory.Comma.left.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f)) (Prefunctor.obj.{succ u1, succ u1, u1, u2} (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.Category.toCategoryStruct.{u1, u1} (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u1, u2} (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X)) (CategoryTheory.Comma.right.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f)) (CategoryTheory.Comma.hom.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f)) f)) (CategoryTheory.MonoOver.arrow.{u1, u2} C _inst_1 X f) (CategoryTheory.MonoOver.mono.{u1, u2} C _inst_1 X f)) f
Case conversion may be inaccurate. Consider using '#align category_theory.mono_over.mk'_arrow_iso CategoryTheory.MonoOver.mk'ArrowIsoₓ'. -/
/-- If `f : mono_over X`, then `mk' f.arrow` is of course just `f`, but not definitionally, so we
    package it as an isomorphism. -/
@[simp]
def mk'ArrowIso {X : C} (f : MonoOver X) : mk' f.arrow ≅ f :=
  isoMk (Iso.refl _) (by simp)
#align category_theory.mono_over.mk'_arrow_iso CategoryTheory.MonoOver.mk'ArrowIso

/- warning: category_theory.mono_over.lift -> CategoryTheory.MonoOver.lift is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.mono_over.lift CategoryTheory.MonoOver.liftₓ'. -/
/-- Lift a functor between over categories to a functor between `mono_over` categories,
given suitable evidence that morphisms are taken to monomorphisms.
-/
@[simps]
def lift {Y : D} (F : Over Y ⥤ Over X)
    (h : ∀ f : MonoOver Y, Mono (F.obj ((MonoOver.forget Y).obj f)).Hom) : MonoOver Y ⥤ MonoOver X
    where
  obj f := ⟨_, h f⟩
  map _ _ k := (MonoOver.forget X).preimage ((MonoOver.forget Y ⋙ F).map k)
#align category_theory.mono_over.lift CategoryTheory.MonoOver.lift

/- warning: category_theory.mono_over.lift_iso -> CategoryTheory.MonoOver.liftIso is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.mono_over.lift_iso CategoryTheory.MonoOver.liftIsoₓ'. -/
/-- Isomorphic functors `over Y ⥤ over X` lift to isomorphic functors `mono_over Y ⥤ mono_over X`.
-/
def liftIso {Y : D} {F₁ F₂ : Over Y ⥤ Over X} (h₁ h₂) (i : F₁ ≅ F₂) : lift F₁ h₁ ≅ lift F₂ h₂ :=
  fullyFaithfulCancelRight (MonoOver.forget X) (isoWhiskerLeft (MonoOver.forget Y) i)
#align category_theory.mono_over.lift_iso CategoryTheory.MonoOver.liftIso

/- warning: category_theory.mono_over.lift_comp -> CategoryTheory.MonoOver.liftComp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.mono_over.lift_comp CategoryTheory.MonoOver.liftCompₓ'. -/
/-- `mono_over.lift` commutes with composition of functors. -/
def liftComp {X Z : C} {Y : D} (F : Over X ⥤ Over Y) (G : Over Y ⥤ Over Z) (h₁ h₂) :
    lift F h₁ ⋙ lift G h₂ ≅ lift (F ⋙ G) fun f => h₂ ⟨_, h₁ f⟩ :=
  fullyFaithfulCancelRight (MonoOver.forget _) (Iso.refl _)
#align category_theory.mono_over.lift_comp CategoryTheory.MonoOver.liftComp

#print CategoryTheory.MonoOver.liftId /-
/-- `mono_over.lift` preserves the identity functor. -/
def liftId : (lift (𝟭 (Over X)) fun f => f.2) ≅ 𝟭 _ :=
  fullyFaithfulCancelRight (MonoOver.forget _) (Iso.refl _)
#align category_theory.mono_over.lift_id CategoryTheory.MonoOver.liftId
-/

/- warning: category_theory.mono_over.lift_comm -> CategoryTheory.MonoOver.lift_comm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.mono_over.lift_comm CategoryTheory.MonoOver.lift_commₓ'. -/
@[simp]
theorem lift_comm (F : Over Y ⥤ Over X)
    (h : ∀ f : MonoOver Y, Mono (F.obj ((MonoOver.forget Y).obj f)).Hom) :
    lift F h ⋙ MonoOver.forget X = MonoOver.forget Y ⋙ F :=
  rfl
#align category_theory.mono_over.lift_comm CategoryTheory.MonoOver.lift_comm

/- warning: category_theory.mono_over.lift_obj_arrow -> CategoryTheory.MonoOver.lift_obj_arrow is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.mono_over.lift_obj_arrow CategoryTheory.MonoOver.lift_obj_arrowₓ'. -/
@[simp]
theorem lift_obj_arrow {Y : D} (F : Over Y ⥤ Over X)
    (h : ∀ f : MonoOver Y, Mono (F.obj ((MonoOver.forget Y).obj f)).Hom) (f : MonoOver Y) :
    ((lift F h).obj f).arrow = (F.obj ((forget Y).obj f)).Hom :=
  rfl
#align category_theory.mono_over.lift_obj_arrow CategoryTheory.MonoOver.lift_obj_arrow

/- warning: category_theory.mono_over.slice -> CategoryTheory.MonoOver.slice is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.mono_over.slice CategoryTheory.MonoOver.sliceₓ'. -/
/-- Monomorphisms over an object `f : over A` in an over category
are equivalent to monomorphisms over the source of `f`.
-/
def slice {A : C} {f : Over A} (h₁ h₂) : MonoOver f ≌ MonoOver f.left
    where
  Functor := MonoOver.lift f.iteratedSliceEquiv.Functor h₁
  inverse := MonoOver.lift f.iteratedSliceEquiv.inverse h₂
  unitIso :=
    MonoOver.liftId.symm ≪≫
      MonoOver.liftIso _ _ f.iteratedSliceEquiv.unitIso ≪≫ (MonoOver.liftComp _ _ _ _).symm
  counitIso :=
    MonoOver.liftComp _ _ _ _ ≪≫
      MonoOver.liftIso _ _ f.iteratedSliceEquiv.counitIso ≪≫ MonoOver.liftId
#align category_theory.mono_over.slice CategoryTheory.MonoOver.slice

section Pullback

variable [HasPullbacks C]

#print CategoryTheory.MonoOver.pullback /-
/-- When `C` has pullbacks, a morphism `f : X ⟶ Y` induces a functor `mono_over Y ⥤ mono_over X`,
by pulling back a monomorphism along `f`. -/
def pullback (f : X ⟶ Y) : MonoOver Y ⥤ MonoOver X :=
  MonoOver.lift (Over.pullback f)
    (by
      intro g
      apply @pullback.snd_of_mono _ _ _ _ _ _ _ _ _
      change mono g.arrow
      infer_instance)
#align category_theory.mono_over.pullback CategoryTheory.MonoOver.pullback
-/

#print CategoryTheory.MonoOver.pullbackComp /-
/-- pullback commutes with composition (up to a natural isomorphism) -/
def pullbackComp (f : X ⟶ Y) (g : Y ⟶ Z) : pullback (f ≫ g) ≅ pullback g ⋙ pullback f :=
  liftIso _ _ (Over.pullbackComp _ _) ≪≫ (liftComp _ _ _ _).symm
#align category_theory.mono_over.pullback_comp CategoryTheory.MonoOver.pullbackComp
-/

#print CategoryTheory.MonoOver.pullbackId /-
/-- pullback preserves the identity (up to a natural isomorphism) -/
def pullbackId : pullback (𝟙 X) ≅ 𝟭 _ :=
  liftIso _ _ Over.pullbackId ≪≫ liftId
#align category_theory.mono_over.pullback_id CategoryTheory.MonoOver.pullbackId
-/

/- warning: category_theory.mono_over.pullback_obj_left -> CategoryTheory.MonoOver.pullback_obj_left is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.mono_over.pullback_obj_left CategoryTheory.MonoOver.pullback_obj_leftₓ'. -/
@[simp]
theorem pullback_obj_left (f : X ⟶ Y) (g : MonoOver Y) :
    ((pullback f).obj g : C) = Limits.pullback g.arrow f :=
  rfl
#align category_theory.mono_over.pullback_obj_left CategoryTheory.MonoOver.pullback_obj_left

/- warning: category_theory.mono_over.pullback_obj_arrow -> CategoryTheory.MonoOver.pullback_obj_arrow is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.mono_over.pullback_obj_arrow CategoryTheory.MonoOver.pullback_obj_arrowₓ'. -/
@[simp]
theorem pullback_obj_arrow (f : X ⟶ Y) (g : MonoOver Y) :
    ((pullback f).obj g).arrow = pullback.snd :=
  rfl
#align category_theory.mono_over.pullback_obj_arrow CategoryTheory.MonoOver.pullback_obj_arrow

end Pullback

section Map

attribute [instance] mono_comp

#print CategoryTheory.MonoOver.map /-
/-- We can map monomorphisms over `X` to monomorphisms over `Y`
by post-composition with a monomorphism `f : X ⟶ Y`.
-/
def map (f : X ⟶ Y) [Mono f] : MonoOver X ⥤ MonoOver Y :=
  lift (Over.map f) fun g => by apply mono_comp g.arrow f
#align category_theory.mono_over.map CategoryTheory.MonoOver.map
-/

#print CategoryTheory.MonoOver.mapComp /-
/-- `mono_over.map` commutes with composition (up to a natural isomorphism). -/
def mapComp (f : X ⟶ Y) (g : Y ⟶ Z) [Mono f] [Mono g] : map (f ≫ g) ≅ map f ⋙ map g :=
  liftIso _ _ (Over.mapComp _ _) ≪≫ (liftComp _ _ _ _).symm
#align category_theory.mono_over.map_comp CategoryTheory.MonoOver.mapComp
-/

#print CategoryTheory.MonoOver.mapId /-
/-- `mono_over.map` preserves the identity (up to a natural isomorphism). -/
def mapId : map (𝟙 X) ≅ 𝟭 _ :=
  liftIso _ _ Over.mapId ≪≫ liftId
#align category_theory.mono_over.map_id CategoryTheory.MonoOver.mapId
-/

/- warning: category_theory.mono_over.map_obj_left -> CategoryTheory.MonoOver.map_obj_left is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y) [_inst_3 : CategoryTheory.Mono.{u1, u2} C _inst_1 X Y f] (g : CategoryTheory.MonoOver.{u1, u2} C _inst_1 X), Eq.{succ u2} C ((fun (a : Type.{max u2 u1}) (b : Type.{u2}) [self : HasLiftT.{succ (max u2 u1), succ u2} a b] => self.0) (CategoryTheory.MonoOver.{u1, u2} C _inst_1 Y) C (HasLiftT.mk.{succ (max u2 u1), succ u2} (CategoryTheory.MonoOver.{u1, u2} C _inst_1 Y) C (CoeTCₓ.coe.{succ (max u2 u1), succ u2} (CategoryTheory.MonoOver.{u1, u2} C _inst_1 Y) C (coeBase.{succ (max u2 u1), succ u2} (CategoryTheory.MonoOver.{u1, u2} C _inst_1 Y) C (CategoryTheory.MonoOver.hasCoe.{u1, u2} C _inst_1 Y)))) (CategoryTheory.Functor.obj.{u1, u1, max u2 u1, max u2 u1} (CategoryTheory.MonoOver.{u1, u2} C _inst_1 X) (CategoryTheory.MonoOver.category.{u2, u1} C _inst_1 X) (CategoryTheory.MonoOver.{u1, u2} C _inst_1 Y) (CategoryTheory.MonoOver.category.{u2, u1} C _inst_1 Y) (CategoryTheory.MonoOver.map.{u1, u2} C _inst_1 X Y f _inst_3) g)) (CategoryTheory.Comma.left.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) (CategoryTheory.FullSubcategoryₓ.obj.{u1, max u2 u1} (CategoryTheory.Over.{u1, u2} C _inst_1 X) (CategoryTheory.Over.category.{u2, u1} C _inst_1 X) (fun (f : CategoryTheory.Over.{u1, u2} C _inst_1 X) => CategoryTheory.Mono.{u1, u2} C _inst_1 (CategoryTheory.Functor.obj.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Comma.left.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f)) (CategoryTheory.Functor.obj.{u1, u1, u1, u2} (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) (CategoryTheory.Comma.right.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f)) (CategoryTheory.Comma.hom.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f)) g))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y) [_inst_3 : CategoryTheory.Mono.{u1, u2} C _inst_1 X Y f] (g : CategoryTheory.MonoOver.{u1, u2} C _inst_1 X), Eq.{succ u2} C (CategoryTheory.Comma.left.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 Y) (CategoryTheory.FullSubcategory.obj.{max u2 u1} (CategoryTheory.Over.{u1, u2} C _inst_1 Y) (fun (f : CategoryTheory.Over.{u1, u2} C _inst_1 Y) => CategoryTheory.Mono.{u1, u2} C _inst_1 (Prefunctor.obj.{succ u1, succ u1, u2, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1)) (CategoryTheory.Comma.left.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 Y) f)) (Prefunctor.obj.{succ u1, succ u1, u1, u2} (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.Category.toCategoryStruct.{u1, u1} (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u1, u2} (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 Y)) (CategoryTheory.Comma.right.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 Y) f)) (CategoryTheory.Comma.hom.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 Y) f)) (Prefunctor.obj.{succ u1, succ u1, max u2 u1, max u2 u1} (CategoryTheory.MonoOver.{u1, u2} C _inst_1 X) (CategoryTheory.CategoryStruct.toQuiver.{u1, max u2 u1} (CategoryTheory.MonoOver.{u1, u2} C _inst_1 X) (CategoryTheory.Category.toCategoryStruct.{u1, max u2 u1} (CategoryTheory.MonoOver.{u1, u2} C _inst_1 X) (CategoryTheory.instCategoryMonoOver.{u1, u2} C _inst_1 X))) (CategoryTheory.MonoOver.{u1, u2} C _inst_1 Y) (CategoryTheory.CategoryStruct.toQuiver.{u1, max u2 u1} (CategoryTheory.MonoOver.{u1, u2} C _inst_1 Y) (CategoryTheory.Category.toCategoryStruct.{u1, max u2 u1} (CategoryTheory.MonoOver.{u1, u2} C _inst_1 Y) (CategoryTheory.instCategoryMonoOver.{u1, u2} C _inst_1 Y))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, max u2 u1, max u2 u1} (CategoryTheory.MonoOver.{u1, u2} C _inst_1 X) (CategoryTheory.instCategoryMonoOver.{u1, u2} C _inst_1 X) (CategoryTheory.MonoOver.{u1, u2} C _inst_1 Y) (CategoryTheory.instCategoryMonoOver.{u1, u2} C _inst_1 Y) (CategoryTheory.MonoOver.map.{u1, u2} C _inst_1 X Y f _inst_3)) g))) (CategoryTheory.Comma.left.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) (CategoryTheory.FullSubcategory.obj.{max u2 u1} (CategoryTheory.Over.{u1, u2} C _inst_1 X) (fun (f : CategoryTheory.Over.{u1, u2} C _inst_1 X) => CategoryTheory.Mono.{u1, u2} C _inst_1 (Prefunctor.obj.{succ u1, succ u1, u2, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1)) (CategoryTheory.Comma.left.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f)) (Prefunctor.obj.{succ u1, succ u1, u1, u2} (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.Category.toCategoryStruct.{u1, u1} (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u1, u2} (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X)) (CategoryTheory.Comma.right.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f)) (CategoryTheory.Comma.hom.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f)) g))
Case conversion may be inaccurate. Consider using '#align category_theory.mono_over.map_obj_left CategoryTheory.MonoOver.map_obj_leftₓ'. -/
@[simp]
theorem map_obj_left (f : X ⟶ Y) [Mono f] (g : MonoOver X) : ((map f).obj g : C) = g.obj.left :=
  rfl
#align category_theory.mono_over.map_obj_left CategoryTheory.MonoOver.map_obj_left

/- warning: category_theory.mono_over.map_obj_arrow -> CategoryTheory.MonoOver.map_obj_arrow is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.mono_over.map_obj_arrow CategoryTheory.MonoOver.map_obj_arrowₓ'. -/
@[simp]
theorem map_obj_arrow (f : X ⟶ Y) [Mono f] (g : MonoOver X) : ((map f).obj g).arrow = g.arrow ≫ f :=
  rfl
#align category_theory.mono_over.map_obj_arrow CategoryTheory.MonoOver.map_obj_arrow

#print CategoryTheory.MonoOver.fullMap /-
instance fullMap (f : X ⟶ Y) [Mono f] : Full (map f)
    where preimage g h e := by
    refine' hom_mk e.left _
    rw [← cancel_mono f, assoc]
    apply w e
#align category_theory.mono_over.full_map CategoryTheory.MonoOver.fullMap
-/

#print CategoryTheory.MonoOver.faithful_map /-
instance faithful_map (f : X ⟶ Y) [Mono f] : Faithful (map f) where
#align category_theory.mono_over.faithful_map CategoryTheory.MonoOver.faithful_map
-/

/- warning: category_theory.mono_over.map_iso -> CategoryTheory.MonoOver.mapIso is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {A : C} {B : C}, (CategoryTheory.Iso.{u1, u2} C _inst_1 A B) -> (CategoryTheory.Equivalence.{u1, u1, max u2 u1, max u2 u1} (CategoryTheory.MonoOver.{u1, u2} C _inst_1 A) (CategoryTheory.MonoOver.category.{u2, u1} C _inst_1 A) (CategoryTheory.MonoOver.{u1, u2} C _inst_1 B) (CategoryTheory.MonoOver.category.{u2, u1} C _inst_1 B))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {A : C} {B : C}, (CategoryTheory.Iso.{u1, u2} C _inst_1 A B) -> (CategoryTheory.Equivalence.{u1, u1, max u2 u1, max u2 u1} (CategoryTheory.MonoOver.{u1, u2} C _inst_1 A) (CategoryTheory.MonoOver.{u1, u2} C _inst_1 B) (CategoryTheory.instCategoryMonoOver.{u1, u2} C _inst_1 A) (CategoryTheory.instCategoryMonoOver.{u1, u2} C _inst_1 B))
Case conversion may be inaccurate. Consider using '#align category_theory.mono_over.map_iso CategoryTheory.MonoOver.mapIsoₓ'. -/
/-- Isomorphic objects have equivalent `mono_over` categories.
-/
@[simps]
def mapIso {A B : C} (e : A ≅ B) : MonoOver A ≌ MonoOver B
    where
  Functor := map e.Hom
  inverse := map e.inv
  unitIso := ((mapComp _ _).symm ≪≫ eqToIso (by simp) ≪≫ mapId).symm
  counitIso := (mapComp _ _).symm ≪≫ eqToIso (by simp) ≪≫ mapId
#align category_theory.mono_over.map_iso CategoryTheory.MonoOver.mapIso

section

variable (X)

/- warning: category_theory.mono_over.congr -> CategoryTheory.MonoOver.congr is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] (X : C) {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (e : CategoryTheory.Equivalence.{u1, u2, u3, u4} C _inst_1 D _inst_2), CategoryTheory.Equivalence.{u1, u2, max u3 u1, max u4 u2} (CategoryTheory.MonoOver.{u1, u3} C _inst_1 X) (CategoryTheory.MonoOver.category.{u3, u1} C _inst_1 X) (CategoryTheory.MonoOver.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 (CategoryTheory.Equivalence.functor.{u1, u2, u3, u4} C _inst_1 D _inst_2 e) X)) (CategoryTheory.MonoOver.category.{u4, u2} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 (CategoryTheory.Equivalence.functor.{u1, u2, u3, u4} C _inst_1 D _inst_2 e) X))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] (X : C) {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (e : CategoryTheory.Equivalence.{u1, u2, u3, u4} C D _inst_1 _inst_2), CategoryTheory.Equivalence.{u1, u2, max u3 u1, max u4 u2} (CategoryTheory.MonoOver.{u1, u3} C _inst_1 X) (CategoryTheory.MonoOver.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 (CategoryTheory.Equivalence.functor.{u1, u2, u3, u4} C D _inst_1 _inst_2 e)) X)) (CategoryTheory.instCategoryMonoOver.{u1, u3} C _inst_1 X) (CategoryTheory.instCategoryMonoOver.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 (CategoryTheory.Equivalence.functor.{u1, u2, u3, u4} C D _inst_1 _inst_2 e)) X))
Case conversion may be inaccurate. Consider using '#align category_theory.mono_over.congr CategoryTheory.MonoOver.congrₓ'. -/
/-- An equivalence of categories `e` between `C` and `D` induces an equivalence between
    `mono_over X` and `mono_over (e.functor.obj X)` whenever `X` is an object of `C`. -/
@[simps]
def congr (e : C ≌ D) : MonoOver X ≌ MonoOver (e.Functor.obj X)
    where
  Functor :=
    lift (Over.post e.Functor) fun f => by
      dsimp
      infer_instance
  inverse :=
    (lift (Over.post e.inverse) fun f => by
        dsimp
        infer_instance) ⋙
      (mapIso (e.unitIso.symm.app X)).Functor
  unitIso := NatIso.ofComponents (fun Y => isoMk (e.unitIso.app Y) (by tidy)) (by tidy)
  counitIso := NatIso.ofComponents (fun Y => isoMk (e.counitIso.app Y) (by tidy)) (by tidy)
#align category_theory.mono_over.congr CategoryTheory.MonoOver.congr

end

section

variable [HasPullbacks C]

#print CategoryTheory.MonoOver.mapPullbackAdj /-
/-- `map f` is left adjoint to `pullback f` when `f` is a monomorphism -/
def mapPullbackAdj (f : X ⟶ Y) [Mono f] : map f ⊣ pullback f :=
  Adjunction.restrictFullyFaithful (forget X) (forget Y) (Over.mapPullbackAdj f) (Iso.refl _)
    (Iso.refl _)
#align category_theory.mono_over.map_pullback_adj CategoryTheory.MonoOver.mapPullbackAdj
-/

#print CategoryTheory.MonoOver.pullbackMapSelf /-
/-- `mono_over.map f` followed by `mono_over.pullback f` is the identity. -/
def pullbackMapSelf (f : X ⟶ Y) [Mono f] : map f ⋙ pullback f ≅ 𝟭 _ :=
  (asIso (MonoOver.mapPullbackAdj f).Unit).symm
#align category_theory.mono_over.pullback_map_self CategoryTheory.MonoOver.pullbackMapSelf
-/

end

end Map

section Image

variable (f : X ⟶ Y) [HasImage f]

#print CategoryTheory.MonoOver.imageMonoOver /-
/-- The `mono_over Y` for the image inclusion for a morphism `f : X ⟶ Y`.
-/
def imageMonoOver (f : X ⟶ Y) [HasImage f] : MonoOver Y :=
  MonoOver.mk' (image.ι f)
#align category_theory.mono_over.image_mono_over CategoryTheory.MonoOver.imageMonoOver
-/

/- warning: category_theory.mono_over.image_mono_over_arrow -> CategoryTheory.MonoOver.imageMonoOver_arrow is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y) [_inst_4 : CategoryTheory.Limits.HasImage.{u1, u2} C _inst_1 X Y f], Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) ((fun (a : Type.{max u2 u1}) (b : Type.{u2}) [self : HasLiftT.{succ (max u2 u1), succ u2} a b] => self.0) (CategoryTheory.MonoOver.{u1, u2} C _inst_1 Y) C (HasLiftT.mk.{succ (max u2 u1), succ u2} (CategoryTheory.MonoOver.{u1, u2} C _inst_1 Y) C (CoeTCₓ.coe.{succ (max u2 u1), succ u2} (CategoryTheory.MonoOver.{u1, u2} C _inst_1 Y) C (coeBase.{succ (max u2 u1), succ u2} (CategoryTheory.MonoOver.{u1, u2} C _inst_1 Y) C (CategoryTheory.MonoOver.hasCoe.{u1, u2} C _inst_1 Y)))) (CategoryTheory.MonoOver.imageMonoOver.{u1, u2} C _inst_1 X Y f _inst_4)) Y) (CategoryTheory.MonoOver.arrow.{u1, u2} C _inst_1 Y (CategoryTheory.MonoOver.imageMonoOver.{u1, u2} C _inst_1 X Y f _inst_4)) (CategoryTheory.Limits.image.ι.{u1, u2} C _inst_1 X Y f _inst_4)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y) [_inst_4 : CategoryTheory.Limits.HasImage.{u1, u2} C _inst_1 X Y f], Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Comma.left.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 Y) (CategoryTheory.FullSubcategory.obj.{max u2 u1} (CategoryTheory.Over.{u1, u2} C _inst_1 Y) (fun (f : CategoryTheory.Over.{u1, u2} C _inst_1 Y) => CategoryTheory.Mono.{u1, u2} C _inst_1 (Prefunctor.obj.{succ u1, succ u1, u2, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1)) (CategoryTheory.Comma.left.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 Y) f)) (Prefunctor.obj.{succ u1, succ u1, u1, u2} (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.Category.toCategoryStruct.{u1, u1} (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u1, u2} (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 Y)) (CategoryTheory.Comma.right.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 Y) f)) (CategoryTheory.Comma.hom.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 Y) f)) (CategoryTheory.MonoOver.imageMonoOver.{u1, u2} C _inst_1 X Y f _inst_4))) Y) (CategoryTheory.MonoOver.arrow.{u1, u2} C _inst_1 Y (CategoryTheory.MonoOver.imageMonoOver.{u1, u2} C _inst_1 X Y f _inst_4)) (CategoryTheory.Limits.image.ι.{u1, u2} C _inst_1 X Y f _inst_4)
Case conversion may be inaccurate. Consider using '#align category_theory.mono_over.image_mono_over_arrow CategoryTheory.MonoOver.imageMonoOver_arrowₓ'. -/
@[simp]
theorem imageMonoOver_arrow (f : X ⟶ Y) [HasImage f] : (imageMonoOver f).arrow = image.ι f :=
  rfl
#align category_theory.mono_over.image_mono_over_arrow CategoryTheory.MonoOver.imageMonoOver_arrow

end Image

section Image

variable [HasImages C]

#print CategoryTheory.MonoOver.image /-
/-- Taking the image of a morphism gives a functor `over X ⥤ mono_over X`.
-/
@[simps]
def image : Over X ⥤ MonoOver X where
  obj f := imageMonoOver f.Hom
  map f g k := by
    apply (forget X).preimage _
    apply over.hom_mk _ _
    refine'
      image.lift
        { i := image _
          m := image.ι g.hom
          e := k.left ≫ factor_thru_image g.hom }
    apply image.lift_fac
#align category_theory.mono_over.image CategoryTheory.MonoOver.image
-/

#print CategoryTheory.MonoOver.imageForgetAdj /-
/-- `mono_over.image : over X ⥤ mono_over X` is left adjoint to
`mono_over.forget : mono_over X ⥤ over X`
-/
def imageForgetAdj : image ⊣ forget X :=
  Adjunction.mkOfHomEquiv
    {
      homEquiv := fun f g =>
        { toFun := fun k =>
            by
            apply over.hom_mk (factor_thru_image f.hom ≫ k.left) _
            change (factor_thru_image f.hom ≫ k.left) ≫ _ = f.hom
            rw [assoc, over.w k]
            apply image.fac
          invFun := fun k => by
            refine' over.hom_mk _ _
            refine'
              image.lift
                { i := g.obj.left
                  m := g.arrow
                  e := k.left
                  fac := over.w k }
            apply image.lift_fac
          left_inv := fun k => Subsingleton.elim _ _
          right_inv := fun k => by
            ext1
            change factor_thru_image _ ≫ image.lift _ = _
            rw [← cancel_mono g.arrow, assoc, image.lift_fac, image.fac f.hom]
            exact (over.w k).symm } }
#align category_theory.mono_over.image_forget_adj CategoryTheory.MonoOver.imageForgetAdj
-/

instance : IsRightAdjoint (forget X) where
  left := image
  adj := imageForgetAdj

/- warning: category_theory.mono_over.reflective -> CategoryTheory.MonoOver.reflective is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} [_inst_3 : CategoryTheory.Limits.HasImages.{u1, u2} C _inst_1], CategoryTheory.Reflective.{u1, u1, max u2 u1, max u2 u1} (CategoryTheory.Over.{u1, u2} C _inst_1 X) (CategoryTheory.MonoOver.{u1, u2} C _inst_1 X) (CategoryTheory.Over.category.{u2, u1} C _inst_1 X) (CategoryTheory.InducedCategory.category.{u1, max u2 u1, max u2 u1} (CategoryTheory.FullSubcategoryₓ.{u1, max u2 u1} (CategoryTheory.Over.{u1, u2} C _inst_1 X) (CategoryTheory.Over.category.{u2, u1} C _inst_1 X) (fun (f : CategoryTheory.Over.{u1, u2} C _inst_1 X) => CategoryTheory.Mono.{u1, u2} C _inst_1 (CategoryTheory.Functor.obj.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Comma.left.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f)) (CategoryTheory.Functor.obj.{u1, u1, u1, u2} (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) (CategoryTheory.Comma.right.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f)) (CategoryTheory.Comma.hom.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f))) (CategoryTheory.Over.{u1, u2} C _inst_1 X) (CategoryTheory.Over.category.{u2, u1} C _inst_1 X) (CategoryTheory.FullSubcategoryₓ.obj.{u1, max u2 u1} (CategoryTheory.Over.{u1, u2} C _inst_1 X) (CategoryTheory.Over.category.{u2, u1} C _inst_1 X) (fun (f : CategoryTheory.Over.{u1, u2} C _inst_1 X) => CategoryTheory.Mono.{u1, u2} C _inst_1 (CategoryTheory.Functor.obj.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Comma.left.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f)) (CategoryTheory.Functor.obj.{u1, u1, u1, u2} (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) (CategoryTheory.Comma.right.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f)) (CategoryTheory.Comma.hom.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f)))) (CategoryTheory.MonoOver.forget.{u1, u2} C _inst_1 X)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} [_inst_3 : CategoryTheory.Limits.HasImages.{u1, u2} C _inst_1], CategoryTheory.Reflective.{u1, u1, max u2 u1, max u2 u1} (CategoryTheory.Over.{u1, u2} C _inst_1 X) (CategoryTheory.MonoOver.{u1, u2} C _inst_1 X) (CategoryTheory.instCategoryOver.{u1, u2} C _inst_1 X) (CategoryTheory.instCategoryMonoOver.{u1, u2} C _inst_1 X) (CategoryTheory.MonoOver.forget.{u1, u2} C _inst_1 X)
Case conversion may be inaccurate. Consider using '#align category_theory.mono_over.reflective CategoryTheory.MonoOver.reflectiveₓ'. -/
instance reflective : Reflective (forget X) where
#align category_theory.mono_over.reflective CategoryTheory.MonoOver.reflective

/- warning: category_theory.mono_over.forget_image -> CategoryTheory.MonoOver.forgetImage is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.mono_over.forget_image CategoryTheory.MonoOver.forgetImageₓ'. -/
/-- Forgetting that a monomorphism over `X` is a monomorphism, then taking its image,
is the identity functor.
-/
def forgetImage : forget X ⋙ image ≅ 𝟭 (MonoOver X) :=
  asIso (Adjunction.counit imageForgetAdj)
#align category_theory.mono_over.forget_image CategoryTheory.MonoOver.forgetImage

end Image

section Exists

variable [HasImages C]

/- warning: category_theory.mono_over.exists -> CategoryTheory.MonoOver.exists is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} [_inst_3 : CategoryTheory.Limits.HasImages.{u1, u2} C _inst_1], (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y) -> (CategoryTheory.Functor.{u1, u1, max u2 u1, max u2 u1} (CategoryTheory.MonoOver.{u1, u2} C _inst_1 X) (CategoryTheory.InducedCategory.category.{u1, max u2 u1, max u2 u1} (CategoryTheory.FullSubcategoryₓ.{u1, max u2 u1} (CategoryTheory.Over.{u1, u2} C _inst_1 X) (CategoryTheory.Over.category.{u2, u1} C _inst_1 X) (fun (f : CategoryTheory.Over.{u1, u2} C _inst_1 X) => CategoryTheory.Mono.{u1, u2} C _inst_1 (CategoryTheory.Functor.obj.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Comma.left.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f)) (CategoryTheory.Functor.obj.{u1, u1, u1, u2} (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) (CategoryTheory.Comma.right.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f)) (CategoryTheory.Comma.hom.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f))) (CategoryTheory.Over.{u1, u2} C _inst_1 X) (CategoryTheory.Over.category.{u2, u1} C _inst_1 X) (CategoryTheory.FullSubcategoryₓ.obj.{u1, max u2 u1} (CategoryTheory.Over.{u1, u2} C _inst_1 X) (CategoryTheory.Over.category.{u2, u1} C _inst_1 X) (fun (f : CategoryTheory.Over.{u1, u2} C _inst_1 X) => CategoryTheory.Mono.{u1, u2} C _inst_1 (CategoryTheory.Functor.obj.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Comma.left.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f)) (CategoryTheory.Functor.obj.{u1, u1, u1, u2} (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) (CategoryTheory.Comma.right.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f)) (CategoryTheory.Comma.hom.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f)))) (CategoryTheory.MonoOver.{u1, u2} C _inst_1 Y) (CategoryTheory.MonoOver.category.{u2, u1} C _inst_1 Y))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} [_inst_3 : CategoryTheory.Limits.HasImages.{u1, u2} C _inst_1], (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y) -> (CategoryTheory.Functor.{u1, u1, max u2 u1, max u2 u1} (CategoryTheory.MonoOver.{u1, u2} C _inst_1 X) (CategoryTheory.instCategoryMonoOver.{u1, u2} C _inst_1 X) (CategoryTheory.MonoOver.{u1, u2} C _inst_1 Y) (CategoryTheory.instCategoryMonoOver.{u1, u2} C _inst_1 Y))
Case conversion may be inaccurate. Consider using '#align category_theory.mono_over.exists CategoryTheory.MonoOver.existsₓ'. -/
/-- In the case where `f` is not a monomorphism but `C` has images,
we can still take the "forward map" under it, which agrees with `mono_over.map f`.
-/
def exists (f : X ⟶ Y) : MonoOver X ⥤ MonoOver Y :=
  forget _ ⋙ Over.map f ⋙ image
#align category_theory.mono_over.exists CategoryTheory.MonoOver.exists

/- warning: category_theory.mono_over.faithful_exists -> CategoryTheory.MonoOver.faithful_exists is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} [_inst_3 : CategoryTheory.Limits.HasImages.{u1, u2} C _inst_1] (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y), CategoryTheory.Faithful.{u1, u1, max u2 u1, max u2 u1} (CategoryTheory.MonoOver.{u1, u2} C _inst_1 X) (CategoryTheory.InducedCategory.category.{u1, max u2 u1, max u2 u1} (CategoryTheory.FullSubcategoryₓ.{u1, max u2 u1} (CategoryTheory.Over.{u1, u2} C _inst_1 X) (CategoryTheory.Over.category.{u2, u1} C _inst_1 X) (fun (f : CategoryTheory.Over.{u1, u2} C _inst_1 X) => CategoryTheory.Mono.{u1, u2} C _inst_1 (CategoryTheory.Functor.obj.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Comma.left.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f)) (CategoryTheory.Functor.obj.{u1, u1, u1, u2} (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) (CategoryTheory.Comma.right.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f)) (CategoryTheory.Comma.hom.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f))) (CategoryTheory.Over.{u1, u2} C _inst_1 X) (CategoryTheory.Over.category.{u2, u1} C _inst_1 X) (CategoryTheory.FullSubcategoryₓ.obj.{u1, max u2 u1} (CategoryTheory.Over.{u1, u2} C _inst_1 X) (CategoryTheory.Over.category.{u2, u1} C _inst_1 X) (fun (f : CategoryTheory.Over.{u1, u2} C _inst_1 X) => CategoryTheory.Mono.{u1, u2} C _inst_1 (CategoryTheory.Functor.obj.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Comma.left.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f)) (CategoryTheory.Functor.obj.{u1, u1, u1, u2} (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) (CategoryTheory.Comma.right.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f)) (CategoryTheory.Comma.hom.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f)))) (CategoryTheory.MonoOver.{u1, u2} C _inst_1 Y) (CategoryTheory.MonoOver.category.{u2, u1} C _inst_1 Y) (CategoryTheory.MonoOver.exists.{u1, u2} C _inst_1 X Y _inst_3 f)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} [_inst_3 : CategoryTheory.Limits.HasImages.{u1, u2} C _inst_1] (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y), CategoryTheory.Faithful.{u1, u1, max u2 u1, max u2 u1} (CategoryTheory.MonoOver.{u1, u2} C _inst_1 X) (CategoryTheory.instCategoryMonoOver.{u1, u2} C _inst_1 X) (CategoryTheory.MonoOver.{u1, u2} C _inst_1 Y) (CategoryTheory.instCategoryMonoOver.{u1, u2} C _inst_1 Y) (CategoryTheory.MonoOver.exists.{u1, u2} C _inst_1 X Y _inst_3 f)
Case conversion may be inaccurate. Consider using '#align category_theory.mono_over.faithful_exists CategoryTheory.MonoOver.faithful_existsₓ'. -/
instance faithful_exists (f : X ⟶ Y) : Faithful (exists f) where
#align category_theory.mono_over.faithful_exists CategoryTheory.MonoOver.faithful_exists

/- warning: category_theory.mono_over.exists_iso_map -> CategoryTheory.MonoOver.existsIsoMap is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.mono_over.exists_iso_map CategoryTheory.MonoOver.existsIsoMapₓ'. -/
/-- When `f : X ⟶ Y` is a monomorphism, `exists f` agrees with `map f`.
-/
def existsIsoMap (f : X ⟶ Y) [Mono f] : exists f ≅ map f :=
  NatIso.ofComponents
    (by
      intro Z
      suffices : (forget _).obj ((exists f).obj Z) ≅ (forget _).obj ((map f).obj Z)
      apply (forget _).preimageIso this
      apply over.iso_mk _ _
      apply image_mono_iso_source (Z.arrow ≫ f)
      apply image_mono_iso_source_hom_self)
    (by
      intro Z₁ Z₂ g
      ext1
      change
        image.lift ⟨_, _, _, _⟩ ≫ (image_mono_iso_source (Z₂.arrow ≫ f)).Hom =
          (image_mono_iso_source (Z₁.arrow ≫ f)).Hom ≫ g.left
      rw [← cancel_mono (Z₂.arrow ≫ f), assoc, assoc, w_assoc g, image_mono_iso_source_hom_self,
        image_mono_iso_source_hom_self]
      apply image.lift_fac)
#align category_theory.mono_over.exists_iso_map CategoryTheory.MonoOver.existsIsoMap

/- warning: category_theory.mono_over.exists_pullback_adj -> CategoryTheory.MonoOver.existsPullbackAdj is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.mono_over.exists_pullback_adj CategoryTheory.MonoOver.existsPullbackAdjₓ'. -/
/-- `exists` is adjoint to `pullback` when images exist -/
def existsPullbackAdj (f : X ⟶ Y) [HasPullbacks C] : exists f ⊣ pullback f :=
  Adjunction.restrictFullyFaithful (forget X) (𝟭 _) ((Over.mapPullbackAdj f).comp imageForgetAdj)
    (Iso.refl _) (Iso.refl _)
#align category_theory.mono_over.exists_pullback_adj CategoryTheory.MonoOver.existsPullbackAdj

end Exists

end MonoOver

end CategoryTheory

