/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel

! This file was ported from Lean 3 source module category_theory.limits.preserves.shapes.zero
! leanprover-community/mathlib commit 69c6a5a12d8a2b159f20933e60115a4f2de62b58
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathbin.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
# Preservation of zero objects and zero morphisms

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define the class `preserves_zero_morphisms` and show basic properties.

## Main results

We provide the following results:
* Left adjoints and right adjoints preserve zero morphisms;
* full functors preserve zero morphisms;
* if both categories involved have a zero object, then a functor preserves zero morphisms if and
  only if it preserves the zero object;
* functors which preserve initial or terminal objects preserve zero morphisms.

-/


universe v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory

open CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

section ZeroMorphisms

variable [HasZeroMorphisms C] [HasZeroMorphisms D]

#print CategoryTheory.Functor.PreservesZeroMorphisms /-
/-- A functor preserves zero morphisms if it sends zero morphisms to zero morphisms. -/
class PreservesZeroMorphisms (F : C ⥤ D) : Prop where
  map_zero' : ∀ X Y : C, F.map (0 : X ⟶ Y) = 0 := by obviously
#align category_theory.functor.preserves_zero_morphisms CategoryTheory.Functor.PreservesZeroMorphisms
-/

/- warning: category_theory.functor.map_zero -> CategoryTheory.Functor.map_zero is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] [_inst_3 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u3} C _inst_1] [_inst_4 : CategoryTheory.Limits.HasZeroMorphisms.{u2, u4} D _inst_2] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) [_inst_5 : CategoryTheory.Functor.PreservesZeroMorphisms.{u1, u2, u3, u4} C _inst_1 D _inst_2 _inst_3 _inst_4 F] (X : C) (Y : C), Eq.{succ u2} (Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F Y)) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X Y (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) 0 (OfNat.mk.{u1} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) 0 (Zero.zero.{u1} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) (CategoryTheory.Limits.HasZeroMorphisms.hasZero.{u1, u3} C _inst_1 _inst_3 X Y))))) (OfNat.ofNat.{u2} (Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F Y)) 0 (OfNat.mk.{u2} (Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F Y)) 0 (Zero.zero.{u2} (Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F Y)) (CategoryTheory.Limits.HasZeroMorphisms.hasZero.{u2, u4} D _inst_2 _inst_4 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F Y)))))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] [_inst_3 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u3} C _inst_1] [_inst_4 : CategoryTheory.Limits.HasZeroMorphisms.{u2, u4} D _inst_2] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) [_inst_5 : CategoryTheory.Functor.PreservesZeroMorphisms.{u1, u2, u3, u4} C _inst_1 D _inst_2 _inst_3 _inst_4 F] (X : C) (Y : C), Eq.{succ u2} (Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) Y)) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X Y (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) 0 (Zero.toOfNat0.{u1} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) (CategoryTheory.Limits.HasZeroMorphisms.Zero.{u1, u3} C _inst_1 _inst_3 X Y)))) (OfNat.ofNat.{u2} (Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) Y)) 0 (Zero.toOfNat0.{u2} (Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) Y)) (CategoryTheory.Limits.HasZeroMorphisms.Zero.{u2, u4} D _inst_2 _inst_4 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) Y))))
Case conversion may be inaccurate. Consider using '#align category_theory.functor.map_zero CategoryTheory.Functor.map_zeroₓ'. -/
@[simp]
protected theorem map_zero (F : C ⥤ D) [PreservesZeroMorphisms F] (X Y : C) :
    F.map (0 : X ⟶ Y) = 0 :=
  PreservesZeroMorphisms.map_zero' _ _
#align category_theory.functor.map_zero CategoryTheory.Functor.map_zero

/- warning: category_theory.functor.zero_of_map_zero -> CategoryTheory.Functor.zero_of_map_zero is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] [_inst_3 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u3} C _inst_1] [_inst_4 : CategoryTheory.Limits.HasZeroMorphisms.{u2, u4} D _inst_2] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) [_inst_5 : CategoryTheory.Functor.PreservesZeroMorphisms.{u1, u2, u3, u4} C _inst_1 D _inst_2 _inst_3 _inst_4 F] [_inst_6 : CategoryTheory.Faithful.{u1, u2, u3, u4} C _inst_1 D _inst_2 F] {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y), (Eq.{succ u2} (Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F Y)) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X Y f) (OfNat.ofNat.{u2} (Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F Y)) 0 (OfNat.mk.{u2} (Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F Y)) 0 (Zero.zero.{u2} (Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F Y)) (CategoryTheory.Limits.HasZeroMorphisms.hasZero.{u2, u4} D _inst_2 _inst_4 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F Y)))))) -> (Eq.{succ u1} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) f (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) 0 (OfNat.mk.{u1} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) 0 (Zero.zero.{u1} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) (CategoryTheory.Limits.HasZeroMorphisms.hasZero.{u1, u3} C _inst_1 _inst_3 X Y)))))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] [_inst_3 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u3} C _inst_1] [_inst_4 : CategoryTheory.Limits.HasZeroMorphisms.{u2, u4} D _inst_2] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) [_inst_5 : CategoryTheory.Functor.PreservesZeroMorphisms.{u1, u2, u3, u4} C _inst_1 D _inst_2 _inst_3 _inst_4 F] [_inst_6 : CategoryTheory.Faithful.{u1, u2, u3, u4} C _inst_1 D _inst_2 F] {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y), (Eq.{succ u2} (Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) Y)) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X Y f) (OfNat.ofNat.{u2} (Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) Y)) 0 (Zero.toOfNat0.{u2} (Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) Y)) (CategoryTheory.Limits.HasZeroMorphisms.Zero.{u2, u4} D _inst_2 _inst_4 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) Y))))) -> (Eq.{succ u1} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) f (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) 0 (Zero.toOfNat0.{u1} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) (CategoryTheory.Limits.HasZeroMorphisms.Zero.{u1, u3} C _inst_1 _inst_3 X Y))))
Case conversion may be inaccurate. Consider using '#align category_theory.functor.zero_of_map_zero CategoryTheory.Functor.zero_of_map_zeroₓ'. -/
theorem zero_of_map_zero (F : C ⥤ D) [PreservesZeroMorphisms F] [Faithful F] {X Y : C} (f : X ⟶ Y)
    (h : F.map f = 0) : f = 0 :=
  F.map_injective <| h.trans <| Eq.symm <| F.map_zero _ _
#align category_theory.functor.zero_of_map_zero CategoryTheory.Functor.zero_of_map_zero

/- warning: category_theory.functor.map_eq_zero_iff -> CategoryTheory.Functor.map_eq_zero_iff is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] [_inst_3 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u3} C _inst_1] [_inst_4 : CategoryTheory.Limits.HasZeroMorphisms.{u2, u4} D _inst_2] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) [_inst_5 : CategoryTheory.Functor.PreservesZeroMorphisms.{u1, u2, u3, u4} C _inst_1 D _inst_2 _inst_3 _inst_4 F] [_inst_6 : CategoryTheory.Faithful.{u1, u2, u3, u4} C _inst_1 D _inst_2 F] {X : C} {Y : C} {f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y}, Iff (Eq.{succ u2} (Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F Y)) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X Y f) (OfNat.ofNat.{u2} (Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F Y)) 0 (OfNat.mk.{u2} (Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F Y)) 0 (Zero.zero.{u2} (Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F Y)) (CategoryTheory.Limits.HasZeroMorphisms.hasZero.{u2, u4} D _inst_2 _inst_4 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F Y)))))) (Eq.{succ u1} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) f (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) 0 (OfNat.mk.{u1} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) 0 (Zero.zero.{u1} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) (CategoryTheory.Limits.HasZeroMorphisms.hasZero.{u1, u3} C _inst_1 _inst_3 X Y)))))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] [_inst_3 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u3} C _inst_1] [_inst_4 : CategoryTheory.Limits.HasZeroMorphisms.{u2, u4} D _inst_2] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) [_inst_5 : CategoryTheory.Functor.PreservesZeroMorphisms.{u1, u2, u3, u4} C _inst_1 D _inst_2 _inst_3 _inst_4 F] [_inst_6 : CategoryTheory.Faithful.{u1, u2, u3, u4} C _inst_1 D _inst_2 F] {X : C} {Y : C} {f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y}, Iff (Eq.{succ u2} (Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) Y)) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X Y f) (OfNat.ofNat.{u2} (Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) Y)) 0 (Zero.toOfNat0.{u2} (Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) Y)) (CategoryTheory.Limits.HasZeroMorphisms.Zero.{u2, u4} D _inst_2 _inst_4 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) Y))))) (Eq.{succ u1} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) f (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) 0 (Zero.toOfNat0.{u1} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) (CategoryTheory.Limits.HasZeroMorphisms.Zero.{u1, u3} C _inst_1 _inst_3 X Y))))
Case conversion may be inaccurate. Consider using '#align category_theory.functor.map_eq_zero_iff CategoryTheory.Functor.map_eq_zero_iffₓ'. -/
theorem map_eq_zero_iff (F : C ⥤ D) [PreservesZeroMorphisms F] [Faithful F] {X Y : C} {f : X ⟶ Y} :
    F.map f = 0 ↔ f = 0 :=
  ⟨F.zero_of_map_zero _, by
    rintro rfl
    exact F.map_zero _ _⟩
#align category_theory.functor.map_eq_zero_iff CategoryTheory.Functor.map_eq_zero_iff

#print CategoryTheory.Functor.preservesZeroMorphisms_of_isLeftAdjoint /-
instance (priority := 100) preservesZeroMorphisms_of_isLeftAdjoint (F : C ⥤ D) [IsLeftAdjoint F] :
    PreservesZeroMorphisms F
    where map_zero' X Y := by
    let adj := Adjunction.ofLeftAdjoint F
    calc
      F.map (0 : X ⟶ Y) = F.map 0 ≫ F.map (adj.unit.app Y) ≫ adj.counit.app (F.obj Y) := _
      _ = F.map 0 ≫ F.map ((right_adjoint F).map (0 : F.obj X ⟶ _)) ≫ adj.counit.app (F.obj Y) := _
      _ = 0 := _
      
    · rw [adjunction.left_triangle_components]
      exact (category.comp_id _).symm
    · simp only [← category.assoc, ← F.map_comp, zero_comp]
    · simp only [adjunction.counit_naturality, comp_zero]
#align category_theory.functor.preserves_zero_morphisms_of_is_left_adjoint CategoryTheory.Functor.preservesZeroMorphisms_of_isLeftAdjoint
-/

#print CategoryTheory.Functor.preservesZeroMorphisms_of_isRightAdjoint /-
instance (priority := 100) preservesZeroMorphisms_of_isRightAdjoint (G : C ⥤ D) [IsRightAdjoint G] :
    PreservesZeroMorphisms G
    where map_zero' X Y := by
    let adj := Adjunction.ofRightAdjoint G
    calc
      G.map (0 : X ⟶ Y) = adj.unit.app (G.obj X) ≫ G.map (adj.counit.app X) ≫ G.map 0 := _
      _ = adj.unit.app (G.obj X) ≫ G.map ((left_adjoint G).map (0 : _ ⟶ G.obj X)) ≫ G.map 0 := _
      _ = 0 := _
      
    · rw [adjunction.right_triangle_components_assoc]
    · simp only [← G.map_comp, comp_zero]
    · simp only [adjunction.unit_naturality_assoc, zero_comp]
#align category_theory.functor.preserves_zero_morphisms_of_is_right_adjoint CategoryTheory.Functor.preservesZeroMorphisms_of_isRightAdjoint
-/

#print CategoryTheory.Functor.preservesZeroMorphisms_of_full /-
instance (priority := 100) preservesZeroMorphisms_of_full (F : C ⥤ D) [Full F] :
    PreservesZeroMorphisms F
    where map_zero' X Y :=
    calc
      F.map (0 : X ⟶ Y) = F.map (0 ≫ F.preimage (0 : F.obj Y ⟶ F.obj Y)) := by rw [zero_comp]
      _ = 0 := by rw [F.map_comp, F.image_preimage, comp_zero]
      
#align category_theory.functor.preserves_zero_morphisms_of_full CategoryTheory.Functor.preservesZeroMorphisms_of_full
-/

end ZeroMorphisms

section ZeroObject

variable [HasZeroObject C] [HasZeroObject D]

open ZeroObject

variable [HasZeroMorphisms C] [HasZeroMorphisms D] (F : C ⥤ D)

/- warning: category_theory.functor.map_zero_object -> CategoryTheory.Functor.mapZeroObject is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] [_inst_3 : CategoryTheory.Limits.HasZeroObject.{u1, u3} C _inst_1] [_inst_4 : CategoryTheory.Limits.HasZeroObject.{u2, u4} D _inst_2] [_inst_5 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u3} C _inst_1] [_inst_6 : CategoryTheory.Limits.HasZeroMorphisms.{u2, u4} D _inst_2] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) [_inst_7 : CategoryTheory.Functor.PreservesZeroMorphisms.{u1, u2, u3, u4} C _inst_1 D _inst_2 _inst_5 _inst_6 F], CategoryTheory.Iso.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F (OfNat.ofNat.{u3} C 0 (OfNat.mk.{u3} C 0 (Zero.zero.{u3} C (CategoryTheory.Limits.HasZeroObject.zero'.{u1, u3} C _inst_1 _inst_3))))) (OfNat.ofNat.{u4} D 0 (OfNat.mk.{u4} D 0 (Zero.zero.{u4} D (CategoryTheory.Limits.HasZeroObject.zero'.{u2, u4} D _inst_2 _inst_4))))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] [_inst_3 : CategoryTheory.Limits.HasZeroObject.{u1, u3} C _inst_1] [_inst_4 : CategoryTheory.Limits.HasZeroObject.{u2, u4} D _inst_2] [_inst_5 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u3} C _inst_1] [_inst_6 : CategoryTheory.Limits.HasZeroMorphisms.{u2, u4} D _inst_2] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) [_inst_7 : CategoryTheory.Functor.PreservesZeroMorphisms.{u1, u2, u3, u4} C _inst_1 D _inst_2 _inst_5 _inst_6 F], CategoryTheory.Iso.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) (OfNat.ofNat.{u3} C 0 (Zero.toOfNat0.{u3} C (CategoryTheory.Limits.HasZeroObject.zero'.{u1, u3} C _inst_1 _inst_3)))) (OfNat.ofNat.{u4} D 0 (Zero.toOfNat0.{u4} D (CategoryTheory.Limits.HasZeroObject.zero'.{u2, u4} D _inst_2 _inst_4)))
Case conversion may be inaccurate. Consider using '#align category_theory.functor.map_zero_object CategoryTheory.Functor.mapZeroObjectₓ'. -/
/-- A functor that preserves zero morphisms also preserves the zero object. -/
@[simps]
def mapZeroObject [PreservesZeroMorphisms F] : F.obj 0 ≅ 0
    where
  Hom := 0
  inv := 0
  hom_inv_id' := by rw [← F.map_id, id_zero, F.map_zero, zero_comp]
  inv_hom_id' := by rw [id_zero, comp_zero]
#align category_theory.functor.map_zero_object CategoryTheory.Functor.mapZeroObject

variable {F}

/- warning: category_theory.functor.preserves_zero_morphisms_of_map_zero_object -> CategoryTheory.Functor.preservesZeroMorphisms_of_map_zero_object is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] [_inst_3 : CategoryTheory.Limits.HasZeroObject.{u1, u3} C _inst_1] [_inst_4 : CategoryTheory.Limits.HasZeroObject.{u2, u4} D _inst_2] [_inst_5 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u3} C _inst_1] [_inst_6 : CategoryTheory.Limits.HasZeroMorphisms.{u2, u4} D _inst_2] {F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2}, (CategoryTheory.Iso.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F (OfNat.ofNat.{u3} C 0 (OfNat.mk.{u3} C 0 (Zero.zero.{u3} C (CategoryTheory.Limits.HasZeroObject.zero'.{u1, u3} C _inst_1 _inst_3))))) (OfNat.ofNat.{u4} D 0 (OfNat.mk.{u4} D 0 (Zero.zero.{u4} D (CategoryTheory.Limits.HasZeroObject.zero'.{u2, u4} D _inst_2 _inst_4))))) -> (CategoryTheory.Functor.PreservesZeroMorphisms.{u1, u2, u3, u4} C _inst_1 D _inst_2 _inst_5 _inst_6 F)
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] [_inst_3 : CategoryTheory.Limits.HasZeroObject.{u1, u3} C _inst_1] [_inst_4 : CategoryTheory.Limits.HasZeroObject.{u2, u4} D _inst_2] [_inst_5 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u3} C _inst_1] [_inst_6 : CategoryTheory.Limits.HasZeroMorphisms.{u2, u4} D _inst_2] {F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2}, (CategoryTheory.Iso.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) (OfNat.ofNat.{u3} C 0 (Zero.toOfNat0.{u3} C (CategoryTheory.Limits.HasZeroObject.zero'.{u1, u3} C _inst_1 _inst_3)))) (OfNat.ofNat.{u4} D 0 (Zero.toOfNat0.{u4} D (CategoryTheory.Limits.HasZeroObject.zero'.{u2, u4} D _inst_2 _inst_4)))) -> (CategoryTheory.Functor.PreservesZeroMorphisms.{u1, u2, u3, u4} C _inst_1 D _inst_2 _inst_5 _inst_6 F)
Case conversion may be inaccurate. Consider using '#align category_theory.functor.preserves_zero_morphisms_of_map_zero_object CategoryTheory.Functor.preservesZeroMorphisms_of_map_zero_objectₓ'. -/
theorem preservesZeroMorphisms_of_map_zero_object (i : F.obj 0 ≅ 0) : PreservesZeroMorphisms F :=
  {
    map_zero' := fun X Y =>
      calc
        F.map (0 : X ⟶ Y) = F.map (0 : X ⟶ 0) ≫ F.map 0 := by rw [← functor.map_comp, comp_zero]
        _ = F.map 0 ≫ (i.Hom ≫ i.inv) ≫ F.map 0 := by rw [iso.hom_inv_id, category.id_comp]
        _ = 0 := by simp only [zero_of_to_zero i.hom, zero_comp, comp_zero]
         }
#align category_theory.functor.preserves_zero_morphisms_of_map_zero_object CategoryTheory.Functor.preservesZeroMorphisms_of_map_zero_object

#print CategoryTheory.Functor.preservesZeroMorphisms_of_preserves_initial_object /-
instance (priority := 100) preservesZeroMorphisms_of_preserves_initial_object
    [PreservesColimit (Functor.empty.{0} C) F] : PreservesZeroMorphisms F :=
  preservesZeroMorphisms_of_map_zero_object <|
    F.mapIso HasZeroObject.zeroIsoInitial ≪≫
      PreservesInitial.iso F ≪≫ HasZeroObject.zeroIsoInitial.symm
#align category_theory.functor.preserves_zero_morphisms_of_preserves_initial_object CategoryTheory.Functor.preservesZeroMorphisms_of_preserves_initial_object
-/

#print CategoryTheory.Functor.preservesZeroMorphisms_of_preserves_terminal_object /-
instance (priority := 100) preservesZeroMorphisms_of_preserves_terminal_object
    [PreservesLimit (Functor.empty.{0} C) F] : PreservesZeroMorphisms F :=
  preservesZeroMorphisms_of_map_zero_object <|
    F.mapIso HasZeroObject.zeroIsoTerminal ≪≫
      PreservesTerminal.iso F ≪≫ HasZeroObject.zeroIsoTerminal.symm
#align category_theory.functor.preserves_zero_morphisms_of_preserves_terminal_object CategoryTheory.Functor.preservesZeroMorphisms_of_preserves_terminal_object
-/

variable (F)

#print CategoryTheory.Functor.preservesTerminalObjectOfPreservesZeroMorphisms /-
/-- Preserving zero morphisms implies preserving terminal objects. -/
def preservesTerminalObjectOfPreservesZeroMorphisms [PreservesZeroMorphisms F] :
    PreservesLimit (Functor.empty C) F :=
  preservesTerminalOfIso F <|
    F.mapIso HasZeroObject.zeroIsoTerminal.symm ≪≫ mapZeroObject F ≪≫ HasZeroObject.zeroIsoTerminal
#align category_theory.functor.preserves_terminal_object_of_preserves_zero_morphisms CategoryTheory.Functor.preservesTerminalObjectOfPreservesZeroMorphisms
-/

#print CategoryTheory.Functor.preservesInitialObjectOfPreservesZeroMorphisms /-
/-- Preserving zero morphisms implies preserving terminal objects. -/
def preservesInitialObjectOfPreservesZeroMorphisms [PreservesZeroMorphisms F] :
    PreservesColimit (Functor.empty C) F :=
  preservesInitialOfIso F <|
    HasZeroObject.zeroIsoInitial.symm ≪≫
      (mapZeroObject F).symm ≪≫ (F.mapIso HasZeroObject.zeroIsoInitial.symm).symm
#align category_theory.functor.preserves_initial_object_of_preserves_zero_morphisms CategoryTheory.Functor.preservesInitialObjectOfPreservesZeroMorphisms
-/

end ZeroObject

end CategoryTheory.Functor

