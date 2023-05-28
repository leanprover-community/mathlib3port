/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module algebra.homology.image_to_kernel
! leanprover-community/mathlib commit ce38d86c0b2d427ce208c3cee3159cb421d2b3c4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Subobject.Limits

/-!
# Image-to-kernel comparison maps

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Whenever `f : A ⟶ B` and `g : B ⟶ C` satisfy `w : f ≫ g = 0`,
we have `image_le_kernel f g w : image_subobject f ≤ kernel_subobject g`
(assuming the appropriate images and kernels exist).

`image_to_kernel f g w` is the corresponding morphism between objects in `C`.

We define `homology f g w` of such a pair as the cokernel of `image_to_kernel f g w`.
-/


universe v u

open CategoryTheory CategoryTheory.Limits

variable {ι : Type _}

variable {V : Type u} [Category.{v} V] [HasZeroMorphisms V]

open Classical

noncomputable section

section

variable {A B C : V} (f : A ⟶ B) [HasImage f] (g : B ⟶ C) [HasKernel g]

/- warning: image_le_kernel -> image_le_kernel is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} V] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u2} V _inst_1] {A : V} {B : V} {C : V} (f : Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A B) [_inst_3 : CategoryTheory.Limits.HasImage.{u1, u2} V _inst_1 A B f] (g : Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) B C) [_inst_4 : CategoryTheory.Limits.HasKernel.{u1, u2} V _inst_1 _inst_2 B C g], (Eq.{succ u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A C) (CategoryTheory.CategoryStruct.comp.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1) A B C f g) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A C) 0 (OfNat.mk.{u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A C) 0 (Zero.zero.{u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A C) (CategoryTheory.Limits.HasZeroMorphisms.hasZero.{u1, u2} V _inst_1 _inst_2 A C))))) -> (LE.le.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (Preorder.toHasLe.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (CategoryTheory.Subobject.partialOrder.{u2, u1} V _inst_1 B))) (CategoryTheory.Limits.imageSubobject.{u1, u2} V _inst_1 A B f _inst_3) (CategoryTheory.Limits.kernelSubobject.{u1, u2} V _inst_1 B C _inst_2 g _inst_4))
but is expected to have type
  forall {V : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} V] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u2} V _inst_1] {A : V} {B : V} {C : V} (f : Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A B) [_inst_3 : CategoryTheory.Limits.HasImage.{u1, u2} V _inst_1 A B f] (g : Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) B C) [_inst_4 : CategoryTheory.Limits.HasKernel.{u1, u2} V _inst_1 _inst_2 B C g], (Eq.{succ u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A C) (CategoryTheory.CategoryStruct.comp.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1) A B C f g) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A C) 0 (Zero.toOfNat0.{u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A C) (CategoryTheory.Limits.HasZeroMorphisms.Zero.{u1, u2} V _inst_1 _inst_2 A C)))) -> (LE.le.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (Preorder.toLE.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (CategoryTheory.instPartialOrderSubobject.{u1, u2} V _inst_1 B))) (CategoryTheory.Limits.imageSubobject.{u1, u2} V _inst_1 A B f _inst_3) (CategoryTheory.Limits.kernelSubobject.{u1, u2} V _inst_1 B C _inst_2 g _inst_4))
Case conversion may be inaccurate. Consider using '#align image_le_kernel image_le_kernelₓ'. -/
theorem image_le_kernel (w : f ≫ g = 0) : imageSubobject f ≤ kernelSubobject g :=
  imageSubobject_le_mk _ _ (kernel.lift _ _ w) (by simp)
#align image_le_kernel image_le_kernel

/- warning: image_to_kernel -> imageToKernel is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} V] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u2} V _inst_1] {A : V} {B : V} {C : V} (f : Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A B) [_inst_3 : CategoryTheory.Limits.HasImage.{u1, u2} V _inst_1 A B f] (g : Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) B C) [_inst_4 : CategoryTheory.Limits.HasKernel.{u1, u2} V _inst_1 _inst_2 B C g], (Eq.{succ u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A C) (CategoryTheory.CategoryStruct.comp.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1) A B C f g) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A C) 0 (OfNat.mk.{u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A C) 0 (Zero.zero.{u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A C) (CategoryTheory.Limits.HasZeroMorphisms.hasZero.{u1, u2} V _inst_1 _inst_2 A C))))) -> (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) ((fun (a : Type.{max u2 u1}) (b : Type.{u2}) [self : HasLiftT.{succ (max u2 u1), succ u2} a b] => self.0) (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) V (HasLiftT.mk.{succ (max u2 u1), succ u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) V (CoeTCₓ.coe.{succ (max u2 u1), succ u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) V (coeBase.{succ (max u2 u1), succ u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) V (CategoryTheory.Subobject.hasCoe.{u1, u2} V _inst_1 B)))) (CategoryTheory.Limits.imageSubobject.{u1, u2} V _inst_1 A B f _inst_3)) ((fun (a : Type.{max u2 u1}) (b : Type.{u2}) [self : HasLiftT.{succ (max u2 u1), succ u2} a b] => self.0) (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) V (HasLiftT.mk.{succ (max u2 u1), succ u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) V (CoeTCₓ.coe.{succ (max u2 u1), succ u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) V (coeBase.{succ (max u2 u1), succ u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) V (CategoryTheory.Subobject.hasCoe.{u1, u2} V _inst_1 B)))) (CategoryTheory.Limits.kernelSubobject.{u1, u2} V _inst_1 B C _inst_2 g _inst_4)))
but is expected to have type
  forall {V : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} V] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u2} V _inst_1] {A : V} {B : V} {C : V} (f : Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A B) [_inst_3 : CategoryTheory.Limits.HasImage.{u1, u2} V _inst_1 A B f] (g : Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) B C) [_inst_4 : CategoryTheory.Limits.HasKernel.{u1, u2} V _inst_1 _inst_2 B C g], (Eq.{succ u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A C) (CategoryTheory.CategoryStruct.comp.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1) A B C f g) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A C) 0 (Zero.toOfNat0.{u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A C) (CategoryTheory.Limits.HasZeroMorphisms.Zero.{u1, u2} V _inst_1 _inst_2 A C)))) -> (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) (Prefunctor.obj.{max (succ u2) (succ u1), succ u1, max u2 u1, u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (Preorder.smallCategory.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (CategoryTheory.instPartialOrderSubobject.{u1, u2} V _inst_1 B))))) V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) (CategoryTheory.Functor.toPrefunctor.{max u2 u1, u1, max u2 u1, u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (Preorder.smallCategory.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (CategoryTheory.instPartialOrderSubobject.{u1, u2} V _inst_1 B))) V _inst_1 (CategoryTheory.Subobject.underlying.{u1, u2} V _inst_1 B)) (CategoryTheory.Limits.imageSubobject.{u1, u2} V _inst_1 A B f _inst_3)) (Prefunctor.obj.{max (succ u2) (succ u1), succ u1, max u2 u1, u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (Preorder.smallCategory.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (CategoryTheory.instPartialOrderSubobject.{u1, u2} V _inst_1 B))))) V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) (CategoryTheory.Functor.toPrefunctor.{max u2 u1, u1, max u2 u1, u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (Preorder.smallCategory.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (CategoryTheory.instPartialOrderSubobject.{u1, u2} V _inst_1 B))) V _inst_1 (CategoryTheory.Subobject.underlying.{u1, u2} V _inst_1 B)) (CategoryTheory.Limits.kernelSubobject.{u1, u2} V _inst_1 B C _inst_2 g _inst_4)))
Case conversion may be inaccurate. Consider using '#align image_to_kernel imageToKernelₓ'. -/
/-- The canonical morphism `image_subobject f ⟶ kernel_subobject g` when `f ≫ g = 0`.
-/
def imageToKernel (w : f ≫ g = 0) : (imageSubobject f : V) ⟶ (kernelSubobject g : V) :=
  Subobject.ofLE _ _ (image_le_kernel _ _ w)deriving Mono
#align image_to_kernel imageToKernel

/- warning: subobject_of_le_as_image_to_kernel -> subobject_ofLE_as_imageToKernel is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} V] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u2} V _inst_1] {A : V} {B : V} {C : V} (f : Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A B) [_inst_3 : CategoryTheory.Limits.HasImage.{u1, u2} V _inst_1 A B f] (g : Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) B C) [_inst_4 : CategoryTheory.Limits.HasKernel.{u1, u2} V _inst_1 _inst_2 B C g] (w : Eq.{succ u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A C) (CategoryTheory.CategoryStruct.comp.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1) A B C f g) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A C) 0 (OfNat.mk.{u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A C) 0 (Zero.zero.{u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A C) (CategoryTheory.Limits.HasZeroMorphisms.hasZero.{u1, u2} V _inst_1 _inst_2 A C))))) (h : LE.le.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (Preorder.toHasLe.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (CategoryTheory.Subobject.partialOrder.{u2, u1} V _inst_1 B))) (CategoryTheory.Limits.imageSubobject.{u1, u2} V _inst_1 A B f _inst_3) (CategoryTheory.Limits.kernelSubobject.{u1, u2} V _inst_1 B C _inst_2 g _inst_4)), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) ((fun (a : Type.{max u2 u1}) (b : Type.{u2}) [self : HasLiftT.{succ (max u2 u1), succ u2} a b] => self.0) (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) V (HasLiftT.mk.{succ (max u2 u1), succ u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) V (CoeTCₓ.coe.{succ (max u2 u1), succ u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) V (coeBase.{succ (max u2 u1), succ u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) V (CategoryTheory.Subobject.hasCoe.{u1, u2} V _inst_1 B)))) (CategoryTheory.Limits.imageSubobject.{u1, u2} V _inst_1 A B f _inst_3)) ((fun (a : Type.{max u2 u1}) (b : Type.{u2}) [self : HasLiftT.{succ (max u2 u1), succ u2} a b] => self.0) (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) V (HasLiftT.mk.{succ (max u2 u1), succ u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) V (CoeTCₓ.coe.{succ (max u2 u1), succ u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) V (coeBase.{succ (max u2 u1), succ u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) V (CategoryTheory.Subobject.hasCoe.{u1, u2} V _inst_1 B)))) (CategoryTheory.Limits.kernelSubobject.{u1, u2} V _inst_1 B C _inst_2 g _inst_4))) (CategoryTheory.Subobject.ofLE.{u1, u2} V _inst_1 B (CategoryTheory.Limits.imageSubobject.{u1, u2} V _inst_1 A B f _inst_3) (CategoryTheory.Limits.kernelSubobject.{u1, u2} V _inst_1 B C _inst_2 g _inst_4) h) (imageToKernel.{u1, u2} V _inst_1 _inst_2 A B C f _inst_3 g _inst_4 w)
but is expected to have type
  forall {V : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} V] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u2} V _inst_1] {A : V} {B : V} {C : V} (f : Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A B) [_inst_3 : CategoryTheory.Limits.HasImage.{u1, u2} V _inst_1 A B f] (g : Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) B C) [_inst_4 : CategoryTheory.Limits.HasKernel.{u1, u2} V _inst_1 _inst_2 B C g] (w : Eq.{succ u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A C) (CategoryTheory.CategoryStruct.comp.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1) A B C f g) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A C) 0 (Zero.toOfNat0.{u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A C) (CategoryTheory.Limits.HasZeroMorphisms.Zero.{u1, u2} V _inst_1 _inst_2 A C)))) (h : LE.le.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (Preorder.toLE.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (CategoryTheory.instPartialOrderSubobject.{u1, u2} V _inst_1 B))) (CategoryTheory.Limits.imageSubobject.{u1, u2} V _inst_1 A B f _inst_3) (CategoryTheory.Limits.kernelSubobject.{u1, u2} V _inst_1 B C _inst_2 g _inst_4)), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) (Prefunctor.obj.{max (succ u2) (succ u1), succ u1, max u2 u1, u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (Preorder.smallCategory.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (CategoryTheory.instPartialOrderSubobject.{u1, u2} V _inst_1 B))))) V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) (CategoryTheory.Functor.toPrefunctor.{max u2 u1, u1, max u2 u1, u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (Preorder.smallCategory.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (CategoryTheory.instPartialOrderSubobject.{u1, u2} V _inst_1 B))) V _inst_1 (CategoryTheory.Subobject.underlying.{u1, u2} V _inst_1 B)) (CategoryTheory.Limits.imageSubobject.{u1, u2} V _inst_1 A B f _inst_3)) (Prefunctor.obj.{max (succ u2) (succ u1), succ u1, max u2 u1, u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (Preorder.smallCategory.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (CategoryTheory.instPartialOrderSubobject.{u1, u2} V _inst_1 B))))) V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) (CategoryTheory.Functor.toPrefunctor.{max u2 u1, u1, max u2 u1, u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (Preorder.smallCategory.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (CategoryTheory.instPartialOrderSubobject.{u1, u2} V _inst_1 B))) V _inst_1 (CategoryTheory.Subobject.underlying.{u1, u2} V _inst_1 B)) (CategoryTheory.Limits.kernelSubobject.{u1, u2} V _inst_1 B C _inst_2 g _inst_4))) (CategoryTheory.Subobject.ofLE.{u1, u2} V _inst_1 B (CategoryTheory.Limits.imageSubobject.{u1, u2} V _inst_1 A B f _inst_3) (CategoryTheory.Limits.kernelSubobject.{u1, u2} V _inst_1 B C _inst_2 g _inst_4) h) (imageToKernel.{u1, u2} V _inst_1 _inst_2 A B C f _inst_3 g _inst_4 w)
Case conversion may be inaccurate. Consider using '#align subobject_of_le_as_image_to_kernel subobject_ofLE_as_imageToKernelₓ'. -/
/-- Prefer `image_to_kernel`. -/
@[simp]
theorem subobject_ofLE_as_imageToKernel (w : f ≫ g = 0) (h) :
    Subobject.ofLE (imageSubobject f) (kernelSubobject g) h = imageToKernel f g w :=
  rfl
#align subobject_of_le_as_image_to_kernel subobject_ofLE_as_imageToKernel

/- warning: image_to_kernel_arrow -> imageToKernel_arrow is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align image_to_kernel_arrow imageToKernel_arrowₓ'. -/
@[simp, reassoc, elementwise]
theorem imageToKernel_arrow (w : f ≫ g = 0) :
    imageToKernel f g w ≫ (kernelSubobject g).arrow = (imageSubobject f).arrow := by
  simp [imageToKernel]
#align image_to_kernel_arrow imageToKernel_arrow

/- warning: factor_thru_image_subobject_comp_image_to_kernel -> factorThruImageSubobject_comp_imageToKernel is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} V] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u2} V _inst_1] {A : V} {B : V} {C : V} (f : Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A B) [_inst_3 : CategoryTheory.Limits.HasImage.{u1, u2} V _inst_1 A B f] (g : Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) B C) [_inst_4 : CategoryTheory.Limits.HasKernel.{u1, u2} V _inst_1 _inst_2 B C g] (w : Eq.{succ u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A C) (CategoryTheory.CategoryStruct.comp.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1) A B C f g) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A C) 0 (OfNat.mk.{u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A C) 0 (Zero.zero.{u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A C) (CategoryTheory.Limits.HasZeroMorphisms.hasZero.{u1, u2} V _inst_1 _inst_2 A C))))), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A ((fun (a : Type.{max u2 u1}) (b : Type.{u2}) [self : HasLiftT.{succ (max u2 u1), succ u2} a b] => self.0) (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) V (HasLiftT.mk.{succ (max u2 u1), succ u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) V (CoeTCₓ.coe.{succ (max u2 u1), succ u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) V (coeBase.{succ (max u2 u1), succ u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) V (CategoryTheory.Subobject.hasCoe.{u1, u2} V _inst_1 B)))) (CategoryTheory.Limits.kernelSubobject.{u1, u2} V _inst_1 B C _inst_2 g _inst_4))) (CategoryTheory.CategoryStruct.comp.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1) A ((fun (a : Type.{max u2 u1}) (b : Type.{u2}) [self : HasLiftT.{succ (max u2 u1), succ u2} a b] => self.0) (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) V (HasLiftT.mk.{succ (max u2 u1), succ u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) V (CoeTCₓ.coe.{succ (max u2 u1), succ u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) V (coeBase.{succ (max u2 u1), succ u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) V (CategoryTheory.Subobject.hasCoe.{u1, u2} V _inst_1 B)))) (CategoryTheory.Limits.imageSubobject.{u1, u2} V _inst_1 A B f _inst_3)) ((fun (a : Type.{max u2 u1}) (b : Type.{u2}) [self : HasLiftT.{succ (max u2 u1), succ u2} a b] => self.0) (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) V (HasLiftT.mk.{succ (max u2 u1), succ u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) V (CoeTCₓ.coe.{succ (max u2 u1), succ u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) V (coeBase.{succ (max u2 u1), succ u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) V (CategoryTheory.Subobject.hasCoe.{u1, u2} V _inst_1 B)))) (CategoryTheory.Limits.kernelSubobject.{u1, u2} V _inst_1 B C _inst_2 g _inst_4)) (CategoryTheory.Limits.factorThruImageSubobject.{u1, u2} V _inst_1 A B f _inst_3) (imageToKernel.{u1, u2} V _inst_1 _inst_2 A B C f _inst_3 g _inst_4 w)) (CategoryTheory.Limits.factorThruKernelSubobject.{u1, u2} V _inst_1 B C _inst_2 g _inst_4 A f w)
but is expected to have type
  forall {V : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} V] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u2} V _inst_1] {A : V} {B : V} {C : V} (f : Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A B) [_inst_3 : CategoryTheory.Limits.HasImage.{u1, u2} V _inst_1 A B f] (g : Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) B C) [_inst_4 : CategoryTheory.Limits.HasKernel.{u1, u2} V _inst_1 _inst_2 B C g] (w : Eq.{succ u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A C) (CategoryTheory.CategoryStruct.comp.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1) A B C f g) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A C) 0 (Zero.toOfNat0.{u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A C) (CategoryTheory.Limits.HasZeroMorphisms.Zero.{u1, u2} V _inst_1 _inst_2 A C)))), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A (Prefunctor.obj.{max (succ u2) (succ u1), succ u1, max u2 u1, u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (Preorder.smallCategory.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (CategoryTheory.instPartialOrderSubobject.{u1, u2} V _inst_1 B))))) V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) (CategoryTheory.Functor.toPrefunctor.{max u2 u1, u1, max u2 u1, u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (Preorder.smallCategory.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (CategoryTheory.instPartialOrderSubobject.{u1, u2} V _inst_1 B))) V _inst_1 (CategoryTheory.Subobject.underlying.{u1, u2} V _inst_1 B)) (CategoryTheory.Limits.kernelSubobject.{u1, u2} V _inst_1 B C _inst_2 g _inst_4))) (CategoryTheory.CategoryStruct.comp.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1) A (Prefunctor.obj.{max (succ u2) (succ u1), succ u1, max u2 u1, u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (Preorder.smallCategory.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (CategoryTheory.instPartialOrderSubobject.{u1, u2} V _inst_1 B))))) V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) (CategoryTheory.Functor.toPrefunctor.{max u2 u1, u1, max u2 u1, u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (Preorder.smallCategory.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (CategoryTheory.instPartialOrderSubobject.{u1, u2} V _inst_1 B))) V _inst_1 (CategoryTheory.Subobject.underlying.{u1, u2} V _inst_1 B)) (CategoryTheory.Limits.imageSubobject.{u1, u2} V _inst_1 A B f _inst_3)) (Prefunctor.obj.{max (succ u2) (succ u1), succ u1, max u2 u1, u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (Preorder.smallCategory.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (CategoryTheory.instPartialOrderSubobject.{u1, u2} V _inst_1 B))))) V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) (CategoryTheory.Functor.toPrefunctor.{max u2 u1, u1, max u2 u1, u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (Preorder.smallCategory.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (CategoryTheory.instPartialOrderSubobject.{u1, u2} V _inst_1 B))) V _inst_1 (CategoryTheory.Subobject.underlying.{u1, u2} V _inst_1 B)) (CategoryTheory.Limits.kernelSubobject.{u1, u2} V _inst_1 B C _inst_2 g _inst_4)) (CategoryTheory.Limits.factorThruImageSubobject.{u1, u2} V _inst_1 A B f _inst_3) (imageToKernel.{u1, u2} V _inst_1 _inst_2 A B C f _inst_3 g _inst_4 w)) (CategoryTheory.Limits.factorThruKernelSubobject.{u1, u2} V _inst_1 B C _inst_2 g _inst_4 A f w)
Case conversion may be inaccurate. Consider using '#align factor_thru_image_subobject_comp_image_to_kernel factorThruImageSubobject_comp_imageToKernelₓ'. -/
-- This is less useful as a `simp` lemma than it initially appears,
-- as it "loses" the information the morphism factors through the image.
theorem factorThruImageSubobject_comp_imageToKernel (w : f ≫ g = 0) :
    factorThruImageSubobject f ≫ imageToKernel f g w = factorThruKernelSubobject g f w :=
  by
  ext
  simp
#align factor_thru_image_subobject_comp_image_to_kernel factorThruImageSubobject_comp_imageToKernel

end

section

variable {A B C : V} (f : A ⟶ B) (g : B ⟶ C)

/- warning: image_to_kernel_zero_left -> imageToKernel_zero_left is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align image_to_kernel_zero_left imageToKernel_zero_leftₓ'. -/
@[simp]
theorem imageToKernel_zero_left [HasKernels V] [HasZeroObject V] {w} :
    imageToKernel (0 : A ⟶ B) g w = 0 := by
  ext
  simp
#align image_to_kernel_zero_left imageToKernel_zero_left

/- warning: image_to_kernel_zero_right -> imageToKernel_zero_right is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align image_to_kernel_zero_right imageToKernel_zero_rightₓ'. -/
theorem imageToKernel_zero_right [HasImages V] {w} :
    imageToKernel f (0 : B ⟶ C) w =
      (imageSubobject f).arrow ≫ inv (kernelSubobject (0 : B ⟶ C)).arrow :=
  by
  ext
  simp
#align image_to_kernel_zero_right imageToKernel_zero_right

section

variable [HasKernels V] [HasImages V]

/- warning: image_to_kernel_comp_right -> imageToKernel_comp_right is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align image_to_kernel_comp_right imageToKernel_comp_rightₓ'. -/
theorem imageToKernel_comp_right {D : V} (h : C ⟶ D) (w : f ≫ g = 0) :
    imageToKernel f (g ≫ h) (by simp [reassoc_of w]) =
      imageToKernel f g w ≫ Subobject.ofLE _ _ (kernelSubobject_comp_le g h) :=
  by
  ext
  simp
#align image_to_kernel_comp_right imageToKernel_comp_right

/- warning: image_to_kernel_comp_left -> imageToKernel_comp_left is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align image_to_kernel_comp_left imageToKernel_comp_leftₓ'. -/
theorem imageToKernel_comp_left {Z : V} (h : Z ⟶ A) (w : f ≫ g = 0) :
    imageToKernel (h ≫ f) g (by simp [w]) =
      Subobject.ofLE _ _ (imageSubobject_comp_le h f) ≫ imageToKernel f g w :=
  by
  ext
  simp
#align image_to_kernel_comp_left imageToKernel_comp_left

/- warning: image_to_kernel_comp_mono -> imageToKernel_comp_mono is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align image_to_kernel_comp_mono imageToKernel_comp_monoₓ'. -/
@[simp]
theorem imageToKernel_comp_mono {D : V} (h : C ⟶ D) [Mono h] (w) :
    imageToKernel f (g ≫ h) w =
      imageToKernel f g ((cancel_mono h).mp (by simpa using w : (f ≫ g) ≫ h = 0 ≫ h)) ≫
        (Subobject.isoOfEq _ _ (kernelSubobject_comp_mono g h)).inv :=
  by
  ext
  simp
#align image_to_kernel_comp_mono imageToKernel_comp_mono

/- warning: image_to_kernel_epi_comp -> imageToKernel_epi_comp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align image_to_kernel_epi_comp imageToKernel_epi_compₓ'. -/
@[simp]
theorem imageToKernel_epi_comp {Z : V} (h : Z ⟶ A) [Epi h] (w) :
    imageToKernel (h ≫ f) g w =
      Subobject.ofLE _ _ (imageSubobject_comp_le h f) ≫
        imageToKernel f g ((cancel_epi h).mp (by simpa using w : h ≫ f ≫ g = h ≫ 0)) :=
  by
  ext
  simp
#align image_to_kernel_epi_comp imageToKernel_epi_comp

end

/- warning: image_to_kernel_comp_hom_inv_comp -> imageToKernel_comp_hom_inv_comp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align image_to_kernel_comp_hom_inv_comp imageToKernel_comp_hom_inv_compₓ'. -/
@[simp]
theorem imageToKernel_comp_hom_inv_comp [HasEqualizers V] [HasImages V] {Z : V} {i : B ≅ Z} (w) :
    imageToKernel (f ≫ i.Hom) (i.inv ≫ g) w =
      (imageSubobjectCompIso _ _).Hom ≫
        imageToKernel f g (by simpa using w) ≫ (kernelSubobjectIsoComp i.inv g).inv :=
  by
  ext
  simp
#align image_to_kernel_comp_hom_inv_comp imageToKernel_comp_hom_inv_comp

open ZeroObject

/- warning: image_to_kernel_epi_of_zero_of_mono -> imageToKernel_epi_of_zero_of_mono is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align image_to_kernel_epi_of_zero_of_mono imageToKernel_epi_of_zero_of_monoₓ'. -/
/-- `image_to_kernel` for `A --0--> B --g--> C`, where `g` is a mono is itself an epi
(i.e. the sequence is exact at `B`).
-/
instance imageToKernel_epi_of_zero_of_mono [HasKernels V] [HasZeroObject V] [Mono g] :
    Epi (imageToKernel (0 : A ⟶ B) g (by simp)) :=
  epi_of_target_iso_zero _ (kernelSubobjectIso g ≪≫ kernel.ofMono g)
#align image_to_kernel_epi_of_zero_of_mono imageToKernel_epi_of_zero_of_mono

/- warning: image_to_kernel_epi_of_epi_of_zero -> imageToKernel_epi_of_epi_of_zero is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align image_to_kernel_epi_of_epi_of_zero imageToKernel_epi_of_epi_of_zeroₓ'. -/
/-- `image_to_kernel` for `A --f--> B --0--> C`, where `g` is an epi is itself an epi
(i.e. the sequence is exact at `B`).
-/
instance imageToKernel_epi_of_epi_of_zero [HasImages V] [Epi f] :
    Epi (imageToKernel f (0 : B ⟶ C) (by simp)) :=
  by
  simp only [imageToKernel_zero_right]
  haveI := epi_image_of_epi f
  rw [← image_subobject_arrow]
  refine' @epi_comp _ _ _ _ _ _ (epi_comp _ _) _ _
#align image_to_kernel_epi_of_epi_of_zero imageToKernel_epi_of_epi_of_zero

end

section

variable {A B C : V} (f : A ⟶ B) [HasImage f] (g : B ⟶ C) [HasKernel g]

/- warning: homology -> homology is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} V] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u2} V _inst_1] {A : V} {B : V} {C : V} (f : Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A B) [_inst_5 : CategoryTheory.Limits.HasImage.{u1, u2} V _inst_1 A B f] (g : Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) B C) [_inst_6 : CategoryTheory.Limits.HasKernel.{u1, u2} V _inst_1 _inst_2 B C g] (w : Eq.{succ u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A C) (CategoryTheory.CategoryStruct.comp.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1) A B C f g) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A C) 0 (OfNat.mk.{u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A C) 0 (Zero.zero.{u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A C) (CategoryTheory.Limits.HasZeroMorphisms.hasZero.{u1, u2} V _inst_1 _inst_2 A C))))) [_inst_7 : CategoryTheory.Limits.HasCokernel.{u1, u2} V _inst_1 _inst_2 ((fun (a : Type.{max u2 u1}) (b : Type.{u2}) [self : HasLiftT.{succ (max u2 u1), succ u2} a b] => self.0) (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) V (HasLiftT.mk.{succ (max u2 u1), succ u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) V (CoeTCₓ.coe.{succ (max u2 u1), succ u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) V (coeBase.{succ (max u2 u1), succ u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) V (CategoryTheory.Subobject.hasCoe.{u1, u2} V _inst_1 B)))) (CategoryTheory.Limits.imageSubobject.{u1, u2} V _inst_1 A B f _inst_5)) ((fun (a : Type.{max u2 u1}) (b : Type.{u2}) [self : HasLiftT.{succ (max u2 u1), succ u2} a b] => self.0) (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) V (HasLiftT.mk.{succ (max u2 u1), succ u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) V (CoeTCₓ.coe.{succ (max u2 u1), succ u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) V (coeBase.{succ (max u2 u1), succ u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) V (CategoryTheory.Subobject.hasCoe.{u1, u2} V _inst_1 B)))) (CategoryTheory.Limits.kernelSubobject.{u1, u2} V _inst_1 B C _inst_2 g _inst_6)) (imageToKernel.{u1, u2} V _inst_1 _inst_2 A B C f _inst_5 g _inst_6 w)], V
but is expected to have type
  forall {V : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} V] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u2} V _inst_1] {A : V} {B : V} {C : V} (f : Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A B) [_inst_5 : CategoryTheory.Limits.HasImage.{u1, u2} V _inst_1 A B f] (g : Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) B C) [_inst_6 : CategoryTheory.Limits.HasKernel.{u1, u2} V _inst_1 _inst_2 B C g] (w : Eq.{succ u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A C) (CategoryTheory.CategoryStruct.comp.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1) A B C f g) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A C) 0 (Zero.toOfNat0.{u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A C) (CategoryTheory.Limits.HasZeroMorphisms.Zero.{u1, u2} V _inst_1 _inst_2 A C)))) [_inst_7 : CategoryTheory.Limits.HasCokernel.{u1, u2} V _inst_1 _inst_2 (Prefunctor.obj.{max (succ u2) (succ u1), succ u1, max u2 u1, u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (Preorder.smallCategory.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (CategoryTheory.instPartialOrderSubobject.{u1, u2} V _inst_1 B))))) V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) (CategoryTheory.Functor.toPrefunctor.{max u2 u1, u1, max u2 u1, u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (Preorder.smallCategory.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (CategoryTheory.instPartialOrderSubobject.{u1, u2} V _inst_1 B))) V _inst_1 (CategoryTheory.Subobject.underlying.{u1, u2} V _inst_1 B)) (CategoryTheory.Limits.imageSubobject.{u1, u2} V _inst_1 A B f _inst_5)) (Prefunctor.obj.{max (succ u2) (succ u1), succ u1, max u2 u1, u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (Preorder.smallCategory.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (CategoryTheory.instPartialOrderSubobject.{u1, u2} V _inst_1 B))))) V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) (CategoryTheory.Functor.toPrefunctor.{max u2 u1, u1, max u2 u1, u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (Preorder.smallCategory.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (CategoryTheory.instPartialOrderSubobject.{u1, u2} V _inst_1 B))) V _inst_1 (CategoryTheory.Subobject.underlying.{u1, u2} V _inst_1 B)) (CategoryTheory.Limits.kernelSubobject.{u1, u2} V _inst_1 B C _inst_2 g _inst_6)) (imageToKernel.{u1, u2} V _inst_1 _inst_2 A B C f _inst_5 g _inst_6 w)], V
Case conversion may be inaccurate. Consider using '#align homology homologyₓ'. -/
/-- The homology of a pair of morphisms `f : A ⟶ B` and `g : B ⟶ C` satisfying `f ≫ g = 0`
is the cokernel of the `image_to_kernel` morphism for `f` and `g`.
-/
def homology {A B C : V} (f : A ⟶ B) [HasImage f] (g : B ⟶ C) [HasKernel g] (w : f ≫ g = 0)
    [HasCokernel (imageToKernel f g w)] : V :=
  cokernel (imageToKernel f g w)
#align homology homology

section

variable (w : f ≫ g = 0) [HasCokernel (imageToKernel f g w)]

/- warning: homology.π -> homology.π is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} V] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u2} V _inst_1] {A : V} {B : V} {C : V} (f : Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A B) [_inst_3 : CategoryTheory.Limits.HasImage.{u1, u2} V _inst_1 A B f] (g : Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) B C) [_inst_4 : CategoryTheory.Limits.HasKernel.{u1, u2} V _inst_1 _inst_2 B C g] (w : Eq.{succ u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A C) (CategoryTheory.CategoryStruct.comp.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1) A B C f g) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A C) 0 (OfNat.mk.{u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A C) 0 (Zero.zero.{u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A C) (CategoryTheory.Limits.HasZeroMorphisms.hasZero.{u1, u2} V _inst_1 _inst_2 A C))))) [_inst_5 : CategoryTheory.Limits.HasCokernel.{u1, u2} V _inst_1 _inst_2 ((fun (a : Type.{max u2 u1}) (b : Type.{u2}) [self : HasLiftT.{succ (max u2 u1), succ u2} a b] => self.0) (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) V (HasLiftT.mk.{succ (max u2 u1), succ u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) V (CoeTCₓ.coe.{succ (max u2 u1), succ u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) V (coeBase.{succ (max u2 u1), succ u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) V (CategoryTheory.Subobject.hasCoe.{u1, u2} V _inst_1 B)))) (CategoryTheory.Limits.imageSubobject.{u1, u2} V _inst_1 A B f _inst_3)) ((fun (a : Type.{max u2 u1}) (b : Type.{u2}) [self : HasLiftT.{succ (max u2 u1), succ u2} a b] => self.0) (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) V (HasLiftT.mk.{succ (max u2 u1), succ u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) V (CoeTCₓ.coe.{succ (max u2 u1), succ u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) V (coeBase.{succ (max u2 u1), succ u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) V (CategoryTheory.Subobject.hasCoe.{u1, u2} V _inst_1 B)))) (CategoryTheory.Limits.kernelSubobject.{u1, u2} V _inst_1 B C _inst_2 g _inst_4)) (imageToKernel.{u1, u2} V _inst_1 _inst_2 A B C f _inst_3 g _inst_4 w)], Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) ((fun (a : Type.{max u2 u1}) (b : Type.{u2}) [self : HasLiftT.{succ (max u2 u1), succ u2} a b] => self.0) (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) V (HasLiftT.mk.{succ (max u2 u1), succ u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) V (CoeTCₓ.coe.{succ (max u2 u1), succ u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) V (coeBase.{succ (max u2 u1), succ u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) V (CategoryTheory.Subobject.hasCoe.{u1, u2} V _inst_1 B)))) (CategoryTheory.Limits.kernelSubobject.{u1, u2} V _inst_1 B C _inst_2 g _inst_4)) (homology.{u1, u2} V _inst_1 _inst_2 A B C f _inst_3 g _inst_4 w _inst_5)
but is expected to have type
  forall {V : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} V] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u2} V _inst_1] {A : V} {B : V} {C : V} (f : Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A B) [_inst_3 : CategoryTheory.Limits.HasImage.{u1, u2} V _inst_1 A B f] (g : Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) B C) [_inst_4 : CategoryTheory.Limits.HasKernel.{u1, u2} V _inst_1 _inst_2 B C g] (w : Eq.{succ u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A C) (CategoryTheory.CategoryStruct.comp.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1) A B C f g) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A C) 0 (Zero.toOfNat0.{u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A C) (CategoryTheory.Limits.HasZeroMorphisms.Zero.{u1, u2} V _inst_1 _inst_2 A C)))) [_inst_5 : CategoryTheory.Limits.HasCokernel.{u1, u2} V _inst_1 _inst_2 (Prefunctor.obj.{max (succ u2) (succ u1), succ u1, max u2 u1, u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (Preorder.smallCategory.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (CategoryTheory.instPartialOrderSubobject.{u1, u2} V _inst_1 B))))) V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) (CategoryTheory.Functor.toPrefunctor.{max u2 u1, u1, max u2 u1, u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (Preorder.smallCategory.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (CategoryTheory.instPartialOrderSubobject.{u1, u2} V _inst_1 B))) V _inst_1 (CategoryTheory.Subobject.underlying.{u1, u2} V _inst_1 B)) (CategoryTheory.Limits.imageSubobject.{u1, u2} V _inst_1 A B f _inst_3)) (Prefunctor.obj.{max (succ u2) (succ u1), succ u1, max u2 u1, u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (Preorder.smallCategory.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (CategoryTheory.instPartialOrderSubobject.{u1, u2} V _inst_1 B))))) V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) (CategoryTheory.Functor.toPrefunctor.{max u2 u1, u1, max u2 u1, u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (Preorder.smallCategory.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (CategoryTheory.instPartialOrderSubobject.{u1, u2} V _inst_1 B))) V _inst_1 (CategoryTheory.Subobject.underlying.{u1, u2} V _inst_1 B)) (CategoryTheory.Limits.kernelSubobject.{u1, u2} V _inst_1 B C _inst_2 g _inst_4)) (imageToKernel.{u1, u2} V _inst_1 _inst_2 A B C f _inst_3 g _inst_4 w)], Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) (Prefunctor.obj.{max (succ u2) (succ u1), succ u1, max u2 u1, u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (Preorder.smallCategory.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (CategoryTheory.instPartialOrderSubobject.{u1, u2} V _inst_1 B))))) V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) (CategoryTheory.Functor.toPrefunctor.{max u2 u1, u1, max u2 u1, u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (Preorder.smallCategory.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (CategoryTheory.instPartialOrderSubobject.{u1, u2} V _inst_1 B))) V _inst_1 (CategoryTheory.Subobject.underlying.{u1, u2} V _inst_1 B)) (CategoryTheory.Limits.kernelSubobject.{u1, u2} V _inst_1 B C _inst_2 g _inst_4)) (homology.{u1, u2} V _inst_1 _inst_2 A B C f _inst_3 g _inst_4 w _inst_5)
Case conversion may be inaccurate. Consider using '#align homology.π homology.πₓ'. -/
/-- The morphism from cycles to homology. -/
def homology.π : (kernelSubobject g : V) ⟶ homology f g w :=
  cokernel.π _
#align homology.π homology.π

/- warning: homology.condition -> homology.condition is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homology.condition homology.conditionₓ'. -/
@[simp]
theorem homology.condition : imageToKernel f g w ≫ homology.π f g w = 0 :=
  cokernel.condition _
#align homology.condition homology.condition

/- warning: homology.desc -> homology.desc is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homology.desc homology.descₓ'. -/
/-- To construct a map out of homology, it suffices to construct a map out of the cycles
which vanishes on boundaries.
-/
def homology.desc {D : V} (k : (kernelSubobject g : V) ⟶ D) (p : imageToKernel f g w ≫ k = 0) :
    homology f g w ⟶ D :=
  cokernel.desc _ k p
#align homology.desc homology.desc

/- warning: homology.π_desc -> homology.π_desc is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homology.π_desc homology.π_descₓ'. -/
@[simp, reassoc, elementwise]
theorem homology.π_desc {D : V} (k : (kernelSubobject g : V) ⟶ D)
    (p : imageToKernel f g w ≫ k = 0) : homology.π f g w ≫ homology.desc f g w k p = k := by
  simp [homology.π, homology.desc]
#align homology.π_desc homology.π_desc

/- warning: homology.ext -> homology.ext is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homology.ext homology.extₓ'. -/
/-- To check two morphisms out of `homology f g w` are equal, it suffices to check on cycles. -/
@[ext]
theorem homology.ext {D : V} {k k' : homology f g w ⟶ D}
    (p : homology.π f g w ≫ k = homology.π f g w ≫ k') : k = k' :=
  by
  ext
  exact p
#align homology.ext homology.ext

/- warning: homology_of_zero_right -> homologyOfZeroRight is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homology_of_zero_right homologyOfZeroRightₓ'. -/
/-- The cokernel of the map `Im f ⟶ Ker 0` is isomorphic to the cokernel of `f.` -/
def homologyOfZeroRight [HasCokernel (imageToKernel f (0 : B ⟶ C) comp_zero)] [HasCokernel f]
    [HasCokernel (image.ι f)] [Epi (factorThruImage f)] :
    homology f (0 : B ⟶ C) comp_zero ≅ cokernel f :=
  (cokernel.mapIso _ _ (imageSubobjectIso _) ((kernelSubobjectIso 0).trans kernelZeroIsoSource)
        (by simp)).trans
    (cokernelImageι _)
#align homology_of_zero_right homologyOfZeroRight

/- warning: homology_of_zero_left -> homologyOfZeroLeft is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} V] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u2} V _inst_1] {A : V} {B : V} {C : V} (g : Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) B C) [_inst_4 : CategoryTheory.Limits.HasKernel.{u1, u2} V _inst_1 _inst_2 B C g] [_inst_6 : CategoryTheory.Limits.HasZeroObject.{u1, u2} V _inst_1] [_inst_7 : CategoryTheory.Limits.HasKernels.{u1, u2} V _inst_1 _inst_2] [_inst_8 : CategoryTheory.Limits.HasImage.{u1, u2} V _inst_1 A B (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A B) 0 (OfNat.mk.{u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A B) 0 (Zero.zero.{u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A B) (CategoryTheory.Limits.HasZeroMorphisms.hasZero.{u1, u2} V _inst_1 _inst_2 A B))))] [_inst_9 : CategoryTheory.Limits.HasCokernel.{u1, u2} V _inst_1 _inst_2 ((fun (a : Type.{max u2 u1}) (b : Type.{u2}) [self : HasLiftT.{succ (max u2 u1), succ u2} a b] => self.0) (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) V (HasLiftT.mk.{succ (max u2 u1), succ u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) V (CoeTCₓ.coe.{succ (max u2 u1), succ u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) V (coeBase.{succ (max u2 u1), succ u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) V (CategoryTheory.Subobject.hasCoe.{u1, u2} V _inst_1 B)))) (CategoryTheory.Limits.imageSubobject.{u1, u2} V _inst_1 A B (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A B) 0 (OfNat.mk.{u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A B) 0 (Zero.zero.{u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A B) (CategoryTheory.Limits.HasZeroMorphisms.hasZero.{u1, u2} V _inst_1 _inst_2 A B)))) _inst_8)) ((fun (a : Type.{max u2 u1}) (b : Type.{u2}) [self : HasLiftT.{succ (max u2 u1), succ u2} a b] => self.0) (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) V (HasLiftT.mk.{succ (max u2 u1), succ u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) V (CoeTCₓ.coe.{succ (max u2 u1), succ u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) V (coeBase.{succ (max u2 u1), succ u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) V (CategoryTheory.Subobject.hasCoe.{u1, u2} V _inst_1 B)))) (CategoryTheory.Limits.kernelSubobject.{u1, u2} V _inst_1 B C _inst_2 g _inst_4)) (imageToKernel.{u1, u2} V _inst_1 _inst_2 A B C (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A B) 0 (OfNat.mk.{u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A B) 0 (Zero.zero.{u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A B) (CategoryTheory.Limits.HasZeroMorphisms.hasZero.{u1, u2} V _inst_1 _inst_2 A B)))) _inst_8 g _inst_4 (CategoryTheory.Limits.zero_comp.{u1, u2} V _inst_1 _inst_2 A B C g))], CategoryTheory.Iso.{u1, u2} V _inst_1 (homology.{u1, u2} V _inst_1 _inst_2 A B C (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A B) 0 (OfNat.mk.{u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A B) 0 (Zero.zero.{u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A B) (CategoryTheory.Limits.HasZeroMorphisms.hasZero.{u1, u2} V _inst_1 _inst_2 A B)))) (CategoryTheory.Limits.hasImage_zero.{u1, u2} V _inst_1 _inst_2 _inst_6 A B) g (CategoryTheory.Limits.HasKernels.has_limit.{u1, u2} V _inst_1 _inst_2 _inst_7 B C g) (CategoryTheory.Limits.zero_comp.{u1, u2} V _inst_1 _inst_2 A B C g) _inst_9) (CategoryTheory.Limits.kernel.{u1, u2} V _inst_1 _inst_2 B C g _inst_4)
but is expected to have type
  forall {V : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} V] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u2} V _inst_1] {A : V} {B : V} {C : V} (g : Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) B C) [_inst_4 : CategoryTheory.Limits.HasKernel.{u1, u2} V _inst_1 _inst_2 B C g] [_inst_6 : CategoryTheory.Limits.HasZeroObject.{u1, u2} V _inst_1] [_inst_7 : CategoryTheory.Limits.HasKernels.{u1, u2} V _inst_1 _inst_2] [_inst_8 : CategoryTheory.Limits.HasImage.{u1, u2} V _inst_1 A B (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A B) 0 (Zero.toOfNat0.{u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A B) (CategoryTheory.Limits.HasZeroMorphisms.Zero.{u1, u2} V _inst_1 _inst_2 A B)))] [_inst_9 : CategoryTheory.Limits.HasCokernel.{u1, u2} V _inst_1 _inst_2 (Prefunctor.obj.{max (succ u2) (succ u1), succ u1, max u2 u1, u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (Preorder.smallCategory.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (CategoryTheory.instPartialOrderSubobject.{u1, u2} V _inst_1 B))))) V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) (CategoryTheory.Functor.toPrefunctor.{max u2 u1, u1, max u2 u1, u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (Preorder.smallCategory.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (CategoryTheory.instPartialOrderSubobject.{u1, u2} V _inst_1 B))) V _inst_1 (CategoryTheory.Subobject.underlying.{u1, u2} V _inst_1 B)) (CategoryTheory.Limits.imageSubobject.{u1, u2} V _inst_1 A B (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A B) 0 (Zero.toOfNat0.{u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A B) (CategoryTheory.Limits.HasZeroMorphisms.Zero.{u1, u2} V _inst_1 _inst_2 A B))) _inst_8)) (Prefunctor.obj.{max (succ u2) (succ u1), succ u1, max u2 u1, u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (Preorder.smallCategory.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (CategoryTheory.instPartialOrderSubobject.{u1, u2} V _inst_1 B))))) V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) (CategoryTheory.Functor.toPrefunctor.{max u2 u1, u1, max u2 u1, u2} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (Preorder.smallCategory.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} V _inst_1 B) (CategoryTheory.instPartialOrderSubobject.{u1, u2} V _inst_1 B))) V _inst_1 (CategoryTheory.Subobject.underlying.{u1, u2} V _inst_1 B)) (CategoryTheory.Limits.kernelSubobject.{u1, u2} V _inst_1 B C _inst_2 g _inst_4)) (imageToKernel.{u1, u2} V _inst_1 _inst_2 A B C (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A B) 0 (Zero.toOfNat0.{u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A B) (CategoryTheory.Limits.HasZeroMorphisms.Zero.{u1, u2} V _inst_1 _inst_2 A B))) _inst_8 g _inst_4 (CategoryTheory.Limits.zero_comp.{u1, u2} V _inst_1 _inst_2 A B C g))], CategoryTheory.Iso.{u1, u2} V _inst_1 (homology.{u1, u2} V _inst_1 _inst_2 A B C (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A B) 0 (Zero.toOfNat0.{u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) A B) (CategoryTheory.Limits.HasZeroMorphisms.Zero.{u1, u2} V _inst_1 _inst_2 A B))) _inst_8 g _inst_4 (CategoryTheory.Limits.zero_comp.{u1, u2} V _inst_1 _inst_2 A B C g) _inst_9) (CategoryTheory.Limits.kernel.{u1, u2} V _inst_1 _inst_2 B C g _inst_4)
Case conversion may be inaccurate. Consider using '#align homology_of_zero_left homologyOfZeroLeftₓ'. -/
/-- The kernel of the map `Im 0 ⟶ Ker f` is isomorphic to the kernel of `f.` -/
def homologyOfZeroLeft [HasZeroObject V] [HasKernels V] [HasImage (0 : A ⟶ B)]
    [HasCokernel (imageToKernel (0 : A ⟶ B) g zero_comp)] :
    homology (0 : A ⟶ B) g zero_comp ≅ kernel g :=
  ((cokernelIsoOfEq <| imageToKernel_zero_left _).trans cokernelZeroIsoTarget).trans
    (kernelSubobjectIso _)
#align homology_of_zero_left homologyOfZeroLeft

/- warning: homology_zero_zero -> homologyZeroZero is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homology_zero_zero homologyZeroZeroₓ'. -/
/-- `homology 0 0 _` is just the middle object. -/
@[simps]
def homologyZeroZero [HasZeroObject V] [HasImage (0 : A ⟶ B)]
    [HasCokernel (imageToKernel (0 : A ⟶ B) (0 : B ⟶ C) (by simp))] :
    homology (0 : A ⟶ B) (0 : B ⟶ C) (by simp) ≅ B
    where
  Hom := homology.desc (0 : A ⟶ B) (0 : B ⟶ C) (by simp) (kernelSubobject 0).arrow (by simp)
  inv := inv (kernelSubobject 0).arrow ≫ homology.π _ _ _
#align homology_zero_zero homologyZeroZero

end

section

variable {f g} (w : f ≫ g = 0) {A' B' C' : V} {f' : A' ⟶ B'} [HasImage f'] {g' : B' ⟶ C'}
  [HasKernel g'] (w' : f' ≫ g' = 0) (α : Arrow.mk f ⟶ Arrow.mk f') [HasImageMap α]
  (β : Arrow.mk g ⟶ Arrow.mk g') {A₁ B₁ C₁ : V} {f₁ : A₁ ⟶ B₁} [HasImage f₁] {g₁ : B₁ ⟶ C₁}
  [HasKernel g₁] (w₁ : f₁ ≫ g₁ = 0) {A₂ B₂ C₂ : V} {f₂ : A₂ ⟶ B₂} [HasImage f₂] {g₂ : B₂ ⟶ C₂}
  [HasKernel g₂] (w₂ : f₂ ≫ g₂ = 0) {A₃ B₃ C₃ : V} {f₃ : A₃ ⟶ B₃} [HasImage f₃] {g₃ : B₃ ⟶ C₃}
  [HasKernel g₃] (w₃ : f₃ ≫ g₃ = 0) (α₁ : Arrow.mk f₁ ⟶ Arrow.mk f₂) [HasImageMap α₁]
  (β₁ : Arrow.mk g₁ ⟶ Arrow.mk g₂) (α₂ : Arrow.mk f₂ ⟶ Arrow.mk f₃) [HasImageMap α₂]
  (β₂ : Arrow.mk g₂ ⟶ Arrow.mk g₃)

#print imageSubobjectMap_comp_imageToKernel /-
/-- Given compatible commutative squares between
a pair `f g` and a pair `f' g'` satisfying `f ≫ g = 0` and `f' ≫ g' = 0`,
the `image_to_kernel` morphisms intertwine the induced map on kernels and the induced map on images.
-/
@[reassoc]
theorem imageSubobjectMap_comp_imageToKernel (p : α.right = β.left) :
    imageToKernel f g w ≫ kernelSubobjectMap β = imageSubobjectMap α ≫ imageToKernel f' g' w' :=
  by
  ext
  simp [p]
#align image_subobject_map_comp_image_to_kernel imageSubobjectMap_comp_imageToKernel
-/

variable [HasCokernel (imageToKernel f g w)] [HasCokernel (imageToKernel f' g' w')]

variable [HasCokernel (imageToKernel f₁ g₁ w₁)]

variable [HasCokernel (imageToKernel f₂ g₂ w₂)]

variable [HasCokernel (imageToKernel f₃ g₃ w₃)]

#print homology.map /-
/-- Given compatible commutative squares between
a pair `f g` and a pair `f' g'` satisfying `f ≫ g = 0` and `f' ≫ g' = 0`,
we get a morphism on homology.
-/
def homology.map (p : α.right = β.left) : homology f g w ⟶ homology f' g' w' :=
  cokernel.desc _ (kernelSubobjectMap β ≫ cokernel.π _)
    (by
      rw [imageSubobjectMap_comp_imageToKernel_assoc w w' α β p]
      simp only [cokernel.condition, comp_zero])
#align homology.map homology.map
-/

#print homology.π_map /-
@[simp, reassoc, elementwise]
theorem homology.π_map (p : α.right = β.left) :
    homology.π f g w ≫ homology.map w w' α β p = kernelSubobjectMap β ≫ homology.π f' g' w' := by
  simp only [homology.π, homology.map, cokernel.π_desc]
#align homology.π_map homology.π_map
-/

#print homology.map_desc /-
@[simp, reassoc, elementwise]
theorem homology.map_desc (p : α.right = β.left) {D : V} (k : (kernelSubobject g' : V) ⟶ D)
    (z : imageToKernel f' g' w' ≫ k = 0) :
    homology.map w w' α β p ≫ homology.desc f' g' w' k z =
      homology.desc f g w (kernelSubobjectMap β ≫ k)
        (by simp only [imageSubobjectMap_comp_imageToKernel_assoc w w' α β p, z, comp_zero]) :=
  by ext <;> simp only [homology.π_desc, homology.π_map_assoc]
#align homology.map_desc homology.map_desc
-/

/- warning: homology.map_id -> homology.map_id is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homology.map_id homology.map_idₓ'. -/
@[simp]
theorem homology.map_id : homology.map w w (𝟙 _) (𝟙 _) rfl = 𝟙 _ := by
  ext <;> simp only [homology.π_map, kernel_subobject_map_id, category.id_comp, category.comp_id]
#align homology.map_id homology.map_id

/- warning: homology.comp_right_eq_comp_left -> homology.comp_right_eq_comp_left is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homology.comp_right_eq_comp_left homology.comp_right_eq_comp_leftₓ'. -/
/-- Auxiliary lemma for homology computations. -/
theorem homology.comp_right_eq_comp_left {V : Type _} [Category V] {A₁ B₁ C₁ A₂ B₂ C₂ A₃ B₃ C₃ : V}
    {f₁ : A₁ ⟶ B₁} {g₁ : B₁ ⟶ C₁} {f₂ : A₂ ⟶ B₂} {g₂ : B₂ ⟶ C₂} {f₃ : A₃ ⟶ B₃} {g₃ : B₃ ⟶ C₃}
    {α₁ : Arrow.mk f₁ ⟶ Arrow.mk f₂} {β₁ : Arrow.mk g₁ ⟶ Arrow.mk g₂}
    {α₂ : Arrow.mk f₂ ⟶ Arrow.mk f₃} {β₂ : Arrow.mk g₂ ⟶ Arrow.mk g₃} (p₁ : α₁.right = β₁.left)
    (p₂ : α₂.right = β₂.left) : (α₁ ≫ α₂).right = (β₁ ≫ β₂).left := by
  simp only [comma.comp_left, comma.comp_right, p₁, p₂]
#align homology.comp_right_eq_comp_left homology.comp_right_eq_comp_left

#print homology.map_comp /-
@[reassoc]
theorem homology.map_comp (p₁ : α₁.right = β₁.left) (p₂ : α₂.right = β₂.left) :
    homology.map w₁ w₂ α₁ β₁ p₁ ≫ homology.map w₂ w₃ α₂ β₂ p₂ =
      homology.map w₁ w₃ (α₁ ≫ α₂) (β₁ ≫ β₂) (homology.comp_right_eq_comp_left p₁ p₂) :=
  by
  ext <;>
    simp only [kernel_subobject_map_comp, homology.π_map_assoc, homology.π_map, category.assoc]
#align homology.map_comp homology.map_comp
-/

/- warning: homology.map_iso -> homology.mapIso is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homology.map_iso homology.mapIsoₓ'. -/
/-- An isomorphism between two three-term complexes induces an isomorphism on homology. -/
def homology.mapIso (α : Arrow.mk f₁ ≅ Arrow.mk f₂) (β : Arrow.mk g₁ ≅ Arrow.mk g₂)
    (p : α.Hom.right = β.Hom.left) : homology f₁ g₁ w₁ ≅ homology f₂ g₂ w₂
    where
  Hom := homology.map w₁ w₂ α.Hom β.Hom p
  inv :=
    homology.map w₂ w₁ α.inv β.inv
      (by
        rw [← cancel_mono α.hom.right, ← comma.comp_right, α.inv_hom_id, comma.id_right, p, ←
          comma.comp_left, β.inv_hom_id, comma.id_left]
        rfl)
  hom_inv_id' := by
    rw [homology.map_comp]
    convert homology.map_id _ <;> rw [iso.hom_inv_id]
  inv_hom_id' := by
    rw [homology.map_comp]
    convert homology.map_id _ <;> rw [iso.inv_hom_id]
#align homology.map_iso homology.mapIso

end

end

section

variable {A B C : V} {f : A ⟶ B} {g : B ⟶ C} (w : f ≫ g = 0) {f' : A ⟶ B} {g' : B ⟶ C}
  (w' : f' ≫ g' = 0) [HasKernels V] [HasCokernels V] [HasImages V] [HasImageMaps V]

/- ./././Mathport/Syntax/Translate/Expr.lean:330:4: warning: unsupported (TODO): `[tacs] -/
/-- Custom tactic to golf and speedup boring proofs in `homology.congr`. -/
private unsafe def aux_tac : tactic Unit :=
  sorry

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.1444910979.aux_tac -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.1444910979.aux_tac -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.1444910979.aux_tac -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.1444910979.aux_tac -/
#print homology.congr /-
/-- `homology f g w ≅ homology f' g' w'` if `f = f'` and `g = g'`.
(Note the objects are not changing here.)
-/
@[simps]
def homology.congr (pf : f = f') (pg : g = g') : homology f g w ≅ homology f' g' w'
    where
  Hom :=
    homology.map w w'
      ⟨𝟙 _, 𝟙 _, by
        run_tac
          aux_tac⟩
      ⟨𝟙 _, 𝟙 _, by
        run_tac
          aux_tac⟩
      rfl
  inv :=
    homology.map w' w
      ⟨𝟙 _, 𝟙 _, by
        run_tac
          aux_tac⟩
      ⟨𝟙 _, 𝟙 _, by
        run_tac
          aux_tac⟩
      rfl
  hom_inv_id' := by
    cases pf; cases pg; rw [homology.map_comp, ← homology.map_id]
    congr 1 <;> exact category.comp_id _
  inv_hom_id' := by
    cases pf; cases pg; rw [homology.map_comp, ← homology.map_id]
    congr 1 <;> exact category.comp_id _
#align homology.congr homology.congr
-/

end

/-!
We provide a variant `image_to_kernel' : image f ⟶ kernel g`,
and use this to give alternative formulas for `homology f g w`.
-/


section imageToKernel'

variable {A B C : V} (f : A ⟶ B) (g : B ⟶ C) (w : f ≫ g = 0) [HasKernels V] [HasImages V]

#print imageToKernel' /-
/-- While `image_to_kernel f g w` provides a morphism
`image_subobject f ⟶ kernel_subobject g`
in terms of the subobject API,
this variant provides a morphism
`image f ⟶ kernel g`,
which is sometimes more convenient.
-/
def imageToKernel' (w : f ≫ g = 0) : image f ⟶ kernel g :=
  kernel.lift g (image.ι f)
    (by
      ext
      simpa using w)
#align image_to_kernel' imageToKernel'
-/

/- warning: image_subobject_iso_image_to_kernel' -> imageSubobjectIso_imageToKernel' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align image_subobject_iso_image_to_kernel' imageSubobjectIso_imageToKernel'ₓ'. -/
@[simp]
theorem imageSubobjectIso_imageToKernel' (w : f ≫ g = 0) :
    (imageSubobjectIso f).Hom ≫ imageToKernel' f g w =
      imageToKernel f g w ≫ (kernelSubobjectIso g).Hom :=
  by
  ext
  simp [imageToKernel']
#align image_subobject_iso_image_to_kernel' imageSubobjectIso_imageToKernel'

/- warning: image_to_kernel'_kernel_subobject_iso -> imageToKernel'_kernelSubobjectIso is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align image_to_kernel'_kernel_subobject_iso imageToKernel'_kernelSubobjectIsoₓ'. -/
@[simp]
theorem imageToKernel'_kernelSubobjectIso (w : f ≫ g = 0) :
    imageToKernel' f g w ≫ (kernelSubobjectIso g).inv =
      (imageSubobjectIso f).inv ≫ imageToKernel f g w :=
  by
  ext
  simp [imageToKernel']
#align image_to_kernel'_kernel_subobject_iso imageToKernel'_kernelSubobjectIso

variable [HasCokernels V]

#print homologyIsoCokernelImageToKernel' /-
/-- `homology f g w` can be computed as the cokernel of `image_to_kernel' f g w`.
-/
def homologyIsoCokernelImageToKernel' (w : f ≫ g = 0) :
    homology f g w ≅ cokernel (imageToKernel' f g w)
    where
  Hom :=
    cokernel.map _ _ (imageSubobjectIso f).Hom (kernelSubobjectIso g).Hom
      (by simp only [imageSubobjectIso_imageToKernel'])
  inv :=
    cokernel.map _ _ (imageSubobjectIso f).inv (kernelSubobjectIso g).inv
      (by simp only [imageToKernel'_kernelSubobjectIso])
  hom_inv_id' := by
    apply coequalizer.hom_ext
    simp only [iso.hom_inv_id_assoc, cokernel.π_desc, cokernel.π_desc_assoc, category.assoc,
      coequalizer_as_cokernel]
    exact (category.comp_id _).symm
  inv_hom_id' := by
    ext1
    simp only [iso.inv_hom_id_assoc, cokernel.π_desc, category.comp_id, cokernel.π_desc_assoc,
      category.assoc]
#align homology_iso_cokernel_image_to_kernel' homologyIsoCokernelImageToKernel'
-/

variable [HasEqualizers V]

#print homologyIsoCokernelLift /-
/-- `homology f g w` can be computed as the cokernel of `kernel.lift g f w`.
-/
def homologyIsoCokernelLift (w : f ≫ g = 0) : homology f g w ≅ cokernel (kernel.lift g f w) :=
  by
  refine' homologyIsoCokernelImageToKernel' f g w ≪≫ _
  have p : factor_thru_image f ≫ imageToKernel' f g w = kernel.lift g f w :=
    by
    ext
    simp [imageToKernel']
  exact (cokernel_epi_comp _ _).symm ≪≫ cokernel_iso_of_eq p
#align homology_iso_cokernel_lift homologyIsoCokernelLift
-/

end imageToKernel'

