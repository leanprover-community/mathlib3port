/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module category_theory.limits.preserves.shapes.kernels
! leanprover-community/mathlib commit 10bf4f825ad729c5653adc039dafa3622e7f93c9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.Shapes.Kernels
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
# Preserving (co)kernels

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Constructions to relate the notions of preserving (co)kernels and reflecting (co)kernels
to concrete (co)forks.

In particular, we show that `kernel_comparison f g G` is an isomorphism iff `G` preserves
the limit of the parallel pair `f,0`, as well as the dual result.
-/


noncomputable section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] [HasZeroMorphisms C]

variable {D : Type u₂} [Category.{v₂} D] [HasZeroMorphisms D]

variable (G : C ⥤ D) [Functor.PreservesZeroMorphisms G]

namespace CategoryTheory.Limits

section Kernels

variable {X Y Z : C} {f : X ⟶ Y} {h : Z ⟶ X} (w : h ≫ f = 0)

/- warning: category_theory.limits.is_limit_map_cone_fork_equiv' -> CategoryTheory.Limits.isLimitMapConeForkEquiv' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.is_limit_map_cone_fork_equiv' CategoryTheory.Limits.isLimitMapConeForkEquiv'ₓ'. -/
/-- The map of a kernel fork is a limit iff
the kernel fork consisting of the mapped morphisms is a limit.
This essentially lets us commute `kernel_fork.of_ι` with `functor.map_cone`.

This is a variant of `is_limit_map_cone_fork_equiv` for equalizers,
which we can't use directly between `G.map 0 = 0` does not hold definitionally.
-/
def isLimitMapConeForkEquiv' :
    IsLimit (G.mapCone (KernelFork.ofι h w)) ≃
      IsLimit
        (KernelFork.ofι (G.map h) (by simp only [← G.map_comp, w, functor.map_zero]) :
          Fork (G.map f) 0) :=
  by
  refine' (is_limit.postcompose_hom_equiv _ _).symm.trans (is_limit.equiv_iso_limit _)
  refine' parallel_pair.ext (iso.refl _) (iso.refl _) _ _ <;> simp
  refine' fork.ext (iso.refl _) _
  simp [fork.ι]
#align category_theory.limits.is_limit_map_cone_fork_equiv' CategoryTheory.Limits.isLimitMapConeForkEquiv'

/- warning: category_theory.limits.is_limit_fork_map_of_is_limit' -> CategoryTheory.Limits.isLimitForkMapOfIsLimit' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.is_limit_fork_map_of_is_limit' CategoryTheory.Limits.isLimitForkMapOfIsLimit'ₓ'. -/
/-- The property of preserving kernels expressed in terms of kernel forks.

This is a variant of `is_limit_fork_map_of_is_limit` for equalizers,
which we can't use directly between `G.map 0 = 0` does not hold definitionally.
-/
def isLimitForkMapOfIsLimit' [PreservesLimit (parallelPair f 0) G]
    (l : IsLimit (KernelFork.ofι h w)) :
    IsLimit
      (KernelFork.ofι (G.map h) (by simp only [← G.map_comp, w, functor.map_zero]) :
        Fork (G.map f) 0) :=
  isLimitMapConeForkEquiv' G w (PreservesLimit.preserves l)
#align category_theory.limits.is_limit_fork_map_of_is_limit' CategoryTheory.Limits.isLimitForkMapOfIsLimit'

variable (f) [HasKernel f]

/- warning: category_theory.limits.is_limit_of_has_kernel_of_preserves_limit -> CategoryTheory.Limits.isLimitOfHasKernelOfPreservesLimit is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.is_limit_of_has_kernel_of_preserves_limit CategoryTheory.Limits.isLimitOfHasKernelOfPreservesLimitₓ'. -/
/-- If `G` preserves kernels and `C` has them, then the fork constructed of the mapped morphisms of
a kernel fork is a limit.
-/
def isLimitOfHasKernelOfPreservesLimit [PreservesLimit (parallelPair f 0) G] :
    IsLimit
      (Fork.ofι (G.map (kernel.ι f))
          (by simp only [← G.map_comp, equalizer.condition, comp_zero, functor.map_zero]) :
        Fork (G.map f) 0) :=
  isLimitForkMapOfIsLimit' G (kernel.condition f) (kernelIsKernel f)
#align category_theory.limits.is_limit_of_has_kernel_of_preserves_limit CategoryTheory.Limits.isLimitOfHasKernelOfPreservesLimit

instance [PreservesLimit (parallelPair f 0) G] : HasKernel (G.map f)
    where exists_limit := ⟨⟨_, isLimitOfHasKernelOfPreservesLimit G f⟩⟩

variable [HasKernel (G.map f)]

/- warning: category_theory.limits.preserves_kernel.of_iso_comparison -> CategoryTheory.Limits.PreservesKernel.ofIsoComparison is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u3} C _inst_1] {D : Type.{u4}} [_inst_3 : CategoryTheory.Category.{u2, u4} D] [_inst_4 : CategoryTheory.Limits.HasZeroMorphisms.{u2, u4} D _inst_3] (G : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_3) [_inst_5 : CategoryTheory.Functor.PreservesZeroMorphisms.{u1, u2, u3, u4} C _inst_1 D _inst_3 _inst_2 _inst_4 G] {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) [_inst_6 : CategoryTheory.Limits.HasKernel.{u1, u3} C _inst_1 _inst_2 X Y f] [_inst_7 : CategoryTheory.Limits.HasKernel.{u2, u4} D _inst_3 _inst_4 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_3 G X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_3 G Y) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_3 G X Y f)] [i : CategoryTheory.IsIso.{u2, u4} D _inst_3 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_3 G (CategoryTheory.Limits.kernel.{u1, u3} C _inst_1 _inst_2 X Y f _inst_6)) (CategoryTheory.Limits.kernel.{u2, u4} D _inst_3 _inst_4 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_3 G X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_3 G Y) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_3 G X Y f) _inst_7) (CategoryTheory.Limits.kernelComparison.{u1, u2, u3, u4} C _inst_1 _inst_2 X Y f D _inst_3 _inst_4 G _inst_5 _inst_6 _inst_7)], CategoryTheory.Limits.PreservesLimit.{0, 0, u1, u2, u3, u4} C _inst_1 D _inst_3 CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory (CategoryTheory.Limits.parallelPair.{u1, u3} C _inst_1 X Y f (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) 0 (OfNat.mk.{u1} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) 0 (Zero.zero.{u1} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) (CategoryTheory.Limits.HasZeroMorphisms.hasZero.{u1, u3} C _inst_1 _inst_2 X Y))))) G
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u3} C _inst_1] {D : Type.{u4}} [_inst_3 : CategoryTheory.Category.{u2, u4} D] [_inst_4 : CategoryTheory.Limits.HasZeroMorphisms.{u2, u4} D _inst_3] (G : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_3) [_inst_5 : CategoryTheory.Functor.PreservesZeroMorphisms.{u1, u2, u3, u4} C _inst_1 D _inst_3 _inst_2 _inst_4 G] {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) [_inst_6 : CategoryTheory.Limits.HasKernel.{u1, u3} C _inst_1 _inst_2 X Y f] [_inst_7 : CategoryTheory.Limits.HasKernel.{u2, u4} D _inst_3 _inst_4 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_3 G) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_3 G) Y) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_3 G) X Y f)] [i : CategoryTheory.IsIso.{u2, u4} D _inst_3 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_3 G) (CategoryTheory.Limits.kernel.{u1, u3} C _inst_1 _inst_2 X Y f _inst_6)) (CategoryTheory.Limits.kernel.{u2, u4} D _inst_3 _inst_4 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_3 G) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_3 G) Y) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_3 G) X Y f) _inst_7) (CategoryTheory.Limits.kernelComparison.{u1, u2, u3, u4} C _inst_1 _inst_2 X Y f D _inst_3 _inst_4 G _inst_5 _inst_6 _inst_7)], CategoryTheory.Limits.PreservesLimit.{0, 0, u1, u2, u3, u4} C _inst_1 D _inst_3 CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory (CategoryTheory.Limits.parallelPair.{u1, u3} C _inst_1 X Y f (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) 0 (Zero.toOfNat0.{u1} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) (CategoryTheory.Limits.HasZeroMorphisms.Zero.{u1, u3} C _inst_1 _inst_2 X Y)))) G
Case conversion may be inaccurate. Consider using '#align category_theory.limits.preserves_kernel.of_iso_comparison CategoryTheory.Limits.PreservesKernel.ofIsoComparisonₓ'. -/
/-- If the kernel comparison map for `G` at `f` is an isomorphism, then `G` preserves the
kernel of `f`.
-/
def PreservesKernel.ofIsoComparison [i : IsIso (kernelComparison f G)] :
    PreservesLimit (parallelPair f 0) G :=
  by
  apply preserves_limit_of_preserves_limit_cone (kernel_is_kernel f)
  apply (is_limit_map_cone_fork_equiv' G (kernel.condition f)).symm _
  apply is_limit.of_point_iso (kernel_is_kernel (G.map f))
  exact i
#align category_theory.limits.preserves_kernel.of_iso_comparison CategoryTheory.Limits.PreservesKernel.ofIsoComparison

variable [PreservesLimit (parallelPair f 0) G]

/- warning: category_theory.limits.preserves_kernel.iso -> CategoryTheory.Limits.PreservesKernel.iso is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u3} C _inst_1] {D : Type.{u4}} [_inst_3 : CategoryTheory.Category.{u2, u4} D] [_inst_4 : CategoryTheory.Limits.HasZeroMorphisms.{u2, u4} D _inst_3] (G : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_3) [_inst_5 : CategoryTheory.Functor.PreservesZeroMorphisms.{u1, u2, u3, u4} C _inst_1 D _inst_3 _inst_2 _inst_4 G] {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) [_inst_6 : CategoryTheory.Limits.HasKernel.{u1, u3} C _inst_1 _inst_2 X Y f] [_inst_7 : CategoryTheory.Limits.HasKernel.{u2, u4} D _inst_3 _inst_4 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_3 G X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_3 G Y) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_3 G X Y f)] [_inst_8 : CategoryTheory.Limits.PreservesLimit.{0, 0, u1, u2, u3, u4} C _inst_1 D _inst_3 CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory (CategoryTheory.Limits.parallelPair.{u1, u3} C _inst_1 X Y f (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) 0 (OfNat.mk.{u1} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) 0 (Zero.zero.{u1} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) (CategoryTheory.Limits.HasZeroMorphisms.hasZero.{u1, u3} C _inst_1 _inst_2 X Y))))) G], CategoryTheory.Iso.{u2, u4} D _inst_3 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_3 G (CategoryTheory.Limits.kernel.{u1, u3} C _inst_1 _inst_2 X Y f _inst_6)) (CategoryTheory.Limits.kernel.{u2, u4} D _inst_3 _inst_4 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_3 G X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_3 G Y) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_3 G X Y f) _inst_7)
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u3} C _inst_1] {D : Type.{u4}} [_inst_3 : CategoryTheory.Category.{u2, u4} D] [_inst_4 : CategoryTheory.Limits.HasZeroMorphisms.{u2, u4} D _inst_3] (G : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_3) [_inst_5 : CategoryTheory.Functor.PreservesZeroMorphisms.{u1, u2, u3, u4} C _inst_1 D _inst_3 _inst_2 _inst_4 G] {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) [_inst_6 : CategoryTheory.Limits.HasKernel.{u1, u3} C _inst_1 _inst_2 X Y f] [_inst_7 : CategoryTheory.Limits.HasKernel.{u2, u4} D _inst_3 _inst_4 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_3 G) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_3 G) Y) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_3 G) X Y f)] [_inst_8 : CategoryTheory.Limits.PreservesLimit.{0, 0, u1, u2, u3, u4} C _inst_1 D _inst_3 CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory (CategoryTheory.Limits.parallelPair.{u1, u3} C _inst_1 X Y f (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) 0 (Zero.toOfNat0.{u1} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) (CategoryTheory.Limits.HasZeroMorphisms.Zero.{u1, u3} C _inst_1 _inst_2 X Y)))) G], CategoryTheory.Iso.{u2, u4} D _inst_3 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_3 G) (CategoryTheory.Limits.kernel.{u1, u3} C _inst_1 _inst_2 X Y f _inst_6)) (CategoryTheory.Limits.kernel.{u2, u4} D _inst_3 _inst_4 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_3 G) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_3 G) Y) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_3 G) X Y f) _inst_7)
Case conversion may be inaccurate. Consider using '#align category_theory.limits.preserves_kernel.iso CategoryTheory.Limits.PreservesKernel.isoₓ'. -/
/-- If `G` preserves the kernel of `f`, then the kernel comparison map for `G` at `f` is
an isomorphism.
-/
def PreservesKernel.iso : G.obj (kernel f) ≅ kernel (G.map f) :=
  IsLimit.conePointUniqueUpToIso (isLimitOfHasKernelOfPreservesLimit G f) (kernelIsKernel _)
#align category_theory.limits.preserves_kernel.iso CategoryTheory.Limits.PreservesKernel.iso

/- warning: category_theory.limits.preserves_kernel.iso_hom -> CategoryTheory.Limits.PreservesKernel.iso_hom is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.preserves_kernel.iso_hom CategoryTheory.Limits.PreservesKernel.iso_homₓ'. -/
@[simp]
theorem PreservesKernel.iso_hom : (PreservesKernel.iso G f).Hom = kernelComparison f G :=
  rfl
#align category_theory.limits.preserves_kernel.iso_hom CategoryTheory.Limits.PreservesKernel.iso_hom

instance : IsIso (kernelComparison f G) :=
  by
  rw [← preserves_kernel.iso_hom]
  infer_instance

/- warning: category_theory.limits.kernel_map_comp_preserves_kernel_iso_inv -> CategoryTheory.Limits.kernel_map_comp_preserves_kernel_iso_inv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.kernel_map_comp_preserves_kernel_iso_inv CategoryTheory.Limits.kernel_map_comp_preserves_kernel_iso_invₓ'. -/
@[reassoc]
theorem kernel_map_comp_preserves_kernel_iso_inv {X' Y' : C} (g : X' ⟶ Y') [HasKernel g]
    [HasKernel (G.map g)] [PreservesLimit (parallelPair g 0) G] (p : X ⟶ X') (q : Y ⟶ Y')
    (hpq : f ≫ q = p ≫ g) :
    kernel.map (G.map f) (G.map g) (G.map p) (G.map q) (by rw [← G.map_comp, hpq, G.map_comp]) ≫
        (PreservesKernel.iso G _).inv =
      (PreservesKernel.iso G _).inv ≫ G.map (kernel.map f g p q hpq) :=
  by
  rw [iso.comp_inv_eq, category.assoc, preserves_kernel.iso_hom, iso.eq_inv_comp]
  exact kernel_comparison_comp_kernel_map _ _ _ _ _ _
#align category_theory.limits.kernel_map_comp_preserves_kernel_iso_inv CategoryTheory.Limits.kernel_map_comp_preserves_kernel_iso_inv

end Kernels

section Cokernels

variable {X Y Z : C} {f : X ⟶ Y} {h : Y ⟶ Z} (w : f ≫ h = 0)

/- warning: category_theory.limits.is_colimit_map_cocone_cofork_equiv' -> CategoryTheory.Limits.isColimitMapCoconeCoforkEquiv' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.is_colimit_map_cocone_cofork_equiv' CategoryTheory.Limits.isColimitMapCoconeCoforkEquiv'ₓ'. -/
/-- The map of a cokernel cofork is a colimit iff
the cokernel cofork consisting of the mapped morphisms is a colimit.
This essentially lets us commute `cokernel_cofork.of_π` with `functor.map_cocone`.

This is a variant of `is_colimit_map_cocone_cofork_equiv` for equalizers,
which we can't use directly between `G.map 0 = 0` does not hold definitionally.
-/
def isColimitMapCoconeCoforkEquiv' :
    IsColimit (G.mapCocone (CokernelCofork.ofπ h w)) ≃
      IsColimit
        (CokernelCofork.ofπ (G.map h) (by simp only [← G.map_comp, w, functor.map_zero]) :
          Cofork (G.map f) 0) :=
  by
  refine' (is_colimit.precompose_hom_equiv _ _).symm.trans (is_colimit.equiv_iso_colimit _)
  refine' parallel_pair.ext (iso.refl _) (iso.refl _) _ _ <;> simp
  refine' cofork.ext (iso.refl _) _
  simp only [cofork.π, iso.refl_hom, id_comp, cocones.precompose_obj_ι, nat_trans.comp_app,
    parallel_pair.ext_hom_app, functor.map_cocone_ι_app, cofork.of_π_ι_app]
  apply category.comp_id
#align category_theory.limits.is_colimit_map_cocone_cofork_equiv' CategoryTheory.Limits.isColimitMapCoconeCoforkEquiv'

/- warning: category_theory.limits.is_colimit_cofork_map_of_is_colimit' -> CategoryTheory.Limits.isColimitCoforkMapOfIsColimit' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.is_colimit_cofork_map_of_is_colimit' CategoryTheory.Limits.isColimitCoforkMapOfIsColimit'ₓ'. -/
/-- The property of preserving cokernels expressed in terms of cokernel coforks.

This is a variant of `is_colimit_cofork_map_of_is_colimit` for equalizers,
which we can't use directly between `G.map 0 = 0` does not hold definitionally.
-/
def isColimitCoforkMapOfIsColimit' [PreservesColimit (parallelPair f 0) G]
    (l : IsColimit (CokernelCofork.ofπ h w)) :
    IsColimit
      (CokernelCofork.ofπ (G.map h) (by simp only [← G.map_comp, w, functor.map_zero]) :
        Cofork (G.map f) 0) :=
  isColimitMapCoconeCoforkEquiv' G w (PreservesColimit.preserves l)
#align category_theory.limits.is_colimit_cofork_map_of_is_colimit' CategoryTheory.Limits.isColimitCoforkMapOfIsColimit'

variable (f) [HasCokernel f]

/- warning: category_theory.limits.is_colimit_of_has_cokernel_of_preserves_colimit -> CategoryTheory.Limits.isColimitOfHasCokernelOfPreservesColimit is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.is_colimit_of_has_cokernel_of_preserves_colimit CategoryTheory.Limits.isColimitOfHasCokernelOfPreservesColimitₓ'. -/
/--
If `G` preserves cokernels and `C` has them, then the cofork constructed of the mapped morphisms of
a cokernel cofork is a colimit.
-/
def isColimitOfHasCokernelOfPreservesColimit [PreservesColimit (parallelPair f 0) G] :
    IsColimit
      (Cofork.ofπ (G.map (cokernel.π f))
          (by simp only [← G.map_comp, coequalizer.condition, zero_comp, functor.map_zero]) :
        Cofork (G.map f) 0) :=
  isColimitCoforkMapOfIsColimit' G (cokernel.condition f) (cokernelIsCokernel f)
#align category_theory.limits.is_colimit_of_has_cokernel_of_preserves_colimit CategoryTheory.Limits.isColimitOfHasCokernelOfPreservesColimit

instance [PreservesColimit (parallelPair f 0) G] : HasCokernel (G.map f)
    where exists_colimit := ⟨⟨_, isColimitOfHasCokernelOfPreservesColimit G f⟩⟩

variable [HasCokernel (G.map f)]

/- warning: category_theory.limits.preserves_cokernel.of_iso_comparison -> CategoryTheory.Limits.PreservesCokernel.ofIsoComparison is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u3} C _inst_1] {D : Type.{u4}} [_inst_3 : CategoryTheory.Category.{u2, u4} D] [_inst_4 : CategoryTheory.Limits.HasZeroMorphisms.{u2, u4} D _inst_3] (G : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_3) [_inst_5 : CategoryTheory.Functor.PreservesZeroMorphisms.{u1, u2, u3, u4} C _inst_1 D _inst_3 _inst_2 _inst_4 G] {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) [_inst_6 : CategoryTheory.Limits.HasCokernel.{u1, u3} C _inst_1 _inst_2 X Y f] [_inst_7 : CategoryTheory.Limits.HasCokernel.{u2, u4} D _inst_3 _inst_4 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_3 G X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_3 G Y) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_3 G X Y f)] [i : CategoryTheory.IsIso.{u2, u4} D _inst_3 (CategoryTheory.Limits.cokernel.{u2, u4} D _inst_3 _inst_4 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_3 G X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_3 G Y) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_3 G X Y f) _inst_7) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_3 G (CategoryTheory.Limits.cokernel.{u1, u3} C _inst_1 _inst_2 X Y f _inst_6)) (CategoryTheory.Limits.cokernelComparison.{u1, u2, u3, u4} C _inst_1 _inst_2 X Y f D _inst_3 _inst_4 G _inst_5 _inst_6 _inst_7)], CategoryTheory.Limits.PreservesColimit.{0, 0, u1, u2, u3, u4} C _inst_1 D _inst_3 CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory (CategoryTheory.Limits.parallelPair.{u1, u3} C _inst_1 X Y f (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) 0 (OfNat.mk.{u1} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) 0 (Zero.zero.{u1} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) (CategoryTheory.Limits.HasZeroMorphisms.hasZero.{u1, u3} C _inst_1 _inst_2 X Y))))) G
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u3} C _inst_1] {D : Type.{u4}} [_inst_3 : CategoryTheory.Category.{u2, u4} D] [_inst_4 : CategoryTheory.Limits.HasZeroMorphisms.{u2, u4} D _inst_3] (G : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_3) [_inst_5 : CategoryTheory.Functor.PreservesZeroMorphisms.{u1, u2, u3, u4} C _inst_1 D _inst_3 _inst_2 _inst_4 G] {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) [_inst_6 : CategoryTheory.Limits.HasCokernel.{u1, u3} C _inst_1 _inst_2 X Y f] [_inst_7 : CategoryTheory.Limits.HasCokernel.{u2, u4} D _inst_3 _inst_4 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_3 G) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_3 G) Y) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_3 G) X Y f)] [i : CategoryTheory.IsIso.{u2, u4} D _inst_3 (CategoryTheory.Limits.cokernel.{u2, u4} D _inst_3 _inst_4 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_3 G) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_3 G) Y) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_3 G) X Y f) _inst_7) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_3 G) (CategoryTheory.Limits.cokernel.{u1, u3} C _inst_1 _inst_2 X Y f _inst_6)) (CategoryTheory.Limits.cokernelComparison.{u1, u2, u3, u4} C _inst_1 _inst_2 X Y f D _inst_3 _inst_4 G _inst_5 _inst_6 _inst_7)], CategoryTheory.Limits.PreservesColimit.{0, 0, u1, u2, u3, u4} C _inst_1 D _inst_3 CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory (CategoryTheory.Limits.parallelPair.{u1, u3} C _inst_1 X Y f (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) 0 (Zero.toOfNat0.{u1} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) (CategoryTheory.Limits.HasZeroMorphisms.Zero.{u1, u3} C _inst_1 _inst_2 X Y)))) G
Case conversion may be inaccurate. Consider using '#align category_theory.limits.preserves_cokernel.of_iso_comparison CategoryTheory.Limits.PreservesCokernel.ofIsoComparisonₓ'. -/
/-- If the cokernel comparison map for `G` at `f` is an isomorphism, then `G` preserves the
cokernel of `f`.
-/
def PreservesCokernel.ofIsoComparison [i : IsIso (cokernelComparison f G)] :
    PreservesColimit (parallelPair f 0) G :=
  by
  apply preserves_colimit_of_preserves_colimit_cocone (cokernel_is_cokernel f)
  apply (is_colimit_map_cocone_cofork_equiv' G (cokernel.condition f)).symm _
  apply is_colimit.of_point_iso (cokernel_is_cokernel (G.map f))
  exact i
#align category_theory.limits.preserves_cokernel.of_iso_comparison CategoryTheory.Limits.PreservesCokernel.ofIsoComparison

variable [PreservesColimit (parallelPair f 0) G]

/- warning: category_theory.limits.preserves_cokernel.iso -> CategoryTheory.Limits.PreservesCokernel.iso is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u3} C _inst_1] {D : Type.{u4}} [_inst_3 : CategoryTheory.Category.{u2, u4} D] [_inst_4 : CategoryTheory.Limits.HasZeroMorphisms.{u2, u4} D _inst_3] (G : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_3) [_inst_5 : CategoryTheory.Functor.PreservesZeroMorphisms.{u1, u2, u3, u4} C _inst_1 D _inst_3 _inst_2 _inst_4 G] {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) [_inst_6 : CategoryTheory.Limits.HasCokernel.{u1, u3} C _inst_1 _inst_2 X Y f] [_inst_7 : CategoryTheory.Limits.HasCokernel.{u2, u4} D _inst_3 _inst_4 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_3 G X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_3 G Y) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_3 G X Y f)] [_inst_8 : CategoryTheory.Limits.PreservesColimit.{0, 0, u1, u2, u3, u4} C _inst_1 D _inst_3 CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory (CategoryTheory.Limits.parallelPair.{u1, u3} C _inst_1 X Y f (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) 0 (OfNat.mk.{u1} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) 0 (Zero.zero.{u1} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) (CategoryTheory.Limits.HasZeroMorphisms.hasZero.{u1, u3} C _inst_1 _inst_2 X Y))))) G], CategoryTheory.Iso.{u2, u4} D _inst_3 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_3 G (CategoryTheory.Limits.cokernel.{u1, u3} C _inst_1 _inst_2 X Y f _inst_6)) (CategoryTheory.Limits.cokernel.{u2, u4} D _inst_3 _inst_4 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_3 G X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_3 G Y) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_3 G X Y f) _inst_7)
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u3} C _inst_1] {D : Type.{u4}} [_inst_3 : CategoryTheory.Category.{u2, u4} D] [_inst_4 : CategoryTheory.Limits.HasZeroMorphisms.{u2, u4} D _inst_3] (G : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_3) [_inst_5 : CategoryTheory.Functor.PreservesZeroMorphisms.{u1, u2, u3, u4} C _inst_1 D _inst_3 _inst_2 _inst_4 G] {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) [_inst_6 : CategoryTheory.Limits.HasCokernel.{u1, u3} C _inst_1 _inst_2 X Y f] [_inst_7 : CategoryTheory.Limits.HasCokernel.{u2, u4} D _inst_3 _inst_4 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_3 G) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_3 G) Y) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_3 G) X Y f)] [_inst_8 : CategoryTheory.Limits.PreservesColimit.{0, 0, u1, u2, u3, u4} C _inst_1 D _inst_3 CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory (CategoryTheory.Limits.parallelPair.{u1, u3} C _inst_1 X Y f (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) 0 (Zero.toOfNat0.{u1} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) (CategoryTheory.Limits.HasZeroMorphisms.Zero.{u1, u3} C _inst_1 _inst_2 X Y)))) G], CategoryTheory.Iso.{u2, u4} D _inst_3 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_3 G) (CategoryTheory.Limits.cokernel.{u1, u3} C _inst_1 _inst_2 X Y f _inst_6)) (CategoryTheory.Limits.cokernel.{u2, u4} D _inst_3 _inst_4 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_3 G) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_3 G) Y) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_3 G) X Y f) _inst_7)
Case conversion may be inaccurate. Consider using '#align category_theory.limits.preserves_cokernel.iso CategoryTheory.Limits.PreservesCokernel.isoₓ'. -/
/-- If `G` preserves the cokernel of `f`, then the cokernel comparison map for `G` at `f` is
an isomorphism.
-/
def PreservesCokernel.iso : G.obj (cokernel f) ≅ cokernel (G.map f) :=
  IsColimit.coconePointUniqueUpToIso (isColimitOfHasCokernelOfPreservesColimit G f)
    (cokernelIsCokernel _)
#align category_theory.limits.preserves_cokernel.iso CategoryTheory.Limits.PreservesCokernel.iso

/- warning: category_theory.limits.preserves_cokernel.iso_inv -> CategoryTheory.Limits.PreservesCokernel.iso_inv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.preserves_cokernel.iso_inv CategoryTheory.Limits.PreservesCokernel.iso_invₓ'. -/
@[simp]
theorem PreservesCokernel.iso_inv : (PreservesCokernel.iso G f).inv = cokernelComparison f G :=
  rfl
#align category_theory.limits.preserves_cokernel.iso_inv CategoryTheory.Limits.PreservesCokernel.iso_inv

instance : IsIso (cokernelComparison f G) :=
  by
  rw [← preserves_cokernel.iso_inv]
  infer_instance

/- warning: category_theory.limits.preserves_cokernel_iso_comp_cokernel_map -> CategoryTheory.Limits.preserves_cokernel_iso_comp_cokernel_map is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.preserves_cokernel_iso_comp_cokernel_map CategoryTheory.Limits.preserves_cokernel_iso_comp_cokernel_mapₓ'. -/
@[reassoc]
theorem preserves_cokernel_iso_comp_cokernel_map {X' Y' : C} (g : X' ⟶ Y') [HasCokernel g]
    [HasCokernel (G.map g)] [PreservesColimit (parallelPair g 0) G] (p : X ⟶ X') (q : Y ⟶ Y')
    (hpq : f ≫ q = p ≫ g) :
    (PreservesCokernel.iso G _).Hom ≫
        cokernel.map (G.map f) (G.map g) (G.map p) (G.map q)
          (by rw [← G.map_comp, hpq, G.map_comp]) =
      G.map (cokernel.map f g p q hpq) ≫ (PreservesCokernel.iso G _).Hom :=
  by
  rw [← iso.comp_inv_eq, category.assoc, ← iso.eq_inv_comp]
  exact cokernel_map_comp_cokernel_comparison _ _ _ _ _ _
#align category_theory.limits.preserves_cokernel_iso_comp_cokernel_map CategoryTheory.Limits.preserves_cokernel_iso_comp_cokernel_map

end Cokernels

end CategoryTheory.Limits

