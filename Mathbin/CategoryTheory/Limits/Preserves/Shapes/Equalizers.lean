/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta

! This file was ported from Lean 3 source module category_theory.limits.preserves.shapes.equalizers
! leanprover-community/mathlib commit f47581155c818e6361af4e4fda60d27d020c226b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.Shapes.SplitCoequalizer
import Mathbin.CategoryTheory.Limits.Preserves.Basic

/-!
# Preserving (co)equalizers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Constructions to relate the notions of preserving (co)equalizers and reflecting (co)equalizers
to concrete (co)forks.

In particular, we show that `equalizer_comparison f g G` is an isomorphism iff `G` preserves
the limit of the parallel pair `f,g`, as well as the dual result.
-/


noncomputable section

universe w v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C]

variable {D : Type u₂} [Category.{v₂} D]

variable (G : C ⥤ D)

namespace CategoryTheory.Limits

section Equalizers

variable {X Y Z : C} {f g : X ⟶ Y} {h : Z ⟶ X} (w : h ≫ f = h ≫ g)

/- warning: category_theory.limits.is_limit_map_cone_fork_equiv -> CategoryTheory.Limits.isLimitMapConeForkEquiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.is_limit_map_cone_fork_equiv CategoryTheory.Limits.isLimitMapConeForkEquivₓ'. -/
/-- The map of a fork is a limit iff the fork consisting of the mapped morphisms is a limit. This
essentially lets us commute `fork.of_ι` with `functor.map_cone`.
-/
def isLimitMapConeForkEquiv :
    IsLimit (G.mapCone (Fork.ofι h w)) ≃
      IsLimit (Fork.ofι (G.map h) (by simp only [← G.map_comp, w]) : Fork (G.map f) (G.map g)) :=
  (IsLimit.postcomposeHomEquiv (diagramIsoParallelPair _) _).symm.trans
    (IsLimit.equivIsoLimit (Fork.ext (Iso.refl _) (by simp [fork.ι])))
#align category_theory.limits.is_limit_map_cone_fork_equiv CategoryTheory.Limits.isLimitMapConeForkEquiv

/- warning: category_theory.limits.is_limit_fork_map_of_is_limit -> CategoryTheory.Limits.isLimitForkMapOfIsLimit is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.is_limit_fork_map_of_is_limit CategoryTheory.Limits.isLimitForkMapOfIsLimitₓ'. -/
/-- The property of preserving equalizers expressed in terms of forks. -/
def isLimitForkMapOfIsLimit [PreservesLimit (parallelPair f g) G] (l : IsLimit (Fork.ofι h w)) :
    IsLimit (Fork.ofι (G.map h) (by simp only [← G.map_comp, w]) : Fork (G.map f) (G.map g)) :=
  isLimitMapConeForkEquiv G w (PreservesLimit.preserves l)
#align category_theory.limits.is_limit_fork_map_of_is_limit CategoryTheory.Limits.isLimitForkMapOfIsLimit

/- warning: category_theory.limits.is_limit_of_is_limit_fork_map -> CategoryTheory.Limits.isLimitOfIsLimitForkMap is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.is_limit_of_is_limit_fork_map CategoryTheory.Limits.isLimitOfIsLimitForkMapₓ'. -/
/-- The property of reflecting equalizers expressed in terms of forks. -/
def isLimitOfIsLimitForkMap [ReflectsLimit (parallelPair f g) G]
    (l : IsLimit (Fork.ofι (G.map h) (by simp only [← G.map_comp, w]) : Fork (G.map f) (G.map g))) :
    IsLimit (Fork.ofι h w) :=
  ReflectsLimit.reflects ((isLimitMapConeForkEquiv G w).symm l)
#align category_theory.limits.is_limit_of_is_limit_fork_map CategoryTheory.Limits.isLimitOfIsLimitForkMap

variable (f g) [HasEqualizer f g]

/- warning: category_theory.limits.is_limit_of_has_equalizer_of_preserves_limit -> CategoryTheory.Limits.isLimitOfHasEqualizerOfPreservesLimit is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.is_limit_of_has_equalizer_of_preserves_limit CategoryTheory.Limits.isLimitOfHasEqualizerOfPreservesLimitₓ'. -/
/--
If `G` preserves equalizers and `C` has them, then the fork constructed of the mapped morphisms of
a fork is a limit.
-/
def isLimitOfHasEqualizerOfPreservesLimit [PreservesLimit (parallelPair f g) G] :
    IsLimit
      (Fork.ofι (G.map (equalizer.ι f g)) (by simp only [← G.map_comp, equalizer.condition])) :=
  isLimitForkMapOfIsLimit G _ (equalizerIsEqualizer f g)
#align category_theory.limits.is_limit_of_has_equalizer_of_preserves_limit CategoryTheory.Limits.isLimitOfHasEqualizerOfPreservesLimit

variable [HasEqualizer (G.map f) (G.map g)]

/- warning: category_theory.limits.preserves_equalizer.of_iso_comparison -> CategoryTheory.Limits.PreservesEqualizer.ofIsoComparison is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (G : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) (g : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) [_inst_3 : CategoryTheory.Limits.HasEqualizer.{u1, u3} C _inst_1 X Y f g] [_inst_4 : CategoryTheory.Limits.HasEqualizer.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 G X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 G Y) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 G X Y f) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 G X Y g)] [i : CategoryTheory.IsIso.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 G (CategoryTheory.Limits.equalizer.{u1, u3} C _inst_1 X Y f g _inst_3)) (CategoryTheory.Limits.equalizer.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 G X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 G Y) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 G X Y f) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 G X Y g) _inst_4) (CategoryTheory.Limits.equalizerComparison.{u1, u2, u3, u4} C _inst_1 X Y f g D _inst_2 G _inst_3 _inst_4)], CategoryTheory.Limits.PreservesLimit.{0, 0, u1, u2, u3, u4} C _inst_1 D _inst_2 CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory (CategoryTheory.Limits.parallelPair.{u1, u3} C _inst_1 X Y f g) G
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (G : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) (g : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) [_inst_3 : CategoryTheory.Limits.HasEqualizer.{u1, u3} C _inst_1 X Y f g] [_inst_4 : CategoryTheory.Limits.HasEqualizer.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) Y) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) X Y f) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) X Y g)] [i : CategoryTheory.IsIso.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) (CategoryTheory.Limits.equalizer.{u1, u3} C _inst_1 X Y f g _inst_3)) (CategoryTheory.Limits.equalizer.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) Y) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) X Y f) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) X Y g) _inst_4) (CategoryTheory.Limits.equalizerComparison.{u1, u2, u3, u4} C _inst_1 X Y f g D _inst_2 G _inst_3 _inst_4)], CategoryTheory.Limits.PreservesLimit.{0, 0, u1, u2, u3, u4} C _inst_1 D _inst_2 CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory (CategoryTheory.Limits.parallelPair.{u1, u3} C _inst_1 X Y f g) G
Case conversion may be inaccurate. Consider using '#align category_theory.limits.preserves_equalizer.of_iso_comparison CategoryTheory.Limits.PreservesEqualizer.ofIsoComparisonₓ'. -/
/-- If the equalizer comparison map for `G` at `(f,g)` is an isomorphism, then `G` preserves the
equalizer of `(f,g)`.
-/
def PreservesEqualizer.ofIsoComparison [i : IsIso (equalizerComparison f g G)] :
    PreservesLimit (parallelPair f g) G :=
  by
  apply preserves_limit_of_preserves_limit_cone (equalizer_is_equalizer f g)
  apply (is_limit_map_cone_fork_equiv _ _).symm _
  apply is_limit.of_point_iso (limit.is_limit (parallel_pair (G.map f) (G.map g)))
  apply i
#align category_theory.limits.preserves_equalizer.of_iso_comparison CategoryTheory.Limits.PreservesEqualizer.ofIsoComparison

variable [PreservesLimit (parallelPair f g) G]

/- warning: category_theory.limits.preserves_equalizer.iso -> CategoryTheory.Limits.PreservesEqualizer.iso is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (G : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) (g : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) [_inst_3 : CategoryTheory.Limits.HasEqualizer.{u1, u3} C _inst_1 X Y f g] [_inst_4 : CategoryTheory.Limits.HasEqualizer.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 G X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 G Y) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 G X Y f) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 G X Y g)] [_inst_5 : CategoryTheory.Limits.PreservesLimit.{0, 0, u1, u2, u3, u4} C _inst_1 D _inst_2 CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory (CategoryTheory.Limits.parallelPair.{u1, u3} C _inst_1 X Y f g) G], CategoryTheory.Iso.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 G (CategoryTheory.Limits.equalizer.{u1, u3} C _inst_1 X Y f g _inst_3)) (CategoryTheory.Limits.equalizer.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 G X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 G Y) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 G X Y f) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 G X Y g) _inst_4)
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (G : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) (g : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) [_inst_3 : CategoryTheory.Limits.HasEqualizer.{u1, u3} C _inst_1 X Y f g] [_inst_4 : CategoryTheory.Limits.HasEqualizer.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) Y) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) X Y f) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) X Y g)] [_inst_5 : CategoryTheory.Limits.PreservesLimit.{0, 0, u1, u2, u3, u4} C _inst_1 D _inst_2 CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory (CategoryTheory.Limits.parallelPair.{u1, u3} C _inst_1 X Y f g) G], CategoryTheory.Iso.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) (CategoryTheory.Limits.equalizer.{u1, u3} C _inst_1 X Y f g _inst_3)) (CategoryTheory.Limits.equalizer.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) Y) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) X Y f) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) X Y g) _inst_4)
Case conversion may be inaccurate. Consider using '#align category_theory.limits.preserves_equalizer.iso CategoryTheory.Limits.PreservesEqualizer.isoₓ'. -/
/--
If `G` preserves the equalizer of `(f,g)`, then the equalizer comparison map for `G` at `(f,g)` is
an isomorphism.
-/
def PreservesEqualizer.iso : G.obj (equalizer f g) ≅ equalizer (G.map f) (G.map g) :=
  IsLimit.conePointUniqueUpToIso (isLimitOfHasEqualizerOfPreservesLimit G f g) (limit.isLimit _)
#align category_theory.limits.preserves_equalizer.iso CategoryTheory.Limits.PreservesEqualizer.iso

/- warning: category_theory.limits.preserves_equalizer.iso_hom -> CategoryTheory.Limits.PreservesEqualizer.iso_hom is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (G : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) (g : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) [_inst_3 : CategoryTheory.Limits.HasEqualizer.{u1, u3} C _inst_1 X Y f g] [_inst_4 : CategoryTheory.Limits.HasEqualizer.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 G X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 G Y) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 G X Y f) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 G X Y g)] [_inst_5 : CategoryTheory.Limits.PreservesLimit.{0, 0, u1, u2, u3, u4} C _inst_1 D _inst_2 CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory (CategoryTheory.Limits.parallelPair.{u1, u3} C _inst_1 X Y f g) G], Eq.{succ u2} (Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 G (CategoryTheory.Limits.equalizer.{u1, u3} C _inst_1 X Y f g _inst_3)) (CategoryTheory.Limits.equalizer.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 G X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 G Y) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 G X Y f) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 G X Y g) _inst_4)) (CategoryTheory.Iso.hom.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 G (CategoryTheory.Limits.equalizer.{u1, u3} C _inst_1 X Y f g _inst_3)) (CategoryTheory.Limits.equalizer.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 G X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 G Y) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 G X Y f) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 G X Y g) _inst_4) (CategoryTheory.Limits.PreservesEqualizer.iso.{u1, u2, u3, u4} C _inst_1 D _inst_2 G X Y f g _inst_3 _inst_4 _inst_5)) (CategoryTheory.Limits.equalizerComparison.{u1, u2, u3, u4} C _inst_1 X Y f g D _inst_2 G _inst_3 _inst_4)
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (G : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) (g : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) [_inst_3 : CategoryTheory.Limits.HasEqualizer.{u1, u3} C _inst_1 X Y f g] [_inst_4 : CategoryTheory.Limits.HasEqualizer.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) Y) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) X Y f) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) X Y g)] [_inst_5 : CategoryTheory.Limits.PreservesLimit.{0, 0, u1, u2, u3, u4} C _inst_1 D _inst_2 CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory (CategoryTheory.Limits.parallelPair.{u1, u3} C _inst_1 X Y f g) G], Eq.{succ u2} (Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) (CategoryTheory.Limits.equalizer.{u1, u3} C _inst_1 X Y f g _inst_3)) (CategoryTheory.Limits.equalizer.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) Y) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) X Y f) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) X Y g) _inst_4)) (CategoryTheory.Iso.hom.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) (CategoryTheory.Limits.equalizer.{u1, u3} C _inst_1 X Y f g _inst_3)) (CategoryTheory.Limits.equalizer.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) Y) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) X Y f) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) X Y g) _inst_4) (CategoryTheory.Limits.PreservesEqualizer.iso.{u1, u2, u3, u4} C _inst_1 D _inst_2 G X Y f g _inst_3 _inst_4 _inst_5)) (CategoryTheory.Limits.equalizerComparison.{u1, u2, u3, u4} C _inst_1 X Y f g D _inst_2 G _inst_3 _inst_4)
Case conversion may be inaccurate. Consider using '#align category_theory.limits.preserves_equalizer.iso_hom CategoryTheory.Limits.PreservesEqualizer.iso_homₓ'. -/
@[simp]
theorem PreservesEqualizer.iso_hom :
    (PreservesEqualizer.iso G f g).Hom = equalizerComparison f g G :=
  rfl
#align category_theory.limits.preserves_equalizer.iso_hom CategoryTheory.Limits.PreservesEqualizer.iso_hom

instance : IsIso (equalizerComparison f g G) :=
  by
  rw [← preserves_equalizer.iso_hom]
  infer_instance

end Equalizers

section Coequalizers

variable {X Y Z : C} {f g : X ⟶ Y} {h : Y ⟶ Z} (w : f ≫ h = g ≫ h)

/- warning: category_theory.limits.is_colimit_map_cocone_cofork_equiv -> CategoryTheory.Limits.isColimitMapCoconeCoforkEquiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.is_colimit_map_cocone_cofork_equiv CategoryTheory.Limits.isColimitMapCoconeCoforkEquivₓ'. -/
/-- The map of a cofork is a colimit iff the cofork consisting of the mapped morphisms is a colimit.
This essentially lets us commute `cofork.of_π` with `functor.map_cocone`.
-/
def isColimitMapCoconeCoforkEquiv :
    IsColimit (G.mapCocone (Cofork.ofπ h w)) ≃
      IsColimit
        (Cofork.ofπ (G.map h) (by simp only [← G.map_comp, w]) : Cofork (G.map f) (G.map g)) :=
  (IsColimit.precomposeInvEquiv (diagramIsoParallelPair _) _).symm.trans <|
    IsColimit.equivIsoColimit <|
      Cofork.ext (Iso.refl _) <|
        by
        dsimp only [cofork.π, cofork.of_π_ι_app]
        dsimp; rw [category.comp_id, category.id_comp]
#align category_theory.limits.is_colimit_map_cocone_cofork_equiv CategoryTheory.Limits.isColimitMapCoconeCoforkEquiv

/- warning: category_theory.limits.is_colimit_cofork_map_of_is_colimit -> CategoryTheory.Limits.isColimitCoforkMapOfIsColimit is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.is_colimit_cofork_map_of_is_colimit CategoryTheory.Limits.isColimitCoforkMapOfIsColimitₓ'. -/
/-- The property of preserving coequalizers expressed in terms of coforks. -/
def isColimitCoforkMapOfIsColimit [PreservesColimit (parallelPair f g) G]
    (l : IsColimit (Cofork.ofπ h w)) :
    IsColimit
      (Cofork.ofπ (G.map h) (by simp only [← G.map_comp, w]) : Cofork (G.map f) (G.map g)) :=
  isColimitMapCoconeCoforkEquiv G w (PreservesColimit.preserves l)
#align category_theory.limits.is_colimit_cofork_map_of_is_colimit CategoryTheory.Limits.isColimitCoforkMapOfIsColimit

/- warning: category_theory.limits.is_colimit_of_is_colimit_cofork_map -> CategoryTheory.Limits.isColimitOfIsColimitCoforkMap is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.is_colimit_of_is_colimit_cofork_map CategoryTheory.Limits.isColimitOfIsColimitCoforkMapₓ'. -/
/-- The property of reflecting coequalizers expressed in terms of coforks. -/
def isColimitOfIsColimitCoforkMap [ReflectsColimit (parallelPair f g) G]
    (l :
      IsColimit
        (Cofork.ofπ (G.map h) (by simp only [← G.map_comp, w]) : Cofork (G.map f) (G.map g))) :
    IsColimit (Cofork.ofπ h w) :=
  ReflectsColimit.reflects ((isColimitMapCoconeCoforkEquiv G w).symm l)
#align category_theory.limits.is_colimit_of_is_colimit_cofork_map CategoryTheory.Limits.isColimitOfIsColimitCoforkMap

variable (f g) [HasCoequalizer f g]

/- warning: category_theory.limits.is_colimit_of_has_coequalizer_of_preserves_colimit -> CategoryTheory.Limits.isColimitOfHasCoequalizerOfPreservesColimit is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.is_colimit_of_has_coequalizer_of_preserves_colimit CategoryTheory.Limits.isColimitOfHasCoequalizerOfPreservesColimitₓ'. -/
/--
If `G` preserves coequalizers and `C` has them, then the cofork constructed of the mapped morphisms
of a cofork is a colimit.
-/
def isColimitOfHasCoequalizerOfPreservesColimit [PreservesColimit (parallelPair f g) G] :
    IsColimit (Cofork.ofπ (G.map (coequalizer.π f g)) _) :=
  isColimitCoforkMapOfIsColimit G _ (coequalizerIsCoequalizer f g)
#align category_theory.limits.is_colimit_of_has_coequalizer_of_preserves_colimit CategoryTheory.Limits.isColimitOfHasCoequalizerOfPreservesColimit

variable [HasCoequalizer (G.map f) (G.map g)]

/- warning: category_theory.limits.of_iso_comparison -> CategoryTheory.Limits.ofIsoComparison is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (G : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) (g : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) [_inst_3 : CategoryTheory.Limits.HasCoequalizer.{u1, u3} C _inst_1 X Y f g] [_inst_4 : CategoryTheory.Limits.HasCoequalizer.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 G X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 G Y) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 G X Y f) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 G X Y g)] [i : CategoryTheory.IsIso.{u2, u4} D _inst_2 (CategoryTheory.Limits.coequalizer.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 G X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 G Y) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 G X Y f) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 G X Y g) _inst_4) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 G (CategoryTheory.Limits.coequalizer.{u1, u3} C _inst_1 X Y f g _inst_3)) (CategoryTheory.Limits.coequalizerComparison.{u1, u2, u3, u4} C _inst_1 X Y f g D _inst_2 G _inst_3 _inst_4)], CategoryTheory.Limits.PreservesColimit.{0, 0, u1, u2, u3, u4} C _inst_1 D _inst_2 CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory (CategoryTheory.Limits.parallelPair.{u1, u3} C _inst_1 X Y f g) G
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (G : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) (g : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) [_inst_3 : CategoryTheory.Limits.HasCoequalizer.{u1, u3} C _inst_1 X Y f g] [_inst_4 : CategoryTheory.Limits.HasCoequalizer.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) Y) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) X Y f) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) X Y g)] [i : CategoryTheory.IsIso.{u2, u4} D _inst_2 (CategoryTheory.Limits.coequalizer.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) Y) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) X Y f) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) X Y g) _inst_4) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) (CategoryTheory.Limits.coequalizer.{u1, u3} C _inst_1 X Y f g _inst_3)) (CategoryTheory.Limits.coequalizerComparison.{u1, u2, u3, u4} C _inst_1 X Y f g D _inst_2 G _inst_3 _inst_4)], CategoryTheory.Limits.PreservesColimit.{0, 0, u1, u2, u3, u4} C _inst_1 D _inst_2 CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory (CategoryTheory.Limits.parallelPair.{u1, u3} C _inst_1 X Y f g) G
Case conversion may be inaccurate. Consider using '#align category_theory.limits.of_iso_comparison CategoryTheory.Limits.ofIsoComparisonₓ'. -/
/-- If the coequalizer comparison map for `G` at `(f,g)` is an isomorphism, then `G` preserves the
coequalizer of `(f,g)`.
-/
def ofIsoComparison [i : IsIso (coequalizerComparison f g G)] :
    PreservesColimit (parallelPair f g) G :=
  by
  apply preserves_colimit_of_preserves_colimit_cocone (coequalizer_is_coequalizer f g)
  apply (is_colimit_map_cocone_cofork_equiv _ _).symm _
  apply is_colimit.of_point_iso (colimit.is_colimit (parallel_pair (G.map f) (G.map g)))
  apply i
#align category_theory.limits.of_iso_comparison CategoryTheory.Limits.ofIsoComparison

variable [PreservesColimit (parallelPair f g) G]

/- warning: category_theory.limits.preserves_coequalizer.iso -> CategoryTheory.Limits.PreservesCoequalizer.iso is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (G : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) (g : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) [_inst_3 : CategoryTheory.Limits.HasCoequalizer.{u1, u3} C _inst_1 X Y f g] [_inst_4 : CategoryTheory.Limits.HasCoequalizer.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 G X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 G Y) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 G X Y f) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 G X Y g)] [_inst_5 : CategoryTheory.Limits.PreservesColimit.{0, 0, u1, u2, u3, u4} C _inst_1 D _inst_2 CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory (CategoryTheory.Limits.parallelPair.{u1, u3} C _inst_1 X Y f g) G], CategoryTheory.Iso.{u2, u4} D _inst_2 (CategoryTheory.Limits.coequalizer.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 G X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 G Y) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 G X Y f) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 G X Y g) _inst_4) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 G (CategoryTheory.Limits.coequalizer.{u1, u3} C _inst_1 X Y f g _inst_3))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (G : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) (g : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) [_inst_3 : CategoryTheory.Limits.HasCoequalizer.{u1, u3} C _inst_1 X Y f g] [_inst_4 : CategoryTheory.Limits.HasCoequalizer.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) Y) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) X Y f) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) X Y g)] [_inst_5 : CategoryTheory.Limits.PreservesColimit.{0, 0, u1, u2, u3, u4} C _inst_1 D _inst_2 CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory (CategoryTheory.Limits.parallelPair.{u1, u3} C _inst_1 X Y f g) G], CategoryTheory.Iso.{u2, u4} D _inst_2 (CategoryTheory.Limits.coequalizer.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) Y) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) X Y f) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) X Y g) _inst_4) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) (CategoryTheory.Limits.coequalizer.{u1, u3} C _inst_1 X Y f g _inst_3))
Case conversion may be inaccurate. Consider using '#align category_theory.limits.preserves_coequalizer.iso CategoryTheory.Limits.PreservesCoequalizer.isoₓ'. -/
/--
If `G` preserves the coequalizer of `(f,g)`, then the coequalizer comparison map for `G` at `(f,g)`
is an isomorphism.
-/
def PreservesCoequalizer.iso : coequalizer (G.map f) (G.map g) ≅ G.obj (coequalizer f g) :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    (isColimitOfHasCoequalizerOfPreservesColimit G f g)
#align category_theory.limits.preserves_coequalizer.iso CategoryTheory.Limits.PreservesCoequalizer.iso

/- warning: category_theory.limits.preserves_coequalizer.iso_hom -> CategoryTheory.Limits.PreservesCoequalizer.iso_hom is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (G : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) (g : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) [_inst_3 : CategoryTheory.Limits.HasCoequalizer.{u1, u3} C _inst_1 X Y f g] [_inst_4 : CategoryTheory.Limits.HasCoequalizer.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 G X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 G Y) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 G X Y f) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 G X Y g)] [_inst_5 : CategoryTheory.Limits.PreservesColimit.{0, 0, u1, u2, u3, u4} C _inst_1 D _inst_2 CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory (CategoryTheory.Limits.parallelPair.{u1, u3} C _inst_1 X Y f g) G], Eq.{succ u2} (Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Limits.coequalizer.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 G X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 G Y) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 G X Y f) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 G X Y g) _inst_4) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 G (CategoryTheory.Limits.coequalizer.{u1, u3} C _inst_1 X Y f g _inst_3))) (CategoryTheory.Iso.hom.{u2, u4} D _inst_2 (CategoryTheory.Limits.coequalizer.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 G X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 G Y) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 G X Y f) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 G X Y g) _inst_4) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 G (CategoryTheory.Limits.coequalizer.{u1, u3} C _inst_1 X Y f g _inst_3)) (CategoryTheory.Limits.PreservesCoequalizer.iso.{u1, u2, u3, u4} C _inst_1 D _inst_2 G X Y f g _inst_3 _inst_4 _inst_5)) (CategoryTheory.Limits.coequalizerComparison.{u1, u2, u3, u4} C _inst_1 X Y f g D _inst_2 G _inst_3 _inst_4)
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (G : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) (g : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) [_inst_3 : CategoryTheory.Limits.HasCoequalizer.{u1, u3} C _inst_1 X Y f g] [_inst_4 : CategoryTheory.Limits.HasCoequalizer.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) Y) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) X Y f) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) X Y g)] [_inst_5 : CategoryTheory.Limits.PreservesColimit.{0, 0, u1, u2, u3, u4} C _inst_1 D _inst_2 CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory (CategoryTheory.Limits.parallelPair.{u1, u3} C _inst_1 X Y f g) G], Eq.{succ u2} (Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Limits.coequalizer.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) Y) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) X Y f) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) X Y g) _inst_4) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) (CategoryTheory.Limits.coequalizer.{u1, u3} C _inst_1 X Y f g _inst_3))) (CategoryTheory.Iso.hom.{u2, u4} D _inst_2 (CategoryTheory.Limits.coequalizer.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) Y) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) X Y f) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) X Y g) _inst_4) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) (CategoryTheory.Limits.coequalizer.{u1, u3} C _inst_1 X Y f g _inst_3)) (CategoryTheory.Limits.PreservesCoequalizer.iso.{u1, u2, u3, u4} C _inst_1 D _inst_2 G X Y f g _inst_3 _inst_4 _inst_5)) (CategoryTheory.Limits.coequalizerComparison.{u1, u2, u3, u4} C _inst_1 X Y f g D _inst_2 G _inst_3 _inst_4)
Case conversion may be inaccurate. Consider using '#align category_theory.limits.preserves_coequalizer.iso_hom CategoryTheory.Limits.PreservesCoequalizer.iso_homₓ'. -/
@[simp]
theorem PreservesCoequalizer.iso_hom :
    (PreservesCoequalizer.iso G f g).Hom = coequalizerComparison f g G :=
  rfl
#align category_theory.limits.preserves_coequalizer.iso_hom CategoryTheory.Limits.PreservesCoequalizer.iso_hom

instance : IsIso (coequalizerComparison f g G) :=
  by
  rw [← preserves_coequalizer.iso_hom]
  infer_instance

/- warning: category_theory.limits.map_π_epi -> CategoryTheory.Limits.map_π_epi is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (G : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) (g : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) [_inst_3 : CategoryTheory.Limits.HasCoequalizer.{u1, u3} C _inst_1 X Y f g] [_inst_4 : CategoryTheory.Limits.HasCoequalizer.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 G X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 G Y) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 G X Y f) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 G X Y g)] [_inst_5 : CategoryTheory.Limits.PreservesColimit.{0, 0, u1, u2, u3, u4} C _inst_1 D _inst_2 CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory (CategoryTheory.Limits.parallelPair.{u1, u3} C _inst_1 X Y f g) G], CategoryTheory.Epi.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 G Y) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 G (CategoryTheory.Limits.coequalizer.{u1, u3} C _inst_1 X Y f g _inst_3)) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 G Y (CategoryTheory.Limits.coequalizer.{u1, u3} C _inst_1 X Y f g _inst_3) (CategoryTheory.Limits.coequalizer.π.{u1, u3} C _inst_1 X Y f g _inst_3))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (G : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) (g : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) [_inst_3 : CategoryTheory.Limits.HasCoequalizer.{u1, u3} C _inst_1 X Y f g] [_inst_4 : CategoryTheory.Limits.HasCoequalizer.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) Y) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) X Y f) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) X Y g)] [_inst_5 : CategoryTheory.Limits.PreservesColimit.{0, 0, u1, u2, u3, u4} C _inst_1 D _inst_2 CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory (CategoryTheory.Limits.parallelPair.{u1, u3} C _inst_1 X Y f g) G], CategoryTheory.Epi.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) Y) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) (CategoryTheory.Limits.coequalizer.{u1, u3} C _inst_1 X Y f g _inst_3)) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) Y (CategoryTheory.Limits.coequalizer.{u1, u3} C _inst_1 X Y f g _inst_3) (CategoryTheory.Limits.coequalizer.π.{u1, u3} C _inst_1 X Y f g _inst_3))
Case conversion may be inaccurate. Consider using '#align category_theory.limits.map_π_epi CategoryTheory.Limits.map_π_epiₓ'. -/
instance map_π_epi : Epi (G.map (coequalizer.π f g)) :=
  ⟨fun W h k => by
    rw [← ι_comp_coequalizer_comparison]
    apply (cancel_epi _).1
    apply epi_comp⟩
#align category_theory.limits.map_π_epi CategoryTheory.Limits.map_π_epi

/- warning: category_theory.limits.map_π_preserves_coequalizer_inv -> CategoryTheory.Limits.map_π_preserves_coequalizer_inv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.map_π_preserves_coequalizer_inv CategoryTheory.Limits.map_π_preserves_coequalizer_invₓ'. -/
@[reassoc]
theorem map_π_preserves_coequalizer_inv :
    G.map (coequalizer.π f g) ≫ (PreservesCoequalizer.iso G f g).inv =
      coequalizer.π (G.map f) (G.map g) :=
  by
  rw [← ι_comp_coequalizer_comparison_assoc, ← preserves_coequalizer.iso_hom, iso.hom_inv_id,
    comp_id]
#align category_theory.limits.map_π_preserves_coequalizer_inv CategoryTheory.Limits.map_π_preserves_coequalizer_inv

/- warning: category_theory.limits.map_π_preserves_coequalizer_inv_desc -> CategoryTheory.Limits.map_π_preserves_coequalizer_inv_desc is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.map_π_preserves_coequalizer_inv_desc CategoryTheory.Limits.map_π_preserves_coequalizer_inv_descₓ'. -/
@[reassoc]
theorem map_π_preserves_coequalizer_inv_desc {W : D} (k : G.obj Y ⟶ W)
    (wk : G.map f ≫ k = G.map g ≫ k) :
    G.map (coequalizer.π f g) ≫ (PreservesCoequalizer.iso G f g).inv ≫ coequalizer.desc k wk = k :=
  by rw [← category.assoc, map_π_preserves_coequalizer_inv, coequalizer.π_desc]
#align category_theory.limits.map_π_preserves_coequalizer_inv_desc CategoryTheory.Limits.map_π_preserves_coequalizer_inv_desc

/- warning: category_theory.limits.map_π_preserves_coequalizer_inv_colim_map -> CategoryTheory.Limits.map_π_preserves_coequalizer_inv_colimMap is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.map_π_preserves_coequalizer_inv_colim_map CategoryTheory.Limits.map_π_preserves_coequalizer_inv_colimMapₓ'. -/
@[reassoc]
theorem map_π_preserves_coequalizer_inv_colimMap {X' Y' : D} (f' g' : X' ⟶ Y')
    [HasCoequalizer f' g'] (p : G.obj X ⟶ X') (q : G.obj Y ⟶ Y') (wf : G.map f ≫ q = p ≫ f')
    (wg : G.map g ≫ q = p ≫ g') :
    G.map (coequalizer.π f g) ≫
        (PreservesCoequalizer.iso G f g).inv ≫
          colimMap (parallelPairHom (G.map f) (G.map g) f' g' p q wf wg) =
      q ≫ coequalizer.π f' g' :=
  by rw [← category.assoc, map_π_preserves_coequalizer_inv, ι_colim_map, parallel_pair_hom_app_one]
#align category_theory.limits.map_π_preserves_coequalizer_inv_colim_map CategoryTheory.Limits.map_π_preserves_coequalizer_inv_colimMap

/- warning: category_theory.limits.map_π_preserves_coequalizer_inv_colim_map_desc -> CategoryTheory.Limits.map_π_preserves_coequalizer_inv_colimMap_desc is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.map_π_preserves_coequalizer_inv_colim_map_desc CategoryTheory.Limits.map_π_preserves_coequalizer_inv_colimMap_descₓ'. -/
@[reassoc]
theorem map_π_preserves_coequalizer_inv_colimMap_desc {X' Y' : D} (f' g' : X' ⟶ Y')
    [HasCoequalizer f' g'] (p : G.obj X ⟶ X') (q : G.obj Y ⟶ Y') (wf : G.map f ≫ q = p ≫ f')
    (wg : G.map g ≫ q = p ≫ g') {Z' : D} (h : Y' ⟶ Z') (wh : f' ≫ h = g' ≫ h) :
    G.map (coequalizer.π f g) ≫
        (PreservesCoequalizer.iso G f g).inv ≫
          colimMap (parallelPairHom (G.map f) (G.map g) f' g' p q wf wg) ≫ coequalizer.desc h wh =
      q ≫ h :=
  by
  slice_lhs 1 3 => rw [map_π_preserves_coequalizer_inv_colim_map]
  slice_lhs 2 3 => rw [coequalizer.π_desc]
#align category_theory.limits.map_π_preserves_coequalizer_inv_colim_map_desc CategoryTheory.Limits.map_π_preserves_coequalizer_inv_colimMap_desc

#print CategoryTheory.Limits.preservesSplitCoequalizers /-
/-- Any functor preserves coequalizers of split pairs. -/
instance (priority := 1) preservesSplitCoequalizers (f g : X ⟶ Y) [HasSplitCoequalizer f g] :
    PreservesColimit (parallelPair f g) G :=
  by
  apply
    preserves_colimit_of_preserves_colimit_cocone
      (has_split_coequalizer.is_split_coequalizer f g).isCoequalizer
  apply
    (is_colimit_map_cocone_cofork_equiv G _).symm
      ((has_split_coequalizer.is_split_coequalizer f g).map G).isCoequalizer
#align category_theory.limits.preserves_split_coequalizers CategoryTheory.Limits.preservesSplitCoequalizers
-/

end Coequalizers

end CategoryTheory.Limits

