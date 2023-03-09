/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta

! This file was ported from Lean 3 source module category_theory.limits.constructions.epi_mono
! leanprover-community/mathlib commit f47581155c818e6361af4e4fda60d27d020c226b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.Shapes.Pullbacks
import Mathbin.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
# Relating monomorphisms and epimorphisms to limits and colimits

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

If `F` preserves (resp. reflects) pullbacks, then it preserves (resp. reflects) monomorphisms.

We also provide the dual version for epimorphisms.

-/


universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category Limits

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

variable (F : C ⥤ D)

/- warning: category_theory.preserves_mono_of_preserves_limit -> CategoryTheory.preserves_mono_of_preservesLimit is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} {D : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) [_inst_3 : CategoryTheory.Limits.PreservesLimit.{0, 0, u1, u2, u3, u4} C _inst_1 D _inst_2 CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.Limits.cospan.{u1, u3} C _inst_1 X X Y f f) F] [_inst_4 : CategoryTheory.Mono.{u1, u3} C _inst_1 X Y f], CategoryTheory.Mono.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F Y) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X Y f)
but is expected to have type
  forall {C : Type.{u3}} {D : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) [_inst_3 : CategoryTheory.Limits.PreservesLimit.{0, 0, u1, u2, u3, u4} C _inst_1 D _inst_2 CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.Limits.cospan.{u1, u3} C _inst_1 X X Y f f) F] [_inst_4 : CategoryTheory.Mono.{u1, u3} C _inst_1 X Y f], CategoryTheory.Mono.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) Y) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X Y f)
Case conversion may be inaccurate. Consider using '#align category_theory.preserves_mono_of_preserves_limit CategoryTheory.preserves_mono_of_preservesLimitₓ'. -/
/-- If `F` preserves pullbacks, then it preserves monomorphisms. -/
theorem preserves_mono_of_preservesLimit {X Y : C} (f : X ⟶ Y) [PreservesLimit (cospan f f) F]
    [Mono f] : Mono (F.map f) :=
  by
  have := is_limit_pullback_cone_map_of_is_limit F _ (pullback_cone.is_limit_mk_id_id f)
  simp_rw [F.map_id] at this
  apply pullback_cone.mono_of_is_limit_mk_id_id _ this
#align category_theory.preserves_mono_of_preserves_limit CategoryTheory.preserves_mono_of_preservesLimit

#print CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape /-
instance (priority := 100) preservesMonomorphisms_of_preservesLimitsOfShape
    [PreservesLimitsOfShape WalkingCospan F] : F.PreservesMonomorphisms
    where preserves X Y f hf := preserves_mono_of_preserves_limit F f
#align category_theory.preserves_monomorphisms_of_preserves_limits_of_shape CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape
-/

/- warning: category_theory.reflects_mono_of_reflects_limit -> CategoryTheory.reflects_mono_of_reflectsLimit is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} {D : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) [_inst_3 : CategoryTheory.Limits.ReflectsLimit.{0, 0, u1, u2, u3, u4} C _inst_1 D _inst_2 CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.Limits.cospan.{u1, u3} C _inst_1 X X Y f f) F] [_inst_4 : CategoryTheory.Mono.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F Y) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X Y f)], CategoryTheory.Mono.{u1, u3} C _inst_1 X Y f
but is expected to have type
  forall {C : Type.{u3}} {D : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) [_inst_3 : CategoryTheory.Limits.ReflectsLimit.{0, 0, u1, u2, u3, u4} C _inst_1 D _inst_2 CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.Limits.cospan.{u1, u3} C _inst_1 X X Y f f) F] [_inst_4 : CategoryTheory.Mono.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) Y) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X Y f)], CategoryTheory.Mono.{u1, u3} C _inst_1 X Y f
Case conversion may be inaccurate. Consider using '#align category_theory.reflects_mono_of_reflects_limit CategoryTheory.reflects_mono_of_reflectsLimitₓ'. -/
/-- If `F` reflects pullbacks, then it reflects monomorphisms. -/
theorem reflects_mono_of_reflectsLimit {X Y : C} (f : X ⟶ Y) [ReflectsLimit (cospan f f) F]
    [Mono (F.map f)] : Mono f :=
  by
  have := pullback_cone.is_limit_mk_id_id (F.map f)
  simp_rw [← F.map_id] at this
  apply pullback_cone.mono_of_is_limit_mk_id_id _ (is_limit_of_is_limit_pullback_cone_map F _ this)
#align category_theory.reflects_mono_of_reflects_limit CategoryTheory.reflects_mono_of_reflectsLimit

#print CategoryTheory.reflectsMonomorphisms_of_reflectsLimitsOfShape /-
instance (priority := 100) reflectsMonomorphisms_of_reflectsLimitsOfShape
    [ReflectsLimitsOfShape WalkingCospan F] : F.ReflectsMonomorphisms
    where reflects X Y f hf := reflects_mono_of_reflects_limit F f
#align category_theory.reflects_monomorphisms_of_reflects_limits_of_shape CategoryTheory.reflectsMonomorphisms_of_reflectsLimitsOfShape
-/

/- warning: category_theory.preserves_epi_of_preserves_colimit -> CategoryTheory.preserves_epi_of_preservesColimit is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} {D : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) [_inst_3 : CategoryTheory.Limits.PreservesColimit.{0, 0, u1, u2, u3, u4} C _inst_1 D _inst_2 CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.Limits.span.{u1, u3} C _inst_1 X Y Y f f) F] [_inst_4 : CategoryTheory.Epi.{u1, u3} C _inst_1 X Y f], CategoryTheory.Epi.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F Y) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X Y f)
but is expected to have type
  forall {C : Type.{u3}} {D : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) [_inst_3 : CategoryTheory.Limits.PreservesColimit.{0, 0, u1, u2, u3, u4} C _inst_1 D _inst_2 CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.Limits.span.{u1, u3} C _inst_1 X Y Y f f) F] [_inst_4 : CategoryTheory.Epi.{u1, u3} C _inst_1 X Y f], CategoryTheory.Epi.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) Y) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X Y f)
Case conversion may be inaccurate. Consider using '#align category_theory.preserves_epi_of_preserves_colimit CategoryTheory.preserves_epi_of_preservesColimitₓ'. -/
/-- If `F` preserves pushouts, then it preserves epimorphisms. -/
theorem preserves_epi_of_preservesColimit {X Y : C} (f : X ⟶ Y) [PreservesColimit (span f f) F]
    [Epi f] : Epi (F.map f) :=
  by
  have := is_colimit_pushout_cocone_map_of_is_colimit F _ (pushout_cocone.is_colimit_mk_id_id f)
  simp_rw [F.map_id] at this
  apply pushout_cocone.epi_of_is_colimit_mk_id_id _ this
#align category_theory.preserves_epi_of_preserves_colimit CategoryTheory.preserves_epi_of_preservesColimit

#print CategoryTheory.preservesEpimorphisms_of_preservesColimitsOfShape /-
instance (priority := 100) preservesEpimorphisms_of_preservesColimitsOfShape
    [PreservesColimitsOfShape WalkingSpan F] : F.PreservesEpimorphisms
    where preserves X Y f hf := preserves_epi_of_preserves_colimit F f
#align category_theory.preserves_epimorphisms_of_preserves_colimits_of_shape CategoryTheory.preservesEpimorphisms_of_preservesColimitsOfShape
-/

/- warning: category_theory.reflects_epi_of_reflects_colimit -> CategoryTheory.reflects_epi_of_reflectsColimit is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} {D : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) [_inst_3 : CategoryTheory.Limits.ReflectsColimit.{0, 0, u1, u2, u3, u4} C _inst_1 D _inst_2 CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.Limits.span.{u1, u3} C _inst_1 X Y Y f f) F] [_inst_4 : CategoryTheory.Epi.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F Y) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X Y f)], CategoryTheory.Epi.{u1, u3} C _inst_1 X Y f
but is expected to have type
  forall {C : Type.{u3}} {D : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) [_inst_3 : CategoryTheory.Limits.ReflectsColimit.{0, 0, u1, u2, u3, u4} C _inst_1 D _inst_2 CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.Limits.span.{u1, u3} C _inst_1 X Y Y f f) F] [_inst_4 : CategoryTheory.Epi.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) Y) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X Y f)], CategoryTheory.Epi.{u1, u3} C _inst_1 X Y f
Case conversion may be inaccurate. Consider using '#align category_theory.reflects_epi_of_reflects_colimit CategoryTheory.reflects_epi_of_reflectsColimitₓ'. -/
/-- If `F` reflects pushouts, then it reflects epimorphisms. -/
theorem reflects_epi_of_reflectsColimit {X Y : C} (f : X ⟶ Y) [ReflectsColimit (span f f) F]
    [Epi (F.map f)] : Epi f :=
  by
  have := pushout_cocone.is_colimit_mk_id_id (F.map f)
  simp_rw [← F.map_id] at this
  apply
    pushout_cocone.epi_of_is_colimit_mk_id_id _
      (is_colimit_of_is_colimit_pushout_cocone_map F _ this)
#align category_theory.reflects_epi_of_reflects_colimit CategoryTheory.reflects_epi_of_reflectsColimit

#print CategoryTheory.reflectsEpimorphisms_of_reflectsColimitsOfShape /-
instance (priority := 100) reflectsEpimorphisms_of_reflectsColimitsOfShape
    [ReflectsColimitsOfShape WalkingSpan F] : F.ReflectsEpimorphisms
    where reflects X Y f hf := reflects_epi_of_reflects_colimit F f
#align category_theory.reflects_epimorphisms_of_reflects_colimits_of_shape CategoryTheory.reflectsEpimorphisms_of_reflectsColimitsOfShape
-/

end CategoryTheory

