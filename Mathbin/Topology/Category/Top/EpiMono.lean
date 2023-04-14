/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton

! This file was ported from Lean 3 source module topology.category.Top.epi_mono
! leanprover-community/mathlib commit 70fd9563a21e7b963887c9360bd29b2393e6225a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Category.Top.Adjunctions

/-!
# Epi- and monomorphisms in `Top`

This file shows that a continuous function is an epimorphism in the category of topological spaces
if and only if it is surjective, and that a continuous function is a monomorphism in the category of
topological spaces if and only if it is injective.
-/


universe u

open CategoryTheory

open TopCat

namespace TopCat

/- warning: Top.epi_iff_surjective -> TopCat.epi_iff_surjective is a dubious translation:
lean 3 declaration is
  forall {X : TopCat.{u1}} {Y : TopCat.{u1}} (f : Quiver.Hom.{succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1})) X Y), Iff (CategoryTheory.Epi.{u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1} X Y f) (Function.Surjective.{succ u1, succ u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) X) (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) Y) (coeFn.{succ u1, succ u1} (Quiver.Hom.{succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1})) X Y) (fun (_x : ContinuousMap.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) X) (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) Y) (CategoryTheory.Bundled.str.{u1, u1} TopologicalSpace.{u1} X) (CategoryTheory.Bundled.str.{u1, u1} TopologicalSpace.{u1} Y)) => (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) X) -> (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) Y)) (ContinuousMap.hasCoeToFun.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) X) (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) Y) (CategoryTheory.Bundled.str.{u1, u1} TopologicalSpace.{u1} X) (CategoryTheory.Bundled.str.{u1, u1} TopologicalSpace.{u1} Y)) f))
but is expected to have type
  forall {X : TopCat.{u1}} {Y : TopCat.{u1}} (f : Quiver.Hom.{succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) X Y), Iff (CategoryTheory.Epi.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} X Y f) (Function.Surjective.{succ u1, succ u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.forget.{succ u1, u1, u1} TopCat.{u1} instTopCatLargeCategory.{u1} TopCat.concreteCategory.{u1})) X) (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.forget.{succ u1, u1, u1} TopCat.{u1} instTopCatLargeCategory.{u1} TopCat.concreteCategory.{u1})) Y) (Prefunctor.map.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.forget.{succ u1, u1, u1} TopCat.{u1} instTopCatLargeCategory.{u1} TopCat.concreteCategory.{u1})) X Y f))
Case conversion may be inaccurate. Consider using '#align Top.epi_iff_surjective TopCat.epi_iff_surjectiveₓ'. -/
theorem epi_iff_surjective {X Y : TopCat.{u}} (f : X ⟶ Y) : Epi f ↔ Function.Surjective f :=
  by
  suffices epi f ↔ epi ((forget TopCat).map f)
    by
    rw [this, CategoryTheory.epi_iff_surjective]
    rfl
  constructor
  · intro
    infer_instance
  · apply functor.epi_of_epi_map
#align Top.epi_iff_surjective TopCat.epi_iff_surjective

/- warning: Top.mono_iff_injective -> TopCat.mono_iff_injective is a dubious translation:
lean 3 declaration is
  forall {X : TopCat.{u1}} {Y : TopCat.{u1}} (f : Quiver.Hom.{succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1})) X Y), Iff (CategoryTheory.Mono.{u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1} X Y f) (Function.Injective.{succ u1, succ u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) X) (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) Y) (coeFn.{succ u1, succ u1} (Quiver.Hom.{succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1})) X Y) (fun (_x : ContinuousMap.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) X) (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) Y) (CategoryTheory.Bundled.str.{u1, u1} TopologicalSpace.{u1} X) (CategoryTheory.Bundled.str.{u1, u1} TopologicalSpace.{u1} Y)) => (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) X) -> (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) Y)) (ContinuousMap.hasCoeToFun.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) X) (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) Y) (CategoryTheory.Bundled.str.{u1, u1} TopologicalSpace.{u1} X) (CategoryTheory.Bundled.str.{u1, u1} TopologicalSpace.{u1} Y)) f))
but is expected to have type
  forall {X : TopCat.{u1}} {Y : TopCat.{u1}} (f : Quiver.Hom.{succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) X Y), Iff (CategoryTheory.Mono.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} X Y f) (Function.Injective.{succ u1, succ u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.forget.{succ u1, u1, u1} TopCat.{u1} instTopCatLargeCategory.{u1} TopCat.concreteCategory.{u1})) X) (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.forget.{succ u1, u1, u1} TopCat.{u1} instTopCatLargeCategory.{u1} TopCat.concreteCategory.{u1})) Y) (Prefunctor.map.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.forget.{succ u1, u1, u1} TopCat.{u1} instTopCatLargeCategory.{u1} TopCat.concreteCategory.{u1})) X Y f))
Case conversion may be inaccurate. Consider using '#align Top.mono_iff_injective TopCat.mono_iff_injectiveₓ'. -/
theorem mono_iff_injective {X Y : TopCat.{u}} (f : X ⟶ Y) : Mono f ↔ Function.Injective f :=
  by
  suffices mono f ↔ mono ((forget TopCat).map f)
    by
    rw [this, CategoryTheory.mono_iff_injective]
    rfl
  constructor
  · intro
    infer_instance
  · apply functor.mono_of_mono_map
#align Top.mono_iff_injective TopCat.mono_iff_injective

end TopCat

