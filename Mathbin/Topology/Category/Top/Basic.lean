/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Scott Morrison, Mario Carneiro

! This file was ported from Lean 3 source module topology.category.Top.basic
! leanprover-community/mathlib commit 814d76e2247d5ba8bc024843552da1278bfe9e5c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.ConcreteCategory.BundledHom
import Mathbin.CategoryTheory.Elementwise
import Mathbin.Topology.ContinuousFunction.Basic

/-!
# Category instance for topological spaces

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We introduce the bundled category `Top` of topological spaces together with the functors `discrete`
and `trivial` from the category of types to `Top` which equip a type with the corresponding
discrete, resp. trivial, topology. For a proof that these functors are left, resp. right adjoint
to the forgetful functor, see `topology.category.Top.adjunctions`.
-/


open CategoryTheory

open TopologicalSpace

universe u

#print TopCat /-
/-- The category of topological spaces and continuous maps. -/
def TopCat : Type (u + 1) :=
  Bundled TopologicalSpace
#align Top TopCat
-/

namespace TopCat

#print TopCat.bundledHom /-
instance bundledHom : BundledHom @ContinuousMap :=
  ⟨@ContinuousMap.toFun, @ContinuousMap.id, @ContinuousMap.comp, @ContinuousMap.coe_injective⟩
#align Top.bundled_hom TopCat.bundledHom
-/

deriving instance LargeCategory, ConcreteCategory for TopCat

instance : CoeSort TopCat (Type _) :=
  Bundled.hasCoeToSort

#print TopCat.topologicalSpaceUnbundled /-
instance topologicalSpaceUnbundled (x : TopCat) : TopologicalSpace x :=
  x.str
#align Top.topological_space_unbundled TopCat.topologicalSpaceUnbundled
-/

/- warning: Top.id_app -> TopCat.id_app is a dubious translation:
lean 3 declaration is
  forall (X : TopCat.{u1}) (x : coeSort.{succ (succ u1), succ (succ u1)} TopCat.{u1} Type.{u1} TopCat.hasCoeToSort.{u1} X), Eq.{succ u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) X) (coeFn.{succ u1, succ u1} (Quiver.Hom.{succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1})) X X) (fun (_x : ContinuousMap.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) X) (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) X) (CategoryTheory.Bundled.str.{u1, u1} TopologicalSpace.{u1} X) (CategoryTheory.Bundled.str.{u1, u1} TopologicalSpace.{u1} X)) => (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) X) -> (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) X)) (ContinuousMap.hasCoeToFun.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) X) (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) X) (CategoryTheory.Bundled.str.{u1, u1} TopologicalSpace.{u1} X) (CategoryTheory.Bundled.str.{u1, u1} TopologicalSpace.{u1} X)) (CategoryTheory.CategoryStruct.id.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1}) X) x) x
but is expected to have type
  forall (X : TopCat.{u1}) (x : CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} X), Eq.{succ u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.forget.{succ u1, u1, u1} TopCat.{u1} instTopCatLargeCategory.{u1} TopCat.concreteCategory.{u1})) X) (Prefunctor.map.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.forget.{succ u1, u1, u1} TopCat.{u1} instTopCatLargeCategory.{u1} TopCat.concreteCategory.{u1})) X X (CategoryTheory.CategoryStruct.id.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1}) X) x) x
Case conversion may be inaccurate. Consider using '#align Top.id_app TopCat.id_appₓ'. -/
@[simp]
theorem id_app (X : TopCat.{u}) (x : X) : (𝟙 X : X → X) x = x :=
  rfl
#align Top.id_app TopCat.id_app

/- warning: Top.comp_app -> TopCat.comp_app is a dubious translation:
lean 3 declaration is
  forall {X : TopCat.{u1}} {Y : TopCat.{u1}} {Z : TopCat.{u1}} (f : Quiver.Hom.{succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1})) X Y) (g : Quiver.Hom.{succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1})) Y Z) (x : coeSort.{succ (succ u1), succ (succ u1)} TopCat.{u1} Type.{u1} TopCat.hasCoeToSort.{u1} X), Eq.{succ u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) Z) (coeFn.{succ u1, succ u1} (Quiver.Hom.{succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1})) X Z) (fun (_x : ContinuousMap.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) X) (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) Z) (CategoryTheory.Bundled.str.{u1, u1} TopologicalSpace.{u1} X) (CategoryTheory.Bundled.str.{u1, u1} TopologicalSpace.{u1} Z)) => (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) X) -> (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) Z)) (ContinuousMap.hasCoeToFun.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) X) (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) Z) (CategoryTheory.Bundled.str.{u1, u1} TopologicalSpace.{u1} X) (CategoryTheory.Bundled.str.{u1, u1} TopologicalSpace.{u1} Z)) (CategoryTheory.CategoryStruct.comp.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1}) X Y Z f g) x) (coeFn.{succ u1, succ u1} (Quiver.Hom.{succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1})) Y Z) (fun (_x : ContinuousMap.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) Y) (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) Z) (CategoryTheory.Bundled.str.{u1, u1} TopologicalSpace.{u1} Y) (CategoryTheory.Bundled.str.{u1, u1} TopologicalSpace.{u1} Z)) => (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) Y) -> (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) Z)) (ContinuousMap.hasCoeToFun.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) Y) (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) Z) (CategoryTheory.Bundled.str.{u1, u1} TopologicalSpace.{u1} Y) (CategoryTheory.Bundled.str.{u1, u1} TopologicalSpace.{u1} Z)) g (coeFn.{succ u1, succ u1} (Quiver.Hom.{succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1})) X Y) (fun (_x : ContinuousMap.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) X) (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) Y) (CategoryTheory.Bundled.str.{u1, u1} TopologicalSpace.{u1} X) (CategoryTheory.Bundled.str.{u1, u1} TopologicalSpace.{u1} Y)) => (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) X) -> (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) Y)) (ContinuousMap.hasCoeToFun.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) X) (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) Y) (CategoryTheory.Bundled.str.{u1, u1} TopologicalSpace.{u1} X) (CategoryTheory.Bundled.str.{u1, u1} TopologicalSpace.{u1} Y)) f x))
but is expected to have type
  forall {X : TopCat.{u1}} {Y : TopCat.{u1}} {Z : TopCat.{u1}} (f : Quiver.Hom.{succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) X Y) (g : Quiver.Hom.{succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) Y Z) (x : CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} X), Eq.{succ u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.forget.{succ u1, u1, u1} TopCat.{u1} instTopCatLargeCategory.{u1} TopCat.concreteCategory.{u1})) Z) (Prefunctor.map.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.forget.{succ u1, u1, u1} TopCat.{u1} instTopCatLargeCategory.{u1} TopCat.concreteCategory.{u1})) X Z (CategoryTheory.CategoryStruct.comp.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1}) X Y Z f g) x) (Prefunctor.map.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.forget.{succ u1, u1, u1} TopCat.{u1} instTopCatLargeCategory.{u1} TopCat.concreteCategory.{u1})) Y Z g (Prefunctor.map.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.forget.{succ u1, u1, u1} TopCat.{u1} instTopCatLargeCategory.{u1} TopCat.concreteCategory.{u1})) X Y f x))
Case conversion may be inaccurate. Consider using '#align Top.comp_app TopCat.comp_appₓ'. -/
@[simp]
theorem comp_app {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g : X → Z) x = g (f x) :=
  rfl
#align Top.comp_app TopCat.comp_app

#print TopCat.of /-
/-- Construct a bundled `Top` from the underlying type and the typeclass. -/
def of (X : Type u) [TopologicalSpace X] : TopCat :=
  ⟨X⟩
#align Top.of TopCat.of
-/

instance (X : TopCat) : TopologicalSpace X :=
  X.str

#print TopCat.coe_of /-
@[simp]
theorem coe_of (X : Type u) [TopologicalSpace X] : (of X : Type u) = X :=
  rfl
#align Top.coe_of TopCat.coe_of
-/

instance : Inhabited TopCat :=
  ⟨TopCat.of Empty⟩

#print TopCat.discrete /-
/-- The discrete topology on any type. -/
def discrete : Type u ⥤ TopCat.{u} where
  obj X := ⟨X, ⊥⟩
  map X Y f :=
    { toFun := f
      continuous_toFun := continuous_bot }
#align Top.discrete TopCat.discrete
-/

instance {X : Type u} : DiscreteTopology (discrete.obj X) :=
  ⟨rfl⟩

#print TopCat.trivial /-
/-- The trivial topology on any type. -/
def trivial : Type u ⥤ TopCat.{u} where
  obj X := ⟨X, ⊤⟩
  map X Y f :=
    { toFun := f
      continuous_toFun := continuous_top }
#align Top.trivial TopCat.trivial
-/

#print TopCat.isoOfHomeo /-
/-- Any homeomorphisms induces an isomorphism in `Top`. -/
@[simps]
def isoOfHomeo {X Y : TopCat.{u}} (f : X ≃ₜ Y) : X ≅ Y
    where
  Hom := ⟨f⟩
  inv := ⟨f.symm⟩
#align Top.iso_of_homeo TopCat.isoOfHomeo
-/

#print TopCat.homeoOfIso /-
/-- Any isomorphism in `Top` induces a homeomorphism. -/
@[simps]
def homeoOfIso {X Y : TopCat.{u}} (f : X ≅ Y) : X ≃ₜ Y
    where
  toFun := f.Hom
  invFun := f.inv
  left_inv x := by simp
  right_inv x := by simp
  continuous_toFun := f.Hom.Continuous
  continuous_invFun := f.inv.Continuous
#align Top.homeo_of_iso TopCat.homeoOfIso
-/

#print TopCat.of_isoOfHomeo /-
@[simp]
theorem of_isoOfHomeo {X Y : TopCat.{u}} (f : X ≃ₜ Y) : homeoOfIso (isoOfHomeo f) = f :=
  by
  ext
  rfl
#align Top.of_iso_of_homeo TopCat.of_isoOfHomeo
-/

#print TopCat.of_homeoOfIso /-
@[simp]
theorem of_homeoOfIso {X Y : TopCat.{u}} (f : X ≅ Y) : isoOfHomeo (homeoOfIso f) = f :=
  by
  ext
  rfl
#align Top.of_homeo_of_iso TopCat.of_homeoOfIso
-/

/- warning: Top.open_embedding_iff_comp_is_iso -> TopCat.openEmbedding_iff_comp_isIso is a dubious translation:
lean 3 declaration is
  forall {X : TopCat.{u1}} {Y : TopCat.{u1}} {Z : TopCat.{u1}} (f : Quiver.Hom.{succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1})) X Y) (g : Quiver.Hom.{succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1})) Y Z) [_inst_1 : CategoryTheory.IsIso.{u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1} Y Z g], Iff (OpenEmbedding.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) X) (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) Z) (TopCat.topologicalSpace.{u1} X) (TopCat.topologicalSpace.{u1} Z) (coeFn.{succ u1, succ u1} (Quiver.Hom.{succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1})) X Z) (fun (_x : ContinuousMap.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) X) (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) Z) (CategoryTheory.Bundled.str.{u1, u1} TopologicalSpace.{u1} X) (CategoryTheory.Bundled.str.{u1, u1} TopologicalSpace.{u1} Z)) => (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) X) -> (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) Z)) (ContinuousMap.hasCoeToFun.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) X) (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) Z) (CategoryTheory.Bundled.str.{u1, u1} TopologicalSpace.{u1} X) (CategoryTheory.Bundled.str.{u1, u1} TopologicalSpace.{u1} Z)) (CategoryTheory.CategoryStruct.comp.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1}) X Y Z f g))) (OpenEmbedding.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) X) (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) Y) (TopCat.topologicalSpace.{u1} X) (TopCat.topologicalSpace.{u1} Y) (coeFn.{succ u1, succ u1} (Quiver.Hom.{succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1})) X Y) (fun (_x : ContinuousMap.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) X) (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) Y) (CategoryTheory.Bundled.str.{u1, u1} TopologicalSpace.{u1} X) (CategoryTheory.Bundled.str.{u1, u1} TopologicalSpace.{u1} Y)) => (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) X) -> (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) Y)) (ContinuousMap.hasCoeToFun.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) X) (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) Y) (CategoryTheory.Bundled.str.{u1, u1} TopologicalSpace.{u1} X) (CategoryTheory.Bundled.str.{u1, u1} TopologicalSpace.{u1} Y)) f))
but is expected to have type
  forall {X : TopCat.{u1}} {Y : TopCat.{u1}} {Z : TopCat.{u1}} (f : Quiver.Hom.{succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) X Y) (g : Quiver.Hom.{succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) Y Z) [_inst_1 : CategoryTheory.IsIso.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} Y Z g], Iff (OpenEmbedding.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.forget.{succ u1, u1, u1} TopCat.{u1} instTopCatLargeCategory.{u1} TopCat.concreteCategory.{u1})) X) (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.forget.{succ u1, u1, u1} TopCat.{u1} instTopCatLargeCategory.{u1} TopCat.concreteCategory.{u1})) Z) (TopCat.instTopologicalSpaceObjTopCatToQuiverToCategoryStructInstTopCatLargeCategoryTypeTypesToPrefunctorForgetConcreteCategory.{u1} X) (TopCat.instTopologicalSpaceObjTopCatToQuiverToCategoryStructInstTopCatLargeCategoryTypeTypesToPrefunctorForgetConcreteCategory.{u1} Z) (Prefunctor.map.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.forget.{succ u1, u1, u1} TopCat.{u1} instTopCatLargeCategory.{u1} TopCat.concreteCategory.{u1})) X Z (CategoryTheory.CategoryStruct.comp.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1}) X Y Z f g))) (OpenEmbedding.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.forget.{succ u1, u1, u1} TopCat.{u1} instTopCatLargeCategory.{u1} TopCat.concreteCategory.{u1})) X) (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.forget.{succ u1, u1, u1} TopCat.{u1} instTopCatLargeCategory.{u1} TopCat.concreteCategory.{u1})) Y) (TopCat.instTopologicalSpaceObjTopCatToQuiverToCategoryStructInstTopCatLargeCategoryTypeTypesToPrefunctorForgetConcreteCategory.{u1} X) (TopCat.instTopologicalSpaceObjTopCatToQuiverToCategoryStructInstTopCatLargeCategoryTypeTypesToPrefunctorForgetConcreteCategory.{u1} Y) (Prefunctor.map.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.forget.{succ u1, u1, u1} TopCat.{u1} instTopCatLargeCategory.{u1} TopCat.concreteCategory.{u1})) X Y f))
Case conversion may be inaccurate. Consider using '#align Top.open_embedding_iff_comp_is_iso TopCat.openEmbedding_iff_comp_isIsoₓ'. -/
@[simp]
theorem openEmbedding_iff_comp_isIso {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso g] :
    OpenEmbedding (f ≫ g) ↔ OpenEmbedding f :=
  (TopCat.homeoOfIso (asIso g)).OpenEmbedding.of_comp_iff f
#align Top.open_embedding_iff_comp_is_iso TopCat.openEmbedding_iff_comp_isIso

/- warning: Top.open_embedding_iff_is_iso_comp -> TopCat.openEmbedding_iff_isIso_comp is a dubious translation:
lean 3 declaration is
  forall {X : TopCat.{u1}} {Y : TopCat.{u1}} {Z : TopCat.{u1}} (f : Quiver.Hom.{succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1})) X Y) (g : Quiver.Hom.{succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1})) Y Z) [_inst_1 : CategoryTheory.IsIso.{u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1} X Y f], Iff (OpenEmbedding.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) X) (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) Z) (TopCat.topologicalSpace.{u1} X) (TopCat.topologicalSpace.{u1} Z) (coeFn.{succ u1, succ u1} (Quiver.Hom.{succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1})) X Z) (fun (_x : ContinuousMap.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) X) (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) Z) (CategoryTheory.Bundled.str.{u1, u1} TopologicalSpace.{u1} X) (CategoryTheory.Bundled.str.{u1, u1} TopologicalSpace.{u1} Z)) => (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) X) -> (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) Z)) (ContinuousMap.hasCoeToFun.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) X) (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) Z) (CategoryTheory.Bundled.str.{u1, u1} TopologicalSpace.{u1} X) (CategoryTheory.Bundled.str.{u1, u1} TopologicalSpace.{u1} Z)) (CategoryTheory.CategoryStruct.comp.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1}) X Y Z f g))) (OpenEmbedding.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) Y) (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) Z) (TopCat.topologicalSpace.{u1} Y) (TopCat.topologicalSpace.{u1} Z) (coeFn.{succ u1, succ u1} (Quiver.Hom.{succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1})) Y Z) (fun (_x : ContinuousMap.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) Y) (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) Z) (CategoryTheory.Bundled.str.{u1, u1} TopologicalSpace.{u1} Y) (CategoryTheory.Bundled.str.{u1, u1} TopologicalSpace.{u1} Z)) => (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) Y) -> (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) Z)) (ContinuousMap.hasCoeToFun.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) Y) (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} TopologicalSpace.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} TopologicalSpace.{u1}) Z) (CategoryTheory.Bundled.str.{u1, u1} TopologicalSpace.{u1} Y) (CategoryTheory.Bundled.str.{u1, u1} TopologicalSpace.{u1} Z)) g))
but is expected to have type
  forall {X : TopCat.{u1}} {Y : TopCat.{u1}} {Z : TopCat.{u1}} (f : Quiver.Hom.{succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) X Y) (g : Quiver.Hom.{succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) Y Z) [_inst_1 : CategoryTheory.IsIso.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} X Y f], Iff (OpenEmbedding.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.forget.{succ u1, u1, u1} TopCat.{u1} instTopCatLargeCategory.{u1} TopCat.concreteCategory.{u1})) X) (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.forget.{succ u1, u1, u1} TopCat.{u1} instTopCatLargeCategory.{u1} TopCat.concreteCategory.{u1})) Z) (TopCat.instTopologicalSpaceObjTopCatToQuiverToCategoryStructInstTopCatLargeCategoryTypeTypesToPrefunctorForgetConcreteCategory.{u1} X) (TopCat.instTopologicalSpaceObjTopCatToQuiverToCategoryStructInstTopCatLargeCategoryTypeTypesToPrefunctorForgetConcreteCategory.{u1} Z) (Prefunctor.map.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.forget.{succ u1, u1, u1} TopCat.{u1} instTopCatLargeCategory.{u1} TopCat.concreteCategory.{u1})) X Z (CategoryTheory.CategoryStruct.comp.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1}) X Y Z f g))) (OpenEmbedding.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.forget.{succ u1, u1, u1} TopCat.{u1} instTopCatLargeCategory.{u1} TopCat.concreteCategory.{u1})) Y) (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.forget.{succ u1, u1, u1} TopCat.{u1} instTopCatLargeCategory.{u1} TopCat.concreteCategory.{u1})) Z) (TopCat.instTopologicalSpaceObjTopCatToQuiverToCategoryStructInstTopCatLargeCategoryTypeTypesToPrefunctorForgetConcreteCategory.{u1} Y) (TopCat.instTopologicalSpaceObjTopCatToQuiverToCategoryStructInstTopCatLargeCategoryTypeTypesToPrefunctorForgetConcreteCategory.{u1} Z) (Prefunctor.map.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.forget.{succ u1, u1, u1} TopCat.{u1} instTopCatLargeCategory.{u1} TopCat.concreteCategory.{u1})) Y Z g))
Case conversion may be inaccurate. Consider using '#align Top.open_embedding_iff_is_iso_comp TopCat.openEmbedding_iff_isIso_compₓ'. -/
@[simp]
theorem openEmbedding_iff_isIso_comp {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] :
    OpenEmbedding (f ≫ g) ↔ OpenEmbedding g :=
  by
  constructor
  · intro h
    convert h.comp (TopCat.homeoOfIso (as_iso f).symm).OpenEmbedding
    exact congr_arg _ (is_iso.inv_hom_id_assoc f g).symm
  · exact fun h => h.comp (TopCat.homeoOfIso (as_iso f)).OpenEmbedding
#align Top.open_embedding_iff_is_iso_comp TopCat.openEmbedding_iff_isIso_comp

end TopCat

