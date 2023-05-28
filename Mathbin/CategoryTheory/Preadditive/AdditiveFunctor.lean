/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Scott Morrison

! This file was ported from Lean 3 source module category_theory.preadditive.additive_functor
! leanprover-community/mathlib commit 69c6a5a12d8a2b159f20933e60115a4f2de62b58
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.ExactFunctor
import Mathbin.CategoryTheory.Limits.Preserves.Finite
import Mathbin.CategoryTheory.Preadditive.Biproducts
import Mathbin.CategoryTheory.Preadditive.FunctorCategory

/-!
# Additive Functors

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A functor between two preadditive categories is called *additive*
provided that the induced map on hom types is a morphism of abelian
groups.

An additive functor between preadditive categories creates and preserves biproducts.
Conversely, if `F : C ⥤ D` is a functor between preadditive categories, where `C` has binary
biproducts, and if `F` preserves binary biproducts, then `F` is additive.

We also define the category of bundled additive functors.

# Implementation details

`functor.additive` is a `Prop`-valued class, defined by saying that for every two objects `X` and
`Y`, the map `F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)` is a morphism of abelian groups.

-/


universe v₁ v₂ u₁ u₂

namespace CategoryTheory

#print CategoryTheory.Functor.Additive /-
/-- A functor `F` is additive provided `F.map` is an additive homomorphism. -/
class Functor.Additive {C D : Type _} [Category C] [Category D] [Preadditive C] [Preadditive D]
  (F : C ⥤ D) : Prop where
  map_add' : ∀ {X Y : C} {f g : X ⟶ Y}, F.map (f + g) = F.map f + F.map g := by obviously
#align category_theory.functor.additive CategoryTheory.Functor.Additive
-/

section Preadditive

namespace Functor

section

variable {C D : Type _} [Category C] [Category D] [Preadditive C] [Preadditive D] (F : C ⥤ D)
  [Functor.Additive F]

/- warning: category_theory.functor.map_add -> CategoryTheory.Functor.map_add is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.functor.map_add CategoryTheory.Functor.map_addₓ'. -/
@[simp]
theorem map_add {X Y : C} {f g : X ⟶ Y} : F.map (f + g) = F.map f + F.map g :=
  Functor.Additive.map_add'
#align category_theory.functor.map_add CategoryTheory.Functor.map_add

/- warning: category_theory.functor.map_add_hom -> CategoryTheory.Functor.mapAddHom is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} {D : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u1} C] [_inst_2 : CategoryTheory.Category.{u4, u2} D] [_inst_3 : CategoryTheory.Preadditive.{u3, u1} C _inst_1] [_inst_4 : CategoryTheory.Preadditive.{u4, u2} D _inst_2] (F : CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2) [_inst_5 : CategoryTheory.Functor.Additive.{u1, u2, u3, u4} C D _inst_1 _inst_2 _inst_3 _inst_4 F] {X : C} {Y : C}, AddMonoidHom.{u3, u4} (Quiver.Hom.{succ u3, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} C (CategoryTheory.Category.toCategoryStruct.{u3, u1} C _inst_1)) X Y) (Quiver.Hom.{succ u4, u2} D (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} D (CategoryTheory.Category.toCategoryStruct.{u4, u2} D _inst_2)) (CategoryTheory.Functor.obj.{u3, u4, u1, u2} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u3, u4, u1, u2} C _inst_1 D _inst_2 F Y)) (AddMonoid.toAddZeroClass.{u3} (Quiver.Hom.{succ u3, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} C (CategoryTheory.Category.toCategoryStruct.{u3, u1} C _inst_1)) X Y) (SubNegMonoid.toAddMonoid.{u3} (Quiver.Hom.{succ u3, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} C (CategoryTheory.Category.toCategoryStruct.{u3, u1} C _inst_1)) X Y) (AddGroup.toSubNegMonoid.{u3} (Quiver.Hom.{succ u3, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} C (CategoryTheory.Category.toCategoryStruct.{u3, u1} C _inst_1)) X Y) (AddCommGroup.toAddGroup.{u3} (Quiver.Hom.{succ u3, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} C (CategoryTheory.Category.toCategoryStruct.{u3, u1} C _inst_1)) X Y) (CategoryTheory.Preadditive.homGroup.{u3, u1} C _inst_1 _inst_3 X Y))))) (AddMonoid.toAddZeroClass.{u4} (Quiver.Hom.{succ u4, u2} D (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} D (CategoryTheory.Category.toCategoryStruct.{u4, u2} D _inst_2)) (CategoryTheory.Functor.obj.{u3, u4, u1, u2} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u3, u4, u1, u2} C _inst_1 D _inst_2 F Y)) (SubNegMonoid.toAddMonoid.{u4} (Quiver.Hom.{succ u4, u2} D (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} D (CategoryTheory.Category.toCategoryStruct.{u4, u2} D _inst_2)) (CategoryTheory.Functor.obj.{u3, u4, u1, u2} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u3, u4, u1, u2} C _inst_1 D _inst_2 F Y)) (AddGroup.toSubNegMonoid.{u4} (Quiver.Hom.{succ u4, u2} D (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} D (CategoryTheory.Category.toCategoryStruct.{u4, u2} D _inst_2)) (CategoryTheory.Functor.obj.{u3, u4, u1, u2} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u3, u4, u1, u2} C _inst_1 D _inst_2 F Y)) (AddCommGroup.toAddGroup.{u4} (Quiver.Hom.{succ u4, u2} D (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} D (CategoryTheory.Category.toCategoryStruct.{u4, u2} D _inst_2)) (CategoryTheory.Functor.obj.{u3, u4, u1, u2} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u3, u4, u1, u2} C _inst_1 D _inst_2 F Y)) (CategoryTheory.Preadditive.homGroup.{u4, u2} D _inst_2 _inst_4 (CategoryTheory.Functor.obj.{u3, u4, u1, u2} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u3, u4, u1, u2} C _inst_1 D _inst_2 F Y))))))
but is expected to have type
  forall {C : Type.{u1}} {D : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u1} C] [_inst_2 : CategoryTheory.Category.{u4, u2} D] [_inst_3 : CategoryTheory.Preadditive.{u3, u1} C _inst_1] [_inst_4 : CategoryTheory.Preadditive.{u4, u2} D _inst_2] (F : CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2) [_inst_5 : CategoryTheory.Functor.Additive.{u1, u2, u3, u4} C D _inst_1 _inst_2 _inst_3 _inst_4 F] {X : C} {Y : C}, AddMonoidHom.{u3, u4} (Quiver.Hom.{succ u3, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} C (CategoryTheory.Category.toCategoryStruct.{u3, u1} C _inst_1)) X Y) (Quiver.Hom.{succ u4, u2} D (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} D (CategoryTheory.Category.toCategoryStruct.{u4, u2} D _inst_2)) (Prefunctor.obj.{succ u3, succ u4, u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} C (CategoryTheory.Category.toCategoryStruct.{u3, u1} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} D (CategoryTheory.Category.toCategoryStruct.{u4, u2} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u3, u4, u1, u2} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u3, succ u4, u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} C (CategoryTheory.Category.toCategoryStruct.{u3, u1} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} D (CategoryTheory.Category.toCategoryStruct.{u4, u2} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u3, u4, u1, u2} C _inst_1 D _inst_2 F) Y)) (AddMonoid.toAddZeroClass.{u3} (Quiver.Hom.{succ u3, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} C (CategoryTheory.Category.toCategoryStruct.{u3, u1} C _inst_1)) X Y) (SubNegMonoid.toAddMonoid.{u3} (Quiver.Hom.{succ u3, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} C (CategoryTheory.Category.toCategoryStruct.{u3, u1} C _inst_1)) X Y) (AddGroup.toSubNegMonoid.{u3} (Quiver.Hom.{succ u3, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} C (CategoryTheory.Category.toCategoryStruct.{u3, u1} C _inst_1)) X Y) (AddCommGroup.toAddGroup.{u3} (Quiver.Hom.{succ u3, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} C (CategoryTheory.Category.toCategoryStruct.{u3, u1} C _inst_1)) X Y) (CategoryTheory.Preadditive.homGroup.{u3, u1} C _inst_1 _inst_3 X Y))))) (AddMonoid.toAddZeroClass.{u4} (Quiver.Hom.{succ u4, u2} D (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} D (CategoryTheory.Category.toCategoryStruct.{u4, u2} D _inst_2)) (Prefunctor.obj.{succ u3, succ u4, u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} C (CategoryTheory.Category.toCategoryStruct.{u3, u1} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} D (CategoryTheory.Category.toCategoryStruct.{u4, u2} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u3, u4, u1, u2} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u3, succ u4, u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} C (CategoryTheory.Category.toCategoryStruct.{u3, u1} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} D (CategoryTheory.Category.toCategoryStruct.{u4, u2} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u3, u4, u1, u2} C _inst_1 D _inst_2 F) Y)) (SubNegMonoid.toAddMonoid.{u4} (Quiver.Hom.{succ u4, u2} D (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} D (CategoryTheory.Category.toCategoryStruct.{u4, u2} D _inst_2)) (Prefunctor.obj.{succ u3, succ u4, u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} C (CategoryTheory.Category.toCategoryStruct.{u3, u1} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} D (CategoryTheory.Category.toCategoryStruct.{u4, u2} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u3, u4, u1, u2} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u3, succ u4, u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} C (CategoryTheory.Category.toCategoryStruct.{u3, u1} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} D (CategoryTheory.Category.toCategoryStruct.{u4, u2} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u3, u4, u1, u2} C _inst_1 D _inst_2 F) Y)) (AddGroup.toSubNegMonoid.{u4} (Quiver.Hom.{succ u4, u2} D (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} D (CategoryTheory.Category.toCategoryStruct.{u4, u2} D _inst_2)) (Prefunctor.obj.{succ u3, succ u4, u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} C (CategoryTheory.Category.toCategoryStruct.{u3, u1} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} D (CategoryTheory.Category.toCategoryStruct.{u4, u2} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u3, u4, u1, u2} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u3, succ u4, u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} C (CategoryTheory.Category.toCategoryStruct.{u3, u1} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} D (CategoryTheory.Category.toCategoryStruct.{u4, u2} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u3, u4, u1, u2} C _inst_1 D _inst_2 F) Y)) (AddCommGroup.toAddGroup.{u4} (Quiver.Hom.{succ u4, u2} D (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} D (CategoryTheory.Category.toCategoryStruct.{u4, u2} D _inst_2)) (Prefunctor.obj.{succ u3, succ u4, u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} C (CategoryTheory.Category.toCategoryStruct.{u3, u1} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} D (CategoryTheory.Category.toCategoryStruct.{u4, u2} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u3, u4, u1, u2} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u3, succ u4, u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} C (CategoryTheory.Category.toCategoryStruct.{u3, u1} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} D (CategoryTheory.Category.toCategoryStruct.{u4, u2} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u3, u4, u1, u2} C _inst_1 D _inst_2 F) Y)) (CategoryTheory.Preadditive.homGroup.{u4, u2} D _inst_2 _inst_4 (Prefunctor.obj.{succ u3, succ u4, u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} C (CategoryTheory.Category.toCategoryStruct.{u3, u1} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} D (CategoryTheory.Category.toCategoryStruct.{u4, u2} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u3, u4, u1, u2} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u3, succ u4, u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} C (CategoryTheory.Category.toCategoryStruct.{u3, u1} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} D (CategoryTheory.Category.toCategoryStruct.{u4, u2} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u3, u4, u1, u2} C _inst_1 D _inst_2 F) Y))))))
Case conversion may be inaccurate. Consider using '#align category_theory.functor.map_add_hom CategoryTheory.Functor.mapAddHomₓ'. -/
/-- `F.map_add_hom` is an additive homomorphism whose underlying function is `F.map`. -/
@[simps (config := { fullyApplied := false })]
def mapAddHom {X Y : C} : (X ⟶ Y) →+ (F.obj X ⟶ F.obj Y) :=
  AddMonoidHom.mk' (fun f => F.map f) fun f g => F.map_add
#align category_theory.functor.map_add_hom CategoryTheory.Functor.mapAddHom

/- warning: category_theory.functor.coe_map_add_hom -> CategoryTheory.Functor.coe_mapAddHom is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.functor.coe_map_add_hom CategoryTheory.Functor.coe_mapAddHomₓ'. -/
theorem coe_mapAddHom {X Y : C} : ⇑(F.mapAddHom : (X ⟶ Y) →+ _) = @map C _ D _ F X Y :=
  rfl
#align category_theory.functor.coe_map_add_hom CategoryTheory.Functor.coe_mapAddHom

#print CategoryTheory.Functor.preservesZeroMorphisms_of_additive /-
instance (priority := 100) preservesZeroMorphisms_of_additive : PreservesZeroMorphisms F
    where map_zero' X Y := F.mapAddHom.map_zero
#align category_theory.functor.preserves_zero_morphisms_of_additive CategoryTheory.Functor.preservesZeroMorphisms_of_additive
-/

instance : Additive (𝟭 C) where

instance {E : Type _} [Category E] [Preadditive E] (G : D ⥤ E) [Functor.Additive G] :
    Additive (F ⋙ G) where

/- warning: category_theory.functor.map_neg -> CategoryTheory.Functor.map_neg is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.functor.map_neg CategoryTheory.Functor.map_negₓ'. -/
@[simp]
theorem map_neg {X Y : C} {f : X ⟶ Y} : F.map (-f) = -F.map f :=
  (F.mapAddHom : (X ⟶ Y) →+ (F.obj X ⟶ F.obj Y)).map_neg _
#align category_theory.functor.map_neg CategoryTheory.Functor.map_neg

/- warning: category_theory.functor.map_sub -> CategoryTheory.Functor.map_sub is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.functor.map_sub CategoryTheory.Functor.map_subₓ'. -/
@[simp]
theorem map_sub {X Y : C} {f g : X ⟶ Y} : F.map (f - g) = F.map f - F.map g :=
  (F.mapAddHom : (X ⟶ Y) →+ (F.obj X ⟶ F.obj Y)).map_sub _ _
#align category_theory.functor.map_sub CategoryTheory.Functor.map_sub

/- warning: category_theory.functor.map_nsmul -> CategoryTheory.Functor.map_nsmul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.functor.map_nsmul CategoryTheory.Functor.map_nsmulₓ'. -/
theorem map_nsmul {X Y : C} {f : X ⟶ Y} {n : ℕ} : F.map (n • f) = n • F.map f :=
  (F.mapAddHom : (X ⟶ Y) →+ (F.obj X ⟶ F.obj Y)).map_nsmul _ _
#align category_theory.functor.map_nsmul CategoryTheory.Functor.map_nsmul

/- warning: category_theory.functor.map_zsmul -> CategoryTheory.Functor.map_zsmul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.functor.map_zsmul CategoryTheory.Functor.map_zsmulₓ'. -/
-- You can alternatively just use `functor.map_smul` here, with an explicit `(r : ℤ)` argument.
theorem map_zsmul {X Y : C} {f : X ⟶ Y} {r : ℤ} : F.map (r • f) = r • F.map f :=
  (F.mapAddHom : (X ⟶ Y) →+ (F.obj X ⟶ F.obj Y)).map_zsmul _ _
#align category_theory.functor.map_zsmul CategoryTheory.Functor.map_zsmul

open BigOperators

/- warning: category_theory.functor.map_sum -> CategoryTheory.Functor.map_sum is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} {D : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u1} C] [_inst_2 : CategoryTheory.Category.{u4, u2} D] [_inst_3 : CategoryTheory.Preadditive.{u3, u1} C _inst_1] [_inst_4 : CategoryTheory.Preadditive.{u4, u2} D _inst_2] (F : CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2) [_inst_5 : CategoryTheory.Functor.Additive.{u1, u2, u3, u4} C D _inst_1 _inst_2 _inst_3 _inst_4 F] {X : C} {Y : C} {α : Type.{u5}} (f : α -> (Quiver.Hom.{succ u3, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} C (CategoryTheory.Category.toCategoryStruct.{u3, u1} C _inst_1)) X Y)) (s : Finset.{u5} α), Eq.{succ u4} (Quiver.Hom.{succ u4, u2} D (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} D (CategoryTheory.Category.toCategoryStruct.{u4, u2} D _inst_2)) (CategoryTheory.Functor.obj.{u3, u4, u1, u2} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u3, u4, u1, u2} C _inst_1 D _inst_2 F Y)) (CategoryTheory.Functor.map.{u3, u4, u1, u2} C _inst_1 D _inst_2 F X Y (Finset.sum.{u3, u5} (Quiver.Hom.{succ u3, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} C (CategoryTheory.Category.toCategoryStruct.{u3, u1} C _inst_1)) X Y) α (AddCommGroup.toAddCommMonoid.{u3} (Quiver.Hom.{succ u3, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} C (CategoryTheory.Category.toCategoryStruct.{u3, u1} C _inst_1)) X Y) (CategoryTheory.Preadditive.homGroup.{u3, u1} C _inst_1 _inst_3 X Y)) s (fun (a : α) => f a))) (Finset.sum.{u4, u5} (Quiver.Hom.{succ u4, u2} D (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} D (CategoryTheory.Category.toCategoryStruct.{u4, u2} D _inst_2)) (CategoryTheory.Functor.obj.{u3, u4, u1, u2} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u3, u4, u1, u2} C _inst_1 D _inst_2 F Y)) α (AddCommGroup.toAddCommMonoid.{u4} (Quiver.Hom.{succ u4, u2} D (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} D (CategoryTheory.Category.toCategoryStruct.{u4, u2} D _inst_2)) (CategoryTheory.Functor.obj.{u3, u4, u1, u2} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u3, u4, u1, u2} C _inst_1 D _inst_2 F Y)) (CategoryTheory.Preadditive.homGroup.{u4, u2} D _inst_2 _inst_4 (CategoryTheory.Functor.obj.{u3, u4, u1, u2} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u3, u4, u1, u2} C _inst_1 D _inst_2 F Y))) s (fun (a : α) => CategoryTheory.Functor.map.{u3, u4, u1, u2} C _inst_1 D _inst_2 F X Y (f a)))
but is expected to have type
  forall {C : Type.{u3}} {D : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u4, u3} C] [_inst_2 : CategoryTheory.Category.{u2, u1} D] [_inst_3 : CategoryTheory.Preadditive.{u4, u3} C _inst_1] [_inst_4 : CategoryTheory.Preadditive.{u2, u1} D _inst_2] (F : CategoryTheory.Functor.{u4, u2, u3, u1} C _inst_1 D _inst_2) [_inst_5 : CategoryTheory.Functor.Additive.{u3, u1, u4, u2} C D _inst_1 _inst_2 _inst_3 _inst_4 F] {X : C} {Y : C} {α : Type.{u5}} (f : α -> (Quiver.Hom.{succ u4, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} C (CategoryTheory.Category.toCategoryStruct.{u4, u3} C _inst_1)) X Y)) (s : Finset.{u5} α), Eq.{succ u2} (Quiver.Hom.{succ u2, u1} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} D (CategoryTheory.Category.toCategoryStruct.{u2, u1} D _inst_2)) (Prefunctor.obj.{succ u4, succ u2, u3, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} C (CategoryTheory.Category.toCategoryStruct.{u4, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} D (CategoryTheory.Category.toCategoryStruct.{u2, u1} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u4, u2, u3, u1} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u4, succ u2, u3, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} C (CategoryTheory.Category.toCategoryStruct.{u4, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} D (CategoryTheory.Category.toCategoryStruct.{u2, u1} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u4, u2, u3, u1} C _inst_1 D _inst_2 F) Y)) (Prefunctor.map.{succ u4, succ u2, u3, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} C (CategoryTheory.Category.toCategoryStruct.{u4, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} D (CategoryTheory.Category.toCategoryStruct.{u2, u1} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u4, u2, u3, u1} C _inst_1 D _inst_2 F) X Y (Finset.sum.{u4, u5} (Quiver.Hom.{succ u4, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} C (CategoryTheory.Category.toCategoryStruct.{u4, u3} C _inst_1)) X Y) α (AddCommGroup.toAddCommMonoid.{u4} (Quiver.Hom.{succ u4, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} C (CategoryTheory.Category.toCategoryStruct.{u4, u3} C _inst_1)) X Y) (CategoryTheory.Preadditive.homGroup.{u4, u3} C _inst_1 _inst_3 X Y)) s (fun (a : α) => f a))) (Finset.sum.{u2, u5} (Quiver.Hom.{succ u2, u1} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} D (CategoryTheory.Category.toCategoryStruct.{u2, u1} D _inst_2)) (Prefunctor.obj.{succ u4, succ u2, u3, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} C (CategoryTheory.Category.toCategoryStruct.{u4, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} D (CategoryTheory.Category.toCategoryStruct.{u2, u1} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u4, u2, u3, u1} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u4, succ u2, u3, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} C (CategoryTheory.Category.toCategoryStruct.{u4, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} D (CategoryTheory.Category.toCategoryStruct.{u2, u1} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u4, u2, u3, u1} C _inst_1 D _inst_2 F) Y)) α (AddCommGroup.toAddCommMonoid.{u2} (Quiver.Hom.{succ u2, u1} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} D (CategoryTheory.Category.toCategoryStruct.{u2, u1} D _inst_2)) (Prefunctor.obj.{succ u4, succ u2, u3, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} C (CategoryTheory.Category.toCategoryStruct.{u4, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} D (CategoryTheory.Category.toCategoryStruct.{u2, u1} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u4, u2, u3, u1} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u4, succ u2, u3, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} C (CategoryTheory.Category.toCategoryStruct.{u4, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} D (CategoryTheory.Category.toCategoryStruct.{u2, u1} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u4, u2, u3, u1} C _inst_1 D _inst_2 F) Y)) (CategoryTheory.Preadditive.homGroup.{u2, u1} D _inst_2 _inst_4 (Prefunctor.obj.{succ u4, succ u2, u3, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} C (CategoryTheory.Category.toCategoryStruct.{u4, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} D (CategoryTheory.Category.toCategoryStruct.{u2, u1} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u4, u2, u3, u1} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u4, succ u2, u3, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} C (CategoryTheory.Category.toCategoryStruct.{u4, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} D (CategoryTheory.Category.toCategoryStruct.{u2, u1} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u4, u2, u3, u1} C _inst_1 D _inst_2 F) Y))) s (fun (a : α) => Prefunctor.map.{succ u4, succ u2, u3, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} C (CategoryTheory.Category.toCategoryStruct.{u4, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} D (CategoryTheory.Category.toCategoryStruct.{u2, u1} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u4, u2, u3, u1} C _inst_1 D _inst_2 F) X Y (f a)))
Case conversion may be inaccurate. Consider using '#align category_theory.functor.map_sum CategoryTheory.Functor.map_sumₓ'. -/
@[simp]
theorem map_sum {X Y : C} {α : Type _} (f : α → (X ⟶ Y)) (s : Finset α) :
    F.map (∑ a in s, f a) = ∑ a in s, F.map (f a) :=
  (F.mapAddHom : (X ⟶ Y) →+ _).map_sum f s
#align category_theory.functor.map_sum CategoryTheory.Functor.map_sum

end

section InducedCategory

variable {C : Type _} {D : Type _} [Category D] [Preadditive D] (F : C → D)

#print CategoryTheory.Functor.inducedFunctor_additive /-
instance inducedFunctor_additive : Functor.Additive (inducedFunctor F) where
#align category_theory.functor.induced_functor_additive CategoryTheory.Functor.inducedFunctor_additive
-/

end InducedCategory

/- warning: category_theory.functor.full_subcategory_inclusion_additive -> CategoryTheory.Functor.fullSubcategoryInclusion_additive is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C] [_inst_2 : CategoryTheory.Preadditive.{u2, u1} C _inst_1] (Z : C -> Prop), CategoryTheory.Functor.Additive.{u1, u1, u2, u2} (CategoryTheory.FullSubcategoryₓ.{u2, u1} C _inst_1 Z) C (CategoryTheory.InducedCategory.category.{u2, u1, u1} (CategoryTheory.FullSubcategoryₓ.{u2, u1} C _inst_1 Z) C _inst_1 (CategoryTheory.FullSubcategoryₓ.obj.{u2, u1} C _inst_1 Z)) _inst_1 (CategoryTheory.Preadditive.fullSubcategory.{u2, u1} C _inst_1 _inst_2 Z) _inst_2 (CategoryTheory.fullSubcategoryInclusion.{u2, u1} C _inst_1 Z)
but is expected to have type
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C] [_inst_2 : CategoryTheory.Preadditive.{u2, u1} C _inst_1] (Z : C -> Prop), CategoryTheory.Functor.Additive.{u1, u1, u2, u2} (CategoryTheory.FullSubcategory.{u1} C Z) C (CategoryTheory.FullSubcategory.category.{u2, u1} C _inst_1 Z) _inst_1 (CategoryTheory.Preadditive.fullSubcategory.{u2, u1} C _inst_1 _inst_2 Z) _inst_2 (CategoryTheory.fullSubcategoryInclusion.{u2, u1} C _inst_1 Z)
Case conversion may be inaccurate. Consider using '#align category_theory.functor.full_subcategory_inclusion_additive CategoryTheory.Functor.fullSubcategoryInclusion_additiveₓ'. -/
instance fullSubcategoryInclusion_additive {C : Type _} [Category C] [Preadditive C]
    (Z : C → Prop) : (fullSubcategoryInclusion Z).Additive where
#align category_theory.functor.full_subcategory_inclusion_additive CategoryTheory.Functor.fullSubcategoryInclusion_additive

section

-- To talk about preservation of biproducts we need to specify universes explicitly.
noncomputable section

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] [Preadditive C]
  [Preadditive D] (F : C ⥤ D)

open CategoryTheory.Limits

open CategoryTheory.Preadditive

#print CategoryTheory.Functor.preservesFiniteBiproductsOfAdditive /-
instance (priority := 100) preservesFiniteBiproductsOfAdditive [Additive F] :
    PreservesFiniteBiproducts F
    where preserves J _ :=
    {
      preserves := fun f =>
        {
          preserves := fun b hb =>
            is_bilimit_of_total _
              (by
                simp_rw [F.map_bicone_π, F.map_bicone_ι, ← F.map_comp, ← F.map_sum]
                dsimp only [map_bicone_X]
                simp_rw [← F.map_id]
                refine' congr_arg _ (hb.is_limit.hom_ext fun j => hb.is_colimit.hom_ext fun j' => _)
                cases j; cases j'
                dsimp only [limits.bicone.to_cone_π_app]
                simp [sum_comp, comp_sum, bicone.ι_π, comp_dite, dite_comp]) } }
#align category_theory.functor.preserves_finite_biproducts_of_additive CategoryTheory.Functor.preservesFiniteBiproductsOfAdditive
-/

#print CategoryTheory.Functor.additive_of_preservesBinaryBiproducts /-
theorem additive_of_preservesBinaryBiproducts [HasBinaryBiproducts C] [PreservesZeroMorphisms F]
    [PreservesBinaryBiproducts F] : Additive F :=
  {
    map_add' := fun X Y f g => by
      rw [biprod.add_eq_lift_id_desc, F.map_comp, ← biprod.lift_map_biprod, ←
        biprod.map_biprod_hom_desc, category.assoc, iso.inv_hom_id_assoc, F.map_id,
        biprod.add_eq_lift_id_desc] }
#align category_theory.functor.additive_of_preserves_binary_biproducts CategoryTheory.Functor.additive_of_preservesBinaryBiproducts
-/

end

end Functor

namespace Equivalence

variable {C D : Type _} [Category C] [Category D] [Preadditive C] [Preadditive D]

/- warning: category_theory.equivalence.inverse_additive -> CategoryTheory.Equivalence.inverse_additive is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} {D : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u1} C] [_inst_2 : CategoryTheory.Category.{u4, u2} D] [_inst_3 : CategoryTheory.Preadditive.{u3, u1} C _inst_1] [_inst_4 : CategoryTheory.Preadditive.{u4, u2} D _inst_2] (e : CategoryTheory.Equivalence.{u3, u4, u1, u2} C _inst_1 D _inst_2) [_inst_5 : CategoryTheory.Functor.Additive.{u1, u2, u3, u4} C D _inst_1 _inst_2 _inst_3 _inst_4 (CategoryTheory.Equivalence.functor.{u3, u4, u1, u2} C _inst_1 D _inst_2 e)], CategoryTheory.Functor.Additive.{u2, u1, u4, u3} D C _inst_2 _inst_1 _inst_4 _inst_3 (CategoryTheory.Equivalence.inverse.{u3, u4, u1, u2} C _inst_1 D _inst_2 e)
but is expected to have type
  forall {C : Type.{u1}} {D : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u1} C] [_inst_2 : CategoryTheory.Category.{u4, u2} D] [_inst_3 : CategoryTheory.Preadditive.{u3, u1} C _inst_1] [_inst_4 : CategoryTheory.Preadditive.{u4, u2} D _inst_2] (e : CategoryTheory.Equivalence.{u3, u4, u1, u2} C D _inst_1 _inst_2) [_inst_5 : CategoryTheory.Functor.Additive.{u1, u2, u3, u4} C D _inst_1 _inst_2 _inst_3 _inst_4 (CategoryTheory.Equivalence.functor.{u3, u4, u1, u2} C D _inst_1 _inst_2 e)], CategoryTheory.Functor.Additive.{u2, u1, u4, u3} D C _inst_2 _inst_1 _inst_4 _inst_3 (CategoryTheory.Equivalence.inverse.{u3, u4, u1, u2} C D _inst_1 _inst_2 e)
Case conversion may be inaccurate. Consider using '#align category_theory.equivalence.inverse_additive CategoryTheory.Equivalence.inverse_additiveₓ'. -/
instance inverse_additive (e : C ≌ D) [e.Functor.Additive] : e.inverse.Additive
    where map_add' X Y f g := by apply e.functor.map_injective; simp
#align category_theory.equivalence.inverse_additive CategoryTheory.Equivalence.inverse_additive

end Equivalence

section

variable (C D : Type _) [Category C] [Category D] [Preadditive C] [Preadditive D]

#print CategoryTheory.AdditiveFunctor /-
/-- Bundled additive functors. -/
@[nolint has_nonempty_instance]
def AdditiveFunctor :=
  FullSubcategory fun F : C ⥤ D => F.Additive deriving Category
#align category_theory.AdditiveFunctor CategoryTheory.AdditiveFunctor
-/

-- mathport name: «expr ⥤+ »
infixr:26 " ⥤+ " => AdditiveFunctor

instance : Preadditive (C ⥤+ D) :=
  Preadditive.inducedCategory _

#print CategoryTheory.AdditiveFunctor.forget /-
/-- An additive functor is in particular a functor. -/
def AdditiveFunctor.forget : (C ⥤+ D) ⥤ C ⥤ D :=
  fullSubcategoryInclusion _ deriving Full, Faithful
#align category_theory.AdditiveFunctor.forget CategoryTheory.AdditiveFunctor.forget
-/

variable {C D}

#print CategoryTheory.AdditiveFunctor.of /-
/-- Turn an additive functor into an object of the category `AdditiveFunctor C D`. -/
def AdditiveFunctor.of (F : C ⥤ D) [F.Additive] : C ⥤+ D :=
  ⟨F, inferInstance⟩
#align category_theory.AdditiveFunctor.of CategoryTheory.AdditiveFunctor.of
-/

/- warning: category_theory.AdditiveFunctor.of_fst -> CategoryTheory.AdditiveFunctor.of_fst is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} {D : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u1} C] [_inst_2 : CategoryTheory.Category.{u4, u2} D] [_inst_3 : CategoryTheory.Preadditive.{u3, u1} C _inst_1] [_inst_4 : CategoryTheory.Preadditive.{u4, u2} D _inst_2] (F : CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2) [_inst_5 : CategoryTheory.Functor.Additive.{u1, u2, u3, u4} C D _inst_1 _inst_2 _inst_3 _inst_4 F], Eq.{succ (max u3 u4 u1 u2)} (CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2) (CategoryTheory.FullSubcategoryₓ.obj.{max u1 u4, max u3 u4 u1 u2} (CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u3, u4, u1, u2} C _inst_1 D _inst_2) (fun (F : CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2) => CategoryTheory.Functor.Additive.{u1, u2, u3, u4} C D _inst_1 _inst_2 _inst_3 _inst_4 F) (CategoryTheory.AdditiveFunctor.of.{u1, u2, u3, u4} C D _inst_1 _inst_2 _inst_3 _inst_4 F _inst_5)) F
but is expected to have type
  forall {C : Type.{u2}} {D : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u4, u2} C] [_inst_2 : CategoryTheory.Category.{u3, u1} D] [_inst_3 : CategoryTheory.Preadditive.{u4, u2} C _inst_1] [_inst_4 : CategoryTheory.Preadditive.{u3, u1} D _inst_2] (F : CategoryTheory.Functor.{u4, u3, u2, u1} C _inst_1 D _inst_2) [_inst_5 : CategoryTheory.Functor.Additive.{u2, u1, u4, u3} C D _inst_1 _inst_2 _inst_3 _inst_4 F], Eq.{max (max (max (succ u2) (succ u1)) (succ u4)) (succ u3)} (CategoryTheory.Functor.{u4, u3, u2, u1} C _inst_1 D _inst_2) (CategoryTheory.FullSubcategory.obj.{max (max (max u2 u1) u4) u3} (CategoryTheory.Functor.{u4, u3, u2, u1} C _inst_1 D _inst_2) (fun (F : CategoryTheory.Functor.{u4, u3, u2, u1} C _inst_1 D _inst_2) => CategoryTheory.Functor.Additive.{u2, u1, u4, u3} C D _inst_1 _inst_2 _inst_3 _inst_4 F) (CategoryTheory.AdditiveFunctor.of.{u2, u1, u4, u3} C D _inst_1 _inst_2 _inst_3 _inst_4 F _inst_5)) F
Case conversion may be inaccurate. Consider using '#align category_theory.AdditiveFunctor.of_fst CategoryTheory.AdditiveFunctor.of_fstₓ'. -/
@[simp]
theorem AdditiveFunctor.of_fst (F : C ⥤ D) [F.Additive] : (AdditiveFunctor.of F).1 = F :=
  rfl
#align category_theory.AdditiveFunctor.of_fst CategoryTheory.AdditiveFunctor.of_fst

/- warning: category_theory.AdditiveFunctor.forget_obj -> CategoryTheory.AdditiveFunctor.forget_obj is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} {D : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u1} C] [_inst_2 : CategoryTheory.Category.{u4, u2} D] [_inst_3 : CategoryTheory.Preadditive.{u3, u1} C _inst_1] [_inst_4 : CategoryTheory.Preadditive.{u4, u2} D _inst_2] (F : CategoryTheory.AdditiveFunctor.{u1, u2, u3, u4} C D _inst_1 _inst_2 _inst_3 _inst_4), Eq.{succ (max u3 u4 u1 u2)} (CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2) (CategoryTheory.Functor.obj.{max u1 u4, max u1 u4, max u3 u4 u1 u2, max u3 u4 u1 u2} (CategoryTheory.AdditiveFunctor.{u1, u2, u3, u4} C D _inst_1 _inst_2 _inst_3 _inst_4) (CategoryTheory.AdditiveFunctor.category.{u1, u4, u3, u2} C D _inst_1 _inst_2 _inst_3 _inst_4) (CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u3, u4, u1, u2} C _inst_1 D _inst_2) (CategoryTheory.AdditiveFunctor.forget.{u1, u2, u3, u4} C D _inst_1 _inst_2 _inst_3 _inst_4) F) (CategoryTheory.FullSubcategoryₓ.obj.{max u1 u4, max u3 u4 u1 u2} (CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u3, u4, u1, u2} C _inst_1 D _inst_2) (fun (F : CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2) => CategoryTheory.Functor.Additive.{u1, u2, u3, u4} C D _inst_1 _inst_2 _inst_3 _inst_4 F) F)
but is expected to have type
  forall {C : Type.{u4}} {D : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u4} C] [_inst_2 : CategoryTheory.Category.{u1, u3} D] [_inst_3 : CategoryTheory.Preadditive.{u2, u4} C _inst_1] [_inst_4 : CategoryTheory.Preadditive.{u1, u3} D _inst_2] (F : CategoryTheory.AdditiveFunctor.{u4, u3, u2, u1} C D _inst_1 _inst_2 _inst_3 _inst_4), Eq.{max (max (max (succ u4) (succ u3)) (succ u2)) (succ u1)} (CategoryTheory.Functor.{u2, u1, u4, u3} C _inst_1 D _inst_2) (Prefunctor.obj.{max (succ u4) (succ u1), max (succ u4) (succ u1), max (max (max u4 u3) u2) u1, max (max (max u4 u3) u2) u1} (CategoryTheory.AdditiveFunctor.{u4, u3, u2, u1} C D _inst_1 _inst_2 _inst_3 _inst_4) (CategoryTheory.CategoryStruct.toQuiver.{max u4 u1, max (max (max u4 u3) u2) u1} (CategoryTheory.AdditiveFunctor.{u4, u3, u2, u1} C D _inst_1 _inst_2 _inst_3 _inst_4) (CategoryTheory.Category.toCategoryStruct.{max u4 u1, max (max (max u4 u3) u2) u1} (CategoryTheory.AdditiveFunctor.{u4, u3, u2, u1} C D _inst_1 _inst_2 _inst_3 _inst_4) (CategoryTheory.instCategoryAdditiveFunctor.{u4, u3, u2, u1} C D _inst_1 _inst_2 _inst_3 _inst_4))) (CategoryTheory.Functor.{u2, u1, u4, u3} C _inst_1 D _inst_2) (CategoryTheory.CategoryStruct.toQuiver.{max u4 u1, max (max (max u4 u3) u2) u1} (CategoryTheory.Functor.{u2, u1, u4, u3} C _inst_1 D _inst_2) (CategoryTheory.Category.toCategoryStruct.{max u4 u1, max (max (max u4 u3) u2) u1} (CategoryTheory.Functor.{u2, u1, u4, u3} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u2, u1, u4, u3} C _inst_1 D _inst_2))) (CategoryTheory.Functor.toPrefunctor.{max u4 u1, max u4 u1, max (max (max u4 u3) u2) u1, max (max (max u4 u3) u2) u1} (CategoryTheory.AdditiveFunctor.{u4, u3, u2, u1} C D _inst_1 _inst_2 _inst_3 _inst_4) (CategoryTheory.instCategoryAdditiveFunctor.{u4, u3, u2, u1} C D _inst_1 _inst_2 _inst_3 _inst_4) (CategoryTheory.Functor.{u2, u1, u4, u3} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u2, u1, u4, u3} C _inst_1 D _inst_2) (CategoryTheory.AdditiveFunctor.forget.{u4, u3, u2, u1} C D _inst_1 _inst_2 _inst_3 _inst_4)) F) (CategoryTheory.FullSubcategory.obj.{max (max (max u4 u3) u2) u1} (CategoryTheory.Functor.{u2, u1, u4, u3} C _inst_1 D _inst_2) (fun (F : CategoryTheory.Functor.{u2, u1, u4, u3} C _inst_1 D _inst_2) => CategoryTheory.Functor.Additive.{u4, u3, u2, u1} C D _inst_1 _inst_2 _inst_3 _inst_4 F) F)
Case conversion may be inaccurate. Consider using '#align category_theory.AdditiveFunctor.forget_obj CategoryTheory.AdditiveFunctor.forget_objₓ'. -/
@[simp]
theorem AdditiveFunctor.forget_obj (F : C ⥤+ D) : (AdditiveFunctor.forget C D).obj F = F.1 :=
  rfl
#align category_theory.AdditiveFunctor.forget_obj CategoryTheory.AdditiveFunctor.forget_obj

/- warning: category_theory.AdditiveFunctor.forget_obj_of -> CategoryTheory.AdditiveFunctor.forget_obj_of is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} {D : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u1} C] [_inst_2 : CategoryTheory.Category.{u4, u2} D] [_inst_3 : CategoryTheory.Preadditive.{u3, u1} C _inst_1] [_inst_4 : CategoryTheory.Preadditive.{u4, u2} D _inst_2] (F : CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2) [_inst_5 : CategoryTheory.Functor.Additive.{u1, u2, u3, u4} C D _inst_1 _inst_2 _inst_3 _inst_4 F], Eq.{succ (max u3 u4 u1 u2)} (CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2) (CategoryTheory.Functor.obj.{max u1 u4, max u1 u4, max u3 u4 u1 u2, max u3 u4 u1 u2} (CategoryTheory.AdditiveFunctor.{u1, u2, u3, u4} C D _inst_1 _inst_2 _inst_3 _inst_4) (CategoryTheory.AdditiveFunctor.category.{u1, u4, u3, u2} C D _inst_1 _inst_2 _inst_3 _inst_4) (CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u3, u4, u1, u2} C _inst_1 D _inst_2) (CategoryTheory.AdditiveFunctor.forget.{u1, u2, u3, u4} C D _inst_1 _inst_2 _inst_3 _inst_4) (CategoryTheory.AdditiveFunctor.of.{u1, u2, u3, u4} C D _inst_1 _inst_2 _inst_3 _inst_4 F _inst_5)) F
but is expected to have type
  forall {C : Type.{u2}} {D : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u4, u2} C] [_inst_2 : CategoryTheory.Category.{u3, u1} D] [_inst_3 : CategoryTheory.Preadditive.{u4, u2} C _inst_1] [_inst_4 : CategoryTheory.Preadditive.{u3, u1} D _inst_2] (F : CategoryTheory.Functor.{u4, u3, u2, u1} C _inst_1 D _inst_2) [_inst_5 : CategoryTheory.Functor.Additive.{u2, u1, u4, u3} C D _inst_1 _inst_2 _inst_3 _inst_4 F], Eq.{max (max (max (succ u2) (succ u1)) (succ u4)) (succ u3)} (CategoryTheory.Functor.{u4, u3, u2, u1} C _inst_1 D _inst_2) (Prefunctor.obj.{max (succ u2) (succ u3), max (succ u2) (succ u3), max (max (max u2 u1) u4) u3, max (max (max u2 u1) u4) u3} (CategoryTheory.AdditiveFunctor.{u2, u1, u4, u3} C D _inst_1 _inst_2 _inst_3 _inst_4) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u3, max (max (max u2 u1) u4) u3} (CategoryTheory.AdditiveFunctor.{u2, u1, u4, u3} C D _inst_1 _inst_2 _inst_3 _inst_4) (CategoryTheory.Category.toCategoryStruct.{max u2 u3, max (max (max u2 u1) u4) u3} (CategoryTheory.AdditiveFunctor.{u2, u1, u4, u3} C D _inst_1 _inst_2 _inst_3 _inst_4) (CategoryTheory.instCategoryAdditiveFunctor.{u2, u1, u4, u3} C D _inst_1 _inst_2 _inst_3 _inst_4))) (CategoryTheory.Functor.{u4, u3, u2, u1} C _inst_1 D _inst_2) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u3, max (max (max u2 u1) u4) u3} (CategoryTheory.Functor.{u4, u3, u2, u1} C _inst_1 D _inst_2) (CategoryTheory.Category.toCategoryStruct.{max u2 u3, max (max (max u2 u1) u4) u3} (CategoryTheory.Functor.{u4, u3, u2, u1} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u4, u3, u2, u1} C _inst_1 D _inst_2))) (CategoryTheory.Functor.toPrefunctor.{max u2 u3, max u2 u3, max (max (max u2 u1) u4) u3, max (max (max u2 u1) u4) u3} (CategoryTheory.AdditiveFunctor.{u2, u1, u4, u3} C D _inst_1 _inst_2 _inst_3 _inst_4) (CategoryTheory.instCategoryAdditiveFunctor.{u2, u1, u4, u3} C D _inst_1 _inst_2 _inst_3 _inst_4) (CategoryTheory.Functor.{u4, u3, u2, u1} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u4, u3, u2, u1} C _inst_1 D _inst_2) (CategoryTheory.AdditiveFunctor.forget.{u2, u1, u4, u3} C D _inst_1 _inst_2 _inst_3 _inst_4)) (CategoryTheory.AdditiveFunctor.of.{u2, u1, u4, u3} C D _inst_1 _inst_2 _inst_3 _inst_4 F _inst_5)) F
Case conversion may be inaccurate. Consider using '#align category_theory.AdditiveFunctor.forget_obj_of CategoryTheory.AdditiveFunctor.forget_obj_ofₓ'. -/
theorem AdditiveFunctor.forget_obj_of (F : C ⥤ D) [F.Additive] :
    (AdditiveFunctor.forget C D).obj (AdditiveFunctor.of F) = F :=
  rfl
#align category_theory.AdditiveFunctor.forget_obj_of CategoryTheory.AdditiveFunctor.forget_obj_of

/- warning: category_theory.AdditiveFunctor.forget_map -> CategoryTheory.AdditiveFunctor.forget_map is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} {D : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u1} C] [_inst_2 : CategoryTheory.Category.{u4, u2} D] [_inst_3 : CategoryTheory.Preadditive.{u3, u1} C _inst_1] [_inst_4 : CategoryTheory.Preadditive.{u4, u2} D _inst_2] (F : CategoryTheory.AdditiveFunctor.{u1, u2, u3, u4} C D _inst_1 _inst_2 _inst_3 _inst_4) (G : CategoryTheory.AdditiveFunctor.{u1, u2, u3, u4} C D _inst_1 _inst_2 _inst_3 _inst_4) (α : Quiver.Hom.{succ (max u1 u4), max u3 u4 u1 u2} (CategoryTheory.AdditiveFunctor.{u1, u2, u3, u4} C D _inst_1 _inst_2 _inst_3 _inst_4) (CategoryTheory.CategoryStruct.toQuiver.{max u1 u4, max u3 u4 u1 u2} (CategoryTheory.AdditiveFunctor.{u1, u2, u3, u4} C D _inst_1 _inst_2 _inst_3 _inst_4) (CategoryTheory.Category.toCategoryStruct.{max u1 u4, max u3 u4 u1 u2} (CategoryTheory.AdditiveFunctor.{u1, u2, u3, u4} C D _inst_1 _inst_2 _inst_3 _inst_4) (CategoryTheory.AdditiveFunctor.category.{u1, u4, u3, u2} C D _inst_1 _inst_2 _inst_3 _inst_4))) F G), Eq.{succ (max u1 u4)} (Quiver.Hom.{succ (max u1 u4), max u3 u4 u1 u2} (CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2) (CategoryTheory.CategoryStruct.toQuiver.{max u1 u4, max u3 u4 u1 u2} (CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2) (CategoryTheory.Category.toCategoryStruct.{max u1 u4, max u3 u4 u1 u2} (CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u3, u4, u1, u2} C _inst_1 D _inst_2))) (CategoryTheory.Functor.obj.{max u1 u4, max u1 u4, max u3 u4 u1 u2, max u3 u4 u1 u2} (CategoryTheory.AdditiveFunctor.{u1, u2, u3, u4} C D _inst_1 _inst_2 _inst_3 _inst_4) (CategoryTheory.AdditiveFunctor.category.{u1, u4, u3, u2} C D _inst_1 _inst_2 _inst_3 _inst_4) (CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u3, u4, u1, u2} C _inst_1 D _inst_2) (CategoryTheory.AdditiveFunctor.forget.{u1, u2, u3, u4} C D _inst_1 _inst_2 _inst_3 _inst_4) F) (CategoryTheory.Functor.obj.{max u1 u4, max u1 u4, max u3 u4 u1 u2, max u3 u4 u1 u2} (CategoryTheory.AdditiveFunctor.{u1, u2, u3, u4} C D _inst_1 _inst_2 _inst_3 _inst_4) (CategoryTheory.AdditiveFunctor.category.{u1, u4, u3, u2} C D _inst_1 _inst_2 _inst_3 _inst_4) (CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u3, u4, u1, u2} C _inst_1 D _inst_2) (CategoryTheory.AdditiveFunctor.forget.{u1, u2, u3, u4} C D _inst_1 _inst_2 _inst_3 _inst_4) G)) (CategoryTheory.Functor.map.{max u1 u4, max u1 u4, max u3 u4 u1 u2, max u3 u4 u1 u2} (CategoryTheory.AdditiveFunctor.{u1, u2, u3, u4} C D _inst_1 _inst_2 _inst_3 _inst_4) (CategoryTheory.AdditiveFunctor.category.{u1, u4, u3, u2} C D _inst_1 _inst_2 _inst_3 _inst_4) (CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u3, u4, u1, u2} C _inst_1 D _inst_2) (CategoryTheory.AdditiveFunctor.forget.{u1, u2, u3, u4} C D _inst_1 _inst_2 _inst_3 _inst_4) F G α) α
but is expected to have type
  forall {C : Type.{u4}} {D : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u4} C] [_inst_2 : CategoryTheory.Category.{u1, u3} D] [_inst_3 : CategoryTheory.Preadditive.{u2, u4} C _inst_1] [_inst_4 : CategoryTheory.Preadditive.{u1, u3} D _inst_2] (F : CategoryTheory.AdditiveFunctor.{u4, u3, u2, u1} C D _inst_1 _inst_2 _inst_3 _inst_4) (G : CategoryTheory.AdditiveFunctor.{u4, u3, u2, u1} C D _inst_1 _inst_2 _inst_3 _inst_4) (α : Quiver.Hom.{max (succ u4) (succ u1), max (max (max u4 u3) u2) u1} (CategoryTheory.AdditiveFunctor.{u4, u3, u2, u1} C D _inst_1 _inst_2 _inst_3 _inst_4) (CategoryTheory.CategoryStruct.toQuiver.{max u4 u1, max (max (max u4 u3) u2) u1} (CategoryTheory.AdditiveFunctor.{u4, u3, u2, u1} C D _inst_1 _inst_2 _inst_3 _inst_4) (CategoryTheory.Category.toCategoryStruct.{max u4 u1, max (max (max u4 u3) u2) u1} (CategoryTheory.AdditiveFunctor.{u4, u3, u2, u1} C D _inst_1 _inst_2 _inst_3 _inst_4) (CategoryTheory.instCategoryAdditiveFunctor.{u4, u3, u2, u1} C D _inst_1 _inst_2 _inst_3 _inst_4))) F G), Eq.{max (succ u4) (succ u1)} (Quiver.Hom.{max (succ u4) (succ u1), max (max (max u4 u3) u2) u1} (CategoryTheory.Functor.{u2, u1, u4, u3} C _inst_1 D _inst_2) (CategoryTheory.CategoryStruct.toQuiver.{max u4 u1, max (max (max u4 u3) u2) u1} (CategoryTheory.Functor.{u2, u1, u4, u3} C _inst_1 D _inst_2) (CategoryTheory.Category.toCategoryStruct.{max u4 u1, max (max (max u4 u3) u2) u1} (CategoryTheory.Functor.{u2, u1, u4, u3} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u2, u1, u4, u3} C _inst_1 D _inst_2))) (Prefunctor.obj.{max (succ u4) (succ u1), max (succ u4) (succ u1), max (max (max u4 u3) u2) u1, max (max (max u4 u3) u2) u1} (CategoryTheory.AdditiveFunctor.{u4, u3, u2, u1} C D _inst_1 _inst_2 _inst_3 _inst_4) (CategoryTheory.CategoryStruct.toQuiver.{max u4 u1, max (max (max u4 u3) u2) u1} (CategoryTheory.AdditiveFunctor.{u4, u3, u2, u1} C D _inst_1 _inst_2 _inst_3 _inst_4) (CategoryTheory.Category.toCategoryStruct.{max u4 u1, max (max (max u4 u3) u2) u1} (CategoryTheory.AdditiveFunctor.{u4, u3, u2, u1} C D _inst_1 _inst_2 _inst_3 _inst_4) (CategoryTheory.instCategoryAdditiveFunctor.{u4, u3, u2, u1} C D _inst_1 _inst_2 _inst_3 _inst_4))) (CategoryTheory.Functor.{u2, u1, u4, u3} C _inst_1 D _inst_2) (CategoryTheory.CategoryStruct.toQuiver.{max u4 u1, max (max (max u4 u3) u2) u1} (CategoryTheory.Functor.{u2, u1, u4, u3} C _inst_1 D _inst_2) (CategoryTheory.Category.toCategoryStruct.{max u4 u1, max (max (max u4 u3) u2) u1} (CategoryTheory.Functor.{u2, u1, u4, u3} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u2, u1, u4, u3} C _inst_1 D _inst_2))) (CategoryTheory.Functor.toPrefunctor.{max u4 u1, max u4 u1, max (max (max u4 u3) u2) u1, max (max (max u4 u3) u2) u1} (CategoryTheory.AdditiveFunctor.{u4, u3, u2, u1} C D _inst_1 _inst_2 _inst_3 _inst_4) (CategoryTheory.instCategoryAdditiveFunctor.{u4, u3, u2, u1} C D _inst_1 _inst_2 _inst_3 _inst_4) (CategoryTheory.Functor.{u2, u1, u4, u3} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u2, u1, u4, u3} C _inst_1 D _inst_2) (CategoryTheory.AdditiveFunctor.forget.{u4, u3, u2, u1} C D _inst_1 _inst_2 _inst_3 _inst_4)) F) (Prefunctor.obj.{max (succ u4) (succ u1), max (succ u4) (succ u1), max (max (max u4 u3) u2) u1, max (max (max u4 u3) u2) u1} (CategoryTheory.AdditiveFunctor.{u4, u3, u2, u1} C D _inst_1 _inst_2 _inst_3 _inst_4) (CategoryTheory.CategoryStruct.toQuiver.{max u4 u1, max (max (max u4 u3) u2) u1} (CategoryTheory.AdditiveFunctor.{u4, u3, u2, u1} C D _inst_1 _inst_2 _inst_3 _inst_4) (CategoryTheory.Category.toCategoryStruct.{max u4 u1, max (max (max u4 u3) u2) u1} (CategoryTheory.AdditiveFunctor.{u4, u3, u2, u1} C D _inst_1 _inst_2 _inst_3 _inst_4) (CategoryTheory.instCategoryAdditiveFunctor.{u4, u3, u2, u1} C D _inst_1 _inst_2 _inst_3 _inst_4))) (CategoryTheory.Functor.{u2, u1, u4, u3} C _inst_1 D _inst_2) (CategoryTheory.CategoryStruct.toQuiver.{max u4 u1, max (max (max u4 u3) u2) u1} (CategoryTheory.Functor.{u2, u1, u4, u3} C _inst_1 D _inst_2) (CategoryTheory.Category.toCategoryStruct.{max u4 u1, max (max (max u4 u3) u2) u1} (CategoryTheory.Functor.{u2, u1, u4, u3} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u2, u1, u4, u3} C _inst_1 D _inst_2))) (CategoryTheory.Functor.toPrefunctor.{max u4 u1, max u4 u1, max (max (max u4 u3) u2) u1, max (max (max u4 u3) u2) u1} (CategoryTheory.AdditiveFunctor.{u4, u3, u2, u1} C D _inst_1 _inst_2 _inst_3 _inst_4) (CategoryTheory.instCategoryAdditiveFunctor.{u4, u3, u2, u1} C D _inst_1 _inst_2 _inst_3 _inst_4) (CategoryTheory.Functor.{u2, u1, u4, u3} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u2, u1, u4, u3} C _inst_1 D _inst_2) (CategoryTheory.AdditiveFunctor.forget.{u4, u3, u2, u1} C D _inst_1 _inst_2 _inst_3 _inst_4)) G)) (Prefunctor.map.{max (succ u4) (succ u1), max (succ u4) (succ u1), max (max (max u4 u3) u2) u1, max (max (max u4 u3) u2) u1} (CategoryTheory.AdditiveFunctor.{u4, u3, u2, u1} C D _inst_1 _inst_2 _inst_3 _inst_4) (CategoryTheory.CategoryStruct.toQuiver.{max u4 u1, max (max (max u4 u3) u2) u1} (CategoryTheory.AdditiveFunctor.{u4, u3, u2, u1} C D _inst_1 _inst_2 _inst_3 _inst_4) (CategoryTheory.Category.toCategoryStruct.{max u4 u1, max (max (max u4 u3) u2) u1} (CategoryTheory.AdditiveFunctor.{u4, u3, u2, u1} C D _inst_1 _inst_2 _inst_3 _inst_4) (CategoryTheory.instCategoryAdditiveFunctor.{u4, u3, u2, u1} C D _inst_1 _inst_2 _inst_3 _inst_4))) (CategoryTheory.Functor.{u2, u1, u4, u3} C _inst_1 D _inst_2) (CategoryTheory.CategoryStruct.toQuiver.{max u4 u1, max (max (max u4 u3) u2) u1} (CategoryTheory.Functor.{u2, u1, u4, u3} C _inst_1 D _inst_2) (CategoryTheory.Category.toCategoryStruct.{max u4 u1, max (max (max u4 u3) u2) u1} (CategoryTheory.Functor.{u2, u1, u4, u3} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u2, u1, u4, u3} C _inst_1 D _inst_2))) (CategoryTheory.Functor.toPrefunctor.{max u4 u1, max u4 u1, max (max (max u4 u3) u2) u1, max (max (max u4 u3) u2) u1} (CategoryTheory.AdditiveFunctor.{u4, u3, u2, u1} C D _inst_1 _inst_2 _inst_3 _inst_4) (CategoryTheory.instCategoryAdditiveFunctor.{u4, u3, u2, u1} C D _inst_1 _inst_2 _inst_3 _inst_4) (CategoryTheory.Functor.{u2, u1, u4, u3} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u2, u1, u4, u3} C _inst_1 D _inst_2) (CategoryTheory.AdditiveFunctor.forget.{u4, u3, u2, u1} C D _inst_1 _inst_2 _inst_3 _inst_4)) F G α) α
Case conversion may be inaccurate. Consider using '#align category_theory.AdditiveFunctor.forget_map CategoryTheory.AdditiveFunctor.forget_mapₓ'. -/
@[simp]
theorem AdditiveFunctor.forget_map (F G : C ⥤+ D) (α : F ⟶ G) :
    (AdditiveFunctor.forget C D).map α = α :=
  rfl
#align category_theory.AdditiveFunctor.forget_map CategoryTheory.AdditiveFunctor.forget_map

instance : Functor.Additive (AdditiveFunctor.forget C D) where map_add' F G α β := rfl

instance (F : C ⥤+ D) : Functor.Additive F.1 :=
  F.2

end

section Exact

open CategoryTheory.Limits

variable (C : Type u₁) (D : Type u₂) [Category.{v₁} C] [Category.{v₂} D] [Preadditive C]

variable [Preadditive D] [HasZeroObject C] [HasZeroObject D] [HasBinaryBiproducts C]

section

attribute [local instance] preserves_binary_biproducts_of_preserves_binary_products

attribute [local instance] preserves_binary_biproducts_of_preserves_binary_coproducts

#print CategoryTheory.AdditiveFunctor.ofLeftExact /-
/-- Turn a left exact functor into an additive functor. -/
def AdditiveFunctor.ofLeftExact : (C ⥤ₗ D) ⥤ C ⥤+ D :=
  FullSubcategory.map fun F h =>
    let hF := Classical.choice h
    functor.additive_of_preserves_binary_biproducts F deriving
  Full, Faithful
#align category_theory.AdditiveFunctor.of_left_exact CategoryTheory.AdditiveFunctor.ofLeftExact
-/

#print CategoryTheory.AdditiveFunctor.ofRightExact /-
/-- Turn a right exact functor into an additive functor. -/
def AdditiveFunctor.ofRightExact : (C ⥤ᵣ D) ⥤ C ⥤+ D :=
  FullSubcategory.map fun F h =>
    let hF := Classical.choice h
    functor.additive_of_preserves_binary_biproducts F deriving
  Full, Faithful
#align category_theory.AdditiveFunctor.of_right_exact CategoryTheory.AdditiveFunctor.ofRightExact
-/

#print CategoryTheory.AdditiveFunctor.ofExact /-
/-- Turn an exact functor into an additive functor. -/
def AdditiveFunctor.ofExact : (C ⥤ₑ D) ⥤ C ⥤+ D :=
  FullSubcategory.map fun F h =>
    let hF := Classical.choice h.1
    functor.additive_of_preserves_binary_biproducts F deriving
  Full, Faithful
#align category_theory.AdditiveFunctor.of_exact CategoryTheory.AdditiveFunctor.ofExact
-/

end

variable {C D}

#print CategoryTheory.AdditiveFunctor.ofLeftExact_obj_fst /-
@[simp]
theorem AdditiveFunctor.ofLeftExact_obj_fst (F : C ⥤ₗ D) :
    ((AdditiveFunctor.ofLeftExact C D).obj F).obj = F.obj :=
  rfl
#align category_theory.AdditiveFunctor.of_left_exact_obj_fst CategoryTheory.AdditiveFunctor.ofLeftExact_obj_fst
-/

#print CategoryTheory.AdditiveFunctor.ofRightExact_obj_fst /-
@[simp]
theorem AdditiveFunctor.ofRightExact_obj_fst (F : C ⥤ᵣ D) :
    ((AdditiveFunctor.ofRightExact C D).obj F).obj = F.obj :=
  rfl
#align category_theory.AdditiveFunctor.of_right_exact_obj_fst CategoryTheory.AdditiveFunctor.ofRightExact_obj_fst
-/

#print CategoryTheory.AdditiveFunctor.ofExact_obj_fst /-
@[simp]
theorem AdditiveFunctor.ofExact_obj_fst (F : C ⥤ₑ D) :
    ((AdditiveFunctor.ofExact C D).obj F).obj = F.obj :=
  rfl
#align category_theory.AdditiveFunctor.of_exact_obj_fst CategoryTheory.AdditiveFunctor.ofExact_obj_fst
-/

/- warning: category_theory.Additive_Functor.of_left_exact_map -> CategoryTheory.AdditiveFunctor.ofLeftExact_map is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.Additive_Functor.of_left_exact_map CategoryTheory.AdditiveFunctor.ofLeftExact_mapₓ'. -/
@[simp]
theorem AdditiveFunctor.ofLeftExact_map {F G : C ⥤ₗ D} (α : F ⟶ G) :
    (AdditiveFunctor.ofLeftExact C D).map α = α :=
  rfl
#align category_theory.Additive_Functor.of_left_exact_map CategoryTheory.AdditiveFunctor.ofLeftExact_map

/- warning: category_theory.Additive_Functor.of_right_exact_map -> CategoryTheory.AdditiveFunctor.ofRightExact_map is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.Additive_Functor.of_right_exact_map CategoryTheory.AdditiveFunctor.ofRightExact_mapₓ'. -/
@[simp]
theorem AdditiveFunctor.ofRightExact_map {F G : C ⥤ᵣ D} (α : F ⟶ G) :
    (AdditiveFunctor.ofRightExact C D).map α = α :=
  rfl
#align category_theory.Additive_Functor.of_right_exact_map CategoryTheory.AdditiveFunctor.ofRightExact_map

/- warning: category_theory.Additive_Functor.of_exact_map -> CategoryTheory.AdditiveFunctor.ofExact_map is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.Additive_Functor.of_exact_map CategoryTheory.AdditiveFunctor.ofExact_mapₓ'. -/
@[simp]
theorem AdditiveFunctor.ofExact_map {F G : C ⥤ₑ D} (α : F ⟶ G) :
    (AdditiveFunctor.ofExact C D).map α = α :=
  rfl
#align category_theory.Additive_Functor.of_exact_map CategoryTheory.AdditiveFunctor.ofExact_map

end Exact

end Preadditive

end CategoryTheory

