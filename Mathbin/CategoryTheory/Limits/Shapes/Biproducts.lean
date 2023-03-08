/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Jakob von Raumer

! This file was ported from Lean 3 source module category_theory.limits.shapes.biproducts
! leanprover-community/mathlib commit ac3ae212f394f508df43e37aa093722fa9b65d31
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathbin.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathbin.CategoryTheory.Limits.Shapes.Kernels

/-!
# Biproducts and binary biproducts

We introduce the notion of (finite) biproducts and binary biproducts.

These are slightly unusual relative to the other shapes in the library,
as they are simultaneously limits and colimits.
(Zero objects are similar; they are "biterminal".)

For results about biproducts in preadditive categories see
`category_theory.preadditive.biproducts`.

In a category with zero morphisms, we model the (binary) biproduct of `P Q : C`
using a `binary_bicone`, which has a cone point `X`,
and morphisms `fst : X ⟶ P`, `snd : X ⟶ Q`, `inl : P ⟶ X` and `inr : X ⟶ Q`,
such that `inl ≫ fst = 𝟙 P`, `inl ≫ snd = 0`, `inr ≫ fst = 0`, and `inr ≫ snd = 𝟙 Q`.
Such a `binary_bicone` is a biproduct if the cone is a limit cone, and the cocone is a colimit
cocone.

For biproducts indexed by a `fintype J`, a `bicone` again consists of a cone point `X`
and morphisms `π j : X ⟶ F j` and `ι j : F j ⟶ X` for each `j`,
such that `ι j ≫ π j'` is the identity when `j = j'` and zero otherwise.

## Notation
As `⊕` is already taken for the sum of types, we introduce the notation `X ⊞ Y` for
a binary biproduct. We introduce `⨁ f` for the indexed biproduct.

## Implementation
Prior to #14046, `has_finite_biproducts` required a `decidable_eq` instance on the indexing type.
As this had no pay-off (everything about limits is non-constructive in mathlib), and occasional cost
(constructing decidability instances appropriate for constructions involving the indexing type),
we made everything classical.
-/


noncomputable section

universe w w' v u

open CategoryTheory

open CategoryTheory.Functor

open Classical

namespace CategoryTheory

namespace Limits

variable {J : Type w}

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

#print CategoryTheory.Limits.Bicone /-
/-- A `c : bicone F` is:
* an object `c.X` and
* morphisms `π j : X ⟶ F j` and `ι j : F j ⟶ X` for each `j`,
* such that `ι j ≫ π j'` is the identity when `j = j'` and zero otherwise.
-/
@[nolint has_nonempty_instance]
structure Bicone (F : J → C) where
  pt : C
  π : ∀ j, X ⟶ F j
  ι : ∀ j, F j ⟶ X
  ι_π : ∀ j j', ι j ≫ π j' = if h : j = j' then eqToHom (congr_arg F h) else 0 := by obviously
#align category_theory.limits.bicone CategoryTheory.Limits.Bicone
-/

#print CategoryTheory.Limits.bicone_ι_π_self /-
@[simp, reassoc.1]
theorem bicone_ι_π_self {F : J → C} (B : Bicone F) (j : J) : B.ι j ≫ B.π j = 𝟙 (F j) := by
  simpa using B.ι_π j j
#align category_theory.limits.bicone_ι_π_self CategoryTheory.Limits.bicone_ι_π_self
-/

#print CategoryTheory.Limits.bicone_ι_π_ne /-
@[simp, reassoc.1]
theorem bicone_ι_π_ne {F : J → C} (B : Bicone F) {j j' : J} (h : j ≠ j') : B.ι j ≫ B.π j' = 0 := by
  simpa [h] using B.ι_π j j'
#align category_theory.limits.bicone_ι_π_ne CategoryTheory.Limits.bicone_ι_π_ne
-/

variable {F : J → C}

namespace Bicone

attribute [local tidy] tactic.discrete_cases

#print CategoryTheory.Limits.Bicone.toCone /-
/-- Extract the cone from a bicone. -/
def toCone (B : Bicone F) : Cone (Discrete.functor F)
    where
  pt := B.pt
  π := { app := fun j => B.π j.as }
#align category_theory.limits.bicone.to_cone CategoryTheory.Limits.Bicone.toCone
-/

#print CategoryTheory.Limits.Bicone.toCone_pt /-
@[simp]
theorem toCone_pt (B : Bicone F) : B.toCone.pt = B.pt :=
  rfl
#align category_theory.limits.bicone.to_cone_X CategoryTheory.Limits.Bicone.toCone_pt
-/

/- warning: category_theory.limits.bicone.to_cone_π_app -> CategoryTheory.Limits.Bicone.toCone_π_app is a dubious translation:
lean 3 declaration is
  forall {J : Type.{u1}} {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u2, u3} C _inst_1] {F : J -> C} (B : CategoryTheory.Limits.Bicone.{u1, u2, u3} J C _inst_1 _inst_2 F) (j : CategoryTheory.Discrete.{u1} J), Eq.{succ u2} (Quiver.Hom.{succ u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) (CategoryTheory.Functor.obj.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1 (CategoryTheory.Functor.obj.{u2, max u1 u2, u3, max u1 u2 u1 u3} C _inst_1 (CategoryTheory.Functor.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.Functor.category.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.Functor.const.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.Limits.Cone.pt.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1 (CategoryTheory.Discrete.functor.{u2, u1, u3} C _inst_1 J F) (CategoryTheory.Limits.Bicone.toCone.{u1, u2, u3} J C _inst_1 _inst_2 F B))) j) (CategoryTheory.Functor.obj.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1 (CategoryTheory.Discrete.functor.{u2, u1, u3} C _inst_1 J F) j)) (CategoryTheory.NatTrans.app.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1 (CategoryTheory.Functor.obj.{u2, max u1 u2, u3, max u1 u2 u1 u3} C _inst_1 (CategoryTheory.Functor.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.Functor.category.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.Functor.const.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.Limits.Cone.pt.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1 (CategoryTheory.Discrete.functor.{u2, u1, u3} C _inst_1 J F) (CategoryTheory.Limits.Bicone.toCone.{u1, u2, u3} J C _inst_1 _inst_2 F B))) (CategoryTheory.Discrete.functor.{u2, u1, u3} C _inst_1 J F) (CategoryTheory.Limits.Cone.π.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1 (CategoryTheory.Discrete.functor.{u2, u1, u3} C _inst_1 J F) (CategoryTheory.Limits.Bicone.toCone.{u1, u2, u3} J C _inst_1 _inst_2 F B)) j) (CategoryTheory.Limits.Bicone.π.{u1, u2, u3} J C _inst_1 _inst_2 F B (CategoryTheory.Discrete.as.{u1} J j))
but is expected to have type
  forall {J : Type.{u1}} {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u2, u3} C _inst_1] {F : J -> C} (B : CategoryTheory.Limits.Bicone.{u1, u2, u3} J C _inst_1 _inst_2 F) (j : CategoryTheory.Discrete.{u1} J), Eq.{succ u2} (Quiver.Hom.{succ u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) (Prefunctor.obj.{succ u1, succ u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.Category.toCategoryStruct.{u1, u1} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J))) C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1 (Prefunctor.obj.{succ u2, max (succ u1) (succ u2), u3, max (max u1 u2) u3} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) (CategoryTheory.Functor.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{max u1 u2, max (max u1 u3) u2} (CategoryTheory.Functor.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.Category.toCategoryStruct.{max u1 u2, max (max u1 u3) u2} (CategoryTheory.Functor.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.Functor.category.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u2, max u1 u2, u3, max (max u1 u3) u2} C _inst_1 (CategoryTheory.Functor.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.Functor.category.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.Functor.const.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1)) (CategoryTheory.Limits.Cone.pt.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1 (CategoryTheory.Discrete.functor.{u2, u1, u3} C _inst_1 J F) (CategoryTheory.Limits.Bicone.toCone.{u1, u2, u3} J C _inst_1 _inst_2 F B)))) j) (Prefunctor.obj.{succ u1, succ u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.Category.toCategoryStruct.{u1, u1} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J))) C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1 (CategoryTheory.Discrete.functor.{u2, u1, u3} C _inst_1 J F)) j)) (CategoryTheory.NatTrans.app.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1 (Prefunctor.obj.{succ u2, max (succ u1) (succ u2), u3, max (max u1 u2) u3} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) (CategoryTheory.Functor.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{max u1 u2, max (max u1 u3) u2} (CategoryTheory.Functor.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.Category.toCategoryStruct.{max u1 u2, max (max u1 u3) u2} (CategoryTheory.Functor.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.Functor.category.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u2, max u1 u2, u3, max (max u1 u3) u2} C _inst_1 (CategoryTheory.Functor.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.Functor.category.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.Functor.const.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1)) (CategoryTheory.Limits.Cone.pt.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1 (CategoryTheory.Discrete.functor.{u2, u1, u3} C _inst_1 J F) (CategoryTheory.Limits.Bicone.toCone.{u1, u2, u3} J C _inst_1 _inst_2 F B))) (CategoryTheory.Discrete.functor.{u2, u1, u3} C _inst_1 J F) (CategoryTheory.Limits.Cone.π.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1 (CategoryTheory.Discrete.functor.{u2, u1, u3} C _inst_1 J F) (CategoryTheory.Limits.Bicone.toCone.{u1, u2, u3} J C _inst_1 _inst_2 F B)) j) (CategoryTheory.Limits.Bicone.π.{u1, u2, u3} J C _inst_1 _inst_2 F B (CategoryTheory.Discrete.as.{u1} J j))
Case conversion may be inaccurate. Consider using '#align category_theory.limits.bicone.to_cone_π_app CategoryTheory.Limits.Bicone.toCone_π_appₓ'. -/
@[simp]
theorem toCone_π_app (B : Bicone F) (j : Discrete J) : B.toCone.π.app j = B.π j.as :=
  rfl
#align category_theory.limits.bicone.to_cone_π_app CategoryTheory.Limits.Bicone.toCone_π_app

/- warning: category_theory.limits.bicone.to_cone_π_app_mk -> CategoryTheory.Limits.Bicone.toCone_π_app_mk is a dubious translation:
lean 3 declaration is
  forall {J : Type.{u1}} {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u2, u3} C _inst_1] {F : J -> C} (B : CategoryTheory.Limits.Bicone.{u1, u2, u3} J C _inst_1 _inst_2 F) (j : J), Eq.{succ u2} (Quiver.Hom.{succ u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) (CategoryTheory.Functor.obj.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1 (CategoryTheory.Functor.obj.{u2, max u1 u2, u3, max u1 u2 u1 u3} C _inst_1 (CategoryTheory.Functor.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.Functor.category.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.Functor.const.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.Limits.Cone.pt.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1 (CategoryTheory.Discrete.functor.{u2, u1, u3} C _inst_1 J F) (CategoryTheory.Limits.Bicone.toCone.{u1, u2, u3} J C _inst_1 _inst_2 F B))) (CategoryTheory.Discrete.mk.{u1} J j)) (CategoryTheory.Functor.obj.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1 (CategoryTheory.Discrete.functor.{u2, u1, u3} C _inst_1 J F) (CategoryTheory.Discrete.mk.{u1} J j))) (CategoryTheory.NatTrans.app.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1 (CategoryTheory.Functor.obj.{u2, max u1 u2, u3, max u1 u2 u1 u3} C _inst_1 (CategoryTheory.Functor.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.Functor.category.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.Functor.const.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.Limits.Cone.pt.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1 (CategoryTheory.Discrete.functor.{u2, u1, u3} C _inst_1 J F) (CategoryTheory.Limits.Bicone.toCone.{u1, u2, u3} J C _inst_1 _inst_2 F B))) (CategoryTheory.Discrete.functor.{u2, u1, u3} C _inst_1 J F) (CategoryTheory.Limits.Cone.π.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1 (CategoryTheory.Discrete.functor.{u2, u1, u3} C _inst_1 J F) (CategoryTheory.Limits.Bicone.toCone.{u1, u2, u3} J C _inst_1 _inst_2 F B)) (CategoryTheory.Discrete.mk.{u1} J j)) (CategoryTheory.Limits.Bicone.π.{u1, u2, u3} J C _inst_1 _inst_2 F B j)
but is expected to have type
  forall {J : Type.{u1}} {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u2, u3} C _inst_1] {F : J -> C} (B : CategoryTheory.Limits.Bicone.{u1, u2, u3} J C _inst_1 _inst_2 F) (j : J), Eq.{succ u2} (Quiver.Hom.{succ u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) (Prefunctor.obj.{succ u1, succ u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.Category.toCategoryStruct.{u1, u1} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J))) C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1 (Prefunctor.obj.{succ u2, max (succ u1) (succ u2), u3, max (max u1 u2) u3} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) (CategoryTheory.Functor.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{max u1 u2, max (max u1 u3) u2} (CategoryTheory.Functor.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.Category.toCategoryStruct.{max u1 u2, max (max u1 u3) u2} (CategoryTheory.Functor.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.Functor.category.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u2, max u1 u2, u3, max (max u1 u3) u2} C _inst_1 (CategoryTheory.Functor.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.Functor.category.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.Functor.const.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1)) (CategoryTheory.Limits.Cone.pt.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1 (CategoryTheory.Discrete.functor.{u2, u1, u3} C _inst_1 J F) (CategoryTheory.Limits.Bicone.toCone.{u1, u2, u3} J C _inst_1 _inst_2 F B)))) (CategoryTheory.Discrete.mk.{u1} J j)) (Prefunctor.obj.{succ u1, succ u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.Category.toCategoryStruct.{u1, u1} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J))) C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1 (CategoryTheory.Discrete.functor.{u2, u1, u3} C _inst_1 J F)) (CategoryTheory.Discrete.mk.{u1} J j))) (CategoryTheory.NatTrans.app.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1 (Prefunctor.obj.{succ u2, max (succ u1) (succ u2), u3, max (max u1 u2) u3} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) (CategoryTheory.Functor.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{max u1 u2, max (max u1 u3) u2} (CategoryTheory.Functor.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.Category.toCategoryStruct.{max u1 u2, max (max u1 u3) u2} (CategoryTheory.Functor.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.Functor.category.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u2, max u1 u2, u3, max (max u1 u3) u2} C _inst_1 (CategoryTheory.Functor.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.Functor.category.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.Functor.const.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1)) (CategoryTheory.Limits.Cone.pt.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1 (CategoryTheory.Discrete.functor.{u2, u1, u3} C _inst_1 J F) (CategoryTheory.Limits.Bicone.toCone.{u1, u2, u3} J C _inst_1 _inst_2 F B))) (CategoryTheory.Discrete.functor.{u2, u1, u3} C _inst_1 J F) (CategoryTheory.Limits.Cone.π.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1 (CategoryTheory.Discrete.functor.{u2, u1, u3} C _inst_1 J F) (CategoryTheory.Limits.Bicone.toCone.{u1, u2, u3} J C _inst_1 _inst_2 F B)) (CategoryTheory.Discrete.mk.{u1} J j)) (CategoryTheory.Limits.Bicone.π.{u1, u2, u3} J C _inst_1 _inst_2 F B j)
Case conversion may be inaccurate. Consider using '#align category_theory.limits.bicone.to_cone_π_app_mk CategoryTheory.Limits.Bicone.toCone_π_app_mkₓ'. -/
theorem toCone_π_app_mk (B : Bicone F) (j : J) : B.toCone.π.app ⟨j⟩ = B.π j :=
  rfl
#align category_theory.limits.bicone.to_cone_π_app_mk CategoryTheory.Limits.Bicone.toCone_π_app_mk

#print CategoryTheory.Limits.Bicone.toCocone /-
/-- Extract the cocone from a bicone. -/
def toCocone (B : Bicone F) : Cocone (Discrete.functor F)
    where
  pt := B.pt
  ι := { app := fun j => B.ι j.as }
#align category_theory.limits.bicone.to_cocone CategoryTheory.Limits.Bicone.toCocone
-/

#print CategoryTheory.Limits.Bicone.toCocone_pt /-
@[simp]
theorem toCocone_pt (B : Bicone F) : B.toCocone.pt = B.pt :=
  rfl
#align category_theory.limits.bicone.to_cocone_X CategoryTheory.Limits.Bicone.toCocone_pt
-/

/- warning: category_theory.limits.bicone.to_cocone_ι_app -> CategoryTheory.Limits.Bicone.toCocone_ι_app is a dubious translation:
lean 3 declaration is
  forall {J : Type.{u1}} {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u2, u3} C _inst_1] {F : J -> C} (B : CategoryTheory.Limits.Bicone.{u1, u2, u3} J C _inst_1 _inst_2 F) (j : CategoryTheory.Discrete.{u1} J), Eq.{succ u2} (Quiver.Hom.{succ u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) (CategoryTheory.Functor.obj.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1 (CategoryTheory.Discrete.functor.{u2, u1, u3} C _inst_1 J F) j) (CategoryTheory.Functor.obj.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1 (CategoryTheory.Functor.obj.{u2, max u1 u2, u3, max u1 u2 u1 u3} C _inst_1 (CategoryTheory.Functor.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.Functor.category.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.Functor.const.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.Limits.Cocone.pt.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1 (CategoryTheory.Discrete.functor.{u2, u1, u3} C _inst_1 J F) (CategoryTheory.Limits.Bicone.toCocone.{u1, u2, u3} J C _inst_1 _inst_2 F B))) j)) (CategoryTheory.NatTrans.app.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1 (CategoryTheory.Discrete.functor.{u2, u1, u3} C _inst_1 J F) (CategoryTheory.Functor.obj.{u2, max u1 u2, u3, max u1 u2 u1 u3} C _inst_1 (CategoryTheory.Functor.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.Functor.category.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.Functor.const.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.Limits.Cocone.pt.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1 (CategoryTheory.Discrete.functor.{u2, u1, u3} C _inst_1 J F) (CategoryTheory.Limits.Bicone.toCocone.{u1, u2, u3} J C _inst_1 _inst_2 F B))) (CategoryTheory.Limits.Cocone.ι.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1 (CategoryTheory.Discrete.functor.{u2, u1, u3} C _inst_1 J F) (CategoryTheory.Limits.Bicone.toCocone.{u1, u2, u3} J C _inst_1 _inst_2 F B)) j) (CategoryTheory.Limits.Bicone.ι.{u1, u2, u3} J C _inst_1 _inst_2 F B (CategoryTheory.Discrete.as.{u1} J j))
but is expected to have type
  forall {J : Type.{u1}} {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u2, u3} C _inst_1] {F : J -> C} (B : CategoryTheory.Limits.Bicone.{u1, u2, u3} J C _inst_1 _inst_2 F) (j : CategoryTheory.Discrete.{u1} J), Eq.{succ u2} (Quiver.Hom.{succ u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) (Prefunctor.obj.{succ u1, succ u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.Category.toCategoryStruct.{u1, u1} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J))) C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1 (CategoryTheory.Discrete.functor.{u2, u1, u3} C _inst_1 J F)) j) (Prefunctor.obj.{succ u1, succ u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.Category.toCategoryStruct.{u1, u1} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J))) C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1 (Prefunctor.obj.{succ u2, max (succ u1) (succ u2), u3, max (max u1 u2) u3} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) (CategoryTheory.Functor.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{max u1 u2, max (max u1 u3) u2} (CategoryTheory.Functor.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.Category.toCategoryStruct.{max u1 u2, max (max u1 u3) u2} (CategoryTheory.Functor.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.Functor.category.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u2, max u1 u2, u3, max (max u1 u3) u2} C _inst_1 (CategoryTheory.Functor.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.Functor.category.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.Functor.const.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1)) (CategoryTheory.Limits.Cocone.pt.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1 (CategoryTheory.Discrete.functor.{u2, u1, u3} C _inst_1 J F) (CategoryTheory.Limits.Bicone.toCocone.{u1, u2, u3} J C _inst_1 _inst_2 F B)))) j)) (CategoryTheory.NatTrans.app.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1 (CategoryTheory.Discrete.functor.{u2, u1, u3} C _inst_1 J F) (Prefunctor.obj.{succ u2, max (succ u1) (succ u2), u3, max (max u1 u2) u3} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) (CategoryTheory.Functor.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{max u1 u2, max (max u1 u3) u2} (CategoryTheory.Functor.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.Category.toCategoryStruct.{max u1 u2, max (max u1 u3) u2} (CategoryTheory.Functor.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.Functor.category.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u2, max u1 u2, u3, max (max u1 u3) u2} C _inst_1 (CategoryTheory.Functor.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.Functor.category.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.Functor.const.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1)) (CategoryTheory.Limits.Cocone.pt.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1 (CategoryTheory.Discrete.functor.{u2, u1, u3} C _inst_1 J F) (CategoryTheory.Limits.Bicone.toCocone.{u1, u2, u3} J C _inst_1 _inst_2 F B))) (CategoryTheory.Limits.Cocone.ι.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1 (CategoryTheory.Discrete.functor.{u2, u1, u3} C _inst_1 J F) (CategoryTheory.Limits.Bicone.toCocone.{u1, u2, u3} J C _inst_1 _inst_2 F B)) j) (CategoryTheory.Limits.Bicone.ι.{u1, u2, u3} J C _inst_1 _inst_2 F B (CategoryTheory.Discrete.as.{u1} J j))
Case conversion may be inaccurate. Consider using '#align category_theory.limits.bicone.to_cocone_ι_app CategoryTheory.Limits.Bicone.toCocone_ι_appₓ'. -/
@[simp]
theorem toCocone_ι_app (B : Bicone F) (j : Discrete J) : B.toCocone.ι.app j = B.ι j.as :=
  rfl
#align category_theory.limits.bicone.to_cocone_ι_app CategoryTheory.Limits.Bicone.toCocone_ι_app

/- warning: category_theory.limits.bicone.to_cocone_ι_app_mk -> CategoryTheory.Limits.Bicone.toCocone_ι_app_mk is a dubious translation:
lean 3 declaration is
  forall {J : Type.{u1}} {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u2, u3} C _inst_1] {F : J -> C} (B : CategoryTheory.Limits.Bicone.{u1, u2, u3} J C _inst_1 _inst_2 F) (j : J), Eq.{succ u2} (Quiver.Hom.{succ u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) (CategoryTheory.Functor.obj.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1 (CategoryTheory.Discrete.functor.{u2, u1, u3} C _inst_1 J F) (CategoryTheory.Discrete.mk.{u1} J j)) (CategoryTheory.Functor.obj.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1 (CategoryTheory.Functor.obj.{u2, max u1 u2, u3, max u1 u2 u1 u3} C _inst_1 (CategoryTheory.Functor.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.Functor.category.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.Functor.const.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.Limits.Cocone.pt.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1 (CategoryTheory.Discrete.functor.{u2, u1, u3} C _inst_1 J F) (CategoryTheory.Limits.Bicone.toCocone.{u1, u2, u3} J C _inst_1 _inst_2 F B))) (CategoryTheory.Discrete.mk.{u1} J j))) (CategoryTheory.NatTrans.app.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1 (CategoryTheory.Discrete.functor.{u2, u1, u3} C _inst_1 J F) (CategoryTheory.Functor.obj.{u2, max u1 u2, u3, max u1 u2 u1 u3} C _inst_1 (CategoryTheory.Functor.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.Functor.category.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.Functor.const.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.Limits.Cocone.pt.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1 (CategoryTheory.Discrete.functor.{u2, u1, u3} C _inst_1 J F) (CategoryTheory.Limits.Bicone.toCocone.{u1, u2, u3} J C _inst_1 _inst_2 F B))) (CategoryTheory.Limits.Cocone.ι.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1 (CategoryTheory.Discrete.functor.{u2, u1, u3} C _inst_1 J F) (CategoryTheory.Limits.Bicone.toCocone.{u1, u2, u3} J C _inst_1 _inst_2 F B)) (CategoryTheory.Discrete.mk.{u1} J j)) (CategoryTheory.Limits.Bicone.ι.{u1, u2, u3} J C _inst_1 _inst_2 F B j)
but is expected to have type
  forall {J : Type.{u1}} {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u2, u3} C _inst_1] {F : J -> C} (B : CategoryTheory.Limits.Bicone.{u1, u2, u3} J C _inst_1 _inst_2 F) (j : J), Eq.{succ u2} (Quiver.Hom.{succ u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) (Prefunctor.obj.{succ u1, succ u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.Category.toCategoryStruct.{u1, u1} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J))) C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1 (CategoryTheory.Discrete.functor.{u2, u1, u3} C _inst_1 J F)) (CategoryTheory.Discrete.mk.{u1} J j)) (Prefunctor.obj.{succ u1, succ u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.Category.toCategoryStruct.{u1, u1} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J))) C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1 (Prefunctor.obj.{succ u2, max (succ u1) (succ u2), u3, max (max u1 u2) u3} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) (CategoryTheory.Functor.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{max u1 u2, max (max u1 u3) u2} (CategoryTheory.Functor.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.Category.toCategoryStruct.{max u1 u2, max (max u1 u3) u2} (CategoryTheory.Functor.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.Functor.category.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u2, max u1 u2, u3, max (max u1 u3) u2} C _inst_1 (CategoryTheory.Functor.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.Functor.category.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.Functor.const.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1)) (CategoryTheory.Limits.Cocone.pt.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1 (CategoryTheory.Discrete.functor.{u2, u1, u3} C _inst_1 J F) (CategoryTheory.Limits.Bicone.toCocone.{u1, u2, u3} J C _inst_1 _inst_2 F B)))) (CategoryTheory.Discrete.mk.{u1} J j))) (CategoryTheory.NatTrans.app.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1 (CategoryTheory.Discrete.functor.{u2, u1, u3} C _inst_1 J F) (Prefunctor.obj.{succ u2, max (succ u1) (succ u2), u3, max (max u1 u2) u3} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) (CategoryTheory.Functor.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{max u1 u2, max (max u1 u3) u2} (CategoryTheory.Functor.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.Category.toCategoryStruct.{max u1 u2, max (max u1 u3) u2} (CategoryTheory.Functor.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.Functor.category.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u2, max u1 u2, u3, max (max u1 u3) u2} C _inst_1 (CategoryTheory.Functor.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.Functor.category.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1) (CategoryTheory.Functor.const.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1)) (CategoryTheory.Limits.Cocone.pt.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1 (CategoryTheory.Discrete.functor.{u2, u1, u3} C _inst_1 J F) (CategoryTheory.Limits.Bicone.toCocone.{u1, u2, u3} J C _inst_1 _inst_2 F B))) (CategoryTheory.Limits.Cocone.ι.{u1, u2, u1, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1 (CategoryTheory.Discrete.functor.{u2, u1, u3} C _inst_1 J F) (CategoryTheory.Limits.Bicone.toCocone.{u1, u2, u3} J C _inst_1 _inst_2 F B)) (CategoryTheory.Discrete.mk.{u1} J j)) (CategoryTheory.Limits.Bicone.ι.{u1, u2, u3} J C _inst_1 _inst_2 F B j)
Case conversion may be inaccurate. Consider using '#align category_theory.limits.bicone.to_cocone_ι_app_mk CategoryTheory.Limits.Bicone.toCocone_ι_app_mkₓ'. -/
theorem toCocone_ι_app_mk (B : Bicone F) (j : J) : B.toCocone.ι.app ⟨j⟩ = B.ι j :=
  rfl
#align category_theory.limits.bicone.to_cocone_ι_app_mk CategoryTheory.Limits.Bicone.toCocone_ι_app_mk

#print CategoryTheory.Limits.Bicone.ofLimitCone /-
/-- We can turn any limit cone over a discrete collection of objects into a bicone. -/
@[simps]
def ofLimitCone {f : J → C} {t : Cone (Discrete.functor f)} (ht : IsLimit t) : Bicone f
    where
  pt := t.pt
  π j := t.π.app ⟨j⟩
  ι j := ht.lift (Fan.mk _ fun j' => if h : j = j' then eqToHom (congr_arg f h) else 0)
  ι_π j j' := by simp
#align category_theory.limits.bicone.of_limit_cone CategoryTheory.Limits.Bicone.ofLimitCone
-/

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `discrete_cases #[] -/
#print CategoryTheory.Limits.Bicone.ι_of_isLimit /-
theorem ι_of_isLimit {f : J → C} {t : Bicone f} (ht : IsLimit t.toCone) (j : J) :
    t.ι j = ht.lift (Fan.mk _ fun j' => if h : j = j' then eqToHom (congr_arg f h) else 0) :=
  ht.hom_ext fun j' => by
    rw [ht.fac]
    trace
      "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `discrete_cases #[]"
    simp [t.ι_π]
#align category_theory.limits.bicone.ι_of_is_limit CategoryTheory.Limits.Bicone.ι_of_isLimit
-/

#print CategoryTheory.Limits.Bicone.ofColimitCocone /-
/-- We can turn any colimit cocone over a discrete collection of objects into a bicone. -/
@[simps]
def ofColimitCocone {f : J → C} {t : Cocone (Discrete.functor f)} (ht : IsColimit t) : Bicone f
    where
  pt := t.pt
  π j := ht.desc (Cofan.mk _ fun j' => if h : j' = j then eqToHom (congr_arg f h) else 0)
  ι j := t.ι.app ⟨j⟩
  ι_π j j' := by simp
#align category_theory.limits.bicone.of_colimit_cocone CategoryTheory.Limits.Bicone.ofColimitCocone
-/

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `discrete_cases #[] -/
#print CategoryTheory.Limits.Bicone.π_of_isColimit /-
theorem π_of_isColimit {f : J → C} {t : Bicone f} (ht : IsColimit t.toCocone) (j : J) :
    t.π j = ht.desc (Cofan.mk _ fun j' => if h : j' = j then eqToHom (congr_arg f h) else 0) :=
  ht.hom_ext fun j' => by
    rw [ht.fac]
    trace
      "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `discrete_cases #[]"
    simp [t.ι_π]
#align category_theory.limits.bicone.π_of_is_colimit CategoryTheory.Limits.Bicone.π_of_isColimit
-/

#print CategoryTheory.Limits.Bicone.IsBilimit /-
/-- Structure witnessing that a bicone is both a limit cone and a colimit cocone. -/
@[nolint has_nonempty_instance]
structure IsBilimit {F : J → C} (B : Bicone F) where
  IsLimit : IsLimit B.toCone
  IsColimit : IsColimit B.toCocone
#align category_theory.limits.bicone.is_bilimit CategoryTheory.Limits.Bicone.IsBilimit
-/

attribute [local ext] bicone.is_bilimit

#print CategoryTheory.Limits.Bicone.subsingleton_isBilimit /-
instance subsingleton_isBilimit {f : J → C} {c : Bicone f} : Subsingleton c.IsBilimit :=
  ⟨fun h h' => Bicone.IsBilimit.ext _ _ (Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩
#align category_theory.limits.bicone.subsingleton_is_bilimit CategoryTheory.Limits.Bicone.subsingleton_isBilimit
-/

section Whisker

variable {K : Type w'}

#print CategoryTheory.Limits.Bicone.whisker /-
/-- Whisker a bicone with an equivalence between the indexing types. -/
@[simps]
def whisker {f : J → C} (c : Bicone f) (g : K ≃ J) : Bicone (f ∘ g)
    where
  pt := c.pt
  π k := c.π (g k)
  ι k := c.ι (g k)
  ι_π k k' := by
    simp only [c.ι_π]
    split_ifs with h h' h' <;> simp [Equiv.apply_eq_iff_eq g] at h h' <;> tauto
#align category_theory.limits.bicone.whisker CategoryTheory.Limits.Bicone.whisker
-/

attribute [local tidy] tactic.discrete_cases

#print CategoryTheory.Limits.Bicone.whiskerToCone /-
/-- Taking the cone of a whiskered bicone results in a cone isomorphic to one gained
by whiskering the cone and postcomposing with a suitable isomorphism. -/
def whiskerToCone {f : J → C} (c : Bicone f) (g : K ≃ J) :
    (c.whisker g).toCone ≅
      (Cones.postcompose (Discrete.functorComp f g).inv).obj
        (c.toCone.whisker (Discrete.functor (Discrete.mk ∘ g))) :=
  Cones.ext (Iso.refl _) (by tidy)
#align category_theory.limits.bicone.whisker_to_cone CategoryTheory.Limits.Bicone.whiskerToCone
-/

#print CategoryTheory.Limits.Bicone.whiskerToCocone /-
/-- Taking the cocone of a whiskered bicone results in a cone isomorphic to one gained
by whiskering the cocone and precomposing with a suitable isomorphism. -/
def whiskerToCocone {f : J → C} (c : Bicone f) (g : K ≃ J) :
    (c.whisker g).toCocone ≅
      (Cocones.precompose (Discrete.functorComp f g).hom).obj
        (c.toCocone.whisker (Discrete.functor (Discrete.mk ∘ g))) :=
  Cocones.ext (Iso.refl _) (by tidy)
#align category_theory.limits.bicone.whisker_to_cocone CategoryTheory.Limits.Bicone.whiskerToCocone
-/

#print CategoryTheory.Limits.Bicone.whiskerIsBilimitIff /-
/-- Whiskering a bicone with an equivalence between types preserves being a bilimit bicone. -/
def whiskerIsBilimitIff {f : J → C} (c : Bicone f) (g : K ≃ J) :
    (c.whisker g).IsBilimit ≃ c.IsBilimit :=
  by
  refine' equivOfSubsingletonOfSubsingleton (fun hc => ⟨_, _⟩) fun hc => ⟨_, _⟩
  · let this := is_limit.of_iso_limit hc.is_limit (bicone.whisker_to_cone c g)
    let this := (is_limit.postcompose_hom_equiv (discrete.functor_comp f g).symm _) this
    exact is_limit.of_whisker_equivalence (discrete.equivalence g) this
  · let this := is_colimit.of_iso_colimit hc.is_colimit (bicone.whisker_to_cocone c g)
    let this := (is_colimit.precompose_hom_equiv (discrete.functor_comp f g) _) this
    exact is_colimit.of_whisker_equivalence (discrete.equivalence g) this
  · apply is_limit.of_iso_limit _ (bicone.whisker_to_cone c g).symm
    apply (is_limit.postcompose_hom_equiv (discrete.functor_comp f g).symm _).symm _
    exact is_limit.whisker_equivalence hc.is_limit (discrete.equivalence g)
  · apply is_colimit.of_iso_colimit _ (bicone.whisker_to_cocone c g).symm
    apply (is_colimit.precompose_hom_equiv (discrete.functor_comp f g) _).symm _
    exact is_colimit.whisker_equivalence hc.is_colimit (discrete.equivalence g)
#align category_theory.limits.bicone.whisker_is_bilimit_iff CategoryTheory.Limits.Bicone.whiskerIsBilimitIff
-/

end Whisker

end Bicone

#print CategoryTheory.Limits.LimitBicone /-
/-- A bicone over `F : J → C`, which is both a limit cone and a colimit cocone.
-/
@[nolint has_nonempty_instance]
structure LimitBicone (F : J → C) where
  Bicone : Bicone F
  IsBilimit : bicone.IsBilimit
#align category_theory.limits.limit_bicone CategoryTheory.Limits.LimitBicone
-/

#print CategoryTheory.Limits.HasBiproduct /-
/-- `has_biproduct F` expresses the mere existence of a bicone which is
simultaneously a limit and a colimit of the diagram `F`.
-/
class HasBiproduct (F : J → C) : Prop where mk' ::
  exists_biproduct : Nonempty (LimitBicone F)
#align category_theory.limits.has_biproduct CategoryTheory.Limits.HasBiproduct
-/

#print CategoryTheory.Limits.HasBiproduct.mk /-
theorem HasBiproduct.mk {F : J → C} (d : LimitBicone F) : HasBiproduct F :=
  ⟨Nonempty.intro d⟩
#align category_theory.limits.has_biproduct.mk CategoryTheory.Limits.HasBiproduct.mk
-/

#print CategoryTheory.Limits.getBiproductData /-
/-- Use the axiom of choice to extract explicit `biproduct_data F` from `has_biproduct F`. -/
def getBiproductData (F : J → C) [HasBiproduct F] : LimitBicone F :=
  Classical.choice HasBiproduct.exists_biproduct
#align category_theory.limits.get_biproduct_data CategoryTheory.Limits.getBiproductData
-/

#print CategoryTheory.Limits.biproduct.bicone /-
/-- A bicone for `F` which is both a limit cone and a colimit cocone. -/
def biproduct.bicone (F : J → C) [HasBiproduct F] : Bicone F :=
  (getBiproductData F).Bicone
#align category_theory.limits.biproduct.bicone CategoryTheory.Limits.biproduct.bicone
-/

#print CategoryTheory.Limits.biproduct.isBilimit /-
/-- `biproduct.bicone F` is a bilimit bicone. -/
def biproduct.isBilimit (F : J → C) [HasBiproduct F] : (biproduct.bicone F).IsBilimit :=
  (getBiproductData F).IsBilimit
#align category_theory.limits.biproduct.is_bilimit CategoryTheory.Limits.biproduct.isBilimit
-/

#print CategoryTheory.Limits.biproduct.isLimit /-
/-- `biproduct.bicone F` is a limit cone. -/
def biproduct.isLimit (F : J → C) [HasBiproduct F] : IsLimit (biproduct.bicone F).toCone :=
  (getBiproductData F).IsBilimit.IsLimit
#align category_theory.limits.biproduct.is_limit CategoryTheory.Limits.biproduct.isLimit
-/

#print CategoryTheory.Limits.biproduct.isColimit /-
/-- `biproduct.bicone F` is a colimit cocone. -/
def biproduct.isColimit (F : J → C) [HasBiproduct F] : IsColimit (biproduct.bicone F).toCocone :=
  (getBiproductData F).IsBilimit.IsColimit
#align category_theory.limits.biproduct.is_colimit CategoryTheory.Limits.biproduct.isColimit
-/

#print CategoryTheory.Limits.hasProduct_of_hasBiproduct /-
instance (priority := 100) hasProduct_of_hasBiproduct [HasBiproduct F] : HasProduct F :=
  HasLimit.mk
    { Cone := (biproduct.bicone F).toCone
      IsLimit := biproduct.isLimit F }
#align category_theory.limits.has_product_of_has_biproduct CategoryTheory.Limits.hasProduct_of_hasBiproduct
-/

#print CategoryTheory.Limits.hasCoproduct_of_hasBiproduct /-
instance (priority := 100) hasCoproduct_of_hasBiproduct [HasBiproduct F] : HasCoproduct F :=
  HasColimit.mk
    { Cocone := (biproduct.bicone F).toCocone
      IsColimit := biproduct.isColimit F }
#align category_theory.limits.has_coproduct_of_has_biproduct CategoryTheory.Limits.hasCoproduct_of_hasBiproduct
-/

variable (J C)

#print CategoryTheory.Limits.HasBiproductsOfShape /-
/-- `C` has biproducts of shape `J` if we have
a limit and a colimit, with the same cone points,
of every function `F : J → C`.
-/
class HasBiproductsOfShape : Prop where
  HasBiproduct : ∀ F : J → C, HasBiproduct F
#align category_theory.limits.has_biproducts_of_shape CategoryTheory.Limits.HasBiproductsOfShape
-/

attribute [instance] has_biproducts_of_shape.has_biproduct

#print CategoryTheory.Limits.HasFiniteBiproducts /-
/- ./././Mathport/Syntax/Translate/Command.lean:388:30: infer kinds are unsupported in Lean 4: #[`out] [] -/
/-- `has_finite_biproducts C` represents a choice of biproduct for every family of objects in `C`
indexed by a finite type. -/
class HasFiniteBiproducts : Prop where
  out : ∀ n, HasBiproductsOfShape (Fin n) C
#align category_theory.limits.has_finite_biproducts CategoryTheory.Limits.HasFiniteBiproducts
-/

variable {J}

#print CategoryTheory.Limits.hasBiproductsOfShape_of_equiv /-
theorem hasBiproductsOfShape_of_equiv {K : Type w'} [HasBiproductsOfShape K C] (e : J ≃ K) :
    HasBiproductsOfShape J C :=
  ⟨fun F =>
    let ⟨⟨h⟩⟩ := HasBiproductsOfShape.hasBiproduct (F ∘ e.symm)
    let ⟨c, hc⟩ := h
    HasBiproduct.mk <| by
      simpa only [(· ∘ ·), e.symm_apply_apply] using
        limit_bicone.mk (c.whisker e) ((c.whisker_is_bilimit_iff _).2 hc)⟩
#align category_theory.limits.has_biproducts_of_shape_of_equiv CategoryTheory.Limits.hasBiproductsOfShape_of_equiv
-/

#print CategoryTheory.Limits.hasBiproductsOfShape_finite /-
instance (priority := 100) hasBiproductsOfShape_finite [HasFiniteBiproducts C] [Finite J] :
    HasBiproductsOfShape J C :=
  by
  rcases Finite.exists_equiv_fin J with ⟨n, ⟨e⟩⟩
  haveI := has_finite_biproducts.out C n
  exact has_biproducts_of_shape_of_equiv C e
#align category_theory.limits.has_biproducts_of_shape_finite CategoryTheory.Limits.hasBiproductsOfShape_finite
-/

#print CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteBiproducts /-
instance (priority := 100) hasFiniteProducts_of_hasFiniteBiproducts [HasFiniteBiproducts C] :
    HasFiniteProducts C where out n := ⟨fun F => hasLimitOfIso Discrete.natIsoFunctor.symm⟩
#align category_theory.limits.has_finite_products_of_has_finite_biproducts CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteBiproducts
-/

#print CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteBiproducts /-
instance (priority := 100) hasFiniteCoproducts_of_hasFiniteBiproducts [HasFiniteBiproducts C] :
    HasFiniteCoproducts C where out n := ⟨fun F => hasColimitOfIso Discrete.natIsoFunctor⟩
#align category_theory.limits.has_finite_coproducts_of_has_finite_biproducts CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteBiproducts
-/

variable {J C}

#print CategoryTheory.Limits.biproductIso /-
/-- The isomorphism between the specified limit and the specified colimit for
a functor with a bilimit.
-/
def biproductIso (F : J → C) [HasBiproduct F] : Limits.piObj F ≅ Limits.sigmaObj F :=
  (IsLimit.conePointUniqueUpToIso (limit.isLimit _) (biproduct.isLimit F)).trans <|
    IsColimit.coconePointUniqueUpToIso (biproduct.isColimit F) (colimit.isColimit _)
#align category_theory.limits.biproduct_iso CategoryTheory.Limits.biproductIso
-/

end Limits

namespace Limits

variable {J : Type w}

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

#print CategoryTheory.Limits.biproduct /-
/-- `biproduct f` computes the biproduct of a family of elements `f`. (It is defined as an
   abbreviation for `limit (discrete.functor f)`, so for most facts about `biproduct f`, you will
   just use general facts about limits and colimits.) -/
abbrev biproduct (f : J → C) [HasBiproduct f] : C :=
  (biproduct.bicone f).pt
#align category_theory.limits.biproduct CategoryTheory.Limits.biproduct
-/

-- mathport name: «expr⨁ »
notation "⨁ " f:20 => biproduct f

#print CategoryTheory.Limits.biproduct.π /-
/-- The projection onto a summand of a biproduct. -/
abbrev biproduct.π (f : J → C) [HasBiproduct f] (b : J) : ⨁ f ⟶ f b :=
  (biproduct.bicone f).π b
#align category_theory.limits.biproduct.π CategoryTheory.Limits.biproduct.π
-/

#print CategoryTheory.Limits.biproduct.bicone_π /-
@[simp]
theorem biproduct.bicone_π (f : J → C) [HasBiproduct f] (b : J) :
    (biproduct.bicone f).π b = biproduct.π f b :=
  rfl
#align category_theory.limits.biproduct.bicone_π CategoryTheory.Limits.biproduct.bicone_π
-/

#print CategoryTheory.Limits.biproduct.ι /-
/-- The inclusion into a summand of a biproduct. -/
abbrev biproduct.ι (f : J → C) [HasBiproduct f] (b : J) : f b ⟶ ⨁ f :=
  (biproduct.bicone f).ι b
#align category_theory.limits.biproduct.ι CategoryTheory.Limits.biproduct.ι
-/

#print CategoryTheory.Limits.biproduct.bicone_ι /-
@[simp]
theorem biproduct.bicone_ι (f : J → C) [HasBiproduct f] (b : J) :
    (biproduct.bicone f).ι b = biproduct.ι f b :=
  rfl
#align category_theory.limits.biproduct.bicone_ι CategoryTheory.Limits.biproduct.bicone_ι
-/

#print CategoryTheory.Limits.biproduct.ι_π /-
/-- Note that as this lemma has a `if` in the statement, we include a `decidable_eq` argument.
This means you may not be able to `simp` using this lemma unless you `open_locale classical`. -/
@[reassoc.1]
theorem biproduct.ι_π [DecidableEq J] (f : J → C) [HasBiproduct f] (j j' : J) :
    biproduct.ι f j ≫ biproduct.π f j' = if h : j = j' then eqToHom (congr_arg f h) else 0 := by
  convert (biproduct.bicone f).ι_π j j'
#align category_theory.limits.biproduct.ι_π CategoryTheory.Limits.biproduct.ι_π
-/

#print CategoryTheory.Limits.biproduct.ι_π_self /-
@[simp, reassoc.1]
theorem biproduct.ι_π_self (f : J → C) [HasBiproduct f] (j : J) :
    biproduct.ι f j ≫ biproduct.π f j = 𝟙 _ := by simp [biproduct.ι_π]
#align category_theory.limits.biproduct.ι_π_self CategoryTheory.Limits.biproduct.ι_π_self
-/

#print CategoryTheory.Limits.biproduct.ι_π_ne /-
@[simp, reassoc.1]
theorem biproduct.ι_π_ne (f : J → C) [HasBiproduct f] {j j' : J} (h : j ≠ j') :
    biproduct.ι f j ≫ biproduct.π f j' = 0 := by simp [biproduct.ι_π, h]
#align category_theory.limits.biproduct.ι_π_ne CategoryTheory.Limits.biproduct.ι_π_ne
-/

#print CategoryTheory.Limits.biproduct.lift /-
/-- Given a collection of maps into the summands, we obtain a map into the biproduct. -/
abbrev biproduct.lift {f : J → C} [HasBiproduct f] {P : C} (p : ∀ b, P ⟶ f b) : P ⟶ ⨁ f :=
  (biproduct.isLimit f).lift (Fan.mk P p)
#align category_theory.limits.biproduct.lift CategoryTheory.Limits.biproduct.lift
-/

#print CategoryTheory.Limits.biproduct.desc /-
/-- Given a collection of maps out of the summands, we obtain a map out of the biproduct. -/
abbrev biproduct.desc {f : J → C} [HasBiproduct f] {P : C} (p : ∀ b, f b ⟶ P) : ⨁ f ⟶ P :=
  (biproduct.isColimit f).desc (Cofan.mk P p)
#align category_theory.limits.biproduct.desc CategoryTheory.Limits.biproduct.desc
-/

#print CategoryTheory.Limits.biproduct.lift_π /-
@[simp, reassoc.1]
theorem biproduct.lift_π {f : J → C} [HasBiproduct f] {P : C} (p : ∀ b, P ⟶ f b) (j : J) :
    biproduct.lift p ≫ biproduct.π f j = p j :=
  (biproduct.isLimit f).fac _ ⟨j⟩
#align category_theory.limits.biproduct.lift_π CategoryTheory.Limits.biproduct.lift_π
-/

#print CategoryTheory.Limits.biproduct.ι_desc /-
@[simp, reassoc.1]
theorem biproduct.ι_desc {f : J → C} [HasBiproduct f] {P : C} (p : ∀ b, f b ⟶ P) (j : J) :
    biproduct.ι f j ≫ biproduct.desc p = p j :=
  (biproduct.isColimit f).fac _ ⟨j⟩
#align category_theory.limits.biproduct.ι_desc CategoryTheory.Limits.biproduct.ι_desc
-/

#print CategoryTheory.Limits.biproduct.map /-
/-- Given a collection of maps between corresponding summands of a pair of biproducts
indexed by the same type, we obtain a map between the biproducts. -/
abbrev biproduct.map {f g : J → C} [HasBiproduct f] [HasBiproduct g] (p : ∀ b, f b ⟶ g b) :
    ⨁ f ⟶ ⨁ g :=
  IsLimit.map (biproduct.bicone f).toCone (biproduct.isLimit g) (Discrete.natTrans fun j => p j.as)
#align category_theory.limits.biproduct.map CategoryTheory.Limits.biproduct.map
-/

#print CategoryTheory.Limits.biproduct.map' /-
/-- An alternative to `biproduct.map` constructed via colimits.
This construction only exists in order to show it is equal to `biproduct.map`. -/
abbrev biproduct.map' {f g : J → C} [HasBiproduct f] [HasBiproduct g] (p : ∀ b, f b ⟶ g b) :
    ⨁ f ⟶ ⨁ g :=
  IsColimit.map (biproduct.isColimit f) (biproduct.bicone g).toCocone
    (Discrete.natTrans fun j => p j.as)
#align category_theory.limits.biproduct.map' CategoryTheory.Limits.biproduct.map'
-/

#print CategoryTheory.Limits.biproduct.hom_ext /-
@[ext]
theorem biproduct.hom_ext {f : J → C} [HasBiproduct f] {Z : C} (g h : Z ⟶ ⨁ f)
    (w : ∀ j, g ≫ biproduct.π f j = h ≫ biproduct.π f j) : g = h :=
  (biproduct.isLimit f).hom_ext fun j => w j.as
#align category_theory.limits.biproduct.hom_ext CategoryTheory.Limits.biproduct.hom_ext
-/

#print CategoryTheory.Limits.biproduct.hom_ext' /-
@[ext]
theorem biproduct.hom_ext' {f : J → C} [HasBiproduct f] {Z : C} (g h : ⨁ f ⟶ Z)
    (w : ∀ j, biproduct.ι f j ≫ g = biproduct.ι f j ≫ h) : g = h :=
  (biproduct.isColimit f).hom_ext fun j => w j.as
#align category_theory.limits.biproduct.hom_ext' CategoryTheory.Limits.biproduct.hom_ext'
-/

#print CategoryTheory.Limits.biproduct.isoProduct /-
/-- The canonical isomorphism between the chosen biproduct and the chosen product. -/
def biproduct.isoProduct (f : J → C) [HasBiproduct f] : ⨁ f ≅ ∏ f :=
  IsLimit.conePointUniqueUpToIso (biproduct.isLimit f) (limit.isLimit _)
#align category_theory.limits.biproduct.iso_product CategoryTheory.Limits.biproduct.isoProduct
-/

#print CategoryTheory.Limits.biproduct.isoProduct_hom /-
@[simp]
theorem biproduct.isoProduct_hom {f : J → C} [HasBiproduct f] :
    (biproduct.isoProduct f).hom = Pi.lift (biproduct.π f) :=
  limit.hom_ext fun j => by simp [biproduct.iso_product]
#align category_theory.limits.biproduct.iso_product_hom CategoryTheory.Limits.biproduct.isoProduct_hom
-/

#print CategoryTheory.Limits.biproduct.isoProduct_inv /-
@[simp]
theorem biproduct.isoProduct_inv {f : J → C} [HasBiproduct f] :
    (biproduct.isoProduct f).inv = biproduct.lift (Pi.π f) :=
  biproduct.hom_ext _ _ fun j => by simp [iso.inv_comp_eq]
#align category_theory.limits.biproduct.iso_product_inv CategoryTheory.Limits.biproduct.isoProduct_inv
-/

#print CategoryTheory.Limits.biproduct.isoCoproduct /-
/-- The canonical isomorphism between the chosen biproduct and the chosen coproduct. -/
def biproduct.isoCoproduct (f : J → C) [HasBiproduct f] : ⨁ f ≅ ∐ f :=
  IsColimit.coconePointUniqueUpToIso (biproduct.isColimit f) (colimit.isColimit _)
#align category_theory.limits.biproduct.iso_coproduct CategoryTheory.Limits.biproduct.isoCoproduct
-/

#print CategoryTheory.Limits.biproduct.isoCoproduct_inv /-
@[simp]
theorem biproduct.isoCoproduct_inv {f : J → C} [HasBiproduct f] :
    (biproduct.isoCoproduct f).inv = Sigma.desc (biproduct.ι f) :=
  colimit.hom_ext fun j => by simp [biproduct.iso_coproduct]
#align category_theory.limits.biproduct.iso_coproduct_inv CategoryTheory.Limits.biproduct.isoCoproduct_inv
-/

#print CategoryTheory.Limits.biproduct.isoCoproduct_hom /-
@[simp]
theorem biproduct.isoCoproduct_hom {f : J → C} [HasBiproduct f] :
    (biproduct.isoCoproduct f).hom = biproduct.desc (Sigma.ι f) :=
  biproduct.hom_ext' _ _ fun j => by simp [← iso.eq_comp_inv]
#align category_theory.limits.biproduct.iso_coproduct_hom CategoryTheory.Limits.biproduct.isoCoproduct_hom
-/

#print CategoryTheory.Limits.biproduct.map_eq_map' /-
theorem biproduct.map_eq_map' {f g : J → C} [HasBiproduct f] [HasBiproduct g] (p : ∀ b, f b ⟶ g b) :
    biproduct.map p = biproduct.map' p := by
  ext (j j')
  simp only [discrete.nat_trans_app, limits.is_colimit.ι_map, limits.is_limit.map_π, category.assoc,
    ← bicone.to_cone_π_app_mk, ← biproduct.bicone_π, ← bicone.to_cocone_ι_app_mk, ←
    biproduct.bicone_ι]
  simp only [biproduct.bicone_ι, biproduct.bicone_π, bicone.to_cocone_ι_app, bicone.to_cone_π_app]
  dsimp
  rw [biproduct.ι_π_assoc, biproduct.ι_π]
  split_ifs
  · subst h
    rw [eq_to_hom_refl, category.id_comp]
    erw [category.comp_id]
  · simp
#align category_theory.limits.biproduct.map_eq_map' CategoryTheory.Limits.biproduct.map_eq_map'
-/

#print CategoryTheory.Limits.biproduct.map_π /-
@[simp, reassoc.1]
theorem biproduct.map_π {f g : J → C} [HasBiproduct f] [HasBiproduct g] (p : ∀ j, f j ⟶ g j)
    (j : J) : biproduct.map p ≫ biproduct.π g j = biproduct.π f j ≫ p j :=
  Limits.IsLimit.map_π _ _ _ (Discrete.mk j)
#align category_theory.limits.biproduct.map_π CategoryTheory.Limits.biproduct.map_π
-/

#print CategoryTheory.Limits.biproduct.ι_map /-
@[simp, reassoc.1]
theorem biproduct.ι_map {f g : J → C} [HasBiproduct f] [HasBiproduct g] (p : ∀ j, f j ⟶ g j)
    (j : J) : biproduct.ι f j ≫ biproduct.map p = p j ≫ biproduct.ι g j :=
  by
  rw [biproduct.map_eq_map']
  convert limits.is_colimit.ι_map _ _ _ (discrete.mk j) <;> rfl
#align category_theory.limits.biproduct.ι_map CategoryTheory.Limits.biproduct.ι_map
-/

#print CategoryTheory.Limits.biproduct.map_desc /-
@[simp, reassoc.1]
theorem biproduct.map_desc {f g : J → C} [HasBiproduct f] [HasBiproduct g] (p : ∀ j, f j ⟶ g j)
    {P : C} (k : ∀ j, g j ⟶ P) :
    biproduct.map p ≫ biproduct.desc k = biproduct.desc fun j => p j ≫ k j :=
  by
  ext
  simp
#align category_theory.limits.biproduct.map_desc CategoryTheory.Limits.biproduct.map_desc
-/

#print CategoryTheory.Limits.biproduct.lift_map /-
@[simp, reassoc.1]
theorem biproduct.lift_map {f g : J → C} [HasBiproduct f] [HasBiproduct g] {P : C}
    (k : ∀ j, P ⟶ f j) (p : ∀ j, f j ⟶ g j) :
    biproduct.lift k ≫ biproduct.map p = biproduct.lift fun j => k j ≫ p j :=
  by
  ext
  simp
#align category_theory.limits.biproduct.lift_map CategoryTheory.Limits.biproduct.lift_map
-/

#print CategoryTheory.Limits.biproduct.mapIso /-
/-- Given a collection of isomorphisms between corresponding summands of a pair of biproducts
indexed by the same type, we obtain an isomorphism between the biproducts. -/
@[simps]
def biproduct.mapIso {f g : J → C} [HasBiproduct f] [HasBiproduct g] (p : ∀ b, f b ≅ g b) :
    ⨁ f ≅ ⨁ g where
  hom := biproduct.map fun b => (p b).hom
  inv := biproduct.map fun b => (p b).inv
#align category_theory.limits.biproduct.map_iso CategoryTheory.Limits.biproduct.mapIso
-/

section πKernel

section

variable (f : J → C) [HasBiproduct f]

variable (p : J → Prop) [HasBiproduct (Subtype.restrict p f)]

#print CategoryTheory.Limits.biproduct.fromSubtype /-
/-- The canonical morphism from the biproduct over a restricted index type to the biproduct of
the full index type. -/
def biproduct.fromSubtype : ⨁ Subtype.restrict p f ⟶ ⨁ f :=
  biproduct.desc fun j => biproduct.ι _ _
#align category_theory.limits.biproduct.from_subtype CategoryTheory.Limits.biproduct.fromSubtype
-/

#print CategoryTheory.Limits.biproduct.toSubtype /-
/-- The canonical morphism from a biproduct to the biproduct over a restriction of its index
type. -/
def biproduct.toSubtype : ⨁ f ⟶ ⨁ Subtype.restrict p f :=
  biproduct.lift fun j => biproduct.π _ _
#align category_theory.limits.biproduct.to_subtype CategoryTheory.Limits.biproduct.toSubtype
-/

#print CategoryTheory.Limits.biproduct.fromSubtype_π /-
@[simp, reassoc.1]
theorem biproduct.fromSubtype_π [DecidablePred p] (j : J) :
    biproduct.fromSubtype f p ≫ biproduct.π f j =
      if h : p j then biproduct.π (Subtype.restrict p f) ⟨j, h⟩ else 0 :=
  by
  ext i
  rw [biproduct.from_subtype, biproduct.ι_desc_assoc, biproduct.ι_π]
  by_cases h : p j
  · rw [dif_pos h, biproduct.ι_π]
    split_ifs with h₁ h₂ h₂
    exacts[rfl, False.elim (h₂ (Subtype.ext h₁)), False.elim (h₁ (congr_arg Subtype.val h₂)), rfl]
  · rw [dif_neg h, dif_neg (show (i : J) ≠ j from fun h₂ => h (h₂ ▸ i.2)), comp_zero]
#align category_theory.limits.biproduct.from_subtype_π CategoryTheory.Limits.biproduct.fromSubtype_π
-/

#print CategoryTheory.Limits.biproduct.fromSubtype_eq_lift /-
theorem biproduct.fromSubtype_eq_lift [DecidablePred p] :
    biproduct.fromSubtype f p =
      biproduct.lift fun j => if h : p j then biproduct.π (Subtype.restrict p f) ⟨j, h⟩ else 0 :=
  biproduct.hom_ext _ _ (by simp)
#align category_theory.limits.biproduct.from_subtype_eq_lift CategoryTheory.Limits.biproduct.fromSubtype_eq_lift
-/

#print CategoryTheory.Limits.biproduct.fromSubtype_π_subtype /-
@[simp, reassoc.1]
theorem biproduct.fromSubtype_π_subtype (j : Subtype p) :
    biproduct.fromSubtype f p ≫ biproduct.π f j = biproduct.π (Subtype.restrict p f) j :=
  by
  ext i
  rw [biproduct.from_subtype, biproduct.ι_desc_assoc, biproduct.ι_π, biproduct.ι_π]
  split_ifs with h₁ h₂ h₂
  exacts[rfl, False.elim (h₂ (Subtype.ext h₁)), False.elim (h₁ (congr_arg Subtype.val h₂)), rfl]
#align category_theory.limits.biproduct.from_subtype_π_subtype CategoryTheory.Limits.biproduct.fromSubtype_π_subtype
-/

#print CategoryTheory.Limits.biproduct.toSubtype_π /-
@[simp, reassoc.1]
theorem biproduct.toSubtype_π (j : Subtype p) :
    biproduct.toSubtype f p ≫ biproduct.π (Subtype.restrict p f) j = biproduct.π f j :=
  biproduct.lift_π _ _
#align category_theory.limits.biproduct.to_subtype_π CategoryTheory.Limits.biproduct.toSubtype_π
-/

#print CategoryTheory.Limits.biproduct.ι_toSubtype /-
@[simp, reassoc.1]
theorem biproduct.ι_toSubtype [DecidablePred p] (j : J) :
    biproduct.ι f j ≫ biproduct.toSubtype f p =
      if h : p j then biproduct.ι (Subtype.restrict p f) ⟨j, h⟩ else 0 :=
  by
  ext i
  rw [biproduct.to_subtype, category.assoc, biproduct.lift_π, biproduct.ι_π]
  by_cases h : p j
  · rw [dif_pos h, biproduct.ι_π]
    split_ifs with h₁ h₂ h₂
    exacts[rfl, False.elim (h₂ (Subtype.ext h₁)), False.elim (h₁ (congr_arg Subtype.val h₂)), rfl]
  · rw [dif_neg h, dif_neg (show j ≠ i from fun h₂ => h (h₂.symm ▸ i.2)), zero_comp]
#align category_theory.limits.biproduct.ι_to_subtype CategoryTheory.Limits.biproduct.ι_toSubtype
-/

#print CategoryTheory.Limits.biproduct.toSubtype_eq_desc /-
theorem biproduct.toSubtype_eq_desc [DecidablePred p] :
    biproduct.toSubtype f p =
      biproduct.desc fun j => if h : p j then biproduct.ι (Subtype.restrict p f) ⟨j, h⟩ else 0 :=
  biproduct.hom_ext' _ _ (by simp)
#align category_theory.limits.biproduct.to_subtype_eq_desc CategoryTheory.Limits.biproduct.toSubtype_eq_desc
-/

#print CategoryTheory.Limits.biproduct.ι_toSubtype_subtype /-
@[simp, reassoc.1]
theorem biproduct.ι_toSubtype_subtype (j : Subtype p) :
    biproduct.ι f j ≫ biproduct.toSubtype f p = biproduct.ι (Subtype.restrict p f) j :=
  by
  ext i
  rw [biproduct.to_subtype, category.assoc, biproduct.lift_π, biproduct.ι_π, biproduct.ι_π]
  split_ifs with h₁ h₂ h₂
  exacts[rfl, False.elim (h₂ (Subtype.ext h₁)), False.elim (h₁ (congr_arg Subtype.val h₂)), rfl]
#align category_theory.limits.biproduct.ι_to_subtype_subtype CategoryTheory.Limits.biproduct.ι_toSubtype_subtype
-/

#print CategoryTheory.Limits.biproduct.ι_fromSubtype /-
@[simp, reassoc.1]
theorem biproduct.ι_fromSubtype (j : Subtype p) :
    biproduct.ι (Subtype.restrict p f) j ≫ biproduct.fromSubtype f p = biproduct.ι f j :=
  biproduct.ι_desc _ _
#align category_theory.limits.biproduct.ι_from_subtype CategoryTheory.Limits.biproduct.ι_fromSubtype
-/

#print CategoryTheory.Limits.biproduct.fromSubtype_toSubtype /-
@[simp, reassoc.1]
theorem biproduct.fromSubtype_toSubtype :
    biproduct.fromSubtype f p ≫ biproduct.toSubtype f p = 𝟙 (⨁ Subtype.restrict p f) :=
  by
  refine' biproduct.hom_ext _ _ fun j => _
  rw [category.assoc, biproduct.to_subtype_π, biproduct.from_subtype_π_subtype, category.id_comp]
#align category_theory.limits.biproduct.from_subtype_to_subtype CategoryTheory.Limits.biproduct.fromSubtype_toSubtype
-/

#print CategoryTheory.Limits.biproduct.toSubtype_fromSubtype /-
@[simp, reassoc.1]
theorem biproduct.toSubtype_fromSubtype [DecidablePred p] :
    biproduct.toSubtype f p ≫ biproduct.fromSubtype f p =
      biproduct.map fun j => if p j then 𝟙 (f j) else 0 :=
  by
  ext1 i
  by_cases h : p i
  · simp [h]
    congr
  · simp [h]
#align category_theory.limits.biproduct.to_subtype_from_subtype CategoryTheory.Limits.biproduct.toSubtype_fromSubtype
-/

end

section

variable (f : J → C) (i : J) [HasBiproduct f] [HasBiproduct (Subtype.restrict (fun j => j ≠ i) f)]

#print CategoryTheory.Limits.biproduct.isLimitFromSubtype /-
/-- The kernel of `biproduct.π f i` is the inclusion from the biproduct which omits `i`
from the index set `J` into the biproduct over `J`. -/
def biproduct.isLimitFromSubtype :
    IsLimit
      (KernelFork.ofι (biproduct.fromSubtype f fun j => j ≠ i) (by simp) :
        KernelFork (biproduct.π f i)) :=
  Fork.IsLimit.mk' _ fun s =>
    ⟨s.ι ≫ biproduct.toSubtype _ _, by
      ext j
      rw [kernel_fork.ι_of_ι, category.assoc, category.assoc,
        biproduct.to_subtype_from_subtype_assoc, biproduct.map_π]
      rcases em (i = j) with (rfl | h)
      · rw [if_neg (Classical.not_not.2 rfl), comp_zero, comp_zero, kernel_fork.condition]
      · rw [if_pos (Ne.symm h), category.comp_id],
      by
      intro m hm
      rw [← hm, kernel_fork.ι_of_ι, category.assoc, biproduct.from_subtype_to_subtype]
      exact (category.comp_id _).symm⟩
#align category_theory.limits.biproduct.is_limit_from_subtype CategoryTheory.Limits.biproduct.isLimitFromSubtype
-/

instance : HasKernel (biproduct.π f i) :=
  HasLimit.mk ⟨_, biproduct.isLimitFromSubtype f i⟩

#print CategoryTheory.Limits.kernelBiproductπIso /-
/-- The kernel of `biproduct.π f i` is `⨁ subtype.restrict {i}ᶜ f`. -/
@[simps]
def kernelBiproductπIso : kernel (biproduct.π f i) ≅ ⨁ Subtype.restrict (fun j => j ≠ i) f :=
  limit.isoLimitCone ⟨_, biproduct.isLimitFromSubtype f i⟩
#align category_theory.limits.kernel_biproduct_π_iso CategoryTheory.Limits.kernelBiproductπIso
-/

#print CategoryTheory.Limits.biproduct.isColimitToSubtype /-
/-- The cokernel of `biproduct.ι f i` is the projection from the biproduct over the index set `J`
onto the biproduct omitting `i`. -/
def biproduct.isColimitToSubtype :
    IsColimit
      (CokernelCofork.ofπ (biproduct.toSubtype f fun j => j ≠ i) (by simp) :
        CokernelCofork (biproduct.ι f i)) :=
  Cofork.IsColimit.mk' _ fun s =>
    ⟨biproduct.fromSubtype _ _ ≫ s.π, by
      ext j
      rw [cokernel_cofork.π_of_π, biproduct.to_subtype_from_subtype_assoc, biproduct.ι_map_assoc]
      rcases em (i = j) with (rfl | h)
      · rw [if_neg (Classical.not_not.2 rfl), zero_comp, cokernel_cofork.condition]
      · rw [if_pos (Ne.symm h), category.id_comp],
      by
      intro m hm
      rw [← hm, cokernel_cofork.π_of_π, ← category.assoc, biproduct.from_subtype_to_subtype]
      exact (category.id_comp _).symm⟩
#align category_theory.limits.biproduct.is_colimit_to_subtype CategoryTheory.Limits.biproduct.isColimitToSubtype
-/

instance : HasCokernel (biproduct.ι f i) :=
  HasColimit.mk ⟨_, biproduct.isColimitToSubtype f i⟩

#print CategoryTheory.Limits.cokernelBiproductιIso /-
/-- The cokernel of `biproduct.ι f i` is `⨁ subtype.restrict {i}ᶜ f`. -/
@[simps]
def cokernelBiproductιIso : cokernel (biproduct.ι f i) ≅ ⨁ Subtype.restrict (fun j => j ≠ i) f :=
  colimit.isoColimitCocone ⟨_, biproduct.isColimitToSubtype f i⟩
#align category_theory.limits.cokernel_biproduct_ι_iso CategoryTheory.Limits.cokernelBiproductιIso
-/

end

section

open Classical

-- Per #15067, we only allow indexing in `Type 0` here.
variable {K : Type} [Fintype K] [HasFiniteBiproducts C] (f : K → C)

#print CategoryTheory.Limits.kernelForkBiproductToSubtype /-
/-- The limit cone exhibiting `⨁ subtype.restrict pᶜ f` as the kernel of
`biproduct.to_subtype f p` -/
@[simps]
def kernelForkBiproductToSubtype (p : Set K) : LimitCone (parallelPair (biproduct.toSubtype f p) 0)
    where
  Cone :=
    KernelFork.ofι (biproduct.fromSubtype f (pᶜ))
      (by
        ext (j k)
        simp only [biproduct.ι_from_subtype_assoc, biproduct.ι_to_subtype, comp_zero, zero_comp]
        erw [dif_neg j.2]
        simp only [zero_comp])
  IsLimit :=
    KernelFork.IsLimit.ofι _ _ (fun W g h => g ≫ biproduct.toSubtype f (pᶜ))
      (by
        intro W' g' w
        ext j
        simp only [category.assoc, biproduct.to_subtype_from_subtype, Pi.compl_apply,
          biproduct.map_π]
        split_ifs
        · simp
        · replace w := w =≫ biproduct.π _ ⟨j, not_not.mp h⟩
          simpa using w.symm)
      (by tidy)
#align category_theory.limits.kernel_fork_biproduct_to_subtype CategoryTheory.Limits.kernelForkBiproductToSubtype
-/

instance (p : Set K) : HasKernel (biproduct.toSubtype f p) :=
  HasLimit.mk (kernelForkBiproductToSubtype f p)

#print CategoryTheory.Limits.kernelBiproductToSubtypeIso /-
/-- The kernel of `biproduct.to_subtype f p` is `⨁ subtype.restrict pᶜ f`. -/
@[simps]
def kernelBiproductToSubtypeIso (p : Set K) :
    kernel (biproduct.toSubtype f p) ≅ ⨁ Subtype.restrict (pᶜ) f :=
  limit.isoLimitCone (kernelForkBiproductToSubtype f p)
#align category_theory.limits.kernel_biproduct_to_subtype_iso CategoryTheory.Limits.kernelBiproductToSubtypeIso
-/

#print CategoryTheory.Limits.cokernelCoforkBiproductFromSubtype /-
/-- The colimit cocone exhibiting `⨁ subtype.restrict pᶜ f` as the cokernel of
`biproduct.from_subtype f p` -/
@[simps]
def cokernelCoforkBiproductFromSubtype (p : Set K) :
    ColimitCocone (parallelPair (biproduct.fromSubtype f p) 0)
    where
  Cocone :=
    CokernelCofork.ofπ (biproduct.toSubtype f (pᶜ))
      (by
        ext (j k)
        simp only [Pi.compl_apply, biproduct.ι_from_subtype_assoc, biproduct.ι_to_subtype,
          comp_zero, zero_comp]
        rw [dif_neg]
        simp only [zero_comp]
        exact not_not.mpr j.2)
  IsColimit :=
    CokernelCofork.IsColimit.ofπ _ _ (fun W g h => biproduct.fromSubtype f (pᶜ) ≫ g)
      (by
        intro W' g' w
        ext j
        simp only [biproduct.to_subtype_from_subtype_assoc, Pi.compl_apply, biproduct.ι_map_assoc]
        split_ifs
        · simp
        · replace w := biproduct.ι _ (⟨j, not_not.mp h⟩ : p) ≫= w
          simpa using w.symm)
      (by tidy)
#align category_theory.limits.cokernel_cofork_biproduct_from_subtype CategoryTheory.Limits.cokernelCoforkBiproductFromSubtype
-/

instance (p : Set K) : HasCokernel (biproduct.fromSubtype f p) :=
  HasColimit.mk (cokernelCoforkBiproductFromSubtype f p)

#print CategoryTheory.Limits.cokernelBiproductFromSubtypeIso /-
/-- The cokernel of `biproduct.from_subtype f p` is `⨁ subtype.restrict pᶜ f`. -/
@[simps]
def cokernelBiproductFromSubtypeIso (p : Set K) :
    cokernel (biproduct.fromSubtype f p) ≅ ⨁ Subtype.restrict (pᶜ) f :=
  colimit.isoColimitCocone (cokernelCoforkBiproductFromSubtype f p)
#align category_theory.limits.cokernel_biproduct_from_subtype_iso CategoryTheory.Limits.cokernelBiproductFromSubtypeIso
-/

end

end πKernel

end Limits

namespace Limits

section FiniteBiproducts

variable {J : Type} [Fintype J] {K : Type} [Fintype K] {C : Type u} [Category.{v} C]
  [HasZeroMorphisms C] [HasFiniteBiproducts C] {f : J → C} {g : K → C}

#print CategoryTheory.Limits.biproduct.matrix /-
/-- Convert a (dependently typed) matrix to a morphism of biproducts.
-/
def biproduct.matrix (m : ∀ j k, f j ⟶ g k) : ⨁ f ⟶ ⨁ g :=
  biproduct.desc fun j => biproduct.lift fun k => m j k
#align category_theory.limits.biproduct.matrix CategoryTheory.Limits.biproduct.matrix
-/

#print CategoryTheory.Limits.biproduct.matrix_π /-
@[simp, reassoc.1]
theorem biproduct.matrix_π (m : ∀ j k, f j ⟶ g k) (k : K) :
    biproduct.matrix m ≫ biproduct.π g k = biproduct.desc fun j => m j k :=
  by
  ext
  simp [biproduct.matrix]
#align category_theory.limits.biproduct.matrix_π CategoryTheory.Limits.biproduct.matrix_π
-/

#print CategoryTheory.Limits.biproduct.ι_matrix /-
@[simp, reassoc.1]
theorem biproduct.ι_matrix (m : ∀ j k, f j ⟶ g k) (j : J) :
    biproduct.ι f j ≫ biproduct.matrix m = biproduct.lift fun k => m j k :=
  by
  ext
  simp [biproduct.matrix]
#align category_theory.limits.biproduct.ι_matrix CategoryTheory.Limits.biproduct.ι_matrix
-/

#print CategoryTheory.Limits.biproduct.components /-
/-- Extract the matrix components from a morphism of biproducts.
-/
def biproduct.components (m : ⨁ f ⟶ ⨁ g) (j : J) (k : K) : f j ⟶ g k :=
  biproduct.ι f j ≫ m ≫ biproduct.π g k
#align category_theory.limits.biproduct.components CategoryTheory.Limits.biproduct.components
-/

#print CategoryTheory.Limits.biproduct.matrix_components /-
@[simp]
theorem biproduct.matrix_components (m : ∀ j k, f j ⟶ g k) (j : J) (k : K) :
    biproduct.components (biproduct.matrix m) j k = m j k := by simp [biproduct.components]
#align category_theory.limits.biproduct.matrix_components CategoryTheory.Limits.biproduct.matrix_components
-/

#print CategoryTheory.Limits.biproduct.components_matrix /-
@[simp]
theorem biproduct.components_matrix (m : ⨁ f ⟶ ⨁ g) :
    (biproduct.matrix fun j k => biproduct.components m j k) = m :=
  by
  ext
  simp [biproduct.components]
#align category_theory.limits.biproduct.components_matrix CategoryTheory.Limits.biproduct.components_matrix
-/

#print CategoryTheory.Limits.biproduct.matrixEquiv /-
/-- Morphisms between direct sums are matrices. -/
@[simps]
def biproduct.matrixEquiv : (⨁ f ⟶ ⨁ g) ≃ ∀ j k, f j ⟶ g k
    where
  toFun := biproduct.components
  invFun := biproduct.matrix
  left_inv := biproduct.components_matrix
  right_inv m := by
    ext
    apply biproduct.matrix_components
#align category_theory.limits.biproduct.matrix_equiv CategoryTheory.Limits.biproduct.matrixEquiv
-/

end FiniteBiproducts

variable {J : Type w} {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

#print CategoryTheory.Limits.biproduct.ι_mono /-
instance biproduct.ι_mono (f : J → C) [HasBiproduct f] (b : J) : IsSplitMono (biproduct.ι f b) :=
  IsSplitMono.mk' { retraction := biproduct.desc <| Pi.single b _ }
#align category_theory.limits.biproduct.ι_mono CategoryTheory.Limits.biproduct.ι_mono
-/

#print CategoryTheory.Limits.biproduct.π_epi /-
instance biproduct.π_epi (f : J → C) [HasBiproduct f] (b : J) : IsSplitEpi (biproduct.π f b) :=
  IsSplitEpi.mk' { section_ := biproduct.lift <| Pi.single b _ }
#align category_theory.limits.biproduct.π_epi CategoryTheory.Limits.biproduct.π_epi
-/

#print CategoryTheory.Limits.biproduct.conePointUniqueUpToIso_hom /-
/-- Auxiliary lemma for `biproduct.unique_up_to_iso`. -/
theorem biproduct.conePointUniqueUpToIso_hom (f : J → C) [HasBiproduct f] {b : Bicone f}
    (hb : b.IsBilimit) :
    (hb.IsLimit.conePointUniqueUpToIso (biproduct.isLimit _)).hom = biproduct.lift b.π :=
  rfl
#align category_theory.limits.biproduct.cone_point_unique_up_to_iso_hom CategoryTheory.Limits.biproduct.conePointUniqueUpToIso_hom
-/

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `discrete_cases #[] -/
#print CategoryTheory.Limits.biproduct.conePointUniqueUpToIso_inv /-
/-- Auxiliary lemma for `biproduct.unique_up_to_iso`. -/
theorem biproduct.conePointUniqueUpToIso_inv (f : J → C) [HasBiproduct f] {b : Bicone f}
    (hb : b.IsBilimit) :
    (hb.IsLimit.conePointUniqueUpToIso (biproduct.isLimit _)).inv = biproduct.desc b.ι :=
  by
  refine' biproduct.hom_ext' _ _ fun j => hb.is_limit.hom_ext fun j' => _
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `discrete_cases #[]"
  rw [category.assoc, is_limit.cone_point_unique_up_to_iso_inv_comp, bicone.to_cone_π_app,
    biproduct.bicone_π, biproduct.ι_desc, biproduct.ι_π, b.to_cone_π_app, b.ι_π]
#align category_theory.limits.biproduct.cone_point_unique_up_to_iso_inv CategoryTheory.Limits.biproduct.conePointUniqueUpToIso_inv
-/

#print CategoryTheory.Limits.biproduct.uniqueUpToIso /-
/-- Biproducts are unique up to isomorphism. This already follows because bilimits are limits,
    but in the case of biproducts we can give an isomorphism with particularly nice definitional
    properties, namely that `biproduct.lift b.π` and `biproduct.desc b.ι` are inverses of each
    other. -/
@[simps]
def biproduct.uniqueUpToIso (f : J → C) [HasBiproduct f] {b : Bicone f} (hb : b.IsBilimit) :
    b.pt ≅ ⨁ f where
  hom := biproduct.lift b.π
  inv := biproduct.desc b.ι
  hom_inv_id' := by
    rw [← biproduct.cone_point_unique_up_to_iso_hom f hb, ←
      biproduct.cone_point_unique_up_to_iso_inv f hb, iso.hom_inv_id]
  inv_hom_id' := by
    rw [← biproduct.cone_point_unique_up_to_iso_hom f hb, ←
      biproduct.cone_point_unique_up_to_iso_inv f hb, iso.inv_hom_id]
#align category_theory.limits.biproduct.unique_up_to_iso CategoryTheory.Limits.biproduct.uniqueUpToIso
-/

variable (C)

#print CategoryTheory.Limits.hasZeroObject_of_hasFiniteBiproducts /-
-- see Note [lower instance priority]
/-- A category with finite biproducts has a zero object. -/
instance (priority := 100) hasZeroObject_of_hasFiniteBiproducts [HasFiniteBiproducts C] :
    HasZeroObject C :=
  by
  refine' ⟨⟨biproduct Empty.elim, fun X => ⟨⟨⟨0⟩, _⟩⟩, fun X => ⟨⟨⟨0⟩, _⟩⟩⟩⟩
  tidy
#align category_theory.limits.has_zero_object_of_has_finite_biproducts CategoryTheory.Limits.hasZeroObject_of_hasFiniteBiproducts
-/

section

variable {C} [Unique J] (f : J → C)

#print CategoryTheory.Limits.limitBiconeOfUnique /-
/-- The limit bicone for the biproduct over an index type with exactly one term. -/
@[simps]
def limitBiconeOfUnique : LimitBicone f
    where
  Bicone :=
    { pt := f default
      π := fun j => eqToHom (by congr )
      ι := fun j => eqToHom (by congr ) }
  IsBilimit :=
    { IsLimit := (limitConeOfUnique f).IsLimit
      IsColimit := (colimitCoconeOfUnique f).IsColimit }
#align category_theory.limits.limit_bicone_of_unique CategoryTheory.Limits.limitBiconeOfUnique
-/

#print CategoryTheory.Limits.hasBiproduct_unique /-
instance (priority := 100) hasBiproduct_unique : HasBiproduct f :=
  HasBiproduct.mk (limitBiconeOfUnique f)
#align category_theory.limits.has_biproduct_unique CategoryTheory.Limits.hasBiproduct_unique
-/

#print CategoryTheory.Limits.biproductUniqueIso /-
/-- A biproduct over a index type with exactly one term is just the object over that term. -/
@[simps]
def biproductUniqueIso : ⨁ f ≅ f default :=
  (biproduct.uniqueUpToIso _ (limitBiconeOfUnique f).IsBilimit).symm
#align category_theory.limits.biproduct_unique_iso CategoryTheory.Limits.biproductUniqueIso
-/

end

variable {C}

#print CategoryTheory.Limits.BinaryBicone /-
/-- A binary bicone for a pair of objects `P Q : C` consists of the cone point `X`,
maps from `X` to both `P` and `Q`, and maps from both `P` and `Q` to `X`,
so that `inl ≫ fst = 𝟙 P`, `inl ≫ snd = 0`, `inr ≫ fst = 0`, and `inr ≫ snd = 𝟙 Q`
-/
@[nolint has_nonempty_instance]
structure BinaryBicone (P Q : C) where
  pt : C
  fst : X ⟶ P
  snd : X ⟶ Q
  inl : P ⟶ X
  inr : Q ⟶ X
  inl_fst : inl ≫ fst = 𝟙 P := by obviously
  inl_snd : inl ≫ snd = 0 := by obviously
  inr_fst : inr ≫ fst = 0 := by obviously
  inr_snd : inr ≫ snd = 𝟙 Q := by obviously
#align category_theory.limits.binary_bicone CategoryTheory.Limits.BinaryBicone
-/

restate_axiom binary_bicone.inl_fst'

restate_axiom binary_bicone.inl_snd'

restate_axiom binary_bicone.inr_fst'

restate_axiom binary_bicone.inr_snd'

attribute [simp, reassoc.1]
  binary_bicone.inl_fst binary_bicone.inl_snd binary_bicone.inr_fst binary_bicone.inr_snd

namespace BinaryBicone

variable {P Q : C}

#print CategoryTheory.Limits.BinaryBicone.toCone /-
/-- Extract the cone from a binary bicone. -/
def toCone (c : BinaryBicone P Q) : Cone (pair P Q) :=
  BinaryFan.mk c.fst c.snd
#align category_theory.limits.binary_bicone.to_cone CategoryTheory.Limits.BinaryBicone.toCone
-/

#print CategoryTheory.Limits.BinaryBicone.toCone_pt /-
@[simp]
theorem toCone_pt (c : BinaryBicone P Q) : c.toCone.pt = c.pt :=
  rfl
#align category_theory.limits.binary_bicone.to_cone_X CategoryTheory.Limits.BinaryBicone.toCone_pt
-/

/- warning: category_theory.limits.binary_bicone.to_cone_π_app_left -> CategoryTheory.Limits.BinaryBicone.toCone_π_app_left is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u2} C _inst_1] {P : C} {Q : C} (c : CategoryTheory.Limits.BinaryBicone.{u1, u2} C _inst_1 _inst_2 P Q), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.obj.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Functor.obj.{u1, u1, u2, max u1 u2} C _inst_1 (CategoryTheory.Functor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.const.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Limits.Cone.pt.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.pair.{u1, u2} C _inst_1 P Q) (CategoryTheory.Limits.BinaryBicone.toCone.{u1, u2} C _inst_1 _inst_2 P Q c))) (CategoryTheory.Discrete.mk.{0} CategoryTheory.Limits.WalkingPair CategoryTheory.Limits.WalkingPair.left)) (CategoryTheory.Functor.obj.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.pair.{u1, u2} C _inst_1 P Q) (CategoryTheory.Discrete.mk.{0} CategoryTheory.Limits.WalkingPair CategoryTheory.Limits.WalkingPair.left))) (CategoryTheory.NatTrans.app.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Functor.obj.{u1, u1, u2, max u1 u2} C _inst_1 (CategoryTheory.Functor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.const.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Limits.Cone.pt.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.pair.{u1, u2} C _inst_1 P Q) (CategoryTheory.Limits.BinaryBicone.toCone.{u1, u2} C _inst_1 _inst_2 P Q c))) (CategoryTheory.Limits.pair.{u1, u2} C _inst_1 P Q) (CategoryTheory.Limits.Cone.π.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.pair.{u1, u2} C _inst_1 P Q) (CategoryTheory.Limits.BinaryBicone.toCone.{u1, u2} C _inst_1 _inst_2 P Q c)) (CategoryTheory.Discrete.mk.{0} CategoryTheory.Limits.WalkingPair CategoryTheory.Limits.WalkingPair.left)) (CategoryTheory.Limits.BinaryBicone.fst.{u1, u2} C _inst_1 _inst_2 P Q c)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u2} C _inst_1] {P : C} {Q : C} (c : CategoryTheory.Limits.BinaryBicone.{u1, u2} C _inst_1 _inst_2 P Q), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prefunctor.obj.{1, succ u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.CategoryStruct.toQuiver.{0, 0} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.Category.toCategoryStruct.{0, 0} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (Prefunctor.obj.{succ u1, succ u1, u2, max u1 u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{u1, max u2 u1} (CategoryTheory.Functor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Category.toCategoryStruct.{u1, max u2 u1} (CategoryTheory.Functor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, max u2 u1} C _inst_1 (CategoryTheory.Functor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.const.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1)) (CategoryTheory.Limits.Cone.pt.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.pair.{u1, u2} C _inst_1 P Q) (CategoryTheory.Limits.BinaryBicone.toCone.{u1, u2} C _inst_1 _inst_2 P Q c)))) (CategoryTheory.Discrete.mk.{0} CategoryTheory.Limits.WalkingPair CategoryTheory.Limits.WalkingPair.left)) (Prefunctor.obj.{1, succ u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.CategoryStruct.toQuiver.{0, 0} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.Category.toCategoryStruct.{0, 0} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.pair.{u1, u2} C _inst_1 P Q)) (CategoryTheory.Discrete.mk.{0} CategoryTheory.Limits.WalkingPair CategoryTheory.Limits.WalkingPair.left))) (CategoryTheory.NatTrans.app.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (Prefunctor.obj.{succ u1, succ u1, u2, max u1 u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{u1, max u2 u1} (CategoryTheory.Functor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Category.toCategoryStruct.{u1, max u2 u1} (CategoryTheory.Functor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, max u2 u1} C _inst_1 (CategoryTheory.Functor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.const.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1)) (CategoryTheory.Limits.Cone.pt.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.pair.{u1, u2} C _inst_1 P Q) (CategoryTheory.Limits.BinaryBicone.toCone.{u1, u2} C _inst_1 _inst_2 P Q c))) (CategoryTheory.Limits.pair.{u1, u2} C _inst_1 P Q) (CategoryTheory.Limits.Cone.π.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.pair.{u1, u2} C _inst_1 P Q) (CategoryTheory.Limits.BinaryBicone.toCone.{u1, u2} C _inst_1 _inst_2 P Q c)) (CategoryTheory.Discrete.mk.{0} CategoryTheory.Limits.WalkingPair CategoryTheory.Limits.WalkingPair.left)) (CategoryTheory.Limits.BinaryBicone.fst.{u1, u2} C _inst_1 _inst_2 P Q c)
Case conversion may be inaccurate. Consider using '#align category_theory.limits.binary_bicone.to_cone_π_app_left CategoryTheory.Limits.BinaryBicone.toCone_π_app_leftₓ'. -/
@[simp]
theorem toCone_π_app_left (c : BinaryBicone P Q) : c.toCone.π.app ⟨WalkingPair.left⟩ = c.fst :=
  rfl
#align category_theory.limits.binary_bicone.to_cone_π_app_left CategoryTheory.Limits.BinaryBicone.toCone_π_app_left

/- warning: category_theory.limits.binary_bicone.to_cone_π_app_right -> CategoryTheory.Limits.BinaryBicone.toCone_π_app_right is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u2} C _inst_1] {P : C} {Q : C} (c : CategoryTheory.Limits.BinaryBicone.{u1, u2} C _inst_1 _inst_2 P Q), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.obj.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Functor.obj.{u1, u1, u2, max u1 u2} C _inst_1 (CategoryTheory.Functor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.const.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Limits.Cone.pt.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.pair.{u1, u2} C _inst_1 P Q) (CategoryTheory.Limits.BinaryBicone.toCone.{u1, u2} C _inst_1 _inst_2 P Q c))) (CategoryTheory.Discrete.mk.{0} CategoryTheory.Limits.WalkingPair CategoryTheory.Limits.WalkingPair.right)) (CategoryTheory.Functor.obj.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.pair.{u1, u2} C _inst_1 P Q) (CategoryTheory.Discrete.mk.{0} CategoryTheory.Limits.WalkingPair CategoryTheory.Limits.WalkingPair.right))) (CategoryTheory.NatTrans.app.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Functor.obj.{u1, u1, u2, max u1 u2} C _inst_1 (CategoryTheory.Functor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.const.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Limits.Cone.pt.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.pair.{u1, u2} C _inst_1 P Q) (CategoryTheory.Limits.BinaryBicone.toCone.{u1, u2} C _inst_1 _inst_2 P Q c))) (CategoryTheory.Limits.pair.{u1, u2} C _inst_1 P Q) (CategoryTheory.Limits.Cone.π.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.pair.{u1, u2} C _inst_1 P Q) (CategoryTheory.Limits.BinaryBicone.toCone.{u1, u2} C _inst_1 _inst_2 P Q c)) (CategoryTheory.Discrete.mk.{0} CategoryTheory.Limits.WalkingPair CategoryTheory.Limits.WalkingPair.right)) (CategoryTheory.Limits.BinaryBicone.snd.{u1, u2} C _inst_1 _inst_2 P Q c)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u2} C _inst_1] {P : C} {Q : C} (c : CategoryTheory.Limits.BinaryBicone.{u1, u2} C _inst_1 _inst_2 P Q), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prefunctor.obj.{1, succ u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.CategoryStruct.toQuiver.{0, 0} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.Category.toCategoryStruct.{0, 0} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (Prefunctor.obj.{succ u1, succ u1, u2, max u1 u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{u1, max u2 u1} (CategoryTheory.Functor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Category.toCategoryStruct.{u1, max u2 u1} (CategoryTheory.Functor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, max u2 u1} C _inst_1 (CategoryTheory.Functor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.const.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1)) (CategoryTheory.Limits.Cone.pt.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.pair.{u1, u2} C _inst_1 P Q) (CategoryTheory.Limits.BinaryBicone.toCone.{u1, u2} C _inst_1 _inst_2 P Q c)))) (CategoryTheory.Discrete.mk.{0} CategoryTheory.Limits.WalkingPair CategoryTheory.Limits.WalkingPair.right)) (Prefunctor.obj.{1, succ u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.CategoryStruct.toQuiver.{0, 0} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.Category.toCategoryStruct.{0, 0} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.pair.{u1, u2} C _inst_1 P Q)) (CategoryTheory.Discrete.mk.{0} CategoryTheory.Limits.WalkingPair CategoryTheory.Limits.WalkingPair.right))) (CategoryTheory.NatTrans.app.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (Prefunctor.obj.{succ u1, succ u1, u2, max u1 u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{u1, max u2 u1} (CategoryTheory.Functor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Category.toCategoryStruct.{u1, max u2 u1} (CategoryTheory.Functor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, max u2 u1} C _inst_1 (CategoryTheory.Functor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.const.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1)) (CategoryTheory.Limits.Cone.pt.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.pair.{u1, u2} C _inst_1 P Q) (CategoryTheory.Limits.BinaryBicone.toCone.{u1, u2} C _inst_1 _inst_2 P Q c))) (CategoryTheory.Limits.pair.{u1, u2} C _inst_1 P Q) (CategoryTheory.Limits.Cone.π.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.pair.{u1, u2} C _inst_1 P Q) (CategoryTheory.Limits.BinaryBicone.toCone.{u1, u2} C _inst_1 _inst_2 P Q c)) (CategoryTheory.Discrete.mk.{0} CategoryTheory.Limits.WalkingPair CategoryTheory.Limits.WalkingPair.right)) (CategoryTheory.Limits.BinaryBicone.snd.{u1, u2} C _inst_1 _inst_2 P Q c)
Case conversion may be inaccurate. Consider using '#align category_theory.limits.binary_bicone.to_cone_π_app_right CategoryTheory.Limits.BinaryBicone.toCone_π_app_rightₓ'. -/
@[simp]
theorem toCone_π_app_right (c : BinaryBicone P Q) : c.toCone.π.app ⟨WalkingPair.right⟩ = c.snd :=
  rfl
#align category_theory.limits.binary_bicone.to_cone_π_app_right CategoryTheory.Limits.BinaryBicone.toCone_π_app_right

/- warning: category_theory.limits.binary_bicone.binary_fan_fst_to_cone -> CategoryTheory.Limits.BinaryBicone.binary_fan_fst_toCone is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u2} C _inst_1] {P : C} {Q : C} (c : CategoryTheory.Limits.BinaryBicone.{u1, u2} C _inst_1 _inst_2 P Q), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.obj.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Functor.obj.{u1, u1, u2, max u1 u2} C _inst_1 (CategoryTheory.Functor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.const.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Limits.Cone.pt.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.pair.{u1, u2} C _inst_1 P Q) (CategoryTheory.Limits.BinaryBicone.toCone.{u1, u2} C _inst_1 _inst_2 P Q c))) (CategoryTheory.Discrete.mk.{0} CategoryTheory.Limits.WalkingPair CategoryTheory.Limits.WalkingPair.left)) (CategoryTheory.Functor.obj.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.pair.{u1, u2} C _inst_1 P Q) (CategoryTheory.Discrete.mk.{0} CategoryTheory.Limits.WalkingPair CategoryTheory.Limits.WalkingPair.left))) (CategoryTheory.Limits.BinaryFan.fst.{u1, u2} C _inst_1 P Q (CategoryTheory.Limits.BinaryBicone.toCone.{u1, u2} C _inst_1 _inst_2 P Q c)) (CategoryTheory.Limits.BinaryBicone.fst.{u1, u2} C _inst_1 _inst_2 P Q c)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u2} C _inst_1] {P : C} {Q : C} (c : CategoryTheory.Limits.BinaryBicone.{u1, u2} C _inst_1 _inst_2 P Q), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prefunctor.obj.{1, succ u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.CategoryStruct.toQuiver.{0, 0} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.Category.toCategoryStruct.{0, 0} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (Prefunctor.obj.{succ u1, succ u1, u2, max u1 u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{u1, max u2 u1} (CategoryTheory.Functor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Category.toCategoryStruct.{u1, max u2 u1} (CategoryTheory.Functor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, max u2 u1} C _inst_1 (CategoryTheory.Functor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.const.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1)) (CategoryTheory.Limits.Cone.pt.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.pair.{u1, u2} C _inst_1 P Q) (CategoryTheory.Limits.BinaryBicone.toCone.{u1, u2} C _inst_1 _inst_2 P Q c)))) (CategoryTheory.Discrete.mk.{0} CategoryTheory.Limits.WalkingPair CategoryTheory.Limits.WalkingPair.left)) (Prefunctor.obj.{1, succ u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.CategoryStruct.toQuiver.{0, 0} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.Category.toCategoryStruct.{0, 0} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.pair.{u1, u2} C _inst_1 P Q)) (CategoryTheory.Discrete.mk.{0} CategoryTheory.Limits.WalkingPair CategoryTheory.Limits.WalkingPair.left))) (CategoryTheory.Limits.BinaryFan.fst.{u1, u2} C _inst_1 P Q (CategoryTheory.Limits.BinaryBicone.toCone.{u1, u2} C _inst_1 _inst_2 P Q c)) (CategoryTheory.Limits.BinaryBicone.fst.{u1, u2} C _inst_1 _inst_2 P Q c)
Case conversion may be inaccurate. Consider using '#align category_theory.limits.binary_bicone.binary_fan_fst_to_cone CategoryTheory.Limits.BinaryBicone.binary_fan_fst_toConeₓ'. -/
@[simp]
theorem binary_fan_fst_toCone (c : BinaryBicone P Q) : BinaryFan.fst c.toCone = c.fst :=
  rfl
#align category_theory.limits.binary_bicone.binary_fan_fst_to_cone CategoryTheory.Limits.BinaryBicone.binary_fan_fst_toCone

/- warning: category_theory.limits.binary_bicone.binary_fan_snd_to_cone -> CategoryTheory.Limits.BinaryBicone.binary_fan_snd_toCone is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u2} C _inst_1] {P : C} {Q : C} (c : CategoryTheory.Limits.BinaryBicone.{u1, u2} C _inst_1 _inst_2 P Q), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.obj.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Functor.obj.{u1, u1, u2, max u1 u2} C _inst_1 (CategoryTheory.Functor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.const.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Limits.Cone.pt.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.pair.{u1, u2} C _inst_1 P Q) (CategoryTheory.Limits.BinaryBicone.toCone.{u1, u2} C _inst_1 _inst_2 P Q c))) (CategoryTheory.Discrete.mk.{0} CategoryTheory.Limits.WalkingPair CategoryTheory.Limits.WalkingPair.right)) (CategoryTheory.Functor.obj.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.pair.{u1, u2} C _inst_1 P Q) (CategoryTheory.Discrete.mk.{0} CategoryTheory.Limits.WalkingPair CategoryTheory.Limits.WalkingPair.right))) (CategoryTheory.Limits.BinaryFan.snd.{u1, u2} C _inst_1 P Q (CategoryTheory.Limits.BinaryBicone.toCone.{u1, u2} C _inst_1 _inst_2 P Q c)) (CategoryTheory.Limits.BinaryBicone.snd.{u1, u2} C _inst_1 _inst_2 P Q c)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u2} C _inst_1] {P : C} {Q : C} (c : CategoryTheory.Limits.BinaryBicone.{u1, u2} C _inst_1 _inst_2 P Q), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prefunctor.obj.{1, succ u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.CategoryStruct.toQuiver.{0, 0} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.Category.toCategoryStruct.{0, 0} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (Prefunctor.obj.{succ u1, succ u1, u2, max u1 u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{u1, max u2 u1} (CategoryTheory.Functor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Category.toCategoryStruct.{u1, max u2 u1} (CategoryTheory.Functor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, max u2 u1} C _inst_1 (CategoryTheory.Functor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.const.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1)) (CategoryTheory.Limits.Cone.pt.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.pair.{u1, u2} C _inst_1 P Q) (CategoryTheory.Limits.BinaryBicone.toCone.{u1, u2} C _inst_1 _inst_2 P Q c)))) (CategoryTheory.Discrete.mk.{0} CategoryTheory.Limits.WalkingPair CategoryTheory.Limits.WalkingPair.right)) (Prefunctor.obj.{1, succ u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.CategoryStruct.toQuiver.{0, 0} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.Category.toCategoryStruct.{0, 0} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.pair.{u1, u2} C _inst_1 P Q)) (CategoryTheory.Discrete.mk.{0} CategoryTheory.Limits.WalkingPair CategoryTheory.Limits.WalkingPair.right))) (CategoryTheory.Limits.BinaryFan.snd.{u1, u2} C _inst_1 P Q (CategoryTheory.Limits.BinaryBicone.toCone.{u1, u2} C _inst_1 _inst_2 P Q c)) (CategoryTheory.Limits.BinaryBicone.snd.{u1, u2} C _inst_1 _inst_2 P Q c)
Case conversion may be inaccurate. Consider using '#align category_theory.limits.binary_bicone.binary_fan_snd_to_cone CategoryTheory.Limits.BinaryBicone.binary_fan_snd_toConeₓ'. -/
@[simp]
theorem binary_fan_snd_toCone (c : BinaryBicone P Q) : BinaryFan.snd c.toCone = c.snd :=
  rfl
#align category_theory.limits.binary_bicone.binary_fan_snd_to_cone CategoryTheory.Limits.BinaryBicone.binary_fan_snd_toCone

#print CategoryTheory.Limits.BinaryBicone.toCocone /-
/-- Extract the cocone from a binary bicone. -/
def toCocone (c : BinaryBicone P Q) : Cocone (pair P Q) :=
  BinaryCofan.mk c.inl c.inr
#align category_theory.limits.binary_bicone.to_cocone CategoryTheory.Limits.BinaryBicone.toCocone
-/

#print CategoryTheory.Limits.BinaryBicone.toCocone_pt /-
@[simp]
theorem toCocone_pt (c : BinaryBicone P Q) : c.toCocone.pt = c.pt :=
  rfl
#align category_theory.limits.binary_bicone.to_cocone_X CategoryTheory.Limits.BinaryBicone.toCocone_pt
-/

/- warning: category_theory.limits.binary_bicone.to_cocone_ι_app_left -> CategoryTheory.Limits.BinaryBicone.toCocone_ι_app_left is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u2} C _inst_1] {P : C} {Q : C} (c : CategoryTheory.Limits.BinaryBicone.{u1, u2} C _inst_1 _inst_2 P Q), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.obj.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.pair.{u1, u2} C _inst_1 P Q) (CategoryTheory.Discrete.mk.{0} CategoryTheory.Limits.WalkingPair CategoryTheory.Limits.WalkingPair.left)) (CategoryTheory.Functor.obj.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Functor.obj.{u1, u1, u2, max u1 u2} C _inst_1 (CategoryTheory.Functor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.const.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Limits.Cocone.pt.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.pair.{u1, u2} C _inst_1 P Q) (CategoryTheory.Limits.BinaryBicone.toCocone.{u1, u2} C _inst_1 _inst_2 P Q c))) (CategoryTheory.Discrete.mk.{0} CategoryTheory.Limits.WalkingPair CategoryTheory.Limits.WalkingPair.left))) (CategoryTheory.NatTrans.app.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.pair.{u1, u2} C _inst_1 P Q) (CategoryTheory.Functor.obj.{u1, u1, u2, max u1 u2} C _inst_1 (CategoryTheory.Functor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.const.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Limits.Cocone.pt.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.pair.{u1, u2} C _inst_1 P Q) (CategoryTheory.Limits.BinaryBicone.toCocone.{u1, u2} C _inst_1 _inst_2 P Q c))) (CategoryTheory.Limits.Cocone.ι.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.pair.{u1, u2} C _inst_1 P Q) (CategoryTheory.Limits.BinaryBicone.toCocone.{u1, u2} C _inst_1 _inst_2 P Q c)) (CategoryTheory.Discrete.mk.{0} CategoryTheory.Limits.WalkingPair CategoryTheory.Limits.WalkingPair.left)) (CategoryTheory.Limits.BinaryBicone.inl.{u1, u2} C _inst_1 _inst_2 P Q c)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u2} C _inst_1] {P : C} {Q : C} (c : CategoryTheory.Limits.BinaryBicone.{u1, u2} C _inst_1 _inst_2 P Q), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prefunctor.obj.{1, succ u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.CategoryStruct.toQuiver.{0, 0} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.Category.toCategoryStruct.{0, 0} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.pair.{u1, u2} C _inst_1 P Q)) (CategoryTheory.Discrete.mk.{0} CategoryTheory.Limits.WalkingPair CategoryTheory.Limits.WalkingPair.left)) (Prefunctor.obj.{1, succ u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.CategoryStruct.toQuiver.{0, 0} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.Category.toCategoryStruct.{0, 0} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (Prefunctor.obj.{succ u1, succ u1, u2, max u1 u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{u1, max u2 u1} (CategoryTheory.Functor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Category.toCategoryStruct.{u1, max u2 u1} (CategoryTheory.Functor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, max u2 u1} C _inst_1 (CategoryTheory.Functor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.const.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1)) (CategoryTheory.Limits.Cocone.pt.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.pair.{u1, u2} C _inst_1 P Q) (CategoryTheory.Limits.BinaryBicone.toCocone.{u1, u2} C _inst_1 _inst_2 P Q c)))) (CategoryTheory.Discrete.mk.{0} CategoryTheory.Limits.WalkingPair CategoryTheory.Limits.WalkingPair.left))) (CategoryTheory.NatTrans.app.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.pair.{u1, u2} C _inst_1 P Q) (Prefunctor.obj.{succ u1, succ u1, u2, max u1 u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{u1, max u2 u1} (CategoryTheory.Functor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Category.toCategoryStruct.{u1, max u2 u1} (CategoryTheory.Functor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, max u2 u1} C _inst_1 (CategoryTheory.Functor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.const.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1)) (CategoryTheory.Limits.Cocone.pt.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.pair.{u1, u2} C _inst_1 P Q) (CategoryTheory.Limits.BinaryBicone.toCocone.{u1, u2} C _inst_1 _inst_2 P Q c))) (CategoryTheory.Limits.Cocone.ι.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.pair.{u1, u2} C _inst_1 P Q) (CategoryTheory.Limits.BinaryBicone.toCocone.{u1, u2} C _inst_1 _inst_2 P Q c)) (CategoryTheory.Discrete.mk.{0} CategoryTheory.Limits.WalkingPair CategoryTheory.Limits.WalkingPair.left)) (CategoryTheory.Limits.BinaryBicone.inl.{u1, u2} C _inst_1 _inst_2 P Q c)
Case conversion may be inaccurate. Consider using '#align category_theory.limits.binary_bicone.to_cocone_ι_app_left CategoryTheory.Limits.BinaryBicone.toCocone_ι_app_leftₓ'. -/
@[simp]
theorem toCocone_ι_app_left (c : BinaryBicone P Q) : c.toCocone.ι.app ⟨WalkingPair.left⟩ = c.inl :=
  rfl
#align category_theory.limits.binary_bicone.to_cocone_ι_app_left CategoryTheory.Limits.BinaryBicone.toCocone_ι_app_left

/- warning: category_theory.limits.binary_bicone.to_cocone_ι_app_right -> CategoryTheory.Limits.BinaryBicone.toCocone_ι_app_right is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u2} C _inst_1] {P : C} {Q : C} (c : CategoryTheory.Limits.BinaryBicone.{u1, u2} C _inst_1 _inst_2 P Q), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.obj.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.pair.{u1, u2} C _inst_1 P Q) (CategoryTheory.Discrete.mk.{0} CategoryTheory.Limits.WalkingPair CategoryTheory.Limits.WalkingPair.right)) (CategoryTheory.Functor.obj.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Functor.obj.{u1, u1, u2, max u1 u2} C _inst_1 (CategoryTheory.Functor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.const.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Limits.Cocone.pt.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.pair.{u1, u2} C _inst_1 P Q) (CategoryTheory.Limits.BinaryBicone.toCocone.{u1, u2} C _inst_1 _inst_2 P Q c))) (CategoryTheory.Discrete.mk.{0} CategoryTheory.Limits.WalkingPair CategoryTheory.Limits.WalkingPair.right))) (CategoryTheory.NatTrans.app.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.pair.{u1, u2} C _inst_1 P Q) (CategoryTheory.Functor.obj.{u1, u1, u2, max u1 u2} C _inst_1 (CategoryTheory.Functor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.const.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Limits.Cocone.pt.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.pair.{u1, u2} C _inst_1 P Q) (CategoryTheory.Limits.BinaryBicone.toCocone.{u1, u2} C _inst_1 _inst_2 P Q c))) (CategoryTheory.Limits.Cocone.ι.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.pair.{u1, u2} C _inst_1 P Q) (CategoryTheory.Limits.BinaryBicone.toCocone.{u1, u2} C _inst_1 _inst_2 P Q c)) (CategoryTheory.Discrete.mk.{0} CategoryTheory.Limits.WalkingPair CategoryTheory.Limits.WalkingPair.right)) (CategoryTheory.Limits.BinaryBicone.inr.{u1, u2} C _inst_1 _inst_2 P Q c)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u2} C _inst_1] {P : C} {Q : C} (c : CategoryTheory.Limits.BinaryBicone.{u1, u2} C _inst_1 _inst_2 P Q), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prefunctor.obj.{1, succ u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.CategoryStruct.toQuiver.{0, 0} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.Category.toCategoryStruct.{0, 0} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.pair.{u1, u2} C _inst_1 P Q)) (CategoryTheory.Discrete.mk.{0} CategoryTheory.Limits.WalkingPair CategoryTheory.Limits.WalkingPair.right)) (Prefunctor.obj.{1, succ u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.CategoryStruct.toQuiver.{0, 0} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.Category.toCategoryStruct.{0, 0} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (Prefunctor.obj.{succ u1, succ u1, u2, max u1 u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{u1, max u2 u1} (CategoryTheory.Functor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Category.toCategoryStruct.{u1, max u2 u1} (CategoryTheory.Functor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, max u2 u1} C _inst_1 (CategoryTheory.Functor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.const.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1)) (CategoryTheory.Limits.Cocone.pt.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.pair.{u1, u2} C _inst_1 P Q) (CategoryTheory.Limits.BinaryBicone.toCocone.{u1, u2} C _inst_1 _inst_2 P Q c)))) (CategoryTheory.Discrete.mk.{0} CategoryTheory.Limits.WalkingPair CategoryTheory.Limits.WalkingPair.right))) (CategoryTheory.NatTrans.app.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.pair.{u1, u2} C _inst_1 P Q) (Prefunctor.obj.{succ u1, succ u1, u2, max u1 u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{u1, max u2 u1} (CategoryTheory.Functor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Category.toCategoryStruct.{u1, max u2 u1} (CategoryTheory.Functor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, max u2 u1} C _inst_1 (CategoryTheory.Functor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.const.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1)) (CategoryTheory.Limits.Cocone.pt.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.pair.{u1, u2} C _inst_1 P Q) (CategoryTheory.Limits.BinaryBicone.toCocone.{u1, u2} C _inst_1 _inst_2 P Q c))) (CategoryTheory.Limits.Cocone.ι.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.pair.{u1, u2} C _inst_1 P Q) (CategoryTheory.Limits.BinaryBicone.toCocone.{u1, u2} C _inst_1 _inst_2 P Q c)) (CategoryTheory.Discrete.mk.{0} CategoryTheory.Limits.WalkingPair CategoryTheory.Limits.WalkingPair.right)) (CategoryTheory.Limits.BinaryBicone.inr.{u1, u2} C _inst_1 _inst_2 P Q c)
Case conversion may be inaccurate. Consider using '#align category_theory.limits.binary_bicone.to_cocone_ι_app_right CategoryTheory.Limits.BinaryBicone.toCocone_ι_app_rightₓ'. -/
@[simp]
theorem toCocone_ι_app_right (c : BinaryBicone P Q) :
    c.toCocone.ι.app ⟨WalkingPair.right⟩ = c.inr :=
  rfl
#align category_theory.limits.binary_bicone.to_cocone_ι_app_right CategoryTheory.Limits.BinaryBicone.toCocone_ι_app_right

/- warning: category_theory.limits.binary_bicone.binary_cofan_inl_to_cocone -> CategoryTheory.Limits.BinaryBicone.binary_cofan_inl_toCocone is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u2} C _inst_1] {P : C} {Q : C} (c : CategoryTheory.Limits.BinaryBicone.{u1, u2} C _inst_1 _inst_2 P Q), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.obj.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.pair.{u1, u2} C _inst_1 P Q) (CategoryTheory.Discrete.mk.{0} CategoryTheory.Limits.WalkingPair CategoryTheory.Limits.WalkingPair.left)) (CategoryTheory.Functor.obj.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Functor.obj.{u1, u1, u2, max u1 u2} C _inst_1 (CategoryTheory.Functor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.const.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Limits.Cocone.pt.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.pair.{u1, u2} C _inst_1 P Q) (CategoryTheory.Limits.BinaryBicone.toCocone.{u1, u2} C _inst_1 _inst_2 P Q c))) (CategoryTheory.Discrete.mk.{0} CategoryTheory.Limits.WalkingPair CategoryTheory.Limits.WalkingPair.left))) (CategoryTheory.Limits.BinaryCofan.inl.{u1, u2} C _inst_1 P Q (CategoryTheory.Limits.BinaryBicone.toCocone.{u1, u2} C _inst_1 _inst_2 P Q c)) (CategoryTheory.Limits.BinaryBicone.inl.{u1, u2} C _inst_1 _inst_2 P Q c)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u2} C _inst_1] {P : C} {Q : C} (c : CategoryTheory.Limits.BinaryBicone.{u1, u2} C _inst_1 _inst_2 P Q), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prefunctor.obj.{1, succ u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.CategoryStruct.toQuiver.{0, 0} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.Category.toCategoryStruct.{0, 0} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.pair.{u1, u2} C _inst_1 P Q)) (CategoryTheory.Discrete.mk.{0} CategoryTheory.Limits.WalkingPair CategoryTheory.Limits.WalkingPair.left)) (Prefunctor.obj.{1, succ u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.CategoryStruct.toQuiver.{0, 0} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.Category.toCategoryStruct.{0, 0} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (Prefunctor.obj.{succ u1, succ u1, u2, max u1 u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{u1, max u2 u1} (CategoryTheory.Functor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Category.toCategoryStruct.{u1, max u2 u1} (CategoryTheory.Functor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, max u2 u1} C _inst_1 (CategoryTheory.Functor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.const.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1)) (CategoryTheory.Limits.Cocone.pt.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.pair.{u1, u2} C _inst_1 P Q) (CategoryTheory.Limits.BinaryBicone.toCocone.{u1, u2} C _inst_1 _inst_2 P Q c)))) (CategoryTheory.Discrete.mk.{0} CategoryTheory.Limits.WalkingPair CategoryTheory.Limits.WalkingPair.left))) (CategoryTheory.Limits.BinaryCofan.inl.{u1, u2} C _inst_1 P Q (CategoryTheory.Limits.BinaryBicone.toCocone.{u1, u2} C _inst_1 _inst_2 P Q c)) (CategoryTheory.Limits.BinaryBicone.inl.{u1, u2} C _inst_1 _inst_2 P Q c)
Case conversion may be inaccurate. Consider using '#align category_theory.limits.binary_bicone.binary_cofan_inl_to_cocone CategoryTheory.Limits.BinaryBicone.binary_cofan_inl_toCoconeₓ'. -/
@[simp]
theorem binary_cofan_inl_toCocone (c : BinaryBicone P Q) : BinaryCofan.inl c.toCocone = c.inl :=
  rfl
#align category_theory.limits.binary_bicone.binary_cofan_inl_to_cocone CategoryTheory.Limits.BinaryBicone.binary_cofan_inl_toCocone

/- warning: category_theory.limits.binary_bicone.binary_cofan_inr_to_cocone -> CategoryTheory.Limits.BinaryBicone.binary_cofan_inr_toCocone is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u2} C _inst_1] {P : C} {Q : C} (c : CategoryTheory.Limits.BinaryBicone.{u1, u2} C _inst_1 _inst_2 P Q), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.obj.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.pair.{u1, u2} C _inst_1 P Q) (CategoryTheory.Discrete.mk.{0} CategoryTheory.Limits.WalkingPair CategoryTheory.Limits.WalkingPair.right)) (CategoryTheory.Functor.obj.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Functor.obj.{u1, u1, u2, max u1 u2} C _inst_1 (CategoryTheory.Functor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.const.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Limits.Cocone.pt.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.pair.{u1, u2} C _inst_1 P Q) (CategoryTheory.Limits.BinaryBicone.toCocone.{u1, u2} C _inst_1 _inst_2 P Q c))) (CategoryTheory.Discrete.mk.{0} CategoryTheory.Limits.WalkingPair CategoryTheory.Limits.WalkingPair.right))) (CategoryTheory.Limits.BinaryCofan.inr.{u1, u2} C _inst_1 P Q (CategoryTheory.Limits.BinaryBicone.toCocone.{u1, u2} C _inst_1 _inst_2 P Q c)) (CategoryTheory.Limits.BinaryBicone.inr.{u1, u2} C _inst_1 _inst_2 P Q c)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u2} C _inst_1] {P : C} {Q : C} (c : CategoryTheory.Limits.BinaryBicone.{u1, u2} C _inst_1 _inst_2 P Q), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prefunctor.obj.{1, succ u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.CategoryStruct.toQuiver.{0, 0} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.Category.toCategoryStruct.{0, 0} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.pair.{u1, u2} C _inst_1 P Q)) (CategoryTheory.Discrete.mk.{0} CategoryTheory.Limits.WalkingPair CategoryTheory.Limits.WalkingPair.right)) (Prefunctor.obj.{1, succ u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.CategoryStruct.toQuiver.{0, 0} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.Category.toCategoryStruct.{0, 0} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (Prefunctor.obj.{succ u1, succ u1, u2, max u1 u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{u1, max u2 u1} (CategoryTheory.Functor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Category.toCategoryStruct.{u1, max u2 u1} (CategoryTheory.Functor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, max u2 u1} C _inst_1 (CategoryTheory.Functor.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.const.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1)) (CategoryTheory.Limits.Cocone.pt.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.pair.{u1, u2} C _inst_1 P Q) (CategoryTheory.Limits.BinaryBicone.toCocone.{u1, u2} C _inst_1 _inst_2 P Q c)))) (CategoryTheory.Discrete.mk.{0} CategoryTheory.Limits.WalkingPair CategoryTheory.Limits.WalkingPair.right))) (CategoryTheory.Limits.BinaryCofan.inr.{u1, u2} C _inst_1 P Q (CategoryTheory.Limits.BinaryBicone.toCocone.{u1, u2} C _inst_1 _inst_2 P Q c)) (CategoryTheory.Limits.BinaryBicone.inr.{u1, u2} C _inst_1 _inst_2 P Q c)
Case conversion may be inaccurate. Consider using '#align category_theory.limits.binary_bicone.binary_cofan_inr_to_cocone CategoryTheory.Limits.BinaryBicone.binary_cofan_inr_toCoconeₓ'. -/
@[simp]
theorem binary_cofan_inr_toCocone (c : BinaryBicone P Q) : BinaryCofan.inr c.toCocone = c.inr :=
  rfl
#align category_theory.limits.binary_bicone.binary_cofan_inr_to_cocone CategoryTheory.Limits.BinaryBicone.binary_cofan_inr_toCocone

instance (c : BinaryBicone P Q) : IsSplitMono c.inl :=
  IsSplitMono.mk'
    { retraction := c.fst
      id' := c.inl_fst }

instance (c : BinaryBicone P Q) : IsSplitMono c.inr :=
  IsSplitMono.mk'
    { retraction := c.snd
      id' := c.inr_snd }

instance (c : BinaryBicone P Q) : IsSplitEpi c.fst :=
  IsSplitEpi.mk'
    { section_ := c.inl
      id' := c.inl_fst }

instance (c : BinaryBicone P Q) : IsSplitEpi c.snd :=
  IsSplitEpi.mk'
    { section_ := c.inr
      id' := c.inr_snd }

#print CategoryTheory.Limits.BinaryBicone.toBicone /-
/-- Convert a `binary_bicone` into a `bicone` over a pair. -/
@[simps]
def toBicone {X Y : C} (b : BinaryBicone X Y) : Bicone (pairFunction X Y)
    where
  pt := b.pt
  π j := WalkingPair.casesOn j b.fst b.snd
  ι j := WalkingPair.casesOn j b.inl b.inr
  ι_π j j' := by
    rcases j with ⟨⟩ <;> rcases j' with ⟨⟩
    tidy
#align category_theory.limits.binary_bicone.to_bicone CategoryTheory.Limits.BinaryBicone.toBicone
-/

#print CategoryTheory.Limits.BinaryBicone.toBiconeIsLimit /-
/-- A binary bicone is a limit cone if and only if the corresponding bicone is a limit cone. -/
def toBiconeIsLimit {X Y : C} (b : BinaryBicone X Y) :
    IsLimit b.toBicone.toCone ≃ IsLimit b.toCone :=
  IsLimit.equivIsoLimit <|
    Cones.ext (Iso.refl _) fun j => by
      cases j
      tidy
#align category_theory.limits.binary_bicone.to_bicone_is_limit CategoryTheory.Limits.BinaryBicone.toBiconeIsLimit
-/

#print CategoryTheory.Limits.BinaryBicone.toBiconeIsColimit /-
/-- A binary bicone is a colimit cocone if and only if the corresponding bicone is a colimit
    cocone. -/
def toBiconeIsColimit {X Y : C} (b : BinaryBicone X Y) :
    IsColimit b.toBicone.toCocone ≃ IsColimit b.toCocone :=
  IsColimit.equivIsoColimit <|
    Cocones.ext (Iso.refl _) fun j => by
      cases j
      tidy
#align category_theory.limits.binary_bicone.to_bicone_is_colimit CategoryTheory.Limits.BinaryBicone.toBiconeIsColimit
-/

end BinaryBicone

namespace Bicone

#print CategoryTheory.Limits.Bicone.toBinaryBicone /-
/-- Convert a `bicone` over a function on `walking_pair` to a binary_bicone. -/
@[simps]
def toBinaryBicone {X Y : C} (b : Bicone (pairFunction X Y)) : BinaryBicone X Y
    where
  pt := b.pt
  fst := b.π WalkingPair.left
  snd := b.π WalkingPair.right
  inl := b.ι WalkingPair.left
  inr := b.ι WalkingPair.right
  inl_fst := by
    simp [bicone.ι_π]
    rfl
  inr_fst := by simp [bicone.ι_π]
  inl_snd := by simp [bicone.ι_π]
  inr_snd := by
    simp [bicone.ι_π]
    rfl
#align category_theory.limits.bicone.to_binary_bicone CategoryTheory.Limits.Bicone.toBinaryBicone
-/

#print CategoryTheory.Limits.Bicone.toBinaryBiconeIsLimit /-
/-- A bicone over a pair is a limit cone if and only if the corresponding binary bicone is a limit
    cone.  -/
def toBinaryBiconeIsLimit {X Y : C} (b : Bicone (pairFunction X Y)) :
    IsLimit b.toBinaryBicone.toCone ≃ IsLimit b.toCone :=
  IsLimit.equivIsoLimit <| Cones.ext (Iso.refl _) fun j => by rcases j with ⟨⟨⟩⟩ <;> tidy
#align category_theory.limits.bicone.to_binary_bicone_is_limit CategoryTheory.Limits.Bicone.toBinaryBiconeIsLimit
-/

#print CategoryTheory.Limits.Bicone.toBinaryBiconeIsColimit /-
/-- A bicone over a pair is a colimit cocone if and only if the corresponding binary bicone is a
    colimit cocone. -/
def toBinaryBiconeIsColimit {X Y : C} (b : Bicone (pairFunction X Y)) :
    IsColimit b.toBinaryBicone.toCocone ≃ IsColimit b.toCocone :=
  IsColimit.equivIsoColimit <| Cocones.ext (Iso.refl _) fun j => by rcases j with ⟨⟨⟩⟩ <;> tidy
#align category_theory.limits.bicone.to_binary_bicone_is_colimit CategoryTheory.Limits.Bicone.toBinaryBiconeIsColimit
-/

end Bicone

#print CategoryTheory.Limits.BinaryBicone.IsBilimit /-
/-- Structure witnessing that a binary bicone is a limit cone and a limit cocone. -/
@[nolint has_nonempty_instance]
structure BinaryBicone.IsBilimit {P Q : C} (b : BinaryBicone P Q) where
  IsLimit : IsLimit b.toCone
  IsColimit : IsColimit b.toCocone
#align category_theory.limits.binary_bicone.is_bilimit CategoryTheory.Limits.BinaryBicone.IsBilimit
-/

#print CategoryTheory.Limits.BinaryBicone.toBiconeIsBilimit /-
/-- A binary bicone is a bilimit bicone if and only if the corresponding bicone is a bilimit. -/
def BinaryBicone.toBiconeIsBilimit {X Y : C} (b : BinaryBicone X Y) :
    b.toBicone.IsBilimit ≃ b.IsBilimit
    where
  toFun h := ⟨b.toBiconeIsLimit h.IsLimit, b.toBiconeIsColimit h.IsColimit⟩
  invFun h := ⟨b.toBiconeIsLimit.symm h.IsLimit, b.toBiconeIsColimit.symm h.IsColimit⟩
  left_inv := fun ⟨h, h'⟩ => by
    dsimp only
    simp
  right_inv := fun ⟨h, h'⟩ => by
    dsimp only
    simp
#align category_theory.limits.binary_bicone.to_bicone_is_bilimit CategoryTheory.Limits.BinaryBicone.toBiconeIsBilimit
-/

#print CategoryTheory.Limits.Bicone.toBinaryBiconeIsBilimit /-
/-- A bicone over a pair is a bilimit bicone if and only if the corresponding binary bicone is a
    bilimit. -/
def Bicone.toBinaryBiconeIsBilimit {X Y : C} (b : Bicone (pairFunction X Y)) :
    b.toBinaryBicone.IsBilimit ≃ b.IsBilimit
    where
  toFun h := ⟨b.toBinaryBiconeIsLimit h.IsLimit, b.toBinaryBiconeIsColimit h.IsColimit⟩
  invFun h := ⟨b.toBinaryBiconeIsLimit.symm h.IsLimit, b.toBinaryBiconeIsColimit.symm h.IsColimit⟩
  left_inv := fun ⟨h, h'⟩ => by
    dsimp only
    simp
  right_inv := fun ⟨h, h'⟩ => by
    dsimp only
    simp
#align category_theory.limits.bicone.to_binary_bicone_is_bilimit CategoryTheory.Limits.Bicone.toBinaryBiconeIsBilimit
-/

#print CategoryTheory.Limits.BinaryBiproductData /-
/-- A bicone over `P Q : C`, which is both a limit cone and a colimit cocone.
-/
@[nolint has_nonempty_instance]
structure BinaryBiproductData (P Q : C) where
  Bicone : BinaryBicone P Q
  IsBilimit : bicone.IsBilimit
#align category_theory.limits.binary_biproduct_data CategoryTheory.Limits.BinaryBiproductData
-/

#print CategoryTheory.Limits.HasBinaryBiproduct /-
/-- `has_binary_biproduct P Q` expresses the mere existence of a bicone which is
simultaneously a limit and a colimit of the diagram `pair P Q`.
-/
class HasBinaryBiproduct (P Q : C) : Prop where mk' ::
  exists_binary_biproduct : Nonempty (BinaryBiproductData P Q)
#align category_theory.limits.has_binary_biproduct CategoryTheory.Limits.HasBinaryBiproduct
-/

#print CategoryTheory.Limits.HasBinaryBiproduct.mk /-
theorem HasBinaryBiproduct.mk {P Q : C} (d : BinaryBiproductData P Q) : HasBinaryBiproduct P Q :=
  ⟨Nonempty.intro d⟩
#align category_theory.limits.has_binary_biproduct.mk CategoryTheory.Limits.HasBinaryBiproduct.mk
-/

#print CategoryTheory.Limits.getBinaryBiproductData /-
/--
Use the axiom of choice to extract explicit `binary_biproduct_data F` from `has_binary_biproduct F`.
-/
def getBinaryBiproductData (P Q : C) [HasBinaryBiproduct P Q] : BinaryBiproductData P Q :=
  Classical.choice HasBinaryBiproduct.exists_binary_biproduct
#align category_theory.limits.get_binary_biproduct_data CategoryTheory.Limits.getBinaryBiproductData
-/

#print CategoryTheory.Limits.BinaryBiproduct.bicone /-
/-- A bicone for `P Q ` which is both a limit cone and a colimit cocone. -/
def BinaryBiproduct.bicone (P Q : C) [HasBinaryBiproduct P Q] : BinaryBicone P Q :=
  (getBinaryBiproductData P Q).Bicone
#align category_theory.limits.binary_biproduct.bicone CategoryTheory.Limits.BinaryBiproduct.bicone
-/

#print CategoryTheory.Limits.BinaryBiproduct.isBilimit /-
/-- `binary_biproduct.bicone P Q` is a limit bicone. -/
def BinaryBiproduct.isBilimit (P Q : C) [HasBinaryBiproduct P Q] :
    (BinaryBiproduct.bicone P Q).IsBilimit :=
  (getBinaryBiproductData P Q).IsBilimit
#align category_theory.limits.binary_biproduct.is_bilimit CategoryTheory.Limits.BinaryBiproduct.isBilimit
-/

#print CategoryTheory.Limits.BinaryBiproduct.isLimit /-
/-- `binary_biproduct.bicone P Q` is a limit cone. -/
def BinaryBiproduct.isLimit (P Q : C) [HasBinaryBiproduct P Q] :
    IsLimit (BinaryBiproduct.bicone P Q).toCone :=
  (getBinaryBiproductData P Q).IsBilimit.IsLimit
#align category_theory.limits.binary_biproduct.is_limit CategoryTheory.Limits.BinaryBiproduct.isLimit
-/

#print CategoryTheory.Limits.BinaryBiproduct.isColimit /-
/-- `binary_biproduct.bicone P Q` is a colimit cocone. -/
def BinaryBiproduct.isColimit (P Q : C) [HasBinaryBiproduct P Q] :
    IsColimit (BinaryBiproduct.bicone P Q).toCocone :=
  (getBinaryBiproductData P Q).IsBilimit.IsColimit
#align category_theory.limits.binary_biproduct.is_colimit CategoryTheory.Limits.BinaryBiproduct.isColimit
-/

section

variable (C)

#print CategoryTheory.Limits.HasBinaryBiproducts /-
/-- `has_binary_biproducts C` represents the existence of a bicone which is
simultaneously a limit and a colimit of the diagram `pair P Q`, for every `P Q : C`.
-/
class HasBinaryBiproducts : Prop where
  HasBinaryBiproduct : ∀ P Q : C, HasBinaryBiproduct P Q
#align category_theory.limits.has_binary_biproducts CategoryTheory.Limits.HasBinaryBiproducts
-/

attribute [instance] has_binary_biproducts.has_binary_biproduct

#print CategoryTheory.Limits.hasBinaryBiproducts_of_finite_biproducts /-
/-- A category with finite biproducts has binary biproducts.

This is not an instance as typically in concrete categories there will be
an alternative construction with nicer definitional properties.
-/
theorem hasBinaryBiproducts_of_finite_biproducts [HasFiniteBiproducts C] : HasBinaryBiproducts C :=
  {
    HasBinaryBiproduct := fun P Q =>
      HasBinaryBiproduct.mk
        { Bicone := (biproduct.bicone (pairFunction P Q)).toBinaryBicone
          IsBilimit := (Bicone.toBinaryBiconeIsBilimit _).symm (biproduct.isBilimit _) } }
#align category_theory.limits.has_binary_biproducts_of_finite_biproducts CategoryTheory.Limits.hasBinaryBiproducts_of_finite_biproducts
-/

end

variable {P Q : C}

#print CategoryTheory.Limits.HasBinaryBiproduct.hasLimit_pair /-
instance HasBinaryBiproduct.hasLimit_pair [HasBinaryBiproduct P Q] : HasLimit (pair P Q) :=
  HasLimit.mk ⟨_, BinaryBiproduct.isLimit P Q⟩
#align category_theory.limits.has_binary_biproduct.has_limit_pair CategoryTheory.Limits.HasBinaryBiproduct.hasLimit_pair
-/

#print CategoryTheory.Limits.HasBinaryBiproduct.hasColimit_pair /-
instance HasBinaryBiproduct.hasColimit_pair [HasBinaryBiproduct P Q] : HasColimit (pair P Q) :=
  HasColimit.mk ⟨_, BinaryBiproduct.isColimit P Q⟩
#align category_theory.limits.has_binary_biproduct.has_colimit_pair CategoryTheory.Limits.HasBinaryBiproduct.hasColimit_pair
-/

#print CategoryTheory.Limits.hasBinaryProducts_of_hasBinaryBiproducts /-
instance (priority := 100) hasBinaryProducts_of_hasBinaryBiproducts [HasBinaryBiproducts C] :
    HasBinaryProducts C where HasLimit F := hasLimitOfIso (diagramIsoPair F).symm
#align category_theory.limits.has_binary_products_of_has_binary_biproducts CategoryTheory.Limits.hasBinaryProducts_of_hasBinaryBiproducts
-/

#print CategoryTheory.Limits.hasBinaryCoproducts_of_hasBinaryBiproducts /-
instance (priority := 100) hasBinaryCoproducts_of_hasBinaryBiproducts [HasBinaryBiproducts C] :
    HasBinaryCoproducts C where HasColimit F := hasColimitOfIso (diagramIsoPair F)
#align category_theory.limits.has_binary_coproducts_of_has_binary_biproducts CategoryTheory.Limits.hasBinaryCoproducts_of_hasBinaryBiproducts
-/

#print CategoryTheory.Limits.biprodIso /-
/-- The isomorphism between the specified binary product and the specified binary coproduct for
a pair for a binary biproduct.
-/
def biprodIso (X Y : C) [HasBinaryBiproduct X Y] : Limits.prod X Y ≅ Limits.coprod X Y :=
  (IsLimit.conePointUniqueUpToIso (limit.isLimit _) (BinaryBiproduct.isLimit X Y)).trans <|
    IsColimit.coconePointUniqueUpToIso (BinaryBiproduct.isColimit X Y) (colimit.isColimit _)
#align category_theory.limits.biprod_iso CategoryTheory.Limits.biprodIso
-/

#print CategoryTheory.Limits.biprod /-
/-- An arbitrary choice of biproduct of a pair of objects. -/
abbrev biprod (X Y : C) [HasBinaryBiproduct X Y] :=
  (BinaryBiproduct.bicone X Y).pt
#align category_theory.limits.biprod CategoryTheory.Limits.biprod
-/

-- mathport name: «expr ⊞ »
notation:20 X " ⊞ " Y:20 => biprod X Y

#print CategoryTheory.Limits.biprod.fst /-
/-- The projection onto the first summand of a binary biproduct. -/
abbrev biprod.fst {X Y : C} [HasBinaryBiproduct X Y] : X ⊞ Y ⟶ X :=
  (BinaryBiproduct.bicone X Y).fst
#align category_theory.limits.biprod.fst CategoryTheory.Limits.biprod.fst
-/

#print CategoryTheory.Limits.biprod.snd /-
/-- The projection onto the second summand of a binary biproduct. -/
abbrev biprod.snd {X Y : C} [HasBinaryBiproduct X Y] : X ⊞ Y ⟶ Y :=
  (BinaryBiproduct.bicone X Y).snd
#align category_theory.limits.biprod.snd CategoryTheory.Limits.biprod.snd
-/

#print CategoryTheory.Limits.biprod.inl /-
/-- The inclusion into the first summand of a binary biproduct. -/
abbrev biprod.inl {X Y : C} [HasBinaryBiproduct X Y] : X ⟶ X ⊞ Y :=
  (BinaryBiproduct.bicone X Y).inl
#align category_theory.limits.biprod.inl CategoryTheory.Limits.biprod.inl
-/

#print CategoryTheory.Limits.biprod.inr /-
/-- The inclusion into the second summand of a binary biproduct. -/
abbrev biprod.inr {X Y : C} [HasBinaryBiproduct X Y] : Y ⟶ X ⊞ Y :=
  (BinaryBiproduct.bicone X Y).inr
#align category_theory.limits.biprod.inr CategoryTheory.Limits.biprod.inr
-/

section

variable {X Y : C} [HasBinaryBiproduct X Y]

#print CategoryTheory.Limits.BinaryBiproduct.bicone_fst /-
@[simp]
theorem BinaryBiproduct.bicone_fst : (BinaryBiproduct.bicone X Y).fst = biprod.fst :=
  rfl
#align category_theory.limits.binary_biproduct.bicone_fst CategoryTheory.Limits.BinaryBiproduct.bicone_fst
-/

#print CategoryTheory.Limits.BinaryBiproduct.bicone_snd /-
@[simp]
theorem BinaryBiproduct.bicone_snd : (BinaryBiproduct.bicone X Y).snd = biprod.snd :=
  rfl
#align category_theory.limits.binary_biproduct.bicone_snd CategoryTheory.Limits.BinaryBiproduct.bicone_snd
-/

#print CategoryTheory.Limits.BinaryBiproduct.bicone_inl /-
@[simp]
theorem BinaryBiproduct.bicone_inl : (BinaryBiproduct.bicone X Y).inl = biprod.inl :=
  rfl
#align category_theory.limits.binary_biproduct.bicone_inl CategoryTheory.Limits.BinaryBiproduct.bicone_inl
-/

#print CategoryTheory.Limits.BinaryBiproduct.bicone_inr /-
@[simp]
theorem BinaryBiproduct.bicone_inr : (BinaryBiproduct.bicone X Y).inr = biprod.inr :=
  rfl
#align category_theory.limits.binary_biproduct.bicone_inr CategoryTheory.Limits.BinaryBiproduct.bicone_inr
-/

end

#print CategoryTheory.Limits.biprod.inl_fst /-
@[simp, reassoc.1]
theorem biprod.inl_fst {X Y : C} [HasBinaryBiproduct X Y] :
    (biprod.inl : X ⟶ X ⊞ Y) ≫ (biprod.fst : X ⊞ Y ⟶ X) = 𝟙 X :=
  (BinaryBiproduct.bicone X Y).inl_fst
#align category_theory.limits.biprod.inl_fst CategoryTheory.Limits.biprod.inl_fst
-/

#print CategoryTheory.Limits.biprod.inl_snd /-
@[simp, reassoc.1]
theorem biprod.inl_snd {X Y : C} [HasBinaryBiproduct X Y] :
    (biprod.inl : X ⟶ X ⊞ Y) ≫ (biprod.snd : X ⊞ Y ⟶ Y) = 0 :=
  (BinaryBiproduct.bicone X Y).inl_snd
#align category_theory.limits.biprod.inl_snd CategoryTheory.Limits.biprod.inl_snd
-/

#print CategoryTheory.Limits.biprod.inr_fst /-
@[simp, reassoc.1]
theorem biprod.inr_fst {X Y : C} [HasBinaryBiproduct X Y] :
    (biprod.inr : Y ⟶ X ⊞ Y) ≫ (biprod.fst : X ⊞ Y ⟶ X) = 0 :=
  (BinaryBiproduct.bicone X Y).inr_fst
#align category_theory.limits.biprod.inr_fst CategoryTheory.Limits.biprod.inr_fst
-/

#print CategoryTheory.Limits.biprod.inr_snd /-
@[simp, reassoc.1]
theorem biprod.inr_snd {X Y : C} [HasBinaryBiproduct X Y] :
    (biprod.inr : Y ⟶ X ⊞ Y) ≫ (biprod.snd : X ⊞ Y ⟶ Y) = 𝟙 Y :=
  (BinaryBiproduct.bicone X Y).inr_snd
#align category_theory.limits.biprod.inr_snd CategoryTheory.Limits.biprod.inr_snd
-/

#print CategoryTheory.Limits.biprod.lift /-
/-- Given a pair of maps into the summands of a binary biproduct,
we obtain a map into the binary biproduct. -/
abbrev biprod.lift {W X Y : C} [HasBinaryBiproduct X Y] (f : W ⟶ X) (g : W ⟶ Y) : W ⟶ X ⊞ Y :=
  (BinaryBiproduct.isLimit X Y).lift (BinaryFan.mk f g)
#align category_theory.limits.biprod.lift CategoryTheory.Limits.biprod.lift
-/

#print CategoryTheory.Limits.biprod.desc /-
/-- Given a pair of maps out of the summands of a binary biproduct,
we obtain a map out of the binary biproduct. -/
abbrev biprod.desc {W X Y : C} [HasBinaryBiproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) : X ⊞ Y ⟶ W :=
  (BinaryBiproduct.isColimit X Y).desc (BinaryCofan.mk f g)
#align category_theory.limits.biprod.desc CategoryTheory.Limits.biprod.desc
-/

#print CategoryTheory.Limits.biprod.lift_fst /-
@[simp, reassoc.1]
theorem biprod.lift_fst {W X Y : C} [HasBinaryBiproduct X Y] (f : W ⟶ X) (g : W ⟶ Y) :
    biprod.lift f g ≫ biprod.fst = f :=
  (BinaryBiproduct.isLimit X Y).fac _ ⟨WalkingPair.left⟩
#align category_theory.limits.biprod.lift_fst CategoryTheory.Limits.biprod.lift_fst
-/

#print CategoryTheory.Limits.biprod.lift_snd /-
@[simp, reassoc.1]
theorem biprod.lift_snd {W X Y : C} [HasBinaryBiproduct X Y] (f : W ⟶ X) (g : W ⟶ Y) :
    biprod.lift f g ≫ biprod.snd = g :=
  (BinaryBiproduct.isLimit X Y).fac _ ⟨WalkingPair.right⟩
#align category_theory.limits.biprod.lift_snd CategoryTheory.Limits.biprod.lift_snd
-/

#print CategoryTheory.Limits.biprod.inl_desc /-
@[simp, reassoc.1]
theorem biprod.inl_desc {W X Y : C} [HasBinaryBiproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) :
    biprod.inl ≫ biprod.desc f g = f :=
  (BinaryBiproduct.isColimit X Y).fac _ ⟨WalkingPair.left⟩
#align category_theory.limits.biprod.inl_desc CategoryTheory.Limits.biprod.inl_desc
-/

#print CategoryTheory.Limits.biprod.inr_desc /-
@[simp, reassoc.1]
theorem biprod.inr_desc {W X Y : C} [HasBinaryBiproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) :
    biprod.inr ≫ biprod.desc f g = g :=
  (BinaryBiproduct.isColimit X Y).fac _ ⟨WalkingPair.right⟩
#align category_theory.limits.biprod.inr_desc CategoryTheory.Limits.biprod.inr_desc
-/

#print CategoryTheory.Limits.biprod.mono_lift_of_mono_left /-
instance biprod.mono_lift_of_mono_left {W X Y : C} [HasBinaryBiproduct X Y] (f : W ⟶ X) (g : W ⟶ Y)
    [Mono f] : Mono (biprod.lift f g) :=
  mono_of_mono_fac <| biprod.lift_fst _ _
#align category_theory.limits.biprod.mono_lift_of_mono_left CategoryTheory.Limits.biprod.mono_lift_of_mono_left
-/

#print CategoryTheory.Limits.biprod.mono_lift_of_mono_right /-
instance biprod.mono_lift_of_mono_right {W X Y : C} [HasBinaryBiproduct X Y] (f : W ⟶ X) (g : W ⟶ Y)
    [Mono g] : Mono (biprod.lift f g) :=
  mono_of_mono_fac <| biprod.lift_snd _ _
#align category_theory.limits.biprod.mono_lift_of_mono_right CategoryTheory.Limits.biprod.mono_lift_of_mono_right
-/

#print CategoryTheory.Limits.biprod.epi_desc_of_epi_left /-
instance biprod.epi_desc_of_epi_left {W X Y : C} [HasBinaryBiproduct X Y] (f : X ⟶ W) (g : Y ⟶ W)
    [Epi f] : Epi (biprod.desc f g) :=
  epi_of_epi_fac <| biprod.inl_desc _ _
#align category_theory.limits.biprod.epi_desc_of_epi_left CategoryTheory.Limits.biprod.epi_desc_of_epi_left
-/

#print CategoryTheory.Limits.biprod.epi_desc_of_epi_right /-
instance biprod.epi_desc_of_epi_right {W X Y : C} [HasBinaryBiproduct X Y] (f : X ⟶ W) (g : Y ⟶ W)
    [Epi g] : Epi (biprod.desc f g) :=
  epi_of_epi_fac <| biprod.inr_desc _ _
#align category_theory.limits.biprod.epi_desc_of_epi_right CategoryTheory.Limits.biprod.epi_desc_of_epi_right
-/

#print CategoryTheory.Limits.biprod.map /-
/-- Given a pair of maps between the summands of a pair of binary biproducts,
we obtain a map between the binary biproducts. -/
abbrev biprod.map {W X Y Z : C} [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) : W ⊞ X ⟶ Y ⊞ Z :=
  IsLimit.map (BinaryBiproduct.bicone W X).toCone (BinaryBiproduct.isLimit Y Z)
    (@mapPair _ _ (pair W X) (pair Y Z) f g)
#align category_theory.limits.biprod.map CategoryTheory.Limits.biprod.map
-/

#print CategoryTheory.Limits.biprod.map' /-
/-- An alternative to `biprod.map` constructed via colimits.
This construction only exists in order to show it is equal to `biprod.map`. -/
abbrev biprod.map' {W X Y Z : C} [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) : W ⊞ X ⟶ Y ⊞ Z :=
  IsColimit.map (BinaryBiproduct.isColimit W X) (BinaryBiproduct.bicone Y Z).toCocone
    (@mapPair _ _ (pair W X) (pair Y Z) f g)
#align category_theory.limits.biprod.map' CategoryTheory.Limits.biprod.map'
-/

#print CategoryTheory.Limits.biprod.hom_ext /-
@[ext]
theorem biprod.hom_ext {X Y Z : C} [HasBinaryBiproduct X Y] (f g : Z ⟶ X ⊞ Y)
    (h₀ : f ≫ biprod.fst = g ≫ biprod.fst) (h₁ : f ≫ biprod.snd = g ≫ biprod.snd) : f = g :=
  BinaryFan.IsLimit.hom_ext (BinaryBiproduct.isLimit X Y) h₀ h₁
#align category_theory.limits.biprod.hom_ext CategoryTheory.Limits.biprod.hom_ext
-/

#print CategoryTheory.Limits.biprod.hom_ext' /-
@[ext]
theorem biprod.hom_ext' {X Y Z : C} [HasBinaryBiproduct X Y] (f g : X ⊞ Y ⟶ Z)
    (h₀ : biprod.inl ≫ f = biprod.inl ≫ g) (h₁ : biprod.inr ≫ f = biprod.inr ≫ g) : f = g :=
  BinaryCofan.IsColimit.hom_ext (BinaryBiproduct.isColimit X Y) h₀ h₁
#align category_theory.limits.biprod.hom_ext' CategoryTheory.Limits.biprod.hom_ext'
-/

#print CategoryTheory.Limits.biprod.isoProd /-
/-- The canonical isomorphism between the chosen biproduct and the chosen product. -/
def biprod.isoProd (X Y : C) [HasBinaryBiproduct X Y] : X ⊞ Y ≅ X ⨯ Y :=
  IsLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit X Y) (limit.isLimit _)
#align category_theory.limits.biprod.iso_prod CategoryTheory.Limits.biprod.isoProd
-/

#print CategoryTheory.Limits.biprod.isoProd_hom /-
@[simp]
theorem biprod.isoProd_hom {X Y : C} [HasBinaryBiproduct X Y] :
    (biprod.isoProd X Y).hom = prod.lift biprod.fst biprod.snd := by ext <;> simp [biprod.iso_prod]
#align category_theory.limits.biprod.iso_prod_hom CategoryTheory.Limits.biprod.isoProd_hom
-/

#print CategoryTheory.Limits.biprod.isoProd_inv /-
@[simp]
theorem biprod.isoProd_inv {X Y : C} [HasBinaryBiproduct X Y] :
    (biprod.isoProd X Y).inv = biprod.lift prod.fst prod.snd := by
  apply biprod.hom_ext <;> simp [iso.inv_comp_eq]
#align category_theory.limits.biprod.iso_prod_inv CategoryTheory.Limits.biprod.isoProd_inv
-/

#print CategoryTheory.Limits.biprod.isoCoprod /-
/-- The canonical isomorphism between the chosen biproduct and the chosen coproduct. -/
def biprod.isoCoprod (X Y : C) [HasBinaryBiproduct X Y] : X ⊞ Y ≅ X ⨿ Y :=
  IsColimit.coconePointUniqueUpToIso (BinaryBiproduct.isColimit X Y) (colimit.isColimit _)
#align category_theory.limits.biprod.iso_coprod CategoryTheory.Limits.biprod.isoCoprod
-/

#print CategoryTheory.Limits.biprod.isoCoprod_inv /-
@[simp]
theorem biprod.isoCoprod_inv {X Y : C} [HasBinaryBiproduct X Y] :
    (biprod.isoCoprod X Y).inv = coprod.desc biprod.inl biprod.inr := by
  ext <;> simp [biprod.iso_coprod] <;> rfl
#align category_theory.limits.biprod.iso_coprod_inv CategoryTheory.Limits.biprod.isoCoprod_inv
-/

#print CategoryTheory.Limits.biprod_isoCoprod_hom /-
@[simp]
theorem biprod_isoCoprod_hom {X Y : C} [HasBinaryBiproduct X Y] :
    (biprod.isoCoprod X Y).hom = biprod.desc coprod.inl coprod.inr := by
  apply biprod.hom_ext' <;> simp [← iso.eq_comp_inv]
#align category_theory.limits.biprod_iso_coprod_hom CategoryTheory.Limits.biprod_isoCoprod_hom
-/

#print CategoryTheory.Limits.biprod.map_eq_map' /-
theorem biprod.map_eq_map' {W X Y Z : C} [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z]
    (f : W ⟶ Y) (g : X ⟶ Z) : biprod.map f g = biprod.map' f g :=
  by
  ext
  · simp only [map_pair_left, is_colimit.ι_map, is_limit.map_π, biprod.inl_fst_assoc,
      category.assoc, ← binary_bicone.to_cone_π_app_left, ← binary_biproduct.bicone_fst, ←
      binary_bicone.to_cocone_ι_app_left, ← binary_biproduct.bicone_inl]
    simp
  · simp only [map_pair_left, is_colimit.ι_map, is_limit.map_π, zero_comp, biprod.inl_snd_assoc,
      category.assoc, ← binary_bicone.to_cone_π_app_right, ← binary_biproduct.bicone_snd, ←
      binary_bicone.to_cocone_ι_app_left, ← binary_biproduct.bicone_inl]
    simp
  · simp only [map_pair_right, biprod.inr_fst_assoc, is_colimit.ι_map, is_limit.map_π, zero_comp,
      category.assoc, ← binary_bicone.to_cone_π_app_left, ← binary_biproduct.bicone_fst, ←
      binary_bicone.to_cocone_ι_app_right, ← binary_biproduct.bicone_inr]
    simp
  · simp only [map_pair_right, is_colimit.ι_map, is_limit.map_π, biprod.inr_snd_assoc,
      category.assoc, ← binary_bicone.to_cone_π_app_right, ← binary_biproduct.bicone_snd, ←
      binary_bicone.to_cocone_ι_app_right, ← binary_biproduct.bicone_inr]
    simp
#align category_theory.limits.biprod.map_eq_map' CategoryTheory.Limits.biprod.map_eq_map'
-/

#print CategoryTheory.Limits.biprod.inl_mono /-
instance biprod.inl_mono {X Y : C} [HasBinaryBiproduct X Y] :
    IsSplitMono (biprod.inl : X ⟶ X ⊞ Y) :=
  IsSplitMono.mk' { retraction := biprod.fst }
#align category_theory.limits.biprod.inl_mono CategoryTheory.Limits.biprod.inl_mono
-/

#print CategoryTheory.Limits.biprod.inr_mono /-
instance biprod.inr_mono {X Y : C} [HasBinaryBiproduct X Y] :
    IsSplitMono (biprod.inr : Y ⟶ X ⊞ Y) :=
  IsSplitMono.mk' { retraction := biprod.snd }
#align category_theory.limits.biprod.inr_mono CategoryTheory.Limits.biprod.inr_mono
-/

#print CategoryTheory.Limits.biprod.fst_epi /-
instance biprod.fst_epi {X Y : C} [HasBinaryBiproduct X Y] : IsSplitEpi (biprod.fst : X ⊞ Y ⟶ X) :=
  IsSplitEpi.mk' { section_ := biprod.inl }
#align category_theory.limits.biprod.fst_epi CategoryTheory.Limits.biprod.fst_epi
-/

#print CategoryTheory.Limits.biprod.snd_epi /-
instance biprod.snd_epi {X Y : C} [HasBinaryBiproduct X Y] : IsSplitEpi (biprod.snd : X ⊞ Y ⟶ Y) :=
  IsSplitEpi.mk' { section_ := biprod.inr }
#align category_theory.limits.biprod.snd_epi CategoryTheory.Limits.biprod.snd_epi
-/

#print CategoryTheory.Limits.biprod.map_fst /-
@[simp, reassoc.1]
theorem biprod.map_fst {W X Y Z : C} [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) : biprod.map f g ≫ biprod.fst = biprod.fst ≫ f :=
  IsLimit.map_π _ _ _ (⟨WalkingPair.left⟩ : Discrete WalkingPair)
#align category_theory.limits.biprod.map_fst CategoryTheory.Limits.biprod.map_fst
-/

#print CategoryTheory.Limits.biprod.map_snd /-
@[simp, reassoc.1]
theorem biprod.map_snd {W X Y Z : C} [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) : biprod.map f g ≫ biprod.snd = biprod.snd ≫ g :=
  IsLimit.map_π _ _ _ (⟨WalkingPair.right⟩ : Discrete WalkingPair)
#align category_theory.limits.biprod.map_snd CategoryTheory.Limits.biprod.map_snd
-/

#print CategoryTheory.Limits.biprod.inl_map /-
-- Because `biprod.map` is defined in terms of `lim` rather than `colim`,
-- we need to provide additional `simp` lemmas.
@[simp, reassoc.1]
theorem biprod.inl_map {W X Y Z : C} [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) : biprod.inl ≫ biprod.map f g = f ≫ biprod.inl :=
  by
  rw [biprod.map_eq_map']
  exact is_colimit.ι_map (binary_biproduct.is_colimit W X) _ _ ⟨walking_pair.left⟩
#align category_theory.limits.biprod.inl_map CategoryTheory.Limits.biprod.inl_map
-/

#print CategoryTheory.Limits.biprod.inr_map /-
@[simp, reassoc.1]
theorem biprod.inr_map {W X Y Z : C} [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) : biprod.inr ≫ biprod.map f g = g ≫ biprod.inr :=
  by
  rw [biprod.map_eq_map']
  exact is_colimit.ι_map (binary_biproduct.is_colimit W X) _ _ ⟨walking_pair.right⟩
#align category_theory.limits.biprod.inr_map CategoryTheory.Limits.biprod.inr_map
-/

#print CategoryTheory.Limits.biprod.mapIso /-
/-- Given a pair of isomorphisms between the summands of a pair of binary biproducts,
we obtain an isomorphism between the binary biproducts. -/
@[simps]
def biprod.mapIso {W X Y Z : C} [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] (f : W ≅ Y)
    (g : X ≅ Z) : W ⊞ X ≅ Y ⊞ Z where
  hom := biprod.map f.hom g.hom
  inv := biprod.map f.inv g.inv
#align category_theory.limits.biprod.map_iso CategoryTheory.Limits.biprod.mapIso
-/

#print CategoryTheory.Limits.biprod.conePointUniqueUpToIso_hom /-
/-- Auxiliary lemma for `biprod.unique_up_to_iso`. -/
theorem biprod.conePointUniqueUpToIso_hom (X Y : C) [HasBinaryBiproduct X Y] {b : BinaryBicone X Y}
    (hb : b.IsBilimit) :
    (hb.IsLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit _ _)).hom =
      biprod.lift b.fst b.snd :=
  rfl
#align category_theory.limits.biprod.cone_point_unique_up_to_iso_hom CategoryTheory.Limits.biprod.conePointUniqueUpToIso_hom
-/

#print CategoryTheory.Limits.biprod.conePointUniqueUpToIso_inv /-
/-- Auxiliary lemma for `biprod.unique_up_to_iso`. -/
theorem biprod.conePointUniqueUpToIso_inv (X Y : C) [HasBinaryBiproduct X Y] {b : BinaryBicone X Y}
    (hb : b.IsBilimit) :
    (hb.IsLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit _ _)).inv =
      biprod.desc b.inl b.inr :=
  by
  refine' biprod.hom_ext' _ _ (hb.is_limit.hom_ext fun j => _) (hb.is_limit.hom_ext fun j => _)
  all_goals
    simp only [category.assoc, is_limit.cone_point_unique_up_to_iso_inv_comp]
    rcases j with ⟨⟨⟩⟩
  all_goals simp
#align category_theory.limits.biprod.cone_point_unique_up_to_iso_inv CategoryTheory.Limits.biprod.conePointUniqueUpToIso_inv
-/

#print CategoryTheory.Limits.biprod.uniqueUpToIso /-
/-- Binary biproducts are unique up to isomorphism. This already follows because bilimits are
    limits, but in the case of biproducts we can give an isomorphism with particularly nice
    definitional properties, namely that `biprod.lift b.fst b.snd` and `biprod.desc b.inl b.inr`
    are inverses of each other. -/
@[simps]
def biprod.uniqueUpToIso (X Y : C) [HasBinaryBiproduct X Y] {b : BinaryBicone X Y}
    (hb : b.IsBilimit) : b.pt ≅ X ⊞ Y
    where
  hom := biprod.lift b.fst b.snd
  inv := biprod.desc b.inl b.inr
  hom_inv_id' := by
    rw [← biprod.cone_point_unique_up_to_iso_hom X Y hb, ←
      biprod.cone_point_unique_up_to_iso_inv X Y hb, iso.hom_inv_id]
  inv_hom_id' := by
    rw [← biprod.cone_point_unique_up_to_iso_hom X Y hb, ←
      biprod.cone_point_unique_up_to_iso_inv X Y hb, iso.inv_hom_id]
#align category_theory.limits.biprod.unique_up_to_iso CategoryTheory.Limits.biprod.uniqueUpToIso
-/

#print CategoryTheory.Limits.biprod.isIso_inl_iff_id_eq_fst_comp_inl /-
-- There are three further variations,
-- about `is_iso biprod.inr`, `is_iso biprod.fst` and `is_iso biprod.snd`,
-- but any one suffices to prove `indecomposable_of_simple`
-- and they are likely not separately useful.
theorem biprod.isIso_inl_iff_id_eq_fst_comp_inl (X Y : C) [HasBinaryBiproduct X Y] :
    IsIso (biprod.inl : X ⟶ X ⊞ Y) ↔ 𝟙 (X ⊞ Y) = biprod.fst ≫ biprod.inl :=
  by
  constructor
  · intro h
    have := (cancel_epi (inv biprod.inl : X ⊞ Y ⟶ X)).2 biprod.inl_fst
    rw [is_iso.inv_hom_id_assoc, category.comp_id] at this
    rw [this, is_iso.inv_hom_id]
  · intro h
    exact ⟨⟨biprod.fst, biprod.inl_fst, h.symm⟩⟩
#align category_theory.limits.biprod.is_iso_inl_iff_id_eq_fst_comp_inl CategoryTheory.Limits.biprod.isIso_inl_iff_id_eq_fst_comp_inl
-/

section BiprodKernel

section BinaryBicone

variable {X Y : C} (c : BinaryBicone X Y)

#print CategoryTheory.Limits.BinaryBicone.fstKernelFork /-
/-- A kernel fork for the kernel of `binary_bicone.fst`. It consists of the morphism
`binary_bicone.inr`. -/
def BinaryBicone.fstKernelFork : KernelFork c.fst :=
  KernelFork.ofι c.inr c.inr_fst
#align category_theory.limits.binary_bicone.fst_kernel_fork CategoryTheory.Limits.BinaryBicone.fstKernelFork
-/

/- warning: category_theory.limits.binary_bicone.fst_kernel_fork_ι -> CategoryTheory.Limits.BinaryBicone.fstKernelFork_ι is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u2} C _inst_1] {X : C} {Y : C} (c : CategoryTheory.Limits.BinaryBicone.{u1, u2} C _inst_1 _inst_2 X Y), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1 (CategoryTheory.Functor.obj.{u1, u1, u2, max u1 u2} C _inst_1 (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Functor.const.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Limits.Cone.pt.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1 (CategoryTheory.Limits.parallelPair.{u1, u2} C _inst_1 (CategoryTheory.Limits.BinaryBicone.x.{u1, u2} C _inst_1 _inst_2 X Y c) X (CategoryTheory.Limits.BinaryBicone.fst.{u1, u2} C _inst_1 _inst_2 X Y c) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.BinaryBicone.x.{u1, u2} C _inst_1 _inst_2 X Y c) X) 0 (OfNat.mk.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.BinaryBicone.x.{u1, u2} C _inst_1 _inst_2 X Y c) X) 0 (Zero.zero.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.BinaryBicone.x.{u1, u2} C _inst_1 _inst_2 X Y c) X) (CategoryTheory.Limits.HasZeroMorphisms.hasZero.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.Limits.BinaryBicone.x.{u1, u2} C _inst_1 _inst_2 X Y c) X))))) (CategoryTheory.Limits.BinaryBicone.fstKernelFork.{u1, u2} C _inst_1 _inst_2 X Y c))) CategoryTheory.Limits.WalkingParallelPair.zero) (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1 (CategoryTheory.Limits.parallelPair.{u1, u2} C _inst_1 (CategoryTheory.Limits.BinaryBicone.x.{u1, u2} C _inst_1 _inst_2 X Y c) X (CategoryTheory.Limits.BinaryBicone.fst.{u1, u2} C _inst_1 _inst_2 X Y c) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.BinaryBicone.x.{u1, u2} C _inst_1 _inst_2 X Y c) X) 0 (OfNat.mk.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.BinaryBicone.x.{u1, u2} C _inst_1 _inst_2 X Y c) X) 0 (Zero.zero.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.BinaryBicone.x.{u1, u2} C _inst_1 _inst_2 X Y c) X) (CategoryTheory.Limits.HasZeroMorphisms.hasZero.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.Limits.BinaryBicone.x.{u1, u2} C _inst_1 _inst_2 X Y c) X))))) CategoryTheory.Limits.WalkingParallelPair.zero)) (CategoryTheory.Limits.Fork.ι.{u1, u2} C _inst_1 (CategoryTheory.Limits.BinaryBicone.x.{u1, u2} C _inst_1 _inst_2 X Y c) X (CategoryTheory.Limits.BinaryBicone.fst.{u1, u2} C _inst_1 _inst_2 X Y c) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.BinaryBicone.x.{u1, u2} C _inst_1 _inst_2 X Y c) X) 0 (OfNat.mk.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.BinaryBicone.x.{u1, u2} C _inst_1 _inst_2 X Y c) X) 0 (Zero.zero.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.BinaryBicone.x.{u1, u2} C _inst_1 _inst_2 X Y c) X) (CategoryTheory.Limits.HasZeroMorphisms.hasZero.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.Limits.BinaryBicone.x.{u1, u2} C _inst_1 _inst_2 X Y c) X)))) (CategoryTheory.Limits.BinaryBicone.fstKernelFork.{u1, u2} C _inst_1 _inst_2 X Y c)) (CategoryTheory.Limits.BinaryBicone.inr.{u1, u2} C _inst_1 _inst_2 X Y c)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u2} C _inst_1] {X : C} {Y : C} (c : CategoryTheory.Limits.BinaryBicone.{u1, u2} C _inst_1 _inst_2 X Y), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingParallelPair (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1 (Prefunctor.obj.{succ u1, succ u1, u2, max u1 u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{u1, max u2 u1} (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Category.toCategoryStruct.{u1, max u2 u1} (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, max u2 u1} C _inst_1 (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Functor.const.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1)) (CategoryTheory.Limits.Cone.pt.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1 (CategoryTheory.Limits.parallelPair.{u1, u2} C _inst_1 (CategoryTheory.Limits.BinaryBicone.pt.{u1, u2} C _inst_1 _inst_2 X Y c) X (CategoryTheory.Limits.BinaryBicone.fst.{u1, u2} C _inst_1 _inst_2 X Y c) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.BinaryBicone.pt.{u1, u2} C _inst_1 _inst_2 X Y c) X) 0 (Zero.toOfNat0.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.BinaryBicone.pt.{u1, u2} C _inst_1 _inst_2 X Y c) X) (CategoryTheory.Limits.HasZeroMorphisms.Zero.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.Limits.BinaryBicone.pt.{u1, u2} C _inst_1 _inst_2 X Y c) X)))) (CategoryTheory.Limits.BinaryBicone.fstKernelFork.{u1, u2} C _inst_1 _inst_2 X Y c)))) CategoryTheory.Limits.WalkingParallelPair.zero) (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingParallelPair (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1 (CategoryTheory.Limits.parallelPair.{u1, u2} C _inst_1 (CategoryTheory.Limits.BinaryBicone.pt.{u1, u2} C _inst_1 _inst_2 X Y c) X (CategoryTheory.Limits.BinaryBicone.fst.{u1, u2} C _inst_1 _inst_2 X Y c) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.BinaryBicone.pt.{u1, u2} C _inst_1 _inst_2 X Y c) X) 0 (Zero.toOfNat0.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.BinaryBicone.pt.{u1, u2} C _inst_1 _inst_2 X Y c) X) (CategoryTheory.Limits.HasZeroMorphisms.Zero.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.Limits.BinaryBicone.pt.{u1, u2} C _inst_1 _inst_2 X Y c) X))))) CategoryTheory.Limits.WalkingParallelPair.zero)) (CategoryTheory.Limits.Fork.ι.{u1, u2} C _inst_1 (CategoryTheory.Limits.BinaryBicone.pt.{u1, u2} C _inst_1 _inst_2 X Y c) X (CategoryTheory.Limits.BinaryBicone.fst.{u1, u2} C _inst_1 _inst_2 X Y c) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.BinaryBicone.pt.{u1, u2} C _inst_1 _inst_2 X Y c) X) 0 (Zero.toOfNat0.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.BinaryBicone.pt.{u1, u2} C _inst_1 _inst_2 X Y c) X) (CategoryTheory.Limits.HasZeroMorphisms.Zero.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.Limits.BinaryBicone.pt.{u1, u2} C _inst_1 _inst_2 X Y c) X))) (CategoryTheory.Limits.BinaryBicone.fstKernelFork.{u1, u2} C _inst_1 _inst_2 X Y c)) (CategoryTheory.Limits.BinaryBicone.inr.{u1, u2} C _inst_1 _inst_2 X Y c)
Case conversion may be inaccurate. Consider using '#align category_theory.limits.binary_bicone.fst_kernel_fork_ι CategoryTheory.Limits.BinaryBicone.fstKernelFork_ιₓ'. -/
@[simp]
theorem BinaryBicone.fstKernelFork_ι : (BinaryBicone.fstKernelFork c).ι = c.inr :=
  rfl
#align category_theory.limits.binary_bicone.fst_kernel_fork_ι CategoryTheory.Limits.BinaryBicone.fstKernelFork_ι

#print CategoryTheory.Limits.BinaryBicone.sndKernelFork /-
/-- A kernel fork for the kernel of `binary_bicone.snd`. It consists of the morphism
`binary_bicone.inl`. -/
def BinaryBicone.sndKernelFork : KernelFork c.snd :=
  KernelFork.ofι c.inl c.inl_snd
#align category_theory.limits.binary_bicone.snd_kernel_fork CategoryTheory.Limits.BinaryBicone.sndKernelFork
-/

/- warning: category_theory.limits.binary_bicone.snd_kernel_fork_ι -> CategoryTheory.Limits.BinaryBicone.sndKernelFork_ι is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u2} C _inst_1] {X : C} {Y : C} (c : CategoryTheory.Limits.BinaryBicone.{u1, u2} C _inst_1 _inst_2 X Y), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1 (CategoryTheory.Functor.obj.{u1, u1, u2, max u1 u2} C _inst_1 (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Functor.const.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Limits.Cone.pt.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1 (CategoryTheory.Limits.parallelPair.{u1, u2} C _inst_1 (CategoryTheory.Limits.BinaryBicone.x.{u1, u2} C _inst_1 _inst_2 X Y c) Y (CategoryTheory.Limits.BinaryBicone.snd.{u1, u2} C _inst_1 _inst_2 X Y c) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.BinaryBicone.x.{u1, u2} C _inst_1 _inst_2 X Y c) Y) 0 (OfNat.mk.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.BinaryBicone.x.{u1, u2} C _inst_1 _inst_2 X Y c) Y) 0 (Zero.zero.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.BinaryBicone.x.{u1, u2} C _inst_1 _inst_2 X Y c) Y) (CategoryTheory.Limits.HasZeroMorphisms.hasZero.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.Limits.BinaryBicone.x.{u1, u2} C _inst_1 _inst_2 X Y c) Y))))) (CategoryTheory.Limits.BinaryBicone.sndKernelFork.{u1, u2} C _inst_1 _inst_2 X Y c))) CategoryTheory.Limits.WalkingParallelPair.zero) (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1 (CategoryTheory.Limits.parallelPair.{u1, u2} C _inst_1 (CategoryTheory.Limits.BinaryBicone.x.{u1, u2} C _inst_1 _inst_2 X Y c) Y (CategoryTheory.Limits.BinaryBicone.snd.{u1, u2} C _inst_1 _inst_2 X Y c) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.BinaryBicone.x.{u1, u2} C _inst_1 _inst_2 X Y c) Y) 0 (OfNat.mk.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.BinaryBicone.x.{u1, u2} C _inst_1 _inst_2 X Y c) Y) 0 (Zero.zero.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.BinaryBicone.x.{u1, u2} C _inst_1 _inst_2 X Y c) Y) (CategoryTheory.Limits.HasZeroMorphisms.hasZero.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.Limits.BinaryBicone.x.{u1, u2} C _inst_1 _inst_2 X Y c) Y))))) CategoryTheory.Limits.WalkingParallelPair.zero)) (CategoryTheory.Limits.Fork.ι.{u1, u2} C _inst_1 (CategoryTheory.Limits.BinaryBicone.x.{u1, u2} C _inst_1 _inst_2 X Y c) Y (CategoryTheory.Limits.BinaryBicone.snd.{u1, u2} C _inst_1 _inst_2 X Y c) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.BinaryBicone.x.{u1, u2} C _inst_1 _inst_2 X Y c) Y) 0 (OfNat.mk.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.BinaryBicone.x.{u1, u2} C _inst_1 _inst_2 X Y c) Y) 0 (Zero.zero.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.BinaryBicone.x.{u1, u2} C _inst_1 _inst_2 X Y c) Y) (CategoryTheory.Limits.HasZeroMorphisms.hasZero.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.Limits.BinaryBicone.x.{u1, u2} C _inst_1 _inst_2 X Y c) Y)))) (CategoryTheory.Limits.BinaryBicone.sndKernelFork.{u1, u2} C _inst_1 _inst_2 X Y c)) (CategoryTheory.Limits.BinaryBicone.inl.{u1, u2} C _inst_1 _inst_2 X Y c)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u2} C _inst_1] {X : C} {Y : C} (c : CategoryTheory.Limits.BinaryBicone.{u1, u2} C _inst_1 _inst_2 X Y), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingParallelPair (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1 (Prefunctor.obj.{succ u1, succ u1, u2, max u1 u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{u1, max u2 u1} (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Category.toCategoryStruct.{u1, max u2 u1} (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, max u2 u1} C _inst_1 (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Functor.const.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1)) (CategoryTheory.Limits.Cone.pt.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1 (CategoryTheory.Limits.parallelPair.{u1, u2} C _inst_1 (CategoryTheory.Limits.BinaryBicone.pt.{u1, u2} C _inst_1 _inst_2 X Y c) Y (CategoryTheory.Limits.BinaryBicone.snd.{u1, u2} C _inst_1 _inst_2 X Y c) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.BinaryBicone.pt.{u1, u2} C _inst_1 _inst_2 X Y c) Y) 0 (Zero.toOfNat0.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.BinaryBicone.pt.{u1, u2} C _inst_1 _inst_2 X Y c) Y) (CategoryTheory.Limits.HasZeroMorphisms.Zero.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.Limits.BinaryBicone.pt.{u1, u2} C _inst_1 _inst_2 X Y c) Y)))) (CategoryTheory.Limits.BinaryBicone.sndKernelFork.{u1, u2} C _inst_1 _inst_2 X Y c)))) CategoryTheory.Limits.WalkingParallelPair.zero) (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingParallelPair (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1 (CategoryTheory.Limits.parallelPair.{u1, u2} C _inst_1 (CategoryTheory.Limits.BinaryBicone.pt.{u1, u2} C _inst_1 _inst_2 X Y c) Y (CategoryTheory.Limits.BinaryBicone.snd.{u1, u2} C _inst_1 _inst_2 X Y c) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.BinaryBicone.pt.{u1, u2} C _inst_1 _inst_2 X Y c) Y) 0 (Zero.toOfNat0.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.BinaryBicone.pt.{u1, u2} C _inst_1 _inst_2 X Y c) Y) (CategoryTheory.Limits.HasZeroMorphisms.Zero.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.Limits.BinaryBicone.pt.{u1, u2} C _inst_1 _inst_2 X Y c) Y))))) CategoryTheory.Limits.WalkingParallelPair.zero)) (CategoryTheory.Limits.Fork.ι.{u1, u2} C _inst_1 (CategoryTheory.Limits.BinaryBicone.pt.{u1, u2} C _inst_1 _inst_2 X Y c) Y (CategoryTheory.Limits.BinaryBicone.snd.{u1, u2} C _inst_1 _inst_2 X Y c) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.BinaryBicone.pt.{u1, u2} C _inst_1 _inst_2 X Y c) Y) 0 (Zero.toOfNat0.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.BinaryBicone.pt.{u1, u2} C _inst_1 _inst_2 X Y c) Y) (CategoryTheory.Limits.HasZeroMorphisms.Zero.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.Limits.BinaryBicone.pt.{u1, u2} C _inst_1 _inst_2 X Y c) Y))) (CategoryTheory.Limits.BinaryBicone.sndKernelFork.{u1, u2} C _inst_1 _inst_2 X Y c)) (CategoryTheory.Limits.BinaryBicone.inl.{u1, u2} C _inst_1 _inst_2 X Y c)
Case conversion may be inaccurate. Consider using '#align category_theory.limits.binary_bicone.snd_kernel_fork_ι CategoryTheory.Limits.BinaryBicone.sndKernelFork_ιₓ'. -/
@[simp]
theorem BinaryBicone.sndKernelFork_ι : (BinaryBicone.sndKernelFork c).ι = c.inl :=
  rfl
#align category_theory.limits.binary_bicone.snd_kernel_fork_ι CategoryTheory.Limits.BinaryBicone.sndKernelFork_ι

#print CategoryTheory.Limits.BinaryBicone.inlCokernelCofork /-
/-- A cokernel cofork for the cokernel of `binary_bicone.inl`. It consists of the morphism
`binary_bicone.snd`. -/
def BinaryBicone.inlCokernelCofork : CokernelCofork c.inl :=
  CokernelCofork.ofπ c.snd c.inl_snd
#align category_theory.limits.binary_bicone.inl_cokernel_cofork CategoryTheory.Limits.BinaryBicone.inlCokernelCofork
-/

/- warning: category_theory.limits.binary_bicone.inl_cokernel_cofork_π -> CategoryTheory.Limits.BinaryBicone.inlCokernelCofork_π is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u2} C _inst_1] {X : C} {Y : C} (c : CategoryTheory.Limits.BinaryBicone.{u1, u2} C _inst_1 _inst_2 X Y), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1 (CategoryTheory.Limits.parallelPair.{u1, u2} C _inst_1 X (CategoryTheory.Limits.BinaryBicone.x.{u1, u2} C _inst_1 _inst_2 X Y c) (CategoryTheory.Limits.BinaryBicone.inl.{u1, u2} C _inst_1 _inst_2 X Y c) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X (CategoryTheory.Limits.BinaryBicone.x.{u1, u2} C _inst_1 _inst_2 X Y c)) 0 (OfNat.mk.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X (CategoryTheory.Limits.BinaryBicone.x.{u1, u2} C _inst_1 _inst_2 X Y c)) 0 (Zero.zero.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X (CategoryTheory.Limits.BinaryBicone.x.{u1, u2} C _inst_1 _inst_2 X Y c)) (CategoryTheory.Limits.HasZeroMorphisms.hasZero.{u1, u2} C _inst_1 _inst_2 X (CategoryTheory.Limits.BinaryBicone.x.{u1, u2} C _inst_1 _inst_2 X Y c)))))) CategoryTheory.Limits.WalkingParallelPair.one) (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1 (CategoryTheory.Functor.obj.{u1, u1, u2, max u1 u2} C _inst_1 (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Functor.const.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Limits.Cocone.pt.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1 (CategoryTheory.Limits.parallelPair.{u1, u2} C _inst_1 X (CategoryTheory.Limits.BinaryBicone.x.{u1, u2} C _inst_1 _inst_2 X Y c) (CategoryTheory.Limits.BinaryBicone.inl.{u1, u2} C _inst_1 _inst_2 X Y c) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X (CategoryTheory.Limits.BinaryBicone.x.{u1, u2} C _inst_1 _inst_2 X Y c)) 0 (OfNat.mk.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X (CategoryTheory.Limits.BinaryBicone.x.{u1, u2} C _inst_1 _inst_2 X Y c)) 0 (Zero.zero.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X (CategoryTheory.Limits.BinaryBicone.x.{u1, u2} C _inst_1 _inst_2 X Y c)) (CategoryTheory.Limits.HasZeroMorphisms.hasZero.{u1, u2} C _inst_1 _inst_2 X (CategoryTheory.Limits.BinaryBicone.x.{u1, u2} C _inst_1 _inst_2 X Y c)))))) (CategoryTheory.Limits.BinaryBicone.inlCokernelCofork.{u1, u2} C _inst_1 _inst_2 X Y c))) CategoryTheory.Limits.WalkingParallelPair.one)) (CategoryTheory.Limits.Cofork.π.{u1, u2} C _inst_1 X (CategoryTheory.Limits.BinaryBicone.x.{u1, u2} C _inst_1 _inst_2 X Y c) (CategoryTheory.Limits.BinaryBicone.inl.{u1, u2} C _inst_1 _inst_2 X Y c) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X (CategoryTheory.Limits.BinaryBicone.x.{u1, u2} C _inst_1 _inst_2 X Y c)) 0 (OfNat.mk.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X (CategoryTheory.Limits.BinaryBicone.x.{u1, u2} C _inst_1 _inst_2 X Y c)) 0 (Zero.zero.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X (CategoryTheory.Limits.BinaryBicone.x.{u1, u2} C _inst_1 _inst_2 X Y c)) (CategoryTheory.Limits.HasZeroMorphisms.hasZero.{u1, u2} C _inst_1 _inst_2 X (CategoryTheory.Limits.BinaryBicone.x.{u1, u2} C _inst_1 _inst_2 X Y c))))) (CategoryTheory.Limits.BinaryBicone.inlCokernelCofork.{u1, u2} C _inst_1 _inst_2 X Y c)) (CategoryTheory.Limits.BinaryBicone.snd.{u1, u2} C _inst_1 _inst_2 X Y c)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u2} C _inst_1] {X : C} {Y : C} (c : CategoryTheory.Limits.BinaryBicone.{u1, u2} C _inst_1 _inst_2 X Y), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingParallelPair (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1 (CategoryTheory.Limits.parallelPair.{u1, u2} C _inst_1 X (CategoryTheory.Limits.BinaryBicone.pt.{u1, u2} C _inst_1 _inst_2 X Y c) (CategoryTheory.Limits.BinaryBicone.inl.{u1, u2} C _inst_1 _inst_2 X Y c) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X (CategoryTheory.Limits.BinaryBicone.pt.{u1, u2} C _inst_1 _inst_2 X Y c)) 0 (Zero.toOfNat0.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X (CategoryTheory.Limits.BinaryBicone.pt.{u1, u2} C _inst_1 _inst_2 X Y c)) (CategoryTheory.Limits.HasZeroMorphisms.Zero.{u1, u2} C _inst_1 _inst_2 X (CategoryTheory.Limits.BinaryBicone.pt.{u1, u2} C _inst_1 _inst_2 X Y c)))))) CategoryTheory.Limits.WalkingParallelPair.one) (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingParallelPair (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1 (Prefunctor.obj.{succ u1, succ u1, u2, max u1 u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{u1, max u2 u1} (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Category.toCategoryStruct.{u1, max u2 u1} (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, max u2 u1} C _inst_1 (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Functor.const.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1)) (CategoryTheory.Limits.Cocone.pt.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1 (CategoryTheory.Limits.parallelPair.{u1, u2} C _inst_1 X (CategoryTheory.Limits.BinaryBicone.pt.{u1, u2} C _inst_1 _inst_2 X Y c) (CategoryTheory.Limits.BinaryBicone.inl.{u1, u2} C _inst_1 _inst_2 X Y c) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X (CategoryTheory.Limits.BinaryBicone.pt.{u1, u2} C _inst_1 _inst_2 X Y c)) 0 (Zero.toOfNat0.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X (CategoryTheory.Limits.BinaryBicone.pt.{u1, u2} C _inst_1 _inst_2 X Y c)) (CategoryTheory.Limits.HasZeroMorphisms.Zero.{u1, u2} C _inst_1 _inst_2 X (CategoryTheory.Limits.BinaryBicone.pt.{u1, u2} C _inst_1 _inst_2 X Y c))))) (CategoryTheory.Limits.BinaryBicone.inlCokernelCofork.{u1, u2} C _inst_1 _inst_2 X Y c)))) CategoryTheory.Limits.WalkingParallelPair.one)) (CategoryTheory.Limits.Cofork.π.{u1, u2} C _inst_1 X (CategoryTheory.Limits.BinaryBicone.pt.{u1, u2} C _inst_1 _inst_2 X Y c) (CategoryTheory.Limits.BinaryBicone.inl.{u1, u2} C _inst_1 _inst_2 X Y c) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X (CategoryTheory.Limits.BinaryBicone.pt.{u1, u2} C _inst_1 _inst_2 X Y c)) 0 (Zero.toOfNat0.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X (CategoryTheory.Limits.BinaryBicone.pt.{u1, u2} C _inst_1 _inst_2 X Y c)) (CategoryTheory.Limits.HasZeroMorphisms.Zero.{u1, u2} C _inst_1 _inst_2 X (CategoryTheory.Limits.BinaryBicone.pt.{u1, u2} C _inst_1 _inst_2 X Y c)))) (CategoryTheory.Limits.BinaryBicone.inlCokernelCofork.{u1, u2} C _inst_1 _inst_2 X Y c)) (CategoryTheory.Limits.BinaryBicone.snd.{u1, u2} C _inst_1 _inst_2 X Y c)
Case conversion may be inaccurate. Consider using '#align category_theory.limits.binary_bicone.inl_cokernel_cofork_π CategoryTheory.Limits.BinaryBicone.inlCokernelCofork_πₓ'. -/
@[simp]
theorem BinaryBicone.inlCokernelCofork_π : (BinaryBicone.inlCokernelCofork c).π = c.snd :=
  rfl
#align category_theory.limits.binary_bicone.inl_cokernel_cofork_π CategoryTheory.Limits.BinaryBicone.inlCokernelCofork_π

#print CategoryTheory.Limits.BinaryBicone.inrCokernelCofork /-
/-- A cokernel cofork for the cokernel of `binary_bicone.inr`. It consists of the morphism
`binary_bicone.fst`. -/
def BinaryBicone.inrCokernelCofork : CokernelCofork c.inr :=
  CokernelCofork.ofπ c.fst c.inr_fst
#align category_theory.limits.binary_bicone.inr_cokernel_cofork CategoryTheory.Limits.BinaryBicone.inrCokernelCofork
-/

/- warning: category_theory.limits.binary_bicone.inr_cokernel_cofork_π -> CategoryTheory.Limits.BinaryBicone.inrCokernelCofork_π is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u2} C _inst_1] {X : C} {Y : C} (c : CategoryTheory.Limits.BinaryBicone.{u1, u2} C _inst_1 _inst_2 X Y), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1 (CategoryTheory.Limits.parallelPair.{u1, u2} C _inst_1 Y (CategoryTheory.Limits.BinaryBicone.x.{u1, u2} C _inst_1 _inst_2 X Y c) (CategoryTheory.Limits.BinaryBicone.inr.{u1, u2} C _inst_1 _inst_2 X Y c) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y (CategoryTheory.Limits.BinaryBicone.x.{u1, u2} C _inst_1 _inst_2 X Y c)) 0 (OfNat.mk.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y (CategoryTheory.Limits.BinaryBicone.x.{u1, u2} C _inst_1 _inst_2 X Y c)) 0 (Zero.zero.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y (CategoryTheory.Limits.BinaryBicone.x.{u1, u2} C _inst_1 _inst_2 X Y c)) (CategoryTheory.Limits.HasZeroMorphisms.hasZero.{u1, u2} C _inst_1 _inst_2 Y (CategoryTheory.Limits.BinaryBicone.x.{u1, u2} C _inst_1 _inst_2 X Y c)))))) CategoryTheory.Limits.WalkingParallelPair.one) (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1 (CategoryTheory.Functor.obj.{u1, u1, u2, max u1 u2} C _inst_1 (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Functor.const.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Limits.Cocone.pt.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1 (CategoryTheory.Limits.parallelPair.{u1, u2} C _inst_1 Y (CategoryTheory.Limits.BinaryBicone.x.{u1, u2} C _inst_1 _inst_2 X Y c) (CategoryTheory.Limits.BinaryBicone.inr.{u1, u2} C _inst_1 _inst_2 X Y c) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y (CategoryTheory.Limits.BinaryBicone.x.{u1, u2} C _inst_1 _inst_2 X Y c)) 0 (OfNat.mk.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y (CategoryTheory.Limits.BinaryBicone.x.{u1, u2} C _inst_1 _inst_2 X Y c)) 0 (Zero.zero.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y (CategoryTheory.Limits.BinaryBicone.x.{u1, u2} C _inst_1 _inst_2 X Y c)) (CategoryTheory.Limits.HasZeroMorphisms.hasZero.{u1, u2} C _inst_1 _inst_2 Y (CategoryTheory.Limits.BinaryBicone.x.{u1, u2} C _inst_1 _inst_2 X Y c)))))) (CategoryTheory.Limits.BinaryBicone.inrCokernelCofork.{u1, u2} C _inst_1 _inst_2 X Y c))) CategoryTheory.Limits.WalkingParallelPair.one)) (CategoryTheory.Limits.Cofork.π.{u1, u2} C _inst_1 Y (CategoryTheory.Limits.BinaryBicone.x.{u1, u2} C _inst_1 _inst_2 X Y c) (CategoryTheory.Limits.BinaryBicone.inr.{u1, u2} C _inst_1 _inst_2 X Y c) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y (CategoryTheory.Limits.BinaryBicone.x.{u1, u2} C _inst_1 _inst_2 X Y c)) 0 (OfNat.mk.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y (CategoryTheory.Limits.BinaryBicone.x.{u1, u2} C _inst_1 _inst_2 X Y c)) 0 (Zero.zero.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y (CategoryTheory.Limits.BinaryBicone.x.{u1, u2} C _inst_1 _inst_2 X Y c)) (CategoryTheory.Limits.HasZeroMorphisms.hasZero.{u1, u2} C _inst_1 _inst_2 Y (CategoryTheory.Limits.BinaryBicone.x.{u1, u2} C _inst_1 _inst_2 X Y c))))) (CategoryTheory.Limits.BinaryBicone.inrCokernelCofork.{u1, u2} C _inst_1 _inst_2 X Y c)) (CategoryTheory.Limits.BinaryBicone.fst.{u1, u2} C _inst_1 _inst_2 X Y c)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u2} C _inst_1] {X : C} {Y : C} (c : CategoryTheory.Limits.BinaryBicone.{u1, u2} C _inst_1 _inst_2 X Y), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingParallelPair (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1 (CategoryTheory.Limits.parallelPair.{u1, u2} C _inst_1 Y (CategoryTheory.Limits.BinaryBicone.pt.{u1, u2} C _inst_1 _inst_2 X Y c) (CategoryTheory.Limits.BinaryBicone.inr.{u1, u2} C _inst_1 _inst_2 X Y c) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y (CategoryTheory.Limits.BinaryBicone.pt.{u1, u2} C _inst_1 _inst_2 X Y c)) 0 (Zero.toOfNat0.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y (CategoryTheory.Limits.BinaryBicone.pt.{u1, u2} C _inst_1 _inst_2 X Y c)) (CategoryTheory.Limits.HasZeroMorphisms.Zero.{u1, u2} C _inst_1 _inst_2 Y (CategoryTheory.Limits.BinaryBicone.pt.{u1, u2} C _inst_1 _inst_2 X Y c)))))) CategoryTheory.Limits.WalkingParallelPair.one) (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingParallelPair (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1 (Prefunctor.obj.{succ u1, succ u1, u2, max u1 u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{u1, max u2 u1} (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Category.toCategoryStruct.{u1, max u2 u1} (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, max u2 u1} C _inst_1 (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Functor.const.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1)) (CategoryTheory.Limits.Cocone.pt.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1 (CategoryTheory.Limits.parallelPair.{u1, u2} C _inst_1 Y (CategoryTheory.Limits.BinaryBicone.pt.{u1, u2} C _inst_1 _inst_2 X Y c) (CategoryTheory.Limits.BinaryBicone.inr.{u1, u2} C _inst_1 _inst_2 X Y c) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y (CategoryTheory.Limits.BinaryBicone.pt.{u1, u2} C _inst_1 _inst_2 X Y c)) 0 (Zero.toOfNat0.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y (CategoryTheory.Limits.BinaryBicone.pt.{u1, u2} C _inst_1 _inst_2 X Y c)) (CategoryTheory.Limits.HasZeroMorphisms.Zero.{u1, u2} C _inst_1 _inst_2 Y (CategoryTheory.Limits.BinaryBicone.pt.{u1, u2} C _inst_1 _inst_2 X Y c))))) (CategoryTheory.Limits.BinaryBicone.inrCokernelCofork.{u1, u2} C _inst_1 _inst_2 X Y c)))) CategoryTheory.Limits.WalkingParallelPair.one)) (CategoryTheory.Limits.Cofork.π.{u1, u2} C _inst_1 Y (CategoryTheory.Limits.BinaryBicone.pt.{u1, u2} C _inst_1 _inst_2 X Y c) (CategoryTheory.Limits.BinaryBicone.inr.{u1, u2} C _inst_1 _inst_2 X Y c) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y (CategoryTheory.Limits.BinaryBicone.pt.{u1, u2} C _inst_1 _inst_2 X Y c)) 0 (Zero.toOfNat0.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y (CategoryTheory.Limits.BinaryBicone.pt.{u1, u2} C _inst_1 _inst_2 X Y c)) (CategoryTheory.Limits.HasZeroMorphisms.Zero.{u1, u2} C _inst_1 _inst_2 Y (CategoryTheory.Limits.BinaryBicone.pt.{u1, u2} C _inst_1 _inst_2 X Y c)))) (CategoryTheory.Limits.BinaryBicone.inrCokernelCofork.{u1, u2} C _inst_1 _inst_2 X Y c)) (CategoryTheory.Limits.BinaryBicone.fst.{u1, u2} C _inst_1 _inst_2 X Y c)
Case conversion may be inaccurate. Consider using '#align category_theory.limits.binary_bicone.inr_cokernel_cofork_π CategoryTheory.Limits.BinaryBicone.inrCokernelCofork_πₓ'. -/
@[simp]
theorem BinaryBicone.inrCokernelCofork_π : (BinaryBicone.inrCokernelCofork c).π = c.fst :=
  rfl
#align category_theory.limits.binary_bicone.inr_cokernel_cofork_π CategoryTheory.Limits.BinaryBicone.inrCokernelCofork_π

variable {c}

#print CategoryTheory.Limits.BinaryBicone.isLimitFstKernelFork /-
/-- The fork defined in `binary_bicone.fst_kernel_fork` is indeed a kernel. -/
def BinaryBicone.isLimitFstKernelFork (i : IsLimit c.toCone) : IsLimit c.fstKernelFork :=
  Fork.IsLimit.mk' _ fun s =>
    ⟨s.ι ≫ c.snd, by apply binary_fan.is_limit.hom_ext i <;> simp, fun m hm => by simp [← hm]⟩
#align category_theory.limits.binary_bicone.is_limit_fst_kernel_fork CategoryTheory.Limits.BinaryBicone.isLimitFstKernelFork
-/

#print CategoryTheory.Limits.BinaryBicone.isLimitSndKernelFork /-
/-- The fork defined in `binary_bicone.snd_kernel_fork` is indeed a kernel. -/
def BinaryBicone.isLimitSndKernelFork (i : IsLimit c.toCone) : IsLimit c.sndKernelFork :=
  Fork.IsLimit.mk' _ fun s =>
    ⟨s.ι ≫ c.fst, by apply binary_fan.is_limit.hom_ext i <;> simp, fun m hm => by simp [← hm]⟩
#align category_theory.limits.binary_bicone.is_limit_snd_kernel_fork CategoryTheory.Limits.BinaryBicone.isLimitSndKernelFork
-/

#print CategoryTheory.Limits.BinaryBicone.isColimitInlCokernelCofork /-
/-- The cofork defined in `binary_bicone.inl_cokernel_cofork` is indeed a cokernel. -/
def BinaryBicone.isColimitInlCokernelCofork (i : IsColimit c.toCocone) :
    IsColimit c.inlCokernelCofork :=
  Cofork.IsColimit.mk' _ fun s =>
    ⟨c.inr ≫ s.π, by apply binary_cofan.is_colimit.hom_ext i <;> simp, fun m hm => by simp [← hm]⟩
#align category_theory.limits.binary_bicone.is_colimit_inl_cokernel_cofork CategoryTheory.Limits.BinaryBicone.isColimitInlCokernelCofork
-/

#print CategoryTheory.Limits.BinaryBicone.isColimitInrCokernelCofork /-
/-- The cofork defined in `binary_bicone.inr_cokernel_cofork` is indeed a cokernel. -/
def BinaryBicone.isColimitInrCokernelCofork (i : IsColimit c.toCocone) :
    IsColimit c.inrCokernelCofork :=
  Cofork.IsColimit.mk' _ fun s =>
    ⟨c.inl ≫ s.π, by apply binary_cofan.is_colimit.hom_ext i <;> simp, fun m hm => by simp [← hm]⟩
#align category_theory.limits.binary_bicone.is_colimit_inr_cokernel_cofork CategoryTheory.Limits.BinaryBicone.isColimitInrCokernelCofork
-/

end BinaryBicone

section HasBinaryBiproduct

variable (X Y : C) [HasBinaryBiproduct X Y]

#print CategoryTheory.Limits.biprod.fstKernelFork /-
/-- A kernel fork for the kernel of `biprod.fst`. It consists of the
morphism `biprod.inr`. -/
def biprod.fstKernelFork : KernelFork (biprod.fst : X ⊞ Y ⟶ X) :=
  BinaryBicone.fstKernelFork _
#align category_theory.limits.biprod.fst_kernel_fork CategoryTheory.Limits.biprod.fstKernelFork
-/

/- warning: category_theory.limits.biprod.fst_kernel_fork_ι -> CategoryTheory.Limits.biprod.fstKernelFork_ι is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u2} C _inst_1] (X : C) (Y : C) [_inst_3 : CategoryTheory.Limits.HasBinaryBiproduct.{u1, u2} C _inst_1 _inst_2 X Y], Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1 (CategoryTheory.Functor.obj.{u1, u1, u2, max u1 u2} C _inst_1 (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Functor.const.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Limits.Cone.pt.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1 (CategoryTheory.Limits.parallelPair.{u1, u2} C _inst_1 (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) X (CategoryTheory.Limits.biprod.fst.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) X) 0 (OfNat.mk.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) X) 0 (Zero.zero.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) X) (CategoryTheory.Limits.HasZeroMorphisms.hasZero.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) X))))) (CategoryTheory.Limits.biprod.fstKernelFork.{u1, u2} C _inst_1 _inst_2 X Y _inst_3))) CategoryTheory.Limits.WalkingParallelPair.zero) (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1 (CategoryTheory.Limits.parallelPair.{u1, u2} C _inst_1 (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) X (CategoryTheory.Limits.biprod.fst.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) X) 0 (OfNat.mk.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) X) 0 (Zero.zero.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) X) (CategoryTheory.Limits.HasZeroMorphisms.hasZero.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) X))))) CategoryTheory.Limits.WalkingParallelPair.zero)) (CategoryTheory.Limits.Fork.ι.{u1, u2} C _inst_1 (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) X (CategoryTheory.Limits.biprod.fst.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) X) 0 (OfNat.mk.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) X) 0 (Zero.zero.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) X) (CategoryTheory.Limits.HasZeroMorphisms.hasZero.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) X)))) (CategoryTheory.Limits.biprod.fstKernelFork.{u1, u2} C _inst_1 _inst_2 X Y _inst_3)) (CategoryTheory.Limits.biprod.inr.{u1, u2} C _inst_1 _inst_2 X (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1 (CategoryTheory.Functor.obj.{u1, u1, u2, max u1 u2} C _inst_1 (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Functor.const.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Limits.Cone.pt.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1 (CategoryTheory.Limits.parallelPair.{u1, u2} C _inst_1 (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) X (CategoryTheory.Limits.biprod.fst.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) X) 0 (OfNat.mk.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) X) 0 (Zero.zero.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) X) (CategoryTheory.Limits.HasZeroMorphisms.hasZero.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) X))))) (CategoryTheory.Limits.biprod.fstKernelFork.{u1, u2} C _inst_1 _inst_2 X Y _inst_3))) CategoryTheory.Limits.WalkingParallelPair.zero) _inst_3)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u2} C _inst_1] (X : C) (Y : C) [_inst_3 : CategoryTheory.Limits.HasBinaryBiproduct.{u1, u2} C _inst_1 _inst_2 X Y], Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingParallelPair (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1 (Prefunctor.obj.{succ u1, succ u1, u2, max u1 u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{u1, max u2 u1} (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Category.toCategoryStruct.{u1, max u2 u1} (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, max u2 u1} C _inst_1 (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Functor.const.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1)) (CategoryTheory.Limits.Cone.pt.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1 (CategoryTheory.Limits.parallelPair.{u1, u2} C _inst_1 (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) X (CategoryTheory.Limits.biprod.fst.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) X) 0 (Zero.toOfNat0.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) X) (CategoryTheory.Limits.HasZeroMorphisms.Zero.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) X)))) (CategoryTheory.Limits.biprod.fstKernelFork.{u1, u2} C _inst_1 _inst_2 X Y _inst_3)))) CategoryTheory.Limits.WalkingParallelPair.zero) (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingParallelPair (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1 (CategoryTheory.Limits.parallelPair.{u1, u2} C _inst_1 (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) X (CategoryTheory.Limits.biprod.fst.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) X) 0 (Zero.toOfNat0.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) X) (CategoryTheory.Limits.HasZeroMorphisms.Zero.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) X))))) CategoryTheory.Limits.WalkingParallelPair.zero)) (CategoryTheory.Limits.Fork.ι.{u1, u2} C _inst_1 (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) X (CategoryTheory.Limits.biprod.fst.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) X) 0 (Zero.toOfNat0.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) X) (CategoryTheory.Limits.HasZeroMorphisms.Zero.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) X))) (CategoryTheory.Limits.biprod.fstKernelFork.{u1, u2} C _inst_1 _inst_2 X Y _inst_3)) (CategoryTheory.Limits.biprod.inr.{u1, u2} C _inst_1 _inst_2 X Y _inst_3)
Case conversion may be inaccurate. Consider using '#align category_theory.limits.biprod.fst_kernel_fork_ι CategoryTheory.Limits.biprod.fstKernelFork_ιₓ'. -/
@[simp]
theorem biprod.fstKernelFork_ι : Fork.ι (biprod.fstKernelFork X Y) = biprod.inr :=
  rfl
#align category_theory.limits.biprod.fst_kernel_fork_ι CategoryTheory.Limits.biprod.fstKernelFork_ι

#print CategoryTheory.Limits.biprod.isKernelFstKernelFork /-
/-- The fork `biprod.fst_kernel_fork` is indeed a limit.  -/
def biprod.isKernelFstKernelFork : IsLimit (biprod.fstKernelFork X Y) :=
  BinaryBicone.isLimitFstKernelFork (BinaryBiproduct.isLimit _ _)
#align category_theory.limits.biprod.is_kernel_fst_kernel_fork CategoryTheory.Limits.biprod.isKernelFstKernelFork
-/

#print CategoryTheory.Limits.biprod.sndKernelFork /-
/-- A kernel fork for the kernel of `biprod.snd`. It consists of the
morphism `biprod.inl`. -/
def biprod.sndKernelFork : KernelFork (biprod.snd : X ⊞ Y ⟶ Y) :=
  BinaryBicone.sndKernelFork _
#align category_theory.limits.biprod.snd_kernel_fork CategoryTheory.Limits.biprod.sndKernelFork
-/

/- warning: category_theory.limits.biprod.snd_kernel_fork_ι -> CategoryTheory.Limits.biprod.sndKernelFork_ι is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u2} C _inst_1] (X : C) (Y : C) [_inst_3 : CategoryTheory.Limits.HasBinaryBiproduct.{u1, u2} C _inst_1 _inst_2 X Y], Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1 (CategoryTheory.Functor.obj.{u1, u1, u2, max u1 u2} C _inst_1 (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Functor.const.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Limits.Cone.pt.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1 (CategoryTheory.Limits.parallelPair.{u1, u2} C _inst_1 (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) Y (CategoryTheory.Limits.biprod.snd.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) Y) 0 (OfNat.mk.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) Y) 0 (Zero.zero.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) Y) (CategoryTheory.Limits.HasZeroMorphisms.hasZero.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) Y))))) (CategoryTheory.Limits.biprod.sndKernelFork.{u1, u2} C _inst_1 _inst_2 X Y _inst_3))) CategoryTheory.Limits.WalkingParallelPair.zero) (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1 (CategoryTheory.Limits.parallelPair.{u1, u2} C _inst_1 (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) Y (CategoryTheory.Limits.biprod.snd.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) Y) 0 (OfNat.mk.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) Y) 0 (Zero.zero.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) Y) (CategoryTheory.Limits.HasZeroMorphisms.hasZero.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) Y))))) CategoryTheory.Limits.WalkingParallelPair.zero)) (CategoryTheory.Limits.Fork.ι.{u1, u2} C _inst_1 (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) Y (CategoryTheory.Limits.biprod.snd.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) Y) 0 (OfNat.mk.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) Y) 0 (Zero.zero.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) Y) (CategoryTheory.Limits.HasZeroMorphisms.hasZero.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) Y)))) (CategoryTheory.Limits.biprod.sndKernelFork.{u1, u2} C _inst_1 _inst_2 X Y _inst_3)) (CategoryTheory.Limits.biprod.inl.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1 (CategoryTheory.Functor.obj.{u1, u1, u2, max u1 u2} C _inst_1 (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Functor.const.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Limits.Cone.pt.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1 (CategoryTheory.Limits.parallelPair.{u1, u2} C _inst_1 (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) Y (CategoryTheory.Limits.biprod.snd.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) Y) 0 (OfNat.mk.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) Y) 0 (Zero.zero.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) Y) (CategoryTheory.Limits.HasZeroMorphisms.hasZero.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) Y))))) (CategoryTheory.Limits.biprod.sndKernelFork.{u1, u2} C _inst_1 _inst_2 X Y _inst_3))) CategoryTheory.Limits.WalkingParallelPair.zero) Y _inst_3)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u2} C _inst_1] (X : C) (Y : C) [_inst_3 : CategoryTheory.Limits.HasBinaryBiproduct.{u1, u2} C _inst_1 _inst_2 X Y], Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingParallelPair (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1 (Prefunctor.obj.{succ u1, succ u1, u2, max u1 u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{u1, max u2 u1} (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Category.toCategoryStruct.{u1, max u2 u1} (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, max u2 u1} C _inst_1 (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Functor.const.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1)) (CategoryTheory.Limits.Cone.pt.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1 (CategoryTheory.Limits.parallelPair.{u1, u2} C _inst_1 (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) Y (CategoryTheory.Limits.biprod.snd.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) Y) 0 (Zero.toOfNat0.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) Y) (CategoryTheory.Limits.HasZeroMorphisms.Zero.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) Y)))) (CategoryTheory.Limits.biprod.sndKernelFork.{u1, u2} C _inst_1 _inst_2 X Y _inst_3)))) CategoryTheory.Limits.WalkingParallelPair.zero) (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingParallelPair (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1 (CategoryTheory.Limits.parallelPair.{u1, u2} C _inst_1 (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) Y (CategoryTheory.Limits.biprod.snd.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) Y) 0 (Zero.toOfNat0.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) Y) (CategoryTheory.Limits.HasZeroMorphisms.Zero.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) Y))))) CategoryTheory.Limits.WalkingParallelPair.zero)) (CategoryTheory.Limits.Fork.ι.{u1, u2} C _inst_1 (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) Y (CategoryTheory.Limits.biprod.snd.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) Y) 0 (Zero.toOfNat0.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) Y) (CategoryTheory.Limits.HasZeroMorphisms.Zero.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) Y))) (CategoryTheory.Limits.biprod.sndKernelFork.{u1, u2} C _inst_1 _inst_2 X Y _inst_3)) (CategoryTheory.Limits.biprod.inl.{u1, u2} C _inst_1 _inst_2 X Y _inst_3)
Case conversion may be inaccurate. Consider using '#align category_theory.limits.biprod.snd_kernel_fork_ι CategoryTheory.Limits.biprod.sndKernelFork_ιₓ'. -/
@[simp]
theorem biprod.sndKernelFork_ι : Fork.ι (biprod.sndKernelFork X Y) = biprod.inl :=
  rfl
#align category_theory.limits.biprod.snd_kernel_fork_ι CategoryTheory.Limits.biprod.sndKernelFork_ι

#print CategoryTheory.Limits.biprod.isKernelSndKernelFork /-
/-- The fork `biprod.snd_kernel_fork` is indeed a limit.  -/
def biprod.isKernelSndKernelFork : IsLimit (biprod.sndKernelFork X Y) :=
  BinaryBicone.isLimitSndKernelFork (BinaryBiproduct.isLimit _ _)
#align category_theory.limits.biprod.is_kernel_snd_kernel_fork CategoryTheory.Limits.biprod.isKernelSndKernelFork
-/

#print CategoryTheory.Limits.biprod.inlCokernelCofork /-
/-- A cokernel cofork for the cokernel of `biprod.inl`. It consists of the
morphism `biprod.snd`. -/
def biprod.inlCokernelCofork : CokernelCofork (biprod.inl : X ⟶ X ⊞ Y) :=
  BinaryBicone.inlCokernelCofork _
#align category_theory.limits.biprod.inl_cokernel_cofork CategoryTheory.Limits.biprod.inlCokernelCofork
-/

/- warning: category_theory.limits.biprod.inl_cokernel_cofork_π -> CategoryTheory.Limits.biprod.inlCokernelCofork_π is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u2} C _inst_1] (X : C) (Y : C) [_inst_3 : CategoryTheory.Limits.HasBinaryBiproduct.{u1, u2} C _inst_1 _inst_2 X Y], Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1 (CategoryTheory.Limits.parallelPair.{u1, u2} C _inst_1 X (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) (CategoryTheory.Limits.biprod.inl.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3)) 0 (OfNat.mk.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3)) 0 (Zero.zero.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3)) (CategoryTheory.Limits.HasZeroMorphisms.hasZero.{u1, u2} C _inst_1 _inst_2 X (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3)))))) CategoryTheory.Limits.WalkingParallelPair.one) (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1 (CategoryTheory.Functor.obj.{u1, u1, u2, max u1 u2} C _inst_1 (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Functor.const.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Limits.Cocone.pt.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1 (CategoryTheory.Limits.parallelPair.{u1, u2} C _inst_1 X (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) (CategoryTheory.Limits.biprod.inl.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3)) 0 (OfNat.mk.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3)) 0 (Zero.zero.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3)) (CategoryTheory.Limits.HasZeroMorphisms.hasZero.{u1, u2} C _inst_1 _inst_2 X (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3)))))) (CategoryTheory.Limits.biprod.inlCokernelCofork.{u1, u2} C _inst_1 _inst_2 X Y _inst_3))) CategoryTheory.Limits.WalkingParallelPair.one)) (CategoryTheory.Limits.Cofork.π.{u1, u2} C _inst_1 X (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) (CategoryTheory.Limits.biprod.inl.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3)) 0 (OfNat.mk.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3)) 0 (Zero.zero.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3)) (CategoryTheory.Limits.HasZeroMorphisms.hasZero.{u1, u2} C _inst_1 _inst_2 X (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3))))) (CategoryTheory.Limits.biprod.inlCokernelCofork.{u1, u2} C _inst_1 _inst_2 X Y _inst_3)) (CategoryTheory.Limits.biprod.snd.{u1, u2} C _inst_1 _inst_2 X Y _inst_3)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u2} C _inst_1] (X : C) (Y : C) [_inst_3 : CategoryTheory.Limits.HasBinaryBiproduct.{u1, u2} C _inst_1 _inst_2 X Y], Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingParallelPair (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1 (CategoryTheory.Limits.parallelPair.{u1, u2} C _inst_1 X (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) (CategoryTheory.Limits.biprod.inl.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3)) 0 (Zero.toOfNat0.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3)) (CategoryTheory.Limits.HasZeroMorphisms.Zero.{u1, u2} C _inst_1 _inst_2 X (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3)))))) CategoryTheory.Limits.WalkingParallelPair.one) (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingParallelPair (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1 (Prefunctor.obj.{succ u1, succ u1, u2, max u1 u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{u1, max u2 u1} (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Category.toCategoryStruct.{u1, max u2 u1} (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, max u2 u1} C _inst_1 (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Functor.const.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1)) (CategoryTheory.Limits.Cocone.pt.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1 (CategoryTheory.Limits.parallelPair.{u1, u2} C _inst_1 X (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) (CategoryTheory.Limits.biprod.inl.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3)) 0 (Zero.toOfNat0.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3)) (CategoryTheory.Limits.HasZeroMorphisms.Zero.{u1, u2} C _inst_1 _inst_2 X (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3))))) (CategoryTheory.Limits.biprod.inlCokernelCofork.{u1, u2} C _inst_1 _inst_2 X Y _inst_3)))) CategoryTheory.Limits.WalkingParallelPair.one)) (CategoryTheory.Limits.Cofork.π.{u1, u2} C _inst_1 X (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) (CategoryTheory.Limits.biprod.inl.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3)) 0 (Zero.toOfNat0.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3)) (CategoryTheory.Limits.HasZeroMorphisms.Zero.{u1, u2} C _inst_1 _inst_2 X (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3)))) (CategoryTheory.Limits.biprod.inlCokernelCofork.{u1, u2} C _inst_1 _inst_2 X Y _inst_3)) (CategoryTheory.Limits.biprod.snd.{u1, u2} C _inst_1 _inst_2 X Y _inst_3)
Case conversion may be inaccurate. Consider using '#align category_theory.limits.biprod.inl_cokernel_cofork_π CategoryTheory.Limits.biprod.inlCokernelCofork_πₓ'. -/
@[simp]
theorem biprod.inlCokernelCofork_π : Cofork.π (biprod.inlCokernelCofork X Y) = biprod.snd :=
  rfl
#align category_theory.limits.biprod.inl_cokernel_cofork_π CategoryTheory.Limits.biprod.inlCokernelCofork_π

#print CategoryTheory.Limits.biprod.isCokernelInlCokernelFork /-
/-- The cofork `biprod.inl_cokernel_fork` is indeed a colimit.  -/
def biprod.isCokernelInlCokernelFork : IsColimit (biprod.inlCokernelCofork X Y) :=
  BinaryBicone.isColimitInlCokernelCofork (BinaryBiproduct.isColimit _ _)
#align category_theory.limits.biprod.is_cokernel_inl_cokernel_fork CategoryTheory.Limits.biprod.isCokernelInlCokernelFork
-/

#print CategoryTheory.Limits.biprod.inrCokernelCofork /-
/-- A cokernel cofork for the cokernel of `biprod.inr`. It consists of the
morphism `biprod.fst`. -/
def biprod.inrCokernelCofork : CokernelCofork (biprod.inr : Y ⟶ X ⊞ Y) :=
  BinaryBicone.inrCokernelCofork _
#align category_theory.limits.biprod.inr_cokernel_cofork CategoryTheory.Limits.biprod.inrCokernelCofork
-/

/- warning: category_theory.limits.biprod.inr_cokernel_cofork_π -> CategoryTheory.Limits.biprod.inrCokernelCofork_π is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u2} C _inst_1] (X : C) (Y : C) [_inst_3 : CategoryTheory.Limits.HasBinaryBiproduct.{u1, u2} C _inst_1 _inst_2 X Y], Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1 (CategoryTheory.Limits.parallelPair.{u1, u2} C _inst_1 Y (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) (CategoryTheory.Limits.biprod.inr.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3)) 0 (OfNat.mk.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3)) 0 (Zero.zero.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3)) (CategoryTheory.Limits.HasZeroMorphisms.hasZero.{u1, u2} C _inst_1 _inst_2 Y (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3)))))) CategoryTheory.Limits.WalkingParallelPair.one) (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1 (CategoryTheory.Functor.obj.{u1, u1, u2, max u1 u2} C _inst_1 (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Functor.const.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Limits.Cocone.pt.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1 (CategoryTheory.Limits.parallelPair.{u1, u2} C _inst_1 Y (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) (CategoryTheory.Limits.biprod.inr.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3)) 0 (OfNat.mk.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3)) 0 (Zero.zero.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3)) (CategoryTheory.Limits.HasZeroMorphisms.hasZero.{u1, u2} C _inst_1 _inst_2 Y (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3)))))) (CategoryTheory.Limits.biprod.inrCokernelCofork.{u1, u2} C _inst_1 _inst_2 X Y _inst_3))) CategoryTheory.Limits.WalkingParallelPair.one)) (CategoryTheory.Limits.Cofork.π.{u1, u2} C _inst_1 Y (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) (CategoryTheory.Limits.biprod.inr.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3)) 0 (OfNat.mk.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3)) 0 (Zero.zero.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3)) (CategoryTheory.Limits.HasZeroMorphisms.hasZero.{u1, u2} C _inst_1 _inst_2 Y (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3))))) (CategoryTheory.Limits.biprod.inrCokernelCofork.{u1, u2} C _inst_1 _inst_2 X Y _inst_3)) (CategoryTheory.Limits.biprod.fst.{u1, u2} C _inst_1 _inst_2 X Y _inst_3)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u2} C _inst_1] (X : C) (Y : C) [_inst_3 : CategoryTheory.Limits.HasBinaryBiproduct.{u1, u2} C _inst_1 _inst_2 X Y], Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingParallelPair (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1 (CategoryTheory.Limits.parallelPair.{u1, u2} C _inst_1 Y (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) (CategoryTheory.Limits.biprod.inr.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3)) 0 (Zero.toOfNat0.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3)) (CategoryTheory.Limits.HasZeroMorphisms.Zero.{u1, u2} C _inst_1 _inst_2 Y (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3)))))) CategoryTheory.Limits.WalkingParallelPair.one) (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingParallelPair (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1 (Prefunctor.obj.{succ u1, succ u1, u2, max u1 u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{u1, max u2 u1} (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Category.toCategoryStruct.{u1, max u2 u1} (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, max u2 u1} C _inst_1 (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Functor.const.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1)) (CategoryTheory.Limits.Cocone.pt.{0, u1, 0, u2} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1 (CategoryTheory.Limits.parallelPair.{u1, u2} C _inst_1 Y (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) (CategoryTheory.Limits.biprod.inr.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3)) 0 (Zero.toOfNat0.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3)) (CategoryTheory.Limits.HasZeroMorphisms.Zero.{u1, u2} C _inst_1 _inst_2 Y (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3))))) (CategoryTheory.Limits.biprod.inrCokernelCofork.{u1, u2} C _inst_1 _inst_2 X Y _inst_3)))) CategoryTheory.Limits.WalkingParallelPair.one)) (CategoryTheory.Limits.Cofork.π.{u1, u2} C _inst_1 Y (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) (CategoryTheory.Limits.biprod.inr.{u1, u2} C _inst_1 _inst_2 X Y _inst_3) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3)) 0 (Zero.toOfNat0.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3)) (CategoryTheory.Limits.HasZeroMorphisms.Zero.{u1, u2} C _inst_1 _inst_2 Y (CategoryTheory.Limits.biprod.{u1, u2} C _inst_1 _inst_2 X Y _inst_3)))) (CategoryTheory.Limits.biprod.inrCokernelCofork.{u1, u2} C _inst_1 _inst_2 X Y _inst_3)) (CategoryTheory.Limits.biprod.fst.{u1, u2} C _inst_1 _inst_2 X Y _inst_3)
Case conversion may be inaccurate. Consider using '#align category_theory.limits.biprod.inr_cokernel_cofork_π CategoryTheory.Limits.biprod.inrCokernelCofork_πₓ'. -/
@[simp]
theorem biprod.inrCokernelCofork_π : Cofork.π (biprod.inrCokernelCofork X Y) = biprod.fst :=
  rfl
#align category_theory.limits.biprod.inr_cokernel_cofork_π CategoryTheory.Limits.biprod.inrCokernelCofork_π

#print CategoryTheory.Limits.biprod.isCokernelInrCokernelFork /-
/-- The cofork `biprod.inr_cokernel_fork` is indeed a colimit.  -/
def biprod.isCokernelInrCokernelFork : IsColimit (biprod.inrCokernelCofork X Y) :=
  BinaryBicone.isColimitInrCokernelCofork (BinaryBiproduct.isColimit _ _)
#align category_theory.limits.biprod.is_cokernel_inr_cokernel_fork CategoryTheory.Limits.biprod.isCokernelInrCokernelFork
-/

end HasBinaryBiproduct

variable {X Y : C} [HasBinaryBiproduct X Y]

instance : HasKernel (biprod.fst : X ⊞ Y ⟶ X) :=
  HasLimit.mk ⟨_, biprod.isKernelFstKernelFork X Y⟩

#print CategoryTheory.Limits.kernelBiprodFstIso /-
/-- The kernel of `biprod.fst : X ⊞ Y ⟶ X` is `Y`. -/
@[simps]
def kernelBiprodFstIso : kernel (biprod.fst : X ⊞ Y ⟶ X) ≅ Y :=
  limit.isoLimitCone ⟨_, biprod.isKernelFstKernelFork X Y⟩
#align category_theory.limits.kernel_biprod_fst_iso CategoryTheory.Limits.kernelBiprodFstIso
-/

instance : HasKernel (biprod.snd : X ⊞ Y ⟶ Y) :=
  HasLimit.mk ⟨_, biprod.isKernelSndKernelFork X Y⟩

#print CategoryTheory.Limits.kernelBiprodSndIso /-
/-- The kernel of `biprod.snd : X ⊞ Y ⟶ Y` is `X`. -/
@[simps]
def kernelBiprodSndIso : kernel (biprod.snd : X ⊞ Y ⟶ Y) ≅ X :=
  limit.isoLimitCone ⟨_, biprod.isKernelSndKernelFork X Y⟩
#align category_theory.limits.kernel_biprod_snd_iso CategoryTheory.Limits.kernelBiprodSndIso
-/

instance : HasCokernel (biprod.inl : X ⟶ X ⊞ Y) :=
  HasColimit.mk ⟨_, biprod.isCokernelInlCokernelFork X Y⟩

#print CategoryTheory.Limits.cokernelBiprodInlIso /-
/-- The cokernel of `biprod.inl : X ⟶ X ⊞ Y` is `Y`. -/
@[simps]
def cokernelBiprodInlIso : cokernel (biprod.inl : X ⟶ X ⊞ Y) ≅ Y :=
  colimit.isoColimitCocone ⟨_, biprod.isCokernelInlCokernelFork X Y⟩
#align category_theory.limits.cokernel_biprod_inl_iso CategoryTheory.Limits.cokernelBiprodInlIso
-/

instance : HasCokernel (biprod.inr : Y ⟶ X ⊞ Y) :=
  HasColimit.mk ⟨_, biprod.isCokernelInrCokernelFork X Y⟩

#print CategoryTheory.Limits.cokernelBiprodInrIso /-
/-- The cokernel of `biprod.inr : Y ⟶ X ⊞ Y` is `X`. -/
@[simps]
def cokernelBiprodInrIso : cokernel (biprod.inr : Y ⟶ X ⊞ Y) ≅ X :=
  colimit.isoColimitCocone ⟨_, biprod.isCokernelInrCokernelFork X Y⟩
#align category_theory.limits.cokernel_biprod_inr_iso CategoryTheory.Limits.cokernelBiprodInrIso
-/

end BiprodKernel

section IsZero

#print CategoryTheory.Limits.isoBiprodZero /-
/-- If `Y` is a zero object, `X ≅ X ⊞ Y` for any `X`. -/
@[simps]
def isoBiprodZero {X Y : C} [HasBinaryBiproduct X Y] (hY : IsZero Y) : X ≅ X ⊞ Y
    where
  hom := biprod.inl
  inv := biprod.fst
  inv_hom_id' :=
    by
    apply CategoryTheory.Limits.biprod.hom_ext <;>
      simp only [category.assoc, biprod.inl_fst, category.comp_id, category.id_comp, biprod.inl_snd,
        comp_zero]
    apply hY.eq_of_tgt
#align category_theory.limits.iso_biprod_zero CategoryTheory.Limits.isoBiprodZero
-/

#print CategoryTheory.Limits.isoZeroBiprod /-
/-- If `X` is a zero object, `Y ≅ X ⊞ Y` for any `Y`. -/
@[simps]
def isoZeroBiprod {X Y : C} [HasBinaryBiproduct X Y] (hY : IsZero X) : Y ≅ X ⊞ Y
    where
  hom := biprod.inr
  inv := biprod.snd
  inv_hom_id' :=
    by
    apply CategoryTheory.Limits.biprod.hom_ext <;>
      simp only [category.assoc, biprod.inr_snd, category.comp_id, category.id_comp, biprod.inr_fst,
        comp_zero]
    apply hY.eq_of_tgt
#align category_theory.limits.iso_zero_biprod CategoryTheory.Limits.isoZeroBiprod
-/

end IsZero

section

variable [HasBinaryBiproducts C]

#print CategoryTheory.Limits.biprod.braiding /-
/-- The braiding isomorphism which swaps a binary biproduct. -/
@[simps]
def biprod.braiding (P Q : C) : P ⊞ Q ≅ Q ⊞ P
    where
  hom := biprod.lift biprod.snd biprod.fst
  inv := biprod.lift biprod.snd biprod.fst
#align category_theory.limits.biprod.braiding CategoryTheory.Limits.biprod.braiding
-/

#print CategoryTheory.Limits.biprod.braiding' /-
/-- An alternative formula for the braiding isomorphism which swaps a binary biproduct,
using the fact that the biproduct is a coproduct.
-/
@[simps]
def biprod.braiding' (P Q : C) : P ⊞ Q ≅ Q ⊞ P
    where
  hom := biprod.desc biprod.inr biprod.inl
  inv := biprod.desc biprod.inr biprod.inl
#align category_theory.limits.biprod.braiding' CategoryTheory.Limits.biprod.braiding'
-/

#print CategoryTheory.Limits.biprod.braiding'_eq_braiding /-
theorem biprod.braiding'_eq_braiding {P Q : C} : biprod.braiding' P Q = biprod.braiding P Q := by
  tidy
#align category_theory.limits.biprod.braiding'_eq_braiding CategoryTheory.Limits.biprod.braiding'_eq_braiding
-/

#print CategoryTheory.Limits.biprod.braid_natural /-
/-- The braiding isomorphism can be passed through a map by swapping the order. -/
@[reassoc.1]
theorem biprod.braid_natural {W X Y Z : C} (f : X ⟶ Y) (g : Z ⟶ W) :
    biprod.map f g ≫ (biprod.braiding _ _).hom = (biprod.braiding _ _).hom ≫ biprod.map g f := by
  tidy
#align category_theory.limits.biprod.braid_natural CategoryTheory.Limits.biprod.braid_natural
-/

#print CategoryTheory.Limits.biprod.braiding_map_braiding /-
@[reassoc.1]
theorem biprod.braiding_map_braiding {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) :
    (biprod.braiding X W).hom ≫ biprod.map f g ≫ (biprod.braiding Y Z).hom = biprod.map g f := by
  tidy
#align category_theory.limits.biprod.braiding_map_braiding CategoryTheory.Limits.biprod.braiding_map_braiding
-/

#print CategoryTheory.Limits.biprod.symmetry' /-
@[simp, reassoc.1]
theorem biprod.symmetry' (P Q : C) :
    biprod.lift biprod.snd biprod.fst ≫ biprod.lift biprod.snd biprod.fst = 𝟙 (P ⊞ Q) := by tidy
#align category_theory.limits.biprod.symmetry' CategoryTheory.Limits.biprod.symmetry'
-/

#print CategoryTheory.Limits.biprod.symmetry /-
/-- The braiding isomorphism is symmetric. -/
@[reassoc.1]
theorem biprod.symmetry (P Q : C) : (biprod.braiding P Q).hom ≫ (biprod.braiding Q P).hom = 𝟙 _ :=
  by simp
#align category_theory.limits.biprod.symmetry CategoryTheory.Limits.biprod.symmetry
-/

end

end Limits

open CategoryTheory.Limits

-- TODO:
-- If someone is interested, they could provide the constructions:
--   has_binary_biproducts ↔ has_finite_biproducts
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasBinaryBiproducts C]

#print CategoryTheory.Indecomposable /-
/-- An object is indecomposable if it cannot be written as the biproduct of two nonzero objects. -/
def Indecomposable (X : C) : Prop :=
  ¬IsZero X ∧ ∀ Y Z, (X ≅ Y ⊞ Z) → IsZero Y ∨ IsZero Z
#align category_theory.indecomposable CategoryTheory.Indecomposable
-/

#print CategoryTheory.isIso_left_of_isIso_biprod_map /-
/-- If
```
(f 0)
(0 g)
```
is invertible, then `f` is invertible.
-/
theorem isIso_left_of_isIso_biprod_map {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z)
    [IsIso (biprod.map f g)] : IsIso f :=
  ⟨⟨biprod.inl ≫ inv (biprod.map f g) ≫ biprod.fst,
      ⟨by
        have t :=
          congr_arg (fun p : W ⊞ X ⟶ W ⊞ X => biprod.inl ≫ p ≫ biprod.fst)
            (is_iso.hom_inv_id (biprod.map f g))
        simp only [category.id_comp, category.assoc, biprod.inl_map_assoc] at t
        simp [t],
        by
        have t :=
          congr_arg (fun p : Y ⊞ Z ⟶ Y ⊞ Z => biprod.inl ≫ p ≫ biprod.fst)
            (is_iso.inv_hom_id (biprod.map f g))
        simp only [category.id_comp, category.assoc, biprod.map_fst] at t
        simp only [category.assoc]
        simp [t]⟩⟩⟩
#align category_theory.is_iso_left_of_is_iso_biprod_map CategoryTheory.isIso_left_of_isIso_biprod_map
-/

#print CategoryTheory.isIso_right_of_isIso_biprod_map /-
/-- If
```
(f 0)
(0 g)
```
is invertible, then `g` is invertible.
-/
theorem isIso_right_of_isIso_biprod_map {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z)
    [IsIso (biprod.map f g)] : IsIso g :=
  letI : is_iso (biprod.map g f) :=
    by
    rw [← biprod.braiding_map_braiding]
    infer_instance
  is_iso_left_of_is_iso_biprod_map g f
#align category_theory.is_iso_right_of_is_iso_biprod_map CategoryTheory.isIso_right_of_isIso_biprod_map
-/

end CategoryTheory

