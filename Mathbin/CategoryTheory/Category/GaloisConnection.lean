/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Scott Morrison, Johannes Hölzl, Reid Barton

! This file was ported from Lean 3 source module category_theory.category.galois_connection
! leanprover-community/mathlib commit d82b87871d9a274884dff5263fa4f5d93bcce1d6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Category.Preorder
import Mathbin.CategoryTheory.Adjunction.Basic
import Mathbin.Order.GaloisConnection

/-!

# Galois connections between preorders are adjunctions.

* `galois_connection.adjunction` is the adjunction associated to a galois connection.

-/


universe u v

section

variable {X : Type u} {Y : Type v} [Preorder X] [Preorder Y]

#print GaloisConnection.adjunction /-
/-- A galois connection between preorders induces an adjunction between the associated categories.
-/
def GaloisConnection.adjunction {l : X → Y} {u : Y → X} (gc : GaloisConnection l u) :
    gc.monotone_l.Functor ⊣ gc.monotone_u.Functor :=
  CategoryTheory.Adjunction.mkOfHomEquiv
    {
      homEquiv := fun X Y =>
        ⟨fun f => (gc.le_u f.le).Hom, fun f => (gc.l_le f.le).Hom, by tidy, by tidy⟩ }
#align galois_connection.adjunction GaloisConnection.adjunction
-/

end

namespace CategoryTheory

variable {X : Type u} {Y : Type v} [Preorder X] [Preorder Y]

/- warning: category_theory.adjunction.gc -> CategoryTheory.Adjunction.gc is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : Preorder.{u1} X] [_inst_2 : Preorder.{u2} Y] {L : CategoryTheory.Functor.{u1, u2, u1, u2} X (Preorder.smallCategory.{u1} X _inst_1) Y (Preorder.smallCategory.{u2} Y _inst_2)} {R : CategoryTheory.Functor.{u2, u1, u2, u1} Y (Preorder.smallCategory.{u2} Y _inst_2) X (Preorder.smallCategory.{u1} X _inst_1)}, (CategoryTheory.Adjunction.{u1, u2, u1, u2} X (Preorder.smallCategory.{u1} X _inst_1) Y (Preorder.smallCategory.{u2} Y _inst_2) L R) -> (GaloisConnection.{u1, u2} X Y _inst_1 _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u1, u2} X (Preorder.smallCategory.{u1} X _inst_1) Y (Preorder.smallCategory.{u2} Y _inst_2) L) (CategoryTheory.Functor.obj.{u2, u1, u2, u1} Y (Preorder.smallCategory.{u2} Y _inst_2) X (Preorder.smallCategory.{u1} X _inst_1) R))
but is expected to have type
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : Preorder.{u1} X] [_inst_2 : Preorder.{u2} Y] {L : CategoryTheory.Functor.{u1, u2, u1, u2} X (Preorder.smallCategory.{u1} X _inst_1) Y (Preorder.smallCategory.{u2} Y _inst_2)} {R : CategoryTheory.Functor.{u2, u1, u2, u1} Y (Preorder.smallCategory.{u2} Y _inst_2) X (Preorder.smallCategory.{u1} X _inst_1)}, (CategoryTheory.Adjunction.{u1, u2, u1, u2} X (Preorder.smallCategory.{u1} X _inst_1) Y (Preorder.smallCategory.{u2} Y _inst_2) L R) -> (GaloisConnection.{u1, u2} X Y _inst_1 _inst_2 (Prefunctor.obj.{succ u1, succ u2, u1, u2} X (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} X (CategoryTheory.Category.toCategoryStruct.{u1, u1} X (Preorder.smallCategory.{u1} X _inst_1))) Y (CategoryTheory.CategoryStruct.toQuiver.{u2, u2} Y (CategoryTheory.Category.toCategoryStruct.{u2, u2} Y (Preorder.smallCategory.{u2} Y _inst_2))) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u1, u2} X (Preorder.smallCategory.{u1} X _inst_1) Y (Preorder.smallCategory.{u2} Y _inst_2) L)) (Prefunctor.obj.{succ u2, succ u1, u2, u1} Y (CategoryTheory.CategoryStruct.toQuiver.{u2, u2} Y (CategoryTheory.Category.toCategoryStruct.{u2, u2} Y (Preorder.smallCategory.{u2} Y _inst_2))) X (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} X (CategoryTheory.Category.toCategoryStruct.{u1, u1} X (Preorder.smallCategory.{u1} X _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u2, u1} Y (Preorder.smallCategory.{u2} Y _inst_2) X (Preorder.smallCategory.{u1} X _inst_1) R)))
Case conversion may be inaccurate. Consider using '#align category_theory.adjunction.gc CategoryTheory.Adjunction.gcₓ'. -/
/-- An adjunction between preorder categories induces a galois connection.
-/
theorem Adjunction.gc {L : X ⥤ Y} {R : Y ⥤ X} (adj : L ⊣ R) : GaloisConnection L.obj R.obj :=
  fun x y =>
  ⟨fun h => ((adj.homEquiv x y).toFun h.Hom).le, fun h => ((adj.homEquiv x y).invFun h.Hom).le⟩
#align category_theory.adjunction.gc CategoryTheory.Adjunction.gc

end CategoryTheory

