/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Scott Morrison, Johannes Hölzl, Reid Barton

! This file was ported from Lean 3 source module category_theory.category.galois_connection
! leanprover-community/mathlib commit 18a5306c091183ac90884daa9373fa3b178e8607
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

/-- A galois connection between preorders induces an adjunction between the associated categories.
-/
def GaloisConnection.adjunction {l : X → Y} {u : Y → X} (gc : GaloisConnection l u) :
    gc.monotone_l.Functor ⊣ gc.monotone_u.Functor :=
  CategoryTheory.Adjunction.mkOfHomEquiv
    {
      homEquiv := fun X Y =>
        ⟨fun f => (gc.le_u f.le).Hom, fun f => (gc.l_le f.le).Hom, by tidy, by tidy⟩ }
#align galois_connection.adjunction GaloisConnection.adjunction

end

namespace CategoryTheory

variable {X : Type u} {Y : Type v} [Preorder X] [Preorder Y]

/-- An adjunction between preorder categories induces a galois connection.
-/
theorem Adjunction.gc {L : X ⥤ Y} {R : Y ⥤ X} (adj : L ⊣ R) : GaloisConnection L.obj R.obj :=
  fun x y =>
  ⟨fun h => ((adj.homEquiv x y).toFun h.Hom).le, fun h => ((adj.homEquiv x y).invFun h.Hom).le⟩
#align category_theory.adjunction.gc CategoryTheory.Adjunction.gc

end CategoryTheory

