/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Scott Morrison, Johannes Hölzl, Reid Barton
-/
import Mathbin.CategoryTheory.Category.Preorder
import Mathbin.CategoryTheory.Adjunction.Basic
import Mathbin.Order.GaloisConnection

#align_import category_theory.category.galois_connection from "leanprover-community/mathlib"@"3dadefa3f544b1db6214777fe47910739b54c66a"

/-!

# Galois connections between preorders are adjunctions.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

#print CategoryTheory.Adjunction.gc /-
/-- An adjunction between preorder categories induces a galois connection.
-/
theorem Adjunction.gc {L : X ⥤ Y} {R : Y ⥤ X} (adj : L ⊣ R) : GaloisConnection L.obj R.obj :=
  fun x y =>
  ⟨fun h => ((adj.homEquiv x y).toFun h.Hom).le, fun h => ((adj.homEquiv x y).invFun h.Hom).le⟩
#align category_theory.adjunction.gc CategoryTheory.Adjunction.gc
-/

end CategoryTheory

