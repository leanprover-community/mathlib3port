/-
Copyright (c) 2019 Scott Morrison, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta

! This file was ported from Lean 3 source module category_theory.thin
! leanprover-community/mathlib commit 509de852e1de55e1efa8eacfa11df0823f26f226
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Functor.Category
import Mathbin.CategoryTheory.Isomorphism

/-!
# Thin categories

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A thin category (also known as a sparse category) is a category with at most one morphism between
each pair of objects.

Examples include posets, but also some indexing categories (diagrams) for special shapes of
(co)limits.

To construct a category instance one only needs to specify the `category_struct` part,
as the axioms hold for free.

If `C` is thin, then the category of functors to `C` is also thin.
Further, to show two objects are isomorphic in a thin category, it suffices only to give a morphism
in each direction.
-/


universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁}

section

variable [CategoryStruct.{v₁} C] [Quiver.IsThin C]

#print CategoryTheory.thin_category /-
/-- Construct a category instance from a category_struct, using the fact that
    hom spaces are subsingletons to prove the axioms. -/
def thin_category : Category C where
#align category_theory.thin_category CategoryTheory.thin_category
-/

end

-- We don't assume anything about where the category instance on `C` came from.
-- In particular this allows `C` to be a preorder, with the category instance inherited from the
-- preorder structure.
variable [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

variable [Quiver.IsThin C]

#print CategoryTheory.functor_thin /-
/-- If `C` is a thin category, then `D ⥤ C` is a thin category. -/
instance functor_thin : Quiver.IsThin (D ⥤ C) := fun _ _ =>
  ⟨fun α β => NatTrans.ext α β (funext fun _ => Subsingleton.elim _ _)⟩
#align category_theory.functor_thin CategoryTheory.functor_thin
-/

#print CategoryTheory.iso_of_both_ways /-
/-- To show `X ≅ Y` in a thin category, it suffices to just give any morphism in each direction. -/
def iso_of_both_ways {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X) : X ≅ Y
    where
  Hom := f
  inv := g
#align category_theory.iso_of_both_ways CategoryTheory.iso_of_both_ways
-/

#print CategoryTheory.subsingleton_iso /-
instance subsingleton_iso {X Y : C} : Subsingleton (X ≅ Y) :=
  ⟨by
    intro i₁ i₂
    ext1
    apply Subsingleton.elim⟩
#align category_theory.subsingleton_iso CategoryTheory.subsingleton_iso
-/

end CategoryTheory

