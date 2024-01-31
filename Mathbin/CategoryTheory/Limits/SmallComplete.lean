/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import CategoryTheory.Limits.Shapes.Products
import SetTheory.Cardinal.Basic

#align_import category_theory.limits.small_complete from "leanprover-community/mathlib"@"69c6a5a12d8a2b159f20933e60115a4f2de62b58"

/-!
# Any small complete category is a preorder

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We show that any small category which has all (small) limits is a preorder: In particular, we show
that if a small category `C` in universe `u` has products of size `u`, then for any `X Y : C`
there is at most one morphism `X ⟶ Y`.
Note that in Lean, a preorder category is strictly one where the morphisms are in `Prop`, so
we instead show that the homsets are subsingleton.

## References

* https://ncatlab.org/nlab/show/complete+small+category#in_classical_logic

## Tags

small complete, preorder, Freyd
-/


namespace CategoryTheory

open Category Limits

open scoped Cardinal

universe u

variable {C : Type u} [SmallCategory C] [HasProducts.{u} C]

/-- A small category with products is a thin category.

in Lean, a preorder category is one where the morphisms are in Prop, which is weaker than the usual
notion of a preorder/thin category which says that each homset is subsingleton; we show the latter
rather than providing a `preorder C` instance.
-/
instance (priority := 100) : Quiver.IsThin C := fun X Y => ⟨fun r s => by classical⟩

end CategoryTheory

