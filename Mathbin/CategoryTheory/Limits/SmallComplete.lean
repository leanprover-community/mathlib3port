/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathbin.CategoryTheory.Limits.Shapes.Products
import Mathbin.SetTheory.Cardinal.Basic

/-!
# Any small complete category is a preorder

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

open Cardinal

universe u

variable {C : Type u} [SmallCategory C] [HasProducts.{u} C]

/-- A small category with products is a thin category.

in Lean, a preorder category is one where the morphisms are in Prop, which is weaker than the usual
notion of a preorder/thin category which says that each homset is subsingleton; we show the latter
rather than providing a `preorder C` instance.
-/
instance (priority := 100) : Quiver.IsThin C := fun X Y =>
  ⟨fun r s => by
    classical by_contra r_ne_s
      · rw [Cardinal.two_le_iff]
        exact ⟨_, _, r_ne_s⟩
        
      let α := #md
      let yp : C := ∏ fun f : md => Y
      · apply le_trans (Cardinal.power_le_power_right z)
        rw [Cardinal.power_def]
        apply le_of_eq
        rw [Cardinal.eq]
        refine' ⟨⟨pi.lift, fun f k => f ≫ pi.π _ k, _, _⟩⟩
        · intro f
          ext k
          simp
          
        · intro f
          ext ⟨j⟩
          simp
          
        ⟩

end CategoryTheory

