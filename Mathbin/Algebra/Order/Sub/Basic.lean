/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

! This file was ported from Lean 3 source module algebra.order.sub.basic
! leanprover-community/mathlib commit 448144f7ae193a8990cb7473c9e9a01990f64ac7
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Hom.Basic
import Mathbin.Algebra.Hom.Equiv.Basic
import Mathbin.Algebra.Ring.Basic
import Mathbin.Algebra.Order.Sub.Defs

/-!
# Additional results about ordered Subtraction

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

-/


variable {α β : Type _}

section Add

variable [Preorder α] [Add α] [Sub α] [OrderedSub α] {a b c d : α}

#print AddHom.le_map_tsub /-
theorem AddHom.le_map_tsub [Preorder β] [Add β] [Sub β] [OrderedSub β] (f : AddHom α β)
    (hf : Monotone f) (a b : α) : f a - f b ≤ f (a - b) := by rw [tsub_le_iff_right, ← f.map_add];
  exact hf le_tsub_add
#align add_hom.le_map_tsub AddHom.le_map_tsub
-/

theorem le_mul_tsub {R : Type _} [Distrib R] [Preorder R] [Sub R] [OrderedSub R]
    [CovariantClass R R (· * ·) (· ≤ ·)] {a b c : R} : a * b - a * c ≤ a * (b - c) :=
  (AddHom.mulLeft a).le_map_tsub (monotone_id.const_mul' a) _ _
#align le_mul_tsub le_mul_tsub

theorem le_tsub_mul {R : Type _} [CommSemiring R] [Preorder R] [Sub R] [OrderedSub R]
    [CovariantClass R R (· * ·) (· ≤ ·)] {a b c : R} : a * c - b * c ≤ (a - b) * c := by
  simpa only [mul_comm _ c] using le_mul_tsub
#align le_tsub_mul le_tsub_mul

end Add

/-- An order isomorphism between types with ordered subtraction preserves subtraction provided that
it preserves addition. -/
theorem OrderIso.map_tsub {M N : Type _} [Preorder M] [Add M] [Sub M] [OrderedSub M]
    [PartialOrder N] [Add N] [Sub N] [OrderedSub N] (e : M ≃o N)
    (h_add : ∀ a b, e (a + b) = e a + e b) (a b : M) : e (a - b) = e a - e b :=
  by
  set e_add : M ≃+ N := { e with map_add' := h_add }
  refine' le_antisymm _ (e_add.to_add_hom.le_map_tsub e.monotone a b)
  suffices e (e.symm (e a) - e.symm (e b)) ≤ e (e.symm (e a - e b)) by simpa
  exact e.monotone (e_add.symm.to_add_hom.le_map_tsub e.symm.monotone _ _)
#align order_iso.map_tsub OrderIso.map_tsub

/-! ### Preorder -/


section Preorder

variable [Preorder α]

variable [AddCommMonoid α] [Sub α] [OrderedSub α] {a b c d : α}

theorem AddMonoidHom.le_map_tsub [Preorder β] [AddCommMonoid β] [Sub β] [OrderedSub β] (f : α →+ β)
    (hf : Monotone f) (a b : α) : f a - f b ≤ f (a - b) :=
  f.toAddHom.le_map_tsub hf a b
#align add_monoid_hom.le_map_tsub AddMonoidHom.le_map_tsub

end Preorder

