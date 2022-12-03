/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathbin.Algebra.Order.Group.Defs
import Mathbin.Algebra.Hom.Equiv.Units.Basic

/-!
# Inverse and multiplication as order isomorphisms in ordered groups

-/


open Function

universe u

variable {α : Type u}

section Group

variable [Group α]

section TypeclassesLeftRightLe

variable [LE α] [CovariantClass α α (· * ·) (· ≤ ·)] [CovariantClass α α (swap (· * ·)) (· ≤ ·)]
  {a b c d : α}

section

variable (α)

/-- `x ↦ x⁻¹` as an order-reversing equivalence. -/
@[to_additive "`x ↦ -x` as an order-reversing equivalence.", simps]
def OrderIso.inv :
    α ≃o αᵒᵈ where 
  toEquiv := (Equiv.inv α).trans OrderDual.toDual
  map_rel_iff' a b := @inv_le_inv_iff α _ _ _ _ _ _
#align order_iso.inv OrderIso.inv

end

@[to_additive neg_le]
theorem inv_le' : a⁻¹ ≤ b ↔ b⁻¹ ≤ a :=
  (OrderIso.inv α).symm_apply_le
#align inv_le' inv_le'

alias inv_le' ↔ inv_le_of_inv_le' _

attribute [to_additive neg_le_of_neg_le] inv_le_of_inv_le'

@[to_additive le_neg]
theorem le_inv' : a ≤ b⁻¹ ↔ b ≤ a⁻¹ :=
  (OrderIso.inv α).le_symm_apply
#align le_inv' le_inv'

end TypeclassesLeftRightLe

end Group

alias le_inv' ↔ le_inv_of_le_inv _

attribute [to_additive] le_inv_of_le_inv

section Group

variable [Group α] [LE α]

section Right

variable [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c d : α}

/-- `equiv.mul_right` as an `order_iso`. See also `order_embedding.mul_right`. -/
@[to_additive "`equiv.add_right` as an `order_iso`. See also `order_embedding.add_right`.",
  simps (config := { simpRhs := true }) toEquiv apply]
def OrderIso.mulRight (a : α) :
    α ≃o α where 
  map_rel_iff' _ _ := mul_le_mul_iff_right a
  toEquiv := Equiv.mulRight a
#align order_iso.mul_right OrderIso.mulRight

@[simp, to_additive]
theorem OrderIso.mul_right_symm (a : α) : (OrderIso.mulRight a).symm = OrderIso.mulRight a⁻¹ := by
  ext x
  rfl
#align order_iso.mul_right_symm OrderIso.mul_right_symm

end Right

section Left

variable [CovariantClass α α (· * ·) (· ≤ ·)]

/-- `equiv.mul_left` as an `order_iso`. See also `order_embedding.mul_left`. -/
@[to_additive "`equiv.add_left` as an `order_iso`. See also `order_embedding.add_left`.",
  simps (config := { simpRhs := true }) toEquiv apply]
def OrderIso.mulLeft (a : α) :
    α ≃o α where 
  map_rel_iff' _ _ := mul_le_mul_iff_left a
  toEquiv := Equiv.mulLeft a
#align order_iso.mul_left OrderIso.mulLeft

@[simp, to_additive]
theorem OrderIso.mul_left_symm (a : α) : (OrderIso.mulLeft a).symm = OrderIso.mulLeft a⁻¹ := by
  ext x
  rfl
#align order_iso.mul_left_symm OrderIso.mul_left_symm

end Left

end Group

