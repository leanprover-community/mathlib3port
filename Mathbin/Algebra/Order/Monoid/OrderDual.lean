/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathbin.Algebra.Group.OrderSynonym
import Mathbin.Algebra.Order.Monoid.Cancel.Defs

#align_import algebra.order.monoid.order_dual from "leanprover-community/mathlib"@"448144f7ae193a8990cb7473c9e9a01990f64ac7"

/-! # Ordered monoid structures on the order dual.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.-/


universe u

variable {α : Type u}

open Function

namespace OrderDual

#print OrderDual.contravariantClass_mul_le /-
@[to_additive]
instance contravariantClass_mul_le [LE α] [Mul α] [c : ContravariantClass α α (· * ·) (· ≤ ·)] :
    ContravariantClass αᵒᵈ αᵒᵈ (· * ·) (· ≤ ·) :=
  ⟨c.1.flip⟩
#align order_dual.contravariant_class_mul_le OrderDual.contravariantClass_mul_le
#align order_dual.contravariant_class_add_le OrderDual.contravariantClass_add_le
-/

#print OrderDual.covariantClass_mul_le /-
@[to_additive]
instance covariantClass_mul_le [LE α] [Mul α] [c : CovariantClass α α (· * ·) (· ≤ ·)] :
    CovariantClass αᵒᵈ αᵒᵈ (· * ·) (· ≤ ·) :=
  ⟨c.1.flip⟩
#align order_dual.covariant_class_mul_le OrderDual.covariantClass_mul_le
#align order_dual.covariant_class_add_le OrderDual.covariantClass_add_le
-/

#print OrderDual.contravariantClass_swap_mul_le /-
@[to_additive]
instance contravariantClass_swap_mul_le [LE α] [Mul α]
    [c : ContravariantClass α α (swap (· * ·)) (· ≤ ·)] :
    ContravariantClass αᵒᵈ αᵒᵈ (swap (· * ·)) (· ≤ ·) :=
  ⟨c.1.flip⟩
#align order_dual.contravariant_class_swap_mul_le OrderDual.contravariantClass_swap_mul_le
#align order_dual.contravariant_class_swap_add_le OrderDual.contravariantClass_swap_add_le
-/

#print OrderDual.covariantClass_swap_mul_le /-
@[to_additive]
instance covariantClass_swap_mul_le [LE α] [Mul α] [c : CovariantClass α α (swap (· * ·)) (· ≤ ·)] :
    CovariantClass αᵒᵈ αᵒᵈ (swap (· * ·)) (· ≤ ·) :=
  ⟨c.1.flip⟩
#align order_dual.covariant_class_swap_mul_le OrderDual.covariantClass_swap_mul_le
#align order_dual.covariant_class_swap_add_le OrderDual.covariantClass_swap_add_le
-/

#print OrderDual.contravariantClass_mul_lt /-
@[to_additive]
instance contravariantClass_mul_lt [LT α] [Mul α] [c : ContravariantClass α α (· * ·) (· < ·)] :
    ContravariantClass αᵒᵈ αᵒᵈ (· * ·) (· < ·) :=
  ⟨c.1.flip⟩
#align order_dual.contravariant_class_mul_lt OrderDual.contravariantClass_mul_lt
#align order_dual.contravariant_class_add_lt OrderDual.contravariantClass_add_lt
-/

#print OrderDual.covariantClass_mul_lt /-
@[to_additive]
instance covariantClass_mul_lt [LT α] [Mul α] [c : CovariantClass α α (· * ·) (· < ·)] :
    CovariantClass αᵒᵈ αᵒᵈ (· * ·) (· < ·) :=
  ⟨c.1.flip⟩
#align order_dual.covariant_class_mul_lt OrderDual.covariantClass_mul_lt
#align order_dual.covariant_class_add_lt OrderDual.covariantClass_add_lt
-/

#print OrderDual.contravariantClass_swap_mul_lt /-
@[to_additive]
instance contravariantClass_swap_mul_lt [LT α] [Mul α]
    [c : ContravariantClass α α (swap (· * ·)) (· < ·)] :
    ContravariantClass αᵒᵈ αᵒᵈ (swap (· * ·)) (· < ·) :=
  ⟨c.1.flip⟩
#align order_dual.contravariant_class_swap_mul_lt OrderDual.contravariantClass_swap_mul_lt
#align order_dual.contravariant_class_swap_add_lt OrderDual.contravariantClass_swap_add_lt
-/

#print OrderDual.covariantClass_swap_mul_lt /-
@[to_additive]
instance covariantClass_swap_mul_lt [LT α] [Mul α] [c : CovariantClass α α (swap (· * ·)) (· < ·)] :
    CovariantClass αᵒᵈ αᵒᵈ (swap (· * ·)) (· < ·) :=
  ⟨c.1.flip⟩
#align order_dual.covariant_class_swap_mul_lt OrderDual.covariantClass_swap_mul_lt
#align order_dual.covariant_class_swap_add_lt OrderDual.covariantClass_swap_add_lt
-/

@[to_additive]
instance [OrderedCommMonoid α] : OrderedCommMonoid αᵒᵈ :=
  { OrderDual.partialOrder α, OrderDual.commMonoid with
    mul_le_mul_left := fun a b h c => mul_le_mul_left' h c }

#print OrderDual.OrderedCancelCommMonoid.to_contravariantClass /-
@[to_additive OrderDual.OrderedCancelAddCommMonoid.to_contravariantClass]
instance OrderedCancelCommMonoid.to_contravariantClass [OrderedCancelCommMonoid α] :
    ContravariantClass αᵒᵈ αᵒᵈ Mul.mul LE.le
    where elim a b c := OrderedCancelCommMonoid.le_of_hMul_le_hMul_left a c b
#align order_dual.ordered_cancel_comm_monoid.to_contravariant_class OrderDual.OrderedCancelCommMonoid.to_contravariantClass
#align ordered_cancel_add_comm_monoid.to_contravariant_class OrderDual.OrderedCancelAddCommMonoid.to_contravariantClass
-/

@[to_additive]
instance [OrderedCancelCommMonoid α] : OrderedCancelCommMonoid αᵒᵈ :=
  { OrderDual.orderedCommMonoid, OrderDual.cancelCommMonoid with
    le_of_mul_le_mul_left := fun a b c : α => le_of_mul_le_mul_left' }

@[to_additive]
instance [LinearOrderedCancelCommMonoid α] : LinearOrderedCancelCommMonoid αᵒᵈ :=
  { OrderDual.instLinearOrder α, OrderDual.orderedCancelCommMonoid with }

@[to_additive]
instance [LinearOrderedCommMonoid α] : LinearOrderedCommMonoid αᵒᵈ :=
  { OrderDual.instLinearOrder α, OrderDual.orderedCommMonoid with }

end OrderDual

