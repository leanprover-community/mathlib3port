/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl

! This file was ported from Lean 3 source module algebra.order.monoid.order_dual
! leanprover-community/mathlib commit 9aba7801eeecebb61f58a5763c2b6dd1b47dc6ef
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Group.OrderSynonym
import Mathbin.Algebra.Order.Monoid.Cancel.Defs

/-! # Ordered monoid structures on the order dual. 

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/786
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
-/

#print OrderDual.covariantClass_mul_le /-
@[to_additive]
instance covariantClass_mul_le [LE α] [Mul α] [c : CovariantClass α α (· * ·) (· ≤ ·)] :
    CovariantClass αᵒᵈ αᵒᵈ (· * ·) (· ≤ ·) :=
  ⟨c.1.flip⟩
#align order_dual.covariant_class_mul_le OrderDual.covariantClass_mul_le
-/

#print OrderDual.contravariantClass_swap_mul_le /-
@[to_additive]
instance contravariantClass_swap_mul_le [LE α] [Mul α]
    [c : ContravariantClass α α (swap (· * ·)) (· ≤ ·)] :
    ContravariantClass αᵒᵈ αᵒᵈ (swap (· * ·)) (· ≤ ·) :=
  ⟨c.1.flip⟩
#align order_dual.contravariant_class_swap_mul_le OrderDual.contravariantClass_swap_mul_le
-/

#print OrderDual.covariantClass_swap_mul_le /-
@[to_additive]
instance covariantClass_swap_mul_le [LE α] [Mul α] [c : CovariantClass α α (swap (· * ·)) (· ≤ ·)] :
    CovariantClass αᵒᵈ αᵒᵈ (swap (· * ·)) (· ≤ ·) :=
  ⟨c.1.flip⟩
#align order_dual.covariant_class_swap_mul_le OrderDual.covariantClass_swap_mul_le
-/

#print OrderDual.contravariantClass_mul_lt /-
@[to_additive]
instance contravariantClass_mul_lt [LT α] [Mul α] [c : ContravariantClass α α (· * ·) (· < ·)] :
    ContravariantClass αᵒᵈ αᵒᵈ (· * ·) (· < ·) :=
  ⟨c.1.flip⟩
#align order_dual.contravariant_class_mul_lt OrderDual.contravariantClass_mul_lt
-/

#print OrderDual.covariantClass_mul_lt /-
@[to_additive]
instance covariantClass_mul_lt [LT α] [Mul α] [c : CovariantClass α α (· * ·) (· < ·)] :
    CovariantClass αᵒᵈ αᵒᵈ (· * ·) (· < ·) :=
  ⟨c.1.flip⟩
#align order_dual.covariant_class_mul_lt OrderDual.covariantClass_mul_lt
-/

#print OrderDual.contravariantClass_swap_mul_lt /-
@[to_additive]
instance contravariantClass_swap_mul_lt [LT α] [Mul α]
    [c : ContravariantClass α α (swap (· * ·)) (· < ·)] :
    ContravariantClass αᵒᵈ αᵒᵈ (swap (· * ·)) (· < ·) :=
  ⟨c.1.flip⟩
#align order_dual.contravariant_class_swap_mul_lt OrderDual.contravariantClass_swap_mul_lt
-/

#print OrderDual.covariantClass_swap_mul_lt /-
@[to_additive]
instance covariantClass_swap_mul_lt [LT α] [Mul α] [c : CovariantClass α α (swap (· * ·)) (· < ·)] :
    CovariantClass αᵒᵈ αᵒᵈ (swap (· * ·)) (· < ·) :=
  ⟨c.1.flip⟩
#align order_dual.covariant_class_swap_mul_lt OrderDual.covariantClass_swap_mul_lt
-/

@[to_additive]
instance [OrderedCommMonoid α] : OrderedCommMonoid αᵒᵈ :=
  { OrderDual.partialOrder α, OrderDual.commMonoid with
    mul_le_mul_left := fun a b h c => mul_le_mul_left' h c }

/- warning: order_dual.ordered_cancel_comm_monoid.to_contravariant_class -> OrderDual.OrderedCancelCommMonoid.to_contravariantClass is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCancelCommMonoid.{u1} α], ContravariantClass.{u1, u1} (OrderDual.{u1} α) (OrderDual.{u1} α) (HMul.hMul.{u1, u1, u1} (OrderDual.{u1} α) (OrderDual.{u1} α) (OrderDual.{u1} α) (instHMul.{u1} (OrderDual.{u1} α) (OrderDual.hasMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α (OrderedCancelCommMonoid.toCancelCommMonoid.{u1} α _inst_1))))))))) (LE.le.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelCommMonoid.toPartialOrder.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCancelCommMonoid.{u1} α], ContravariantClass.{u1, u1} (OrderDual.{u1} α) (OrderDual.{u1} α) (Mul.mul.{u1} (OrderDual.{u1} α) (instMulOrderDual.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α (OrderedCancelCommMonoid.toCancelCommMonoid.{u1} α _inst_1)))))))) (LE.le.{u1} (OrderDual.{u1} α) (OrderDual.instLEOrderDual.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelCommMonoid.toPartialOrder.{u1} α _inst_1)))))
Case conversion may be inaccurate. Consider using '#align order_dual.ordered_cancel_comm_monoid.to_contravariant_class OrderDual.OrderedCancelCommMonoid.to_contravariantClassₓ'. -/
@[to_additive OrderedCancelAddCommMonoid.to_contravariant_class]
instance OrderedCancelCommMonoid.to_contravariantClass [OrderedCancelCommMonoid α] :
    ContravariantClass αᵒᵈ αᵒᵈ Mul.mul LE.le
    where elim a b c := OrderedCancelCommMonoid.le_of_mul_le_mul_left a c b
#align
  order_dual.ordered_cancel_comm_monoid.to_contravariant_class OrderDual.OrderedCancelCommMonoid.to_contravariantClass

@[to_additive]
instance [OrderedCancelCommMonoid α] : OrderedCancelCommMonoid αᵒᵈ :=
  { OrderDual.orderedCommMonoid, OrderDual.cancelCommMonoid with
    le_of_mul_le_mul_left := fun a b c : α => le_of_mul_le_mul_left' }

@[to_additive]
instance [LinearOrderedCancelCommMonoid α] : LinearOrderedCancelCommMonoid αᵒᵈ :=
  { OrderDual.linearOrder α, OrderDual.orderedCancelCommMonoid with }

@[to_additive]
instance [LinearOrderedCommMonoid α] : LinearOrderedCommMonoid αᵒᵈ :=
  { OrderDual.linearOrder α, OrderDual.orderedCommMonoid with }

end OrderDual

