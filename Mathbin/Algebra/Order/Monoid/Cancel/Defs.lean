/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl

! This file was ported from Lean 3 source module algebra.order.monoid.cancel.defs
! leanprover-community/mathlib commit 509de852e1de55e1efa8eacfa11df0823f26f226
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Order.Monoid.Defs

/-!
# Ordered cancellative monoids

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


universe u

variable {α : Type u}

open Function

#print OrderedCancelAddCommMonoid /-
/-- An ordered cancellative additive commutative monoid
is an additive commutative monoid with a partial order,
in which addition is cancellative and monotone. -/
@[protect_proj]
class OrderedCancelAddCommMonoid (α : Type u) extends AddCommMonoid α, PartialOrder α where
  add_le_add_left : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b
  le_of_add_le_add_left : ∀ a b c : α, a + b ≤ a + c → b ≤ c
#align ordered_cancel_add_comm_monoid OrderedCancelAddCommMonoid
-/

#print OrderedCancelCommMonoid /-
/-- An ordered cancellative commutative monoid
is a commutative monoid with a partial order,
in which multiplication is cancellative and monotone. -/
@[protect_proj, to_additive]
class OrderedCancelCommMonoid (α : Type u) extends CommMonoid α, PartialOrder α where
  mul_le_mul_left : ∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b
  le_of_mul_le_mul_left : ∀ a b c : α, a * b ≤ a * c → b ≤ c
#align ordered_cancel_comm_monoid OrderedCancelCommMonoid
#align ordered_cancel_add_comm_monoid OrderedCancelAddCommMonoid
-/

section OrderedCancelCommMonoid

variable [OrderedCancelCommMonoid α] {a b c d : α}

/- warning: ordered_cancel_comm_monoid.to_contravariant_class_le_left -> OrderedCancelCommMonoid.to_contravariantClass_le_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCancelCommMonoid.{u1} α], ContravariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCancelCommMonoid.toCommMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelCommMonoid.toPartialOrder.{u1} α _inst_1))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCancelCommMonoid.{u1} α], ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.158 : α) (x._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.160 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCancelCommMonoid.toCommMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.158 x._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.160) (fun (x._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.173 : α) (x._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.175 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelCommMonoid.toPartialOrder.{u1} α _inst_1))) x._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.173 x._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.175)
Case conversion may be inaccurate. Consider using '#align ordered_cancel_comm_monoid.to_contravariant_class_le_left OrderedCancelCommMonoid.to_contravariantClass_le_leftₓ'. -/
-- see Note [lower instance priority]
@[to_additive]
instance (priority := 200) OrderedCancelCommMonoid.to_contravariantClass_le_left :
    ContravariantClass α α (· * ·) (· ≤ ·) :=
  ⟨OrderedCancelCommMonoid.le_of_mul_le_mul_left⟩
#align ordered_cancel_comm_monoid.to_contravariant_class_le_left OrderedCancelCommMonoid.to_contravariantClass_le_left
#align ordered_cancel_add_comm_monoid.to_contravariant_class_le_left OrderedCancelAddCommMonoid.to_contravariantClass_le_left

/- warning: ordered_cancel_comm_monoid.lt_of_mul_lt_mul_left -> OrderedCancelCommMonoid.lt_of_mul_lt_mul_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCancelCommMonoid.{u1} α] (a : α) (b : α) (c : α), (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelCommMonoid.toPartialOrder.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCancelCommMonoid.toCommMonoid.{u1} α _inst_1))))) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCancelCommMonoid.toCommMonoid.{u1} α _inst_1))))) a c)) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelCommMonoid.toPartialOrder.{u1} α _inst_1))) b c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCancelCommMonoid.{u1} α] (a : α) (b : α) (c : α), (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelCommMonoid.toPartialOrder.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCancelCommMonoid.toCommMonoid.{u1} α _inst_1))))) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCancelCommMonoid.toCommMonoid.{u1} α _inst_1))))) a c)) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelCommMonoid.toPartialOrder.{u1} α _inst_1))) b c)
Case conversion may be inaccurate. Consider using '#align ordered_cancel_comm_monoid.lt_of_mul_lt_mul_left OrderedCancelCommMonoid.lt_of_mul_lt_mul_leftₓ'. -/
@[to_additive]
theorem OrderedCancelCommMonoid.lt_of_mul_lt_mul_left : ∀ a b c : α, a * b < a * c → b < c :=
  fun a b c h =>
  lt_of_le_not_le (OrderedCancelCommMonoid.le_of_mul_le_mul_left a b c h.le) <|
    mt (fun h => OrderedCancelCommMonoid.mul_le_mul_left _ _ h _) (not_le_of_gt h)
#align ordered_cancel_comm_monoid.lt_of_mul_lt_mul_left OrderedCancelCommMonoid.lt_of_mul_lt_mul_left
#align ordered_cancel_add_comm_monoid.lt_of_add_lt_add_left OrderedCancelAddCommMonoid.lt_of_add_lt_add_left

/- warning: ordered_cancel_comm_monoid.to_contravariant_class_left -> OrderedCancelCommMonoid.to_contravariantClass_left is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) [_inst_2 : OrderedCancelCommMonoid.{u1} M], ContravariantClass.{u1, u1} M M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M (OrderedCancelCommMonoid.toCommMonoid.{u1} M _inst_2)))))) (LT.lt.{u1} M (Preorder.toLT.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedCancelCommMonoid.toPartialOrder.{u1} M _inst_2))))
but is expected to have type
  forall (M : Type.{u1}) [_inst_2 : OrderedCancelCommMonoid.{u1} M], ContravariantClass.{u1, u1} M M (fun (x._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.281 : M) (x._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.283 : M) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M (OrderedCancelCommMonoid.toCommMonoid.{u1} M _inst_2))))) x._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.281 x._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.283) (fun (x._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.296 : M) (x._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.298 : M) => LT.lt.{u1} M (Preorder.toLT.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedCancelCommMonoid.toPartialOrder.{u1} M _inst_2))) x._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.296 x._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.298)
Case conversion may be inaccurate. Consider using '#align ordered_cancel_comm_monoid.to_contravariant_class_left OrderedCancelCommMonoid.to_contravariantClass_leftₓ'. -/
@[to_additive]
instance OrderedCancelCommMonoid.to_contravariantClass_left (M : Type _)
    [OrderedCancelCommMonoid M] : ContravariantClass M M (· * ·) (· < ·)
    where elim a b c := OrderedCancelCommMonoid.lt_of_mul_lt_mul_left _ _ _
#align ordered_cancel_comm_monoid.to_contravariant_class_left OrderedCancelCommMonoid.to_contravariantClass_left
#align ordered_cancel_add_comm_monoid.to_contravariant_class_left OrderedCancelAddCommMonoid.to_contravariantClass_left

/- warning: ordered_cancel_comm_monoid.to_contravariant_class_right -> OrderedCancelCommMonoid.to_contravariantClass_right is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) [_inst_2 : OrderedCancelCommMonoid.{u1} M], ContravariantClass.{u1, u1} M M (Function.swap.{succ u1, succ u1, succ u1} M M (fun (ᾰ : M) (ᾰ : M) => M) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M (OrderedCancelCommMonoid.toCommMonoid.{u1} M _inst_2))))))) (LT.lt.{u1} M (Preorder.toLT.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedCancelCommMonoid.toPartialOrder.{u1} M _inst_2))))
but is expected to have type
  forall (M : Type.{u1}) [_inst_2 : OrderedCancelCommMonoid.{u1} M], ContravariantClass.{u1, u1} M M (Function.swap.{succ u1, succ u1, succ u1} M M (fun (ᾰ : M) (ᾰ : M) => M) (fun (x._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.352 : M) (x._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.354 : M) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M (OrderedCancelCommMonoid.toCommMonoid.{u1} M _inst_2))))) x._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.352 x._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.354)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.367 : M) (x._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.369 : M) => LT.lt.{u1} M (Preorder.toLT.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedCancelCommMonoid.toPartialOrder.{u1} M _inst_2))) x._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.367 x._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.369)
Case conversion may be inaccurate. Consider using '#align ordered_cancel_comm_monoid.to_contravariant_class_right OrderedCancelCommMonoid.to_contravariantClass_rightₓ'. -/
/- This instance can be proven with `by apply_instance`.  However, by analogy with the
instance `ordered_cancel_comm_monoid.to_covariant_class_right` above, I imagine that without
this instance, some Type would not have a `contravariant_class M M (function.swap (*)) (<)`
instance. -/
@[to_additive]
instance OrderedCancelCommMonoid.to_contravariantClass_right (M : Type _)
    [OrderedCancelCommMonoid M] : ContravariantClass M M (swap (· * ·)) (· < ·) :=
  contravariant_swap_mul_lt_of_contravariant_mul_lt M
#align ordered_cancel_comm_monoid.to_contravariant_class_right OrderedCancelCommMonoid.to_contravariantClass_right
#align ordered_cancel_add_comm_monoid.to_contravariant_class_right OrderedCancelAddCommMonoid.to_contravariantClass_right

#print OrderedCancelCommMonoid.toOrderedCommMonoid /-
-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) OrderedCancelCommMonoid.toOrderedCommMonoid : OrderedCommMonoid α :=
  { ‹OrderedCancelCommMonoid α› with }
#align ordered_cancel_comm_monoid.to_ordered_comm_monoid OrderedCancelCommMonoid.toOrderedCommMonoid
#align ordered_cancel_add_comm_monoid.to_ordered_comm_monoid OrderedCancelAddCommMonoid.toOrderedAddCommMonoid
-/

#print OrderedCancelCommMonoid.toCancelCommMonoid /-
-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) OrderedCancelCommMonoid.toCancelCommMonoid : CancelCommMonoid α :=
  { ‹OrderedCancelCommMonoid α› with
    mul_left_cancel := fun a b c h =>
      (le_of_mul_le_mul_left' h.le).antisymm <| le_of_mul_le_mul_left' h.ge }
#align ordered_cancel_comm_monoid.to_cancel_comm_monoid OrderedCancelCommMonoid.toCancelCommMonoid
#align ordered_cancel_add_comm_monoid.to_cancel_add_comm_monoid OrderedCancelAddCommMonoid.toCancelAddCommMonoid
-/

end OrderedCancelCommMonoid

#print LinearOrderedCancelAddCommMonoid /-
/-- A linearly ordered cancellative additive commutative monoid
is an additive commutative monoid with a decidable linear order
in which addition is cancellative and monotone. -/
@[protect_proj]
class LinearOrderedCancelAddCommMonoid (α : Type u) extends OrderedCancelAddCommMonoid α,
  LinearOrderedAddCommMonoid α
#align linear_ordered_cancel_add_comm_monoid LinearOrderedCancelAddCommMonoid
-/

#print LinearOrderedCancelCommMonoid /-
/-- A linearly ordered cancellative commutative monoid
is a commutative monoid with a linear order
in which multiplication is cancellative and monotone. -/
@[protect_proj, to_additive]
class LinearOrderedCancelCommMonoid (α : Type u) extends OrderedCancelCommMonoid α,
  LinearOrderedCommMonoid α
#align linear_ordered_cancel_comm_monoid LinearOrderedCancelCommMonoid
#align linear_ordered_cancel_add_comm_monoid LinearOrderedCancelAddCommMonoid
-/

