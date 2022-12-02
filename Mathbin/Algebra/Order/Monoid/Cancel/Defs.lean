/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathbin.Algebra.Order.Monoid.Defs

/-!
# Ordered cancellative monoids

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/774
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
-/

section OrderedCancelCommMonoid

variable [OrderedCancelCommMonoid α] {a b c d : α}

/- warning: ordered_cancel_comm_monoid.to_contravariant_class_le_left -> OrderedCancelCommMonoid.to_ContravariantClass_le_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : OrderedCancelCommMonoid.{u} α], ContravariantClass.{u, u} α α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α (CommMonoid.toMonoid.{u} α (OrderedCancelCommMonoid.toCommMonoid.{u} α _inst_1)))))) (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (OrderedCancelCommMonoid.toPartialOrder.{u} α _inst_1))))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.145 : OrderedCancelCommMonoid.{u} α], ContravariantClass.{u, u} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.158 : α) (x._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.160 : α) => HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α (CommMonoid.toMonoid.{u} α (OrderedCancelCommMonoid.toCommMonoid.{u} α inst._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.145))))) x._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.158 x._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.160) (fun (x._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.173 : α) (x._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.175 : α) => LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (OrderedCancelCommMonoid.toPartialOrder.{u} α inst._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.145))) x._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.173 x._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.175)
Case conversion may be inaccurate. Consider using '#align ordered_cancel_comm_monoid.to_contravariant_class_le_left OrderedCancelCommMonoid.to_ContravariantClass_le_leftₓ'. -/
-- see Note [lower instance priority]
@[to_additive]
instance (priority := 200) OrderedCancelCommMonoid.to_ContravariantClass_le_left :
    ContravariantClass α α (· * ·) (· ≤ ·) :=
  ⟨OrderedCancelCommMonoid.le_of_mul_le_mul_left⟩
#align
  ordered_cancel_comm_monoid.to_contravariant_class_le_left OrderedCancelCommMonoid.to_ContravariantClass_le_left

/- warning: ordered_cancel_comm_monoid.lt_of_mul_lt_mul_left -> OrderedCancelCommMonoid.lt_of_mul_lt_mul_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : OrderedCancelCommMonoid.{u} α] (a : α) (b : α) (c : α), (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (OrderedCancelCommMonoid.toPartialOrder.{u} α _inst_1))) (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α (CommMonoid.toMonoid.{u} α (OrderedCancelCommMonoid.toCommMonoid.{u} α _inst_1))))) a b) (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α (CommMonoid.toMonoid.{u} α (OrderedCancelCommMonoid.toCommMonoid.{u} α _inst_1))))) a c)) -> (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (OrderedCancelCommMonoid.toPartialOrder.{u} α _inst_1))) b c)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.196 : OrderedCancelCommMonoid.{u} α] (a : α) (b : α) (c : α), (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (OrderedCancelCommMonoid.toPartialOrder.{u} α inst._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.196))) (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α (CommMonoid.toMonoid.{u} α (OrderedCancelCommMonoid.toCommMonoid.{u} α inst._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.196))))) a b) (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α (CommMonoid.toMonoid.{u} α (OrderedCancelCommMonoid.toCommMonoid.{u} α inst._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.196))))) a c)) -> (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (OrderedCancelCommMonoid.toPartialOrder.{u} α inst._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.196))) b c)
Case conversion may be inaccurate. Consider using '#align ordered_cancel_comm_monoid.lt_of_mul_lt_mul_left OrderedCancelCommMonoid.lt_of_mul_lt_mul_leftₓ'. -/
@[to_additive]
theorem OrderedCancelCommMonoid.lt_of_mul_lt_mul_left : ∀ a b c : α, a * b < a * c → b < c :=
  fun a b c h =>
  lt_of_le_not_le (OrderedCancelCommMonoid.le_of_mul_le_mul_left a b c h.le) <|
    mt (fun h => OrderedCancelCommMonoid.mul_le_mul_left _ _ h _) (not_le_of_gt h)
#align
  ordered_cancel_comm_monoid.lt_of_mul_lt_mul_left OrderedCancelCommMonoid.lt_of_mul_lt_mul_left

/- warning: ordered_cancel_comm_monoid.to_contravariant_class_left -> OrderedCancelCommMonoid.to_ContravariantClass_left is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u_1}) [_inst_2 : OrderedCancelCommMonoid.{u_1} M], ContravariantClass.{u_1, u_1} M M (HMul.hMul.{u_1, u_1, u_1} M M M (instHMul.{u_1} M (MulOneClass.toHasMul.{u_1} M (Monoid.toMulOneClass.{u_1} M (CommMonoid.toMonoid.{u_1} M (OrderedCancelCommMonoid.toCommMonoid.{u_1} M _inst_2)))))) (LT.lt.{u_1} M (Preorder.toLT.{u_1} M (PartialOrder.toPreorder.{u_1} M (OrderedCancelCommMonoid.toPartialOrder.{u_1} M _inst_2))))
but is expected to have type
  forall (M : Type.{u_1}) [inst._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.272 : OrderedCancelCommMonoid.{u_1} M], ContravariantClass.{u_1, u_1} M M (fun (x._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.281 : M) (x._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.283 : M) => HMul.hMul.{u_1, u_1, u_1} M M M (instHMul.{u_1} M (MulOneClass.toMul.{u_1} M (Monoid.toMulOneClass.{u_1} M (CommMonoid.toMonoid.{u_1} M (OrderedCancelCommMonoid.toCommMonoid.{u_1} M inst._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.272))))) x._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.281 x._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.283) (fun (x._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.296 : M) (x._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.298 : M) => LT.lt.{u_1} M (Preorder.toLT.{u_1} M (PartialOrder.toPreorder.{u_1} M (OrderedCancelCommMonoid.toPartialOrder.{u_1} M inst._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.272))) x._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.296 x._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.298)
Case conversion may be inaccurate. Consider using '#align ordered_cancel_comm_monoid.to_contravariant_class_left OrderedCancelCommMonoid.to_ContravariantClass_leftₓ'. -/
@[to_additive]
instance OrderedCancelCommMonoid.to_ContravariantClass_left (M : Type _)
    [OrderedCancelCommMonoid M] :
    ContravariantClass M M (· * ·)
      (· < ·) where elim a b c := OrderedCancelCommMonoid.lt_of_mul_lt_mul_left _ _ _
#align
  ordered_cancel_comm_monoid.to_contravariant_class_left OrderedCancelCommMonoid.to_ContravariantClass_left

/- warning: ordered_cancel_comm_monoid.to_contravariant_class_right -> OrderedCancelCommMonoid.to_ContravariantClass_right is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u_1}) [_inst_2 : OrderedCancelCommMonoid.{u_1} M], ContravariantClass.{u_1, u_1} M M (Function.swap.{succ u_1, succ u_1, succ u_1} M M (fun (ᾰ : M) (ᾰ : M) => M) (HMul.hMul.{u_1, u_1, u_1} M M M (instHMul.{u_1} M (MulOneClass.toHasMul.{u_1} M (Monoid.toMulOneClass.{u_1} M (CommMonoid.toMonoid.{u_1} M (OrderedCancelCommMonoid.toCommMonoid.{u_1} M _inst_2))))))) (LT.lt.{u_1} M (Preorder.toLT.{u_1} M (PartialOrder.toPreorder.{u_1} M (OrderedCancelCommMonoid.toPartialOrder.{u_1} M _inst_2))))
but is expected to have type
  forall (M : Type.{u_1}) [inst._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.340 : OrderedCancelCommMonoid.{u_1} M], ContravariantClass.{u_1, u_1} M M (Function.swap.{succ u_1, succ u_1, succ u_1} M M (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.141 : M) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.139 : M) => M) (fun (x._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.352 : M) (x._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.354 : M) => HMul.hMul.{u_1, u_1, u_1} M M M (instHMul.{u_1} M (MulOneClass.toMul.{u_1} M (Monoid.toMulOneClass.{u_1} M (CommMonoid.toMonoid.{u_1} M (OrderedCancelCommMonoid.toCommMonoid.{u_1} M inst._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.340))))) x._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.352 x._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.354)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.367 : M) (x._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.369 : M) => LT.lt.{u_1} M (Preorder.toLT.{u_1} M (PartialOrder.toPreorder.{u_1} M (OrderedCancelCommMonoid.toPartialOrder.{u_1} M inst._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.340))) x._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.367 x._@.Mathlib.Algebra.Order.Monoid.Cancel.Defs._hyg.369)
Case conversion may be inaccurate. Consider using '#align ordered_cancel_comm_monoid.to_contravariant_class_right OrderedCancelCommMonoid.to_ContravariantClass_rightₓ'. -/
/- This instance can be proven with `by apply_instance`.  However, by analogy with the
instance `ordered_cancel_comm_monoid.to_covariant_class_right` above, I imagine that without
this instance, some Type would not have a `contravariant_class M M (function.swap (*)) (<)`
instance. -/
@[to_additive]
instance OrderedCancelCommMonoid.to_ContravariantClass_right (M : Type _)
    [OrderedCancelCommMonoid M] : ContravariantClass M M (swap (· * ·)) (· < ·) :=
  contravariant_swap_mul_lt_of_contravariant_mul_lt M
#align
  ordered_cancel_comm_monoid.to_contravariant_class_right OrderedCancelCommMonoid.to_ContravariantClass_right

#print OrderedCancelCommMonoid.toOrderedCommMonoid /-
-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) OrderedCancelCommMonoid.toOrderedCommMonoid : OrderedCommMonoid α :=
  { ‹OrderedCancelCommMonoid α› with }
#align ordered_cancel_comm_monoid.to_ordered_comm_monoid OrderedCancelCommMonoid.toOrderedCommMonoid
-/

#print OrderedCancelCommMonoid.toCancelCommMonoid /-
-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) OrderedCancelCommMonoid.toCancelCommMonoid : CancelCommMonoid α :=
  { ‹OrderedCancelCommMonoid α› with
    mul_left_cancel := fun a b c h =>
      (le_of_mul_le_mul_left' h.le).antisymm <| le_of_mul_le_mul_left' h.ge }
#align ordered_cancel_comm_monoid.to_cancel_comm_monoid OrderedCancelCommMonoid.toCancelCommMonoid
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
-/

