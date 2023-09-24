/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Algebra.Order.Monoid.Defs

#align_import algebra.order.monoid.cancel.defs from "leanprover-community/mathlib"@"448144f7ae193a8990cb7473c9e9a01990f64ac7"

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

#print OrderedCancelCommMonoid.to_contravariantClass_le_left /-
-- see Note [lower instance priority]
@[to_additive]
instance (priority := 200) OrderedCancelCommMonoid.to_contravariantClass_le_left :
    ContravariantClass α α (· * ·) (· ≤ ·) :=
  ⟨OrderedCancelCommMonoid.le_of_hMul_le_hMul_left⟩
#align ordered_cancel_comm_monoid.to_contravariant_class_le_left OrderedCancelCommMonoid.to_contravariantClass_le_left
#align ordered_cancel_add_comm_monoid.to_contravariant_class_le_left OrderedCancelAddCommMonoid.to_contravariantClass_le_left
-/

#print OrderedCancelCommMonoid.lt_of_mul_lt_mul_left /-
@[to_additive]
theorem OrderedCancelCommMonoid.lt_of_mul_lt_mul_left : ∀ a b c : α, a * b < a * c → b < c :=
  fun a b c h =>
  lt_of_le_not_le (OrderedCancelCommMonoid.le_of_hMul_le_hMul_left a b c h.le) <|
    mt (fun h => OrderedCancelCommMonoid.hMul_le_hMul_left _ _ h _) (not_le_of_gt h)
#align ordered_cancel_comm_monoid.lt_of_mul_lt_mul_left OrderedCancelCommMonoid.lt_of_mul_lt_mul_left
#align ordered_cancel_add_comm_monoid.lt_of_add_lt_add_left OrderedCancelAddCommMonoid.lt_of_add_lt_add_left
-/

#print OrderedCancelCommMonoid.to_contravariantClass_left /-
@[to_additive]
instance OrderedCancelCommMonoid.to_contravariantClass_left (M : Type _)
    [OrderedCancelCommMonoid M] : ContravariantClass M M (· * ·) (· < ·)
    where elim a b c := OrderedCancelCommMonoid.lt_of_mul_lt_mul_left _ _ _
#align ordered_cancel_comm_monoid.to_contravariant_class_left OrderedCancelCommMonoid.to_contravariantClass_left
#align ordered_cancel_add_comm_monoid.to_contravariant_class_left OrderedCancelAddCommMonoid.to_contravariantClass_left
-/

#print OrderedCancelCommMonoid.to_contravariantClass_right /-
/- This instance can be proven with `by apply_instance`.  However, by analogy with the
instance `ordered_cancel_comm_monoid.to_covariant_class_right` above, I imagine that without
this instance, some Type would not have a `contravariant_class M M (function.swap (*)) (<)`
instance. -/
@[to_additive]
instance OrderedCancelCommMonoid.to_contravariantClass_right (M : Type _)
    [OrderedCancelCommMonoid M] : ContravariantClass M M (swap (· * ·)) (· < ·) :=
  contravariant_swap_hMul_lt_of_contravariant_hMul_lt M
#align ordered_cancel_comm_monoid.to_contravariant_class_right OrderedCancelCommMonoid.to_contravariantClass_right
#align ordered_cancel_add_comm_monoid.to_contravariant_class_right OrderedCancelAddCommMonoid.to_contravariantClass_right
-/

#print OrderedCancelCommMonoid.toOrderedCommMonoid /-
-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) OrderedCancelCommMonoid.toOrderedCommMonoid : OrderedCommMonoid α :=
  { ‹OrderedCancelCommMonoid α› with }
#align ordered_cancel_comm_monoid.to_ordered_comm_monoid OrderedCancelCommMonoid.toOrderedCommMonoid
#align ordered_cancel_add_comm_monoid.to_ordered_add_comm_monoid OrderedCancelAddCommMonoid.toOrderedAddCommMonoid
-/

#print OrderedCancelCommMonoid.toCancelCommMonoid /-
-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) OrderedCancelCommMonoid.toCancelCommMonoid : CancelCommMonoid α :=
  { ‹OrderedCancelCommMonoid α› with
    hMul_left_cancel := fun a b c h =>
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

