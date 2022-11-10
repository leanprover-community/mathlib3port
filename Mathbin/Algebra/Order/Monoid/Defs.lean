/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathbin.Order.BoundedOrder
import Mathbin.Algebra.GroupWithZero.Defs
import Mathbin.Algebra.Order.ZeroLeOne

/-!
# Ordered monoids

This file provides the definitions of ordered monoids.

-/


open Function

universe u

variable {α : Type u} {β : Type _}

#print OrderedCommMonoid /-
/-- An ordered commutative monoid is a commutative monoid
with a partial order such that `a ≤ b → c * a ≤ c * b` (multiplication is monotone)
-/
@[protect_proj]
class OrderedCommMonoid (α : Type _) extends CommMonoid α, PartialOrder α where
  mul_le_mul_left : ∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b
-/

#print OrderedAddCommMonoid /-
/-- An ordered (additive) commutative monoid is a commutative monoid
  with a partial order such that `a ≤ b → c + a ≤ c + b` (addition is monotone)
-/
@[protect_proj]
class OrderedAddCommMonoid (α : Type _) extends AddCommMonoid α, PartialOrder α where
  add_le_add_left : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b
-/

attribute [to_additive] OrderedCommMonoid

section OrderedInstances

/- warning: ordered_comm_monoid.to_covariant_class_left -> OrderedCommMonoid.to_covariant_class_left is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u_1}) [_inst_1 : OrderedCommMonoid.{u_1} M], CovariantClass.{u_1 u_1} M M (HMul.hMul.{u_1 u_1 u_1} M M M (instHMul.{u_1} M (MulOneClass.toHasMul.{u_1} M (Monoid.toMulOneClass.{u_1} M (CommMonoid.toMonoid.{u_1} M (OrderedCommMonoid.toCommMonoid.{u_1} M _inst_1)))))) (LE.le.{u_1} M (Preorder.toLE.{u_1} M (PartialOrder.toPreorder.{u_1} M (OrderedCommMonoid.toPartialOrder.{u_1} M _inst_1))))
but is expected to have type
  forall (M : Type.{u_1}) [inst._@.Mathlib.Algebra.Order.Monoid._hyg.77 : OrderedCommMonoid.{u_1} M], CovariantClass.{u_1 u_1} M M (fun (x._@.Mathlib.Algebra.Order.Monoid._hyg.86 : M) (x._@.Mathlib.Algebra.Order.Monoid._hyg.88 : M) => HMul.hMul.{u_1 u_1 u_1} M M M (instHMul.{u_1} M (MulOneClass.toMul.{u_1} M (Monoid.toMulOneClass.{u_1} M (CommMonoid.toMonoid.{u_1} M (OrderedCommMonoid.toCommMonoid.{u_1} M inst._@.Mathlib.Algebra.Order.Monoid._hyg.77))))) x._@.Mathlib.Algebra.Order.Monoid._hyg.86 x._@.Mathlib.Algebra.Order.Monoid._hyg.88) (fun (x._@.Mathlib.Algebra.Order.Monoid._hyg.101 : M) (x._@.Mathlib.Algebra.Order.Monoid._hyg.103 : M) => LE.le.{u_1} M (Preorder.toLE.{u_1} M (PartialOrder.toPreorder.{u_1} M (OrderedCommMonoid.toPartialOrder.{u_1} M inst._@.Mathlib.Algebra.Order.Monoid._hyg.77))) x._@.Mathlib.Algebra.Order.Monoid._hyg.101 x._@.Mathlib.Algebra.Order.Monoid._hyg.103)
Case conversion may be inaccurate. Consider using '#align ordered_comm_monoid.to_covariant_class_left OrderedCommMonoid.to_covariant_class_leftₓ'. -/
@[to_additive]
instance OrderedCommMonoid.to_covariant_class_left (M : Type _) [OrderedCommMonoid M] :
    CovariantClass M M (· * ·) (· ≤ ·) where elim a b c bc := OrderedCommMonoid.mul_le_mul_left _ _ bc a

/- warning: ordered_comm_monoid.to_covariant_class_right -> OrderedCommMonoid.to_covariant_class_right is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u_1}) [_inst_1 : OrderedCommMonoid.{u_1} M], CovariantClass.{u_1 u_1} M M (Function.swap.{succ u_1 succ u_1 succ u_1} M M (fun (ᾰ : M) (ᾰ : M) => M) (HMul.hMul.{u_1 u_1 u_1} M M M (instHMul.{u_1} M (MulOneClass.toHasMul.{u_1} M (Monoid.toMulOneClass.{u_1} M (CommMonoid.toMonoid.{u_1} M (OrderedCommMonoid.toCommMonoid.{u_1} M _inst_1))))))) (LE.le.{u_1} M (Preorder.toLE.{u_1} M (PartialOrder.toPreorder.{u_1} M (OrderedCommMonoid.toPartialOrder.{u_1} M _inst_1))))
but is expected to have type
  forall (M : Type.{u_1}) [inst._@.Mathlib.Algebra.Order.Monoid._hyg.137 : OrderedCommMonoid.{u_1} M], CovariantClass.{u_1 u_1} M M (Function.swap.{succ u_1 succ u_1 succ u_1} M M (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : M) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : M) => M) (fun (x._@.Mathlib.Algebra.Order.Monoid._hyg.149 : M) (x._@.Mathlib.Algebra.Order.Monoid._hyg.151 : M) => HMul.hMul.{u_1 u_1 u_1} M M M (instHMul.{u_1} M (MulOneClass.toMul.{u_1} M (Monoid.toMulOneClass.{u_1} M (CommMonoid.toMonoid.{u_1} M (OrderedCommMonoid.toCommMonoid.{u_1} M inst._@.Mathlib.Algebra.Order.Monoid._hyg.137))))) x._@.Mathlib.Algebra.Order.Monoid._hyg.149 x._@.Mathlib.Algebra.Order.Monoid._hyg.151)) (fun (x._@.Mathlib.Algebra.Order.Monoid._hyg.164 : M) (x._@.Mathlib.Algebra.Order.Monoid._hyg.166 : M) => LE.le.{u_1} M (Preorder.toLE.{u_1} M (PartialOrder.toPreorder.{u_1} M (OrderedCommMonoid.toPartialOrder.{u_1} M inst._@.Mathlib.Algebra.Order.Monoid._hyg.137))) x._@.Mathlib.Algebra.Order.Monoid._hyg.164 x._@.Mathlib.Algebra.Order.Monoid._hyg.166)
Case conversion may be inaccurate. Consider using '#align ordered_comm_monoid.to_covariant_class_right OrderedCommMonoid.to_covariant_class_rightₓ'. -/
/- This instance can be proven with `by apply_instance`.  However, `with_bot ℕ` does not
pick up a `covariant_class M M (function.swap (*)) (≤)` instance without it (see PR #7940). -/
@[to_additive]
instance OrderedCommMonoid.to_covariant_class_right (M : Type _) [OrderedCommMonoid M] :
    CovariantClass M M (swap (· * ·)) (· ≤ ·) :=
  covariant_swap_mul_le_of_covariant_mul_le M

#print Mul.to_covariant_class_left /-
/- This is not an instance, to avoid creating a loop in the type-class system: in a
`left_cancel_semigroup` with a `partial_order`, assuming `covariant_class M M (*) (≤)` implies
`covariant_class M M (*) (<)`, see `left_cancel_semigroup.covariant_mul_lt_of_covariant_mul_le`. -/
@[to_additive]
theorem Mul.to_covariant_class_left (M : Type _) [Mul M] [PartialOrder M] [CovariantClass M M (· * ·) (· < ·)] :
    CovariantClass M M (· * ·) (· ≤ ·) :=
  ⟨covariant_le_of_covariant_lt _ _ _ CovariantClass.elim⟩
-/

#print Mul.to_covariant_class_right /-
/- This is not an instance, to avoid creating a loop in the type-class system: in a
`right_cancel_semigroup` with a `partial_order`, assuming `covariant_class M M (swap (*)) (<)`
implies `covariant_class M M (swap (*)) (≤)`, see
`right_cancel_semigroup.covariant_swap_mul_lt_of_covariant_swap_mul_le`. -/
@[to_additive]
theorem Mul.to_covariant_class_right (M : Type _) [Mul M] [PartialOrder M] [CovariantClass M M (swap (· * ·)) (· < ·)] :
    CovariantClass M M (swap (· * ·)) (· ≤ ·) :=
  ⟨covariant_le_of_covariant_lt _ _ _ CovariantClass.elim⟩
-/

end OrderedInstances

theorem bit0_pos [OrderedAddCommMonoid α] {a : α} (h : 0 < a) : 0 < bit0 a :=
  add_pos' h h

#print LinearOrderedAddCommMonoid /-
/-- A linearly ordered additive commutative monoid. -/
@[protect_proj]
class LinearOrderedAddCommMonoid (α : Type _) extends LinearOrder α, OrderedAddCommMonoid α
-/

#print LinearOrderedCommMonoid /-
/-- A linearly ordered commutative monoid. -/
@[protect_proj, to_additive]
class LinearOrderedCommMonoid (α : Type _) extends LinearOrder α, OrderedCommMonoid α
-/

/-- A linearly ordered commutative monoid with a zero element. -/
class LinearOrderedCommMonoidWithZero (α : Type _) extends LinearOrderedCommMonoid α, CommMonoidWithZero α where
  zero_le_one : (0 : α) ≤ 1

instance (priority := 100) LinearOrderedCommMonoidWithZero.zeroLeOneClass [h : LinearOrderedCommMonoidWithZero α] :
    ZeroLeOneClass α :=
  { h with }

/-- A linearly ordered commutative monoid with an additively absorbing `⊤` element.
  Instances should include number systems with an infinite element adjoined.` -/
@[protect_proj]
class LinearOrderedAddCommMonoidWithTop (α : Type _) extends LinearOrderedAddCommMonoid α, HasTop α where
  le_top : ∀ x : α, x ≤ ⊤
  top_add' : ∀ x : α, ⊤ + x = ⊤

-- see Note [lower instance priority]
instance (priority := 100) LinearOrderedAddCommMonoidWithTop.toOrderTop (α : Type u)
    [h : LinearOrderedAddCommMonoidWithTop α] : OrderTop α :=
  { h with }

section LinearOrderedAddCommMonoidWithTop

variable [LinearOrderedAddCommMonoidWithTop α] {a b : α}

@[simp]
theorem top_add (a : α) : ⊤ + a = ⊤ :=
  LinearOrderedAddCommMonoidWithTop.top_add' a

@[simp]
theorem add_top (a : α) : a + ⊤ = ⊤ :=
  trans (add_comm _ _) (top_add _)

end LinearOrderedAddCommMonoidWithTop

