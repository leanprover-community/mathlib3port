/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathbin.Algebra.Order.Monoid.Lemmas
import Mathbin.Order.BoundedOrder

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
#align ordered_comm_monoid OrderedCommMonoid
-/

#print OrderedAddCommMonoid /-
/-- An ordered (additive) commutative monoid is a commutative monoid
  with a partial order such that `a ≤ b → c + a ≤ c + b` (addition is monotone)
-/
@[protect_proj]
class OrderedAddCommMonoid (α : Type _) extends AddCommMonoid α, PartialOrder α where
  add_le_add_left : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b
#align ordered_add_comm_monoid OrderedAddCommMonoid
-/

attribute [to_additive] OrderedCommMonoid

section OrderedInstances

/- warning: ordered_comm_monoid.to_covariant_class_left -> OrderedCommMonoid.to_CovariantClass_left is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u_1}) [_inst_1 : OrderedCommMonoid.{u_1} M], CovariantClass.{u_1, u_1} M M (HMul.hMul.{u_1, u_1, u_1} M M M (instHMul.{u_1} M (MulOneClass.toHasMul.{u_1} M (Monoid.toMulOneClass.{u_1} M (CommMonoid.toMonoid.{u_1} M (OrderedCommMonoid.toCommMonoid.{u_1} M _inst_1)))))) (LE.le.{u_1} M (Preorder.toLE.{u_1} M (PartialOrder.toPreorder.{u_1} M (OrderedCommMonoid.toPartialOrder.{u_1} M _inst_1))))
but is expected to have type
  forall (M : Type.{u_1}) [inst._@.Mathlib.Algebra.Order.Monoid.Defs._hyg.95 : OrderedCommMonoid.{u_1} M], CovariantClass.{u_1, u_1} M M (fun (x._@.Mathlib.Algebra.Order.Monoid.Defs._hyg.104 : M) (x._@.Mathlib.Algebra.Order.Monoid.Defs._hyg.106 : M) => HMul.hMul.{u_1, u_1, u_1} M M M (instHMul.{u_1} M (MulOneClass.toMul.{u_1} M (Monoid.toMulOneClass.{u_1} M (CommMonoid.toMonoid.{u_1} M (OrderedCommMonoid.toCommMonoid.{u_1} M inst._@.Mathlib.Algebra.Order.Monoid.Defs._hyg.95))))) x._@.Mathlib.Algebra.Order.Monoid.Defs._hyg.104 x._@.Mathlib.Algebra.Order.Monoid.Defs._hyg.106) (fun (x._@.Mathlib.Algebra.Order.Monoid.Defs._hyg.119 : M) (x._@.Mathlib.Algebra.Order.Monoid.Defs._hyg.121 : M) => LE.le.{u_1} M (Preorder.toLE.{u_1} M (PartialOrder.toPreorder.{u_1} M (OrderedCommMonoid.toPartialOrder.{u_1} M inst._@.Mathlib.Algebra.Order.Monoid.Defs._hyg.95))) x._@.Mathlib.Algebra.Order.Monoid.Defs._hyg.119 x._@.Mathlib.Algebra.Order.Monoid.Defs._hyg.121)
Case conversion may be inaccurate. Consider using '#align ordered_comm_monoid.to_covariant_class_left OrderedCommMonoid.to_CovariantClass_leftₓ'. -/
@[to_additive]
instance OrderedCommMonoid.to_CovariantClass_left (M : Type _) [OrderedCommMonoid M] :
    CovariantClass M M (· * ·)
      (· ≤ ·) where elim a b c bc := OrderedCommMonoid.mul_le_mul_left _ _ bc a
#align ordered_comm_monoid.to_covariant_class_left OrderedCommMonoid.to_CovariantClass_left

/- warning: ordered_comm_monoid.to_covariant_class_right -> OrderedCommMonoid.to_CovariantClass_right is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u_1}) [_inst_1 : OrderedCommMonoid.{u_1} M], CovariantClass.{u_1, u_1} M M (Function.swap.{succ u_1, succ u_1, succ u_1} M M (fun (ᾰ : M) (ᾰ : M) => M) (HMul.hMul.{u_1, u_1, u_1} M M M (instHMul.{u_1} M (MulOneClass.toHasMul.{u_1} M (Monoid.toMulOneClass.{u_1} M (CommMonoid.toMonoid.{u_1} M (OrderedCommMonoid.toCommMonoid.{u_1} M _inst_1))))))) (LE.le.{u_1} M (Preorder.toLE.{u_1} M (PartialOrder.toPreorder.{u_1} M (OrderedCommMonoid.toPartialOrder.{u_1} M _inst_1))))
but is expected to have type
  forall (M : Type.{u_1}) [inst._@.Mathlib.Algebra.Order.Monoid.Defs._hyg.160 : OrderedCommMonoid.{u_1} M], CovariantClass.{u_1, u_1} M M (Function.swap.{succ u_1, succ u_1, succ u_1} M M (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : M) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : M) => M) (fun (x._@.Mathlib.Algebra.Order.Monoid.Defs._hyg.172 : M) (x._@.Mathlib.Algebra.Order.Monoid.Defs._hyg.174 : M) => HMul.hMul.{u_1, u_1, u_1} M M M (instHMul.{u_1} M (MulOneClass.toMul.{u_1} M (Monoid.toMulOneClass.{u_1} M (CommMonoid.toMonoid.{u_1} M (OrderedCommMonoid.toCommMonoid.{u_1} M inst._@.Mathlib.Algebra.Order.Monoid.Defs._hyg.160))))) x._@.Mathlib.Algebra.Order.Monoid.Defs._hyg.172 x._@.Mathlib.Algebra.Order.Monoid.Defs._hyg.174)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Defs._hyg.187 : M) (x._@.Mathlib.Algebra.Order.Monoid.Defs._hyg.189 : M) => LE.le.{u_1} M (Preorder.toLE.{u_1} M (PartialOrder.toPreorder.{u_1} M (OrderedCommMonoid.toPartialOrder.{u_1} M inst._@.Mathlib.Algebra.Order.Monoid.Defs._hyg.160))) x._@.Mathlib.Algebra.Order.Monoid.Defs._hyg.187 x._@.Mathlib.Algebra.Order.Monoid.Defs._hyg.189)
Case conversion may be inaccurate. Consider using '#align ordered_comm_monoid.to_covariant_class_right OrderedCommMonoid.to_CovariantClass_rightₓ'. -/
/- This instance can be proven with `by apply_instance`.  However, `with_bot ℕ` does not
pick up a `covariant_class M M (function.swap (*)) (≤)` instance without it (see PR #7940). -/
@[to_additive]
instance OrderedCommMonoid.to_CovariantClass_right (M : Type _) [OrderedCommMonoid M] :
    CovariantClass M M (swap (· * ·)) (· ≤ ·) :=
  covariant_swap_mul_le_of_covariant_mul_le M
#align ordered_comm_monoid.to_covariant_class_right OrderedCommMonoid.to_CovariantClass_right

#print Mul.to_CovariantClass_left /-
/- This is not an instance, to avoid creating a loop in the type-class system: in a
`left_cancel_semigroup` with a `partial_order`, assuming `covariant_class M M (*) (≤)` implies
`covariant_class M M (*) (<)`, see `left_cancel_semigroup.covariant_mul_lt_of_covariant_mul_le`. -/
@[to_additive]
theorem Mul.to_CovariantClass_left (M : Type _) [Mul M] [PartialOrder M]
    [CovariantClass M M (· * ·) (· < ·)] : CovariantClass M M (· * ·) (· ≤ ·) :=
  ⟨covariant_le_of_covariant_lt _ _ _ CovariantClass.elim⟩
#align has_mul.to_covariant_class_left Mul.to_CovariantClass_left
-/

#print Mul.to_CovariantClass_right /-
/- This is not an instance, to avoid creating a loop in the type-class system: in a
`right_cancel_semigroup` with a `partial_order`, assuming `covariant_class M M (swap (*)) (<)`
implies `covariant_class M M (swap (*)) (≤)`, see
`right_cancel_semigroup.covariant_swap_mul_lt_of_covariant_swap_mul_le`. -/
@[to_additive]
theorem Mul.to_CovariantClass_right (M : Type _) [Mul M] [PartialOrder M]
    [CovariantClass M M (swap (· * ·)) (· < ·)] : CovariantClass M M (swap (· * ·)) (· ≤ ·) :=
  ⟨covariant_le_of_covariant_lt _ _ _ CovariantClass.elim⟩
#align has_mul.to_covariant_class_right Mul.to_CovariantClass_right
-/

end OrderedInstances

/- warning: bit0_pos -> bit0_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : OrderedAddCommMonoid.{u} α] {a : α}, (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (OrderedAddCommMonoid.toPartialOrder.{u} α _inst_1))) (OfNat.ofNat.{u} α 0 (OfNat.mk.{u} α 0 (Zero.zero.{u} α (AddZeroClass.toHasZero.{u} α (AddMonoid.toAddZeroClass.{u} α (AddCommMonoid.toAddMonoid.{u} α (OrderedAddCommMonoid.toAddCommMonoid.{u} α _inst_1))))))) a) -> (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (OrderedAddCommMonoid.toPartialOrder.{u} α _inst_1))) (OfNat.ofNat.{u} α 0 (OfNat.mk.{u} α 0 (Zero.zero.{u} α (AddZeroClass.toHasZero.{u} α (AddMonoid.toAddZeroClass.{u} α (AddCommMonoid.toAddMonoid.{u} α (OrderedAddCommMonoid.toAddCommMonoid.{u} α _inst_1))))))) (bit0.{u} α (AddZeroClass.toHasAdd.{u} α (AddMonoid.toAddZeroClass.{u} α (AddCommMonoid.toAddMonoid.{u} α (OrderedAddCommMonoid.toAddCommMonoid.{u} α _inst_1)))) a))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Order.Monoid.Defs._hyg.399 : OrderedAddCommMonoid.{u} α] {a : α}, (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (OrderedAddCommMonoid.toPartialOrder.{u} α inst._@.Mathlib.Algebra.Order.Monoid.Defs._hyg.399))) (OfNat.ofNat.{u} α 0 (Zero.toOfNat0.{u} α (AddMonoid.toZero.{u} α (AddCommMonoid.toAddMonoid.{u} α (OrderedAddCommMonoid.toAddCommMonoid.{u} α inst._@.Mathlib.Algebra.Order.Monoid.Defs._hyg.399))))) a) -> (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (OrderedAddCommMonoid.toPartialOrder.{u} α inst._@.Mathlib.Algebra.Order.Monoid.Defs._hyg.399))) (OfNat.ofNat.{u} α 0 (Zero.toOfNat0.{u} α (AddMonoid.toZero.{u} α (AddCommMonoid.toAddMonoid.{u} α (OrderedAddCommMonoid.toAddCommMonoid.{u} α inst._@.Mathlib.Algebra.Order.Monoid.Defs._hyg.399))))) (bit0.{u} α (AddZeroClass.toAdd.{u} α (AddMonoid.toAddZeroClass.{u} α (AddCommMonoid.toAddMonoid.{u} α (OrderedAddCommMonoid.toAddCommMonoid.{u} α inst._@.Mathlib.Algebra.Order.Monoid.Defs._hyg.399)))) a))
Case conversion may be inaccurate. Consider using '#align bit0_pos bit0_posₓ'. -/
theorem bit0_pos [OrderedAddCommMonoid α] {a : α} (h : 0 < a) : 0 < bit0 a :=
  add_pos' h h
#align bit0_pos bit0_pos

#print LinearOrderedAddCommMonoid /-
/-- A linearly ordered additive commutative monoid. -/
@[protect_proj]
class LinearOrderedAddCommMonoid (α : Type _) extends LinearOrder α, OrderedAddCommMonoid α
#align linear_ordered_add_comm_monoid LinearOrderedAddCommMonoid
-/

#print LinearOrderedCommMonoid /-
/-- A linearly ordered commutative monoid. -/
@[protect_proj, to_additive]
class LinearOrderedCommMonoid (α : Type _) extends LinearOrder α, OrderedCommMonoid α
#align linear_ordered_comm_monoid LinearOrderedCommMonoid
-/

#print LinearOrderedAddCommMonoidWithTop /-
/-- A linearly ordered commutative monoid with an additively absorbing `⊤` element.
  Instances should include number systems with an infinite element adjoined.` -/
@[protect_proj]
class LinearOrderedAddCommMonoidWithTop (α : Type _) extends LinearOrderedAddCommMonoid α,
  Top α where
  le_top : ∀ x : α, x ≤ ⊤
  top_add' : ∀ x : α, ⊤ + x = ⊤
#align linear_ordered_add_comm_monoid_with_top LinearOrderedAddCommMonoidWithTop
-/

#print LinearOrderedAddCommMonoidWithTop.toOrderTop /-
-- see Note [lower instance priority]
instance (priority := 100) LinearOrderedAddCommMonoidWithTop.toOrderTop (α : Type u)
    [h : LinearOrderedAddCommMonoidWithTop α] : OrderTop α :=
  { h with }
#align
  linear_ordered_add_comm_monoid_with_top.to_order_top LinearOrderedAddCommMonoidWithTop.toOrderTop
-/

section LinearOrderedAddCommMonoidWithTop

variable [LinearOrderedAddCommMonoidWithTop α] {a b : α}

/- warning: top_add -> top_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrderedAddCommMonoidWithTop.{u} α] (a : α), Eq.{succ u} α (HAdd.hAdd.{u, u, u} α α α (instHAdd.{u} α (AddZeroClass.toHasAdd.{u} α (AddMonoid.toAddZeroClass.{u} α (AddCommMonoid.toAddMonoid.{u} α (OrderedAddCommMonoid.toAddCommMonoid.{u} α (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u} α (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{u} α _inst_1))))))) (Top.top.{u} α (LinearOrderedAddCommMonoidWithTop.toHasTop.{u} α _inst_1)) a) (Top.top.{u} α (LinearOrderedAddCommMonoidWithTop.toHasTop.{u} α _inst_1))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Order.Monoid.Defs._hyg.521 : LinearOrderedAddCommMonoidWithTop.{u} α] (a : α), Eq.{succ u} α (HAdd.hAdd.{u, u, u} α α α (instHAdd.{u} α (AddZeroClass.toAdd.{u} α (AddMonoid.toAddZeroClass.{u} α (AddCommMonoid.toAddMonoid.{u} α (LinearOrderedAddCommMonoid.toAddCommMonoid.{u} α (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{u} α inst._@.Mathlib.Algebra.Order.Monoid.Defs._hyg.521)))))) (Top.top.{u} α (LinearOrderedAddCommMonoidWithTop.toTop.{u} α inst._@.Mathlib.Algebra.Order.Monoid.Defs._hyg.521)) a) (Top.top.{u} α (LinearOrderedAddCommMonoidWithTop.toTop.{u} α inst._@.Mathlib.Algebra.Order.Monoid.Defs._hyg.521))
Case conversion may be inaccurate. Consider using '#align top_add top_addₓ'. -/
@[simp]
theorem top_add (a : α) : ⊤ + a = ⊤ :=
  LinearOrderedAddCommMonoidWithTop.top_add' a
#align top_add top_add

/- warning: add_top -> add_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrderedAddCommMonoidWithTop.{u} α] (a : α), Eq.{succ u} α (HAdd.hAdd.{u, u, u} α α α (instHAdd.{u} α (AddZeroClass.toHasAdd.{u} α (AddMonoid.toAddZeroClass.{u} α (AddCommMonoid.toAddMonoid.{u} α (OrderedAddCommMonoid.toAddCommMonoid.{u} α (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u} α (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{u} α _inst_1))))))) a (Top.top.{u} α (LinearOrderedAddCommMonoidWithTop.toHasTop.{u} α _inst_1))) (Top.top.{u} α (LinearOrderedAddCommMonoidWithTop.toHasTop.{u} α _inst_1))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Order.Monoid.Defs._hyg.546 : LinearOrderedAddCommMonoidWithTop.{u} α] (a : α), Eq.{succ u} α (HAdd.hAdd.{u, u, u} α α α (instHAdd.{u} α (AddZeroClass.toAdd.{u} α (AddMonoid.toAddZeroClass.{u} α (AddCommMonoid.toAddMonoid.{u} α (LinearOrderedAddCommMonoid.toAddCommMonoid.{u} α (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{u} α inst._@.Mathlib.Algebra.Order.Monoid.Defs._hyg.546)))))) a (Top.top.{u} α (LinearOrderedAddCommMonoidWithTop.toTop.{u} α inst._@.Mathlib.Algebra.Order.Monoid.Defs._hyg.546))) (Top.top.{u} α (LinearOrderedAddCommMonoidWithTop.toTop.{u} α inst._@.Mathlib.Algebra.Order.Monoid.Defs._hyg.546))
Case conversion may be inaccurate. Consider using '#align add_top add_topₓ'. -/
@[simp]
theorem add_top (a : α) : a + ⊤ = ⊤ :=
  trans (add_comm _ _) (top_add _)
#align add_top add_top

end LinearOrderedAddCommMonoidWithTop

