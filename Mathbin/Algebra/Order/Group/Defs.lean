/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl

! This file was ported from Lean 3 source module algebra.order.group.defs
! leanprover-community/mathlib commit ffc3730d545623aedf5d5bd46a3153cbf41f6c2c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Hom.Basic
import Mathbin.Algebra.Order.Sub.Defs
import Mathbin.Algebra.Order.Monoid.Cancel.Defs

/-!
# Ordered groups

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/869
> Any changes to this file require a corresponding PR to mathlib4.

This file develops the basics of ordered groups.

## Implementation details

Unfortunately, the number of `'` appended to lemmas in this file
may differ between the multiplicative and the additive version of a lemma.
The reason is that we did not want to change existing names in the library.
-/


open Function

universe u

variable {α : Type u}

#print OrderedAddCommGroup /-
/-- An ordered additive commutative group is an additive commutative group
with a partial order in which addition is strictly monotone. -/
@[protect_proj]
class OrderedAddCommGroup (α : Type u) extends AddCommGroup α, PartialOrder α where
  add_le_add_left : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b
#align ordered_add_comm_group OrderedAddCommGroup
-/

#print OrderedCommGroup /-
/-- An ordered commutative group is an commutative group
with a partial order in which multiplication is strictly monotone. -/
@[protect_proj]
class OrderedCommGroup (α : Type u) extends CommGroup α, PartialOrder α where
  mul_le_mul_left : ∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b
#align ordered_comm_group OrderedCommGroup
-/

attribute [to_additive] OrderedCommGroup

/- warning: ordered_comm_group.to_covariant_class_left_le -> OrderedCommGroup.to_covariantClass_left_le is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : OrderedCommGroup.{u1} α], CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))))
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : OrderedCommGroup.{u1} α], CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.96 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.98 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1))))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.96 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.98) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.111 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.113 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.111 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.113)
Case conversion may be inaccurate. Consider using '#align ordered_comm_group.to_covariant_class_left_le OrderedCommGroup.to_covariantClass_left_leₓ'. -/
@[to_additive]
instance OrderedCommGroup.to_covariantClass_left_le (α : Type u) [OrderedCommGroup α] :
    CovariantClass α α (· * ·) (· ≤ ·)
    where elim a b c bc := OrderedCommGroup.mul_le_mul_left b c bc a
#align ordered_comm_group.to_covariant_class_left_le OrderedCommGroup.to_covariantClass_left_le

#print OrderedCommGroup.to_OrderedCancelCommMonoid /-
-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) OrderedCommGroup.to_OrderedCancelCommMonoid [OrderedCommGroup α] :
    OrderedCancelCommMonoid α :=
  { ‹OrderedCommGroup α› with le_of_mul_le_mul_left := fun a b c => le_of_mul_le_mul_left' }
#align ordered_comm_group.to_ordered_cancel_comm_monoid OrderedCommGroup.to_OrderedCancelCommMonoid
-/

example (α : Type u) [OrderedAddCommGroup α] : CovariantClass α α (swap (· + ·)) (· < ·) :=
  AddRightCancelSemigroup.covariant_swap_add_lt_of_covariant_swap_add_le α

/- warning: ordered_comm_group.to_contravariant_class_left_le -> OrderedCommGroup.to_contravariantClass_left_le is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : OrderedCommGroup.{u1} α], ContravariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))))
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : OrderedCommGroup.{u1} α], ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.245 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.247 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1))))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.245 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.247) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.260 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.262 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.260 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.262)
Case conversion may be inaccurate. Consider using '#align ordered_comm_group.to_contravariant_class_left_le OrderedCommGroup.to_contravariantClass_left_leₓ'. -/
/-- A choice-free shortcut instance. -/
@[to_additive "A choice-free shortcut instance."]
instance OrderedCommGroup.to_contravariantClass_left_le (α : Type u) [OrderedCommGroup α] :
    ContravariantClass α α (· * ·) (· ≤ ·)
    where elim a b c bc := by simpa using mul_le_mul_left' bc a⁻¹
#align
  ordered_comm_group.to_contravariant_class_left_le OrderedCommGroup.to_contravariantClass_left_le

/- warning: ordered_comm_group.to_contravariant_class_right_le -> OrderedCommGroup.to_contravariantClass_right_le is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : OrderedCommGroup.{u1} α], ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1))))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))))
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : OrderedCommGroup.{u1} α], ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.315 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.317 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1))))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.315 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.317)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.330 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.332 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.330 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.332)
Case conversion may be inaccurate. Consider using '#align ordered_comm_group.to_contravariant_class_right_le OrderedCommGroup.to_contravariantClass_right_leₓ'. -/
/-- A choice-free shortcut instance. -/
@[to_additive "A choice-free shortcut instance."]
instance OrderedCommGroup.to_contravariantClass_right_le (α : Type u) [OrderedCommGroup α] :
    ContravariantClass α α (swap (· * ·)) (· ≤ ·)
    where elim a b c bc := by simpa using mul_le_mul_right' bc a⁻¹
#align
  ordered_comm_group.to_contravariant_class_right_le OrderedCommGroup.to_contravariantClass_right_le

section Group

variable [Group α]

section TypeclassesLeftLe

variable [LE α] [CovariantClass α α (· * ·) (· ≤ ·)] {a b c d : α}

/- warning: left.inv_le_one_iff -> Left.inv_le_one_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α _inst_2)] {a : α}, Iff (LE.le.{u1} α _inst_2 (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))))) (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.445 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.447 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.445 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.447) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.460 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.462 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.460 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.462)] {a : α}, Iff (LE.le.{u1} α _inst_2 (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) a)
Case conversion may be inaccurate. Consider using '#align left.inv_le_one_iff Left.inv_le_one_iffₓ'. -/
/-- Uses `left` co(ntra)variant. -/
@[simp, to_additive Left.neg_nonpos_iff "Uses `left` co(ntra)variant."]
theorem Left.inv_le_one_iff : a⁻¹ ≤ 1 ↔ 1 ≤ a :=
  by
  rw [← mul_le_mul_iff_left a]
  simp
#align left.inv_le_one_iff Left.inv_le_one_iff

/- warning: left.one_le_inv_iff -> Left.one_le_inv_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α _inst_2)] {a : α}, Iff (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a)) (LE.le.{u1} α _inst_2 a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.547 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.549 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.547 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.549) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.562 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.564 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.562 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.564)] {a : α}, Iff (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a)) (LE.le.{u1} α _inst_2 a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align left.one_le_inv_iff Left.one_le_inv_iffₓ'. -/
/-- Uses `left` co(ntra)variant. -/
@[simp, to_additive Left.nonneg_neg_iff "Uses `left` co(ntra)variant."]
theorem Left.one_le_inv_iff : 1 ≤ a⁻¹ ↔ a ≤ 1 :=
  by
  rw [← mul_le_mul_iff_left a]
  simp
#align left.one_le_inv_iff Left.one_le_inv_iff

/- warning: le_inv_mul_iff_mul_le -> le_inv_mul_iff_mul_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α _inst_2 b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) c)) (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a b) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.646 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.648 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.646 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.648) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.661 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.663 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.661 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.663)] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α _inst_2 b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) c)) (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a b) c)
Case conversion may be inaccurate. Consider using '#align le_inv_mul_iff_mul_le le_inv_mul_iff_mul_leₓ'. -/
@[simp, to_additive]
theorem le_inv_mul_iff_mul_le : b ≤ a⁻¹ * c ↔ a * b ≤ c :=
  by
  rw [← mul_le_mul_iff_left a]
  simp
#align le_inv_mul_iff_mul_le le_inv_mul_iff_mul_le

/- warning: inv_mul_le_iff_le_mul -> inv_mul_le_iff_le_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b) a) c) (LE.le.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.748 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.750 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.748 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.750) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.763 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.765 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.763 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.765)] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b) a) c) (LE.le.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b c))
Case conversion may be inaccurate. Consider using '#align inv_mul_le_iff_le_mul inv_mul_le_iff_le_mulₓ'. -/
@[simp, to_additive]
theorem inv_mul_le_iff_le_mul : b⁻¹ * a ≤ c ↔ a ≤ b * c := by
  rw [← mul_le_mul_iff_left b, mul_inv_cancel_left]
#align inv_mul_le_iff_le_mul inv_mul_le_iff_le_mul

/- warning: inv_le_iff_one_le_mul' -> inv_le_iff_one_le_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) b) (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.846 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.848 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.846 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.848) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.861 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.863 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.861 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.863)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) b) (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a b))
Case conversion may be inaccurate. Consider using '#align inv_le_iff_one_le_mul' inv_le_iff_one_le_mul'ₓ'. -/
@[to_additive neg_le_iff_add_nonneg']
theorem inv_le_iff_one_le_mul' : a⁻¹ ≤ b ↔ 1 ≤ a * b :=
  (mul_le_mul_iff_left a).symm.trans <| by rw [mul_inv_self]
#align inv_le_iff_one_le_mul' inv_le_iff_one_le_mul'

/- warning: le_inv_iff_mul_le_one_left -> le_inv_iff_mul_le_one_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 a (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b)) (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b a) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.947 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.949 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.947 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.949) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.962 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.964 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.962 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.964)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 a (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b)) (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b a) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align le_inv_iff_mul_le_one_left le_inv_iff_mul_le_one_leftₓ'. -/
@[to_additive]
theorem le_inv_iff_mul_le_one_left : a ≤ b⁻¹ ↔ b * a ≤ 1 :=
  (mul_le_mul_iff_left b).symm.trans <| by rw [mul_inv_self]
#align le_inv_iff_mul_le_one_left le_inv_iff_mul_le_one_left

/- warning: le_inv_mul_iff_le -> le_inv_mul_iff_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b) a)) (LE.le.{u1} α _inst_2 b a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1048 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1050 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1048 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1050) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1063 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1065 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1063 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1065)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b) a)) (LE.le.{u1} α _inst_2 b a)
Case conversion may be inaccurate. Consider using '#align le_inv_mul_iff_le le_inv_mul_iff_leₓ'. -/
@[to_additive]
theorem le_inv_mul_iff_le : 1 ≤ b⁻¹ * a ↔ b ≤ a := by
  rw [← mul_le_mul_iff_left b, mul_one, mul_inv_cancel_left]
#align le_inv_mul_iff_le le_inv_mul_iff_le

/- warning: inv_mul_le_one_iff -> inv_mul_le_one_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))))) (LE.le.{u1} α _inst_2 b a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1145 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1147 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1145 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1147) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1160 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1162 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1160 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1162)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2 b a)
Case conversion may be inaccurate. Consider using '#align inv_mul_le_one_iff inv_mul_le_one_iffₓ'. -/
@[to_additive]
theorem inv_mul_le_one_iff : a⁻¹ * b ≤ 1 ↔ b ≤ a :=
  trans inv_mul_le_iff_le_mul <| by rw [mul_one]
#align inv_mul_le_one_iff inv_mul_le_one_iff

end TypeclassesLeftLe

section TypeclassesLeftLt

variable [LT α] [CovariantClass α α (· * ·) (· < ·)] {a b c : α}

/- warning: left.one_lt_inv_iff -> Left.one_lt_inv_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α _inst_2)] {a : α}, Iff (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a)) (LT.lt.{u1} α _inst_2 a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1298 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1300 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1298 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1300) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1313 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1315 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1313 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1315)] {a : α}, Iff (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a)) (LT.lt.{u1} α _inst_2 a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align left.one_lt_inv_iff Left.one_lt_inv_iffₓ'. -/
/-- Uses `left` co(ntra)variant. -/
@[simp, to_additive Left.neg_pos_iff "Uses `left` co(ntra)variant."]
theorem Left.one_lt_inv_iff : 1 < a⁻¹ ↔ a < 1 := by
  rw [← mul_lt_mul_iff_left a, mul_inv_self, mul_one]
#align left.one_lt_inv_iff Left.one_lt_inv_iff

/- warning: left.inv_lt_one_iff -> Left.inv_lt_one_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α _inst_2)] {a : α}, Iff (LT.lt.{u1} α _inst_2 (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))))) (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1396 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1398 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1396 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1398) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1411 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1413 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1411 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1413)] {a : α}, Iff (LT.lt.{u1} α _inst_2 (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) a)
Case conversion may be inaccurate. Consider using '#align left.inv_lt_one_iff Left.inv_lt_one_iffₓ'. -/
/-- Uses `left` co(ntra)variant. -/
@[simp, to_additive Left.neg_neg_iff "Uses `left` co(ntra)variant."]
theorem Left.inv_lt_one_iff : a⁻¹ < 1 ↔ 1 < a := by
  rw [← mul_lt_mul_iff_left a, mul_inv_self, mul_one]
#align left.inv_lt_one_iff Left.inv_lt_one_iff

/- warning: lt_inv_mul_iff_mul_lt -> lt_inv_mul_iff_mul_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α} {c : α}, Iff (LT.lt.{u1} α _inst_2 b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) c)) (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a b) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1491 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1493 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1491 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1493) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1506 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1508 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1506 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1508)] {a : α} {b : α} {c : α}, Iff (LT.lt.{u1} α _inst_2 b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) c)) (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a b) c)
Case conversion may be inaccurate. Consider using '#align lt_inv_mul_iff_mul_lt lt_inv_mul_iff_mul_ltₓ'. -/
@[simp, to_additive]
theorem lt_inv_mul_iff_mul_lt : b < a⁻¹ * c ↔ a * b < c :=
  by
  rw [← mul_lt_mul_iff_left a]
  simp
#align lt_inv_mul_iff_mul_lt lt_inv_mul_iff_mul_lt

/- warning: inv_mul_lt_iff_lt_mul -> inv_mul_lt_iff_lt_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α} {c : α}, Iff (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b) a) c) (LT.lt.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1592 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1594 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1592 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1594) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1607 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1609 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1607 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1609)] {a : α} {b : α} {c : α}, Iff (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b) a) c) (LT.lt.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b c))
Case conversion may be inaccurate. Consider using '#align inv_mul_lt_iff_lt_mul inv_mul_lt_iff_lt_mulₓ'. -/
@[simp, to_additive]
theorem inv_mul_lt_iff_lt_mul : b⁻¹ * a < c ↔ a < b * c := by
  rw [← mul_lt_mul_iff_left b, mul_inv_cancel_left]
#align inv_mul_lt_iff_lt_mul inv_mul_lt_iff_lt_mul

/- warning: inv_lt_iff_one_lt_mul' -> inv_lt_iff_one_lt_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) b) (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1689 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1691 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1689 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1691) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1704 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1706 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1704 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1706)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) b) (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a b))
Case conversion may be inaccurate. Consider using '#align inv_lt_iff_one_lt_mul' inv_lt_iff_one_lt_mul'ₓ'. -/
@[to_additive]
theorem inv_lt_iff_one_lt_mul' : a⁻¹ < b ↔ 1 < a * b :=
  (mul_lt_mul_iff_left a).symm.trans <| by rw [mul_inv_self]
#align inv_lt_iff_one_lt_mul' inv_lt_iff_one_lt_mul'

/- warning: lt_inv_iff_mul_lt_one' -> lt_inv_iff_mul_lt_one' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 a (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b)) (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b a) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1789 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1791 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1789 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1791) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1804 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1806 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1804 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1806)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 a (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b)) (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b a) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align lt_inv_iff_mul_lt_one' lt_inv_iff_mul_lt_one'ₓ'. -/
@[to_additive]
theorem lt_inv_iff_mul_lt_one' : a < b⁻¹ ↔ b * a < 1 :=
  (mul_lt_mul_iff_left b).symm.trans <| by rw [mul_inv_self]
#align lt_inv_iff_mul_lt_one' lt_inv_iff_mul_lt_one'

/- warning: lt_inv_mul_iff_lt -> lt_inv_mul_iff_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b) a)) (LT.lt.{u1} α _inst_2 b a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1889 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1891 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1889 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1891) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1904 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1906 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1904 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1906)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b) a)) (LT.lt.{u1} α _inst_2 b a)
Case conversion may be inaccurate. Consider using '#align lt_inv_mul_iff_lt lt_inv_mul_iff_ltₓ'. -/
@[to_additive]
theorem lt_inv_mul_iff_lt : 1 < b⁻¹ * a ↔ b < a := by
  rw [← mul_lt_mul_iff_left b, mul_one, mul_inv_cancel_left]
#align lt_inv_mul_iff_lt lt_inv_mul_iff_lt

/- warning: inv_mul_lt_one_iff -> inv_mul_lt_one_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))))) (LT.lt.{u1} α _inst_2 b a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1985 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1987 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1985 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1987) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2000 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2002 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2000 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2002)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2 b a)
Case conversion may be inaccurate. Consider using '#align inv_mul_lt_one_iff inv_mul_lt_one_iffₓ'. -/
@[to_additive]
theorem inv_mul_lt_one_iff : a⁻¹ * b < 1 ↔ b < a :=
  trans inv_mul_lt_iff_lt_mul <| by rw [mul_one]
#align inv_mul_lt_one_iff inv_mul_lt_one_iff

end TypeclassesLeftLt

section TypeclassesRightLe

variable [LE α] [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α}

/- warning: right.inv_le_one_iff -> Right.inv_le_one_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α}, Iff (LE.le.{u1} α _inst_2 (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))))) (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2143 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2145 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2143 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2145)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2158 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2160 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2158 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2160)] {a : α}, Iff (LE.le.{u1} α _inst_2 (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) a)
Case conversion may be inaccurate. Consider using '#align right.inv_le_one_iff Right.inv_le_one_iffₓ'. -/
/-- Uses `right` co(ntra)variant. -/
@[simp, to_additive Right.neg_nonpos_iff "Uses `right` co(ntra)variant."]
theorem Right.inv_le_one_iff : a⁻¹ ≤ 1 ↔ 1 ≤ a :=
  by
  rw [← mul_le_mul_iff_right a]
  simp
#align right.inv_le_one_iff Right.inv_le_one_iff

/- warning: right.one_le_inv_iff -> Right.one_le_inv_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α}, Iff (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a)) (LE.le.{u1} α _inst_2 a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2247 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2249 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2247 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2249)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2262 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2264 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2262 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2264)] {a : α}, Iff (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a)) (LE.le.{u1} α _inst_2 a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align right.one_le_inv_iff Right.one_le_inv_iffₓ'. -/
/-- Uses `right` co(ntra)variant. -/
@[simp, to_additive Right.nonneg_neg_iff "Uses `right` co(ntra)variant."]
theorem Right.one_le_inv_iff : 1 ≤ a⁻¹ ↔ a ≤ 1 :=
  by
  rw [← mul_le_mul_iff_right a]
  simp
#align right.one_le_inv_iff Right.one_le_inv_iff

/- warning: inv_le_iff_one_le_mul -> inv_le_iff_one_le_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) b) (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2348 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2350 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2348 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2350)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2363 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2365 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2363 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2365)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) b) (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b a))
Case conversion may be inaccurate. Consider using '#align inv_le_iff_one_le_mul inv_le_iff_one_le_mulₓ'. -/
@[to_additive neg_le_iff_add_nonneg]
theorem inv_le_iff_one_le_mul : a⁻¹ ≤ b ↔ 1 ≤ b * a :=
  (mul_le_mul_iff_right a).symm.trans <| by rw [inv_mul_self]
#align inv_le_iff_one_le_mul inv_le_iff_one_le_mul

/- warning: le_inv_iff_mul_le_one_right -> le_inv_iff_mul_le_one_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 a (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b)) (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2451 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2453 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2451 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2453)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2466 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2468 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2466 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2468)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 a (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b)) (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align le_inv_iff_mul_le_one_right le_inv_iff_mul_le_one_rightₓ'. -/
@[to_additive]
theorem le_inv_iff_mul_le_one_right : a ≤ b⁻¹ ↔ a * b ≤ 1 :=
  (mul_le_mul_iff_right b).symm.trans <| by rw [inv_mul_self]
#align le_inv_iff_mul_le_one_right le_inv_iff_mul_le_one_right

/- warning: mul_inv_le_iff_le_mul -> mul_inv_le_iff_le_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b)) c) (LE.le.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) c b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2554 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2556 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2554 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2556)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2569 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2571 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2569 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2571)] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b)) c) (LE.le.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) c b))
Case conversion may be inaccurate. Consider using '#align mul_inv_le_iff_le_mul mul_inv_le_iff_le_mulₓ'. -/
@[simp, to_additive]
theorem mul_inv_le_iff_le_mul : a * b⁻¹ ≤ c ↔ a ≤ c * b :=
  (mul_le_mul_iff_right b).symm.trans <| by rw [inv_mul_cancel_right]
#align mul_inv_le_iff_le_mul mul_inv_le_iff_le_mul

/- warning: le_mul_inv_iff_mul_le -> le_mul_inv_iff_mul_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α _inst_2 c (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b))) (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) c b) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2659 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2661 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2659 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2661)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2674 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2676 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2674 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2676)] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α _inst_2 c (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b))) (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) c b) a)
Case conversion may be inaccurate. Consider using '#align le_mul_inv_iff_mul_le le_mul_inv_iff_mul_leₓ'. -/
@[simp, to_additive]
theorem le_mul_inv_iff_mul_le : c ≤ a * b⁻¹ ↔ c * b ≤ a :=
  (mul_le_mul_iff_right b).symm.trans <| by rw [inv_mul_cancel_right]
#align le_mul_inv_iff_mul_le le_mul_inv_iff_mul_le

/- warning: mul_inv_le_one_iff_le -> mul_inv_le_one_iff_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))))) (LE.le.{u1} α _inst_2 a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2764 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2766 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2764 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2766)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2779 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2781 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2779 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2781)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2 a b)
Case conversion may be inaccurate. Consider using '#align mul_inv_le_one_iff_le mul_inv_le_one_iff_leₓ'. -/
@[simp, to_additive]
theorem mul_inv_le_one_iff_le : a * b⁻¹ ≤ 1 ↔ a ≤ b :=
  mul_inv_le_iff_le_mul.trans <| by rw [one_mul]
#align mul_inv_le_one_iff_le mul_inv_le_one_iff_le

/- warning: le_mul_inv_iff_le -> le_mul_inv_iff_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b))) (LE.le.{u1} α _inst_2 b a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2863 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2865 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2863 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2865)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2878 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2880 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2878 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2880)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b))) (LE.le.{u1} α _inst_2 b a)
Case conversion may be inaccurate. Consider using '#align le_mul_inv_iff_le le_mul_inv_iff_leₓ'. -/
@[to_additive]
theorem le_mul_inv_iff_le : 1 ≤ a * b⁻¹ ↔ b ≤ a := by
  rw [← mul_le_mul_iff_right b, one_mul, inv_mul_cancel_right]
#align le_mul_inv_iff_le le_mul_inv_iff_le

/- warning: mul_inv_le_one_iff -> mul_inv_le_one_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))))) (LE.le.{u1} α _inst_2 b a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2962 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2964 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2962 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2964)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2977 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2979 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2977 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2979)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2 b a)
Case conversion may be inaccurate. Consider using '#align mul_inv_le_one_iff mul_inv_le_one_iffₓ'. -/
@[to_additive]
theorem mul_inv_le_one_iff : b * a⁻¹ ≤ 1 ↔ b ≤ a :=
  trans mul_inv_le_iff_le_mul <| by rw [one_mul]
#align mul_inv_le_one_iff mul_inv_le_one_iff

end TypeclassesRightLe

section TypeclassesRightLt

variable [LT α] [CovariantClass α α (swap (· * ·)) (· < ·)] {a b c : α}

/- warning: right.inv_lt_one_iff -> Right.inv_lt_one_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α}, Iff (LT.lt.{u1} α _inst_2 (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))))) (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3120 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3122 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3120 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3122)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3135 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3137 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3135 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3137)] {a : α}, Iff (LT.lt.{u1} α _inst_2 (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) a)
Case conversion may be inaccurate. Consider using '#align right.inv_lt_one_iff Right.inv_lt_one_iffₓ'. -/
/-- Uses `right` co(ntra)variant. -/
@[simp, to_additive Right.neg_neg_iff "Uses `right` co(ntra)variant."]
theorem Right.inv_lt_one_iff : a⁻¹ < 1 ↔ 1 < a := by
  rw [← mul_lt_mul_iff_right a, inv_mul_self, one_mul]
#align right.inv_lt_one_iff Right.inv_lt_one_iff

/- warning: right.one_lt_inv_iff -> Right.one_lt_inv_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α}, Iff (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a)) (LT.lt.{u1} α _inst_2 a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3221 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3223 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3221 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3223)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3236 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3238 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3236 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3238)] {a : α}, Iff (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a)) (LT.lt.{u1} α _inst_2 a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align right.one_lt_inv_iff Right.one_lt_inv_iffₓ'. -/
/-- Uses `right` co(ntra)variant. -/
@[simp, to_additive Right.neg_pos_iff "Uses `right` co(ntra)variant."]
theorem Right.one_lt_inv_iff : 1 < a⁻¹ ↔ a < 1 := by
  rw [← mul_lt_mul_iff_right a, inv_mul_self, one_mul]
#align right.one_lt_inv_iff Right.one_lt_inv_iff

/- warning: inv_lt_iff_one_lt_mul -> inv_lt_iff_one_lt_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) b) (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3319 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3321 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3319 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3321)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3334 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3336 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3334 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3336)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) b) (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b a))
Case conversion may be inaccurate. Consider using '#align inv_lt_iff_one_lt_mul inv_lt_iff_one_lt_mulₓ'. -/
@[to_additive]
theorem inv_lt_iff_one_lt_mul : a⁻¹ < b ↔ 1 < b * a :=
  (mul_lt_mul_iff_right a).symm.trans <| by rw [inv_mul_self]
#align inv_lt_iff_one_lt_mul inv_lt_iff_one_lt_mul

/- warning: lt_inv_iff_mul_lt_one -> lt_inv_iff_mul_lt_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 a (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b)) (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3422 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3424 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3422 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3424)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3437 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3439 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3437 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3439)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 a (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b)) (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align lt_inv_iff_mul_lt_one lt_inv_iff_mul_lt_oneₓ'. -/
@[to_additive]
theorem lt_inv_iff_mul_lt_one : a < b⁻¹ ↔ a * b < 1 :=
  (mul_lt_mul_iff_right b).symm.trans <| by rw [inv_mul_self]
#align lt_inv_iff_mul_lt_one lt_inv_iff_mul_lt_one

/- warning: mul_inv_lt_iff_lt_mul -> mul_inv_lt_iff_lt_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α} {c : α}, Iff (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b)) c) (LT.lt.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) c b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3525 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3527 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3525 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3527)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3540 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3542 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3540 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3542)] {a : α} {b : α} {c : α}, Iff (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b)) c) (LT.lt.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) c b))
Case conversion may be inaccurate. Consider using '#align mul_inv_lt_iff_lt_mul mul_inv_lt_iff_lt_mulₓ'. -/
@[simp, to_additive]
theorem mul_inv_lt_iff_lt_mul : a * b⁻¹ < c ↔ a < c * b := by
  rw [← mul_lt_mul_iff_right b, inv_mul_cancel_right]
#align mul_inv_lt_iff_lt_mul mul_inv_lt_iff_lt_mul

/- warning: lt_mul_inv_iff_mul_lt -> lt_mul_inv_iff_mul_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α} {c : α}, Iff (LT.lt.{u1} α _inst_2 c (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b))) (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) c b) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3625 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3627 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3625 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3627)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3640 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3642 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3640 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3642)] {a : α} {b : α} {c : α}, Iff (LT.lt.{u1} α _inst_2 c (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b))) (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) c b) a)
Case conversion may be inaccurate. Consider using '#align lt_mul_inv_iff_mul_lt lt_mul_inv_iff_mul_ltₓ'. -/
@[simp, to_additive]
theorem lt_mul_inv_iff_mul_lt : c < a * b⁻¹ ↔ c * b < a :=
  (mul_lt_mul_iff_right b).symm.trans <| by rw [inv_mul_cancel_right]
#align lt_mul_inv_iff_mul_lt lt_mul_inv_iff_mul_lt

/- warning: inv_mul_lt_one_iff_lt -> inv_mul_lt_one_iff_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))))) (LT.lt.{u1} α _inst_2 a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3730 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3732 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3730 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3732)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3745 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3747 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3745 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3747)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2 a b)
Case conversion may be inaccurate. Consider using '#align inv_mul_lt_one_iff_lt inv_mul_lt_one_iff_ltₓ'. -/
@[simp, to_additive]
theorem inv_mul_lt_one_iff_lt : a * b⁻¹ < 1 ↔ a < b := by
  rw [← mul_lt_mul_iff_right b, inv_mul_cancel_right, one_mul]
#align inv_mul_lt_one_iff_lt inv_mul_lt_one_iff_lt

/- warning: lt_mul_inv_iff_lt -> lt_mul_inv_iff_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b))) (LT.lt.{u1} α _inst_2 b a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3829 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3831 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3829 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3831)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3844 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3846 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3844 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3846)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b))) (LT.lt.{u1} α _inst_2 b a)
Case conversion may be inaccurate. Consider using '#align lt_mul_inv_iff_lt lt_mul_inv_iff_ltₓ'. -/
@[to_additive]
theorem lt_mul_inv_iff_lt : 1 < a * b⁻¹ ↔ b < a := by
  rw [← mul_lt_mul_iff_right b, one_mul, inv_mul_cancel_right]
#align lt_mul_inv_iff_lt lt_mul_inv_iff_lt

/- warning: mul_inv_lt_one_iff -> mul_inv_lt_one_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))))) (LT.lt.{u1} α _inst_2 b a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3928 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3930 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3928 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3930)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3943 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3945 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3943 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3945)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2 b a)
Case conversion may be inaccurate. Consider using '#align mul_inv_lt_one_iff mul_inv_lt_one_iffₓ'. -/
@[to_additive]
theorem mul_inv_lt_one_iff : b * a⁻¹ < 1 ↔ b < a :=
  trans mul_inv_lt_iff_lt_mul <| by rw [one_mul]
#align mul_inv_lt_one_iff mul_inv_lt_one_iff

end TypeclassesRightLt

section TypeclassesLeftRightLe

variable [LE α] [CovariantClass α α (· * ·) (· ≤ ·)] [CovariantClass α α (swap (· * ·)) (· ≤ ·)]
  {a b c d : α}

/- warning: inv_le_inv_iff -> inv_le_inv_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α _inst_2)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b)) (LE.le.{u1} α _inst_2 b a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4117 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4119 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4117 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4119) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4132 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4134 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4132 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4134)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4154 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4156 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4154 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4156)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4169 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4171 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4169 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4171)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b)) (LE.le.{u1} α _inst_2 b a)
Case conversion may be inaccurate. Consider using '#align inv_le_inv_iff inv_le_inv_iffₓ'. -/
@[simp, to_additive]
theorem inv_le_inv_iff : a⁻¹ ≤ b⁻¹ ↔ b ≤ a :=
  by
  rw [← mul_le_mul_iff_left a, ← mul_le_mul_iff_right b]
  simp
#align inv_le_inv_iff inv_le_inv_iff

alias neg_le_neg_iff ↔ le_of_neg_le_neg _

/- warning: mul_inv_le_inv_mul_iff -> mul_inv_le_inv_mul_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α _inst_2)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α} {c : α} {d : α}, Iff (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) d) c)) (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) d a) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) c b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4259 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4261 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4259 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4261) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4274 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4276 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4274 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4276)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4296 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4298 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4296 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4298)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4311 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4313 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4311 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4313)] {a : α} {b : α} {c : α} {d : α}, Iff (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) d) c)) (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) d a) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) c b))
Case conversion may be inaccurate. Consider using '#align mul_inv_le_inv_mul_iff mul_inv_le_inv_mul_iffₓ'. -/
@[to_additive]
theorem mul_inv_le_inv_mul_iff : a * b⁻¹ ≤ d⁻¹ * c ↔ d * a ≤ c * b := by
  rw [← mul_le_mul_iff_left d, ← mul_le_mul_iff_right b, mul_inv_cancel_left, mul_assoc,
    inv_mul_cancel_right]
#align mul_inv_le_inv_mul_iff mul_inv_le_inv_mul_iff

/- warning: div_le_self_iff -> div_le_self_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α _inst_2)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] (a : α) {b : α}, Iff (LE.le.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a b) a) (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4406 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4408 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4406 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4408) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4421 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4423 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4421 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4423)] (_inst_4 : α) {a : α}, Iff (LE.le.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) _inst_4 a) _inst_4) (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) a)
Case conversion may be inaccurate. Consider using '#align div_le_self_iff div_le_self_iffₓ'. -/
@[simp, to_additive]
theorem div_le_self_iff (a : α) {b : α} : a / b ≤ a ↔ 1 ≤ b := by simp [div_eq_mul_inv]
#align div_le_self_iff div_le_self_iff

/- warning: le_div_self_iff -> le_div_self_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α _inst_2)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] (a : α) {b : α}, Iff (LE.le.{u1} α _inst_2 a (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a b)) (LE.le.{u1} α _inst_2 b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4511 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4513 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4511 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4513) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4526 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4528 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4526 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4528)] (_inst_4 : α) {a : α}, Iff (LE.le.{u1} α _inst_2 _inst_4 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) _inst_4 a)) (LE.le.{u1} α _inst_2 a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align le_div_self_iff le_div_self_iffₓ'. -/
@[simp, to_additive]
theorem le_div_self_iff (a : α) {b : α} : a ≤ a / b ↔ b ≤ 1 := by simp [div_eq_mul_inv]
#align le_div_self_iff le_div_self_iff

alias sub_le_self_iff ↔ _ sub_le_self

end TypeclassesLeftRightLe

section TypeclassesLeftRightLt

variable [LT α] [CovariantClass α α (· * ·) (· < ·)] [CovariantClass α α (swap (· * ·)) (· < ·)]
  {a b c d : α}

/- warning: inv_lt_inv_iff -> inv_lt_inv_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α _inst_2)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b)) (LT.lt.{u1} α _inst_2 b a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4709 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4711 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4709 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4711) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4724 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4726 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4724 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4726)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4746 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4748 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4746 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4748)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4761 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4763 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4761 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4763)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b)) (LT.lt.{u1} α _inst_2 b a)
Case conversion may be inaccurate. Consider using '#align inv_lt_inv_iff inv_lt_inv_iffₓ'. -/
@[simp, to_additive]
theorem inv_lt_inv_iff : a⁻¹ < b⁻¹ ↔ b < a :=
  by
  rw [← mul_lt_mul_iff_left a, ← mul_lt_mul_iff_right b]
  simp
#align inv_lt_inv_iff inv_lt_inv_iff

/- warning: inv_lt' -> inv_lt' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α _inst_2)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) b) (LT.lt.{u1} α _inst_2 (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4850 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4852 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4850 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4852) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4865 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4867 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4865 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4867)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4887 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4889 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4887 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4889)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4902 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4904 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4902 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4904)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) b) (LT.lt.{u1} α _inst_2 (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b) a)
Case conversion may be inaccurate. Consider using '#align inv_lt' inv_lt'ₓ'. -/
@[to_additive neg_lt]
theorem inv_lt' : a⁻¹ < b ↔ b⁻¹ < a := by rw [← inv_lt_inv_iff, inv_inv]
#align inv_lt' inv_lt'

/- warning: lt_inv' -> lt_inv' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α _inst_2)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 a (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b)) (LT.lt.{u1} α _inst_2 b (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4984 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4986 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4984 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4986) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4999 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5001 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4999 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5001)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5021 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5023 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5021 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5023)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5036 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5038 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5036 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5038)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 a (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b)) (LT.lt.{u1} α _inst_2 b (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a))
Case conversion may be inaccurate. Consider using '#align lt_inv' lt_inv'ₓ'. -/
@[to_additive lt_neg]
theorem lt_inv' : a < b⁻¹ ↔ b < a⁻¹ := by rw [← inv_lt_inv_iff, inv_inv]
#align lt_inv' lt_inv'

alias lt_inv' ↔ lt_inv_of_lt_inv _

attribute [to_additive] lt_inv_of_lt_inv

alias inv_lt' ↔ inv_lt_of_inv_lt' _

attribute [to_additive neg_lt_of_neg_lt] inv_lt_of_inv_lt'

/- warning: mul_inv_lt_inv_mul_iff -> mul_inv_lt_inv_mul_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α _inst_2)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α} {c : α} {d : α}, Iff (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) d) c)) (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) d a) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) c b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5122 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5124 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5122 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5124) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5137 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5139 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5137 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5139)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5159 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5161 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5159 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5161)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5174 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5176 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5174 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5176)] {a : α} {b : α} {c : α} {d : α}, Iff (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) d) c)) (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) d a) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) c b))
Case conversion may be inaccurate. Consider using '#align mul_inv_lt_inv_mul_iff mul_inv_lt_inv_mul_iffₓ'. -/
@[to_additive]
theorem mul_inv_lt_inv_mul_iff : a * b⁻¹ < d⁻¹ * c ↔ d * a < c * b := by
  rw [← mul_lt_mul_iff_left d, ← mul_lt_mul_iff_right b, mul_inv_cancel_left, mul_assoc,
    inv_mul_cancel_right]
#align mul_inv_lt_inv_mul_iff mul_inv_lt_inv_mul_iff

/- warning: div_lt_self_iff -> div_lt_self_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α _inst_2)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] (a : α) {b : α}, Iff (LT.lt.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a b) a) (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5269 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5271 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5269 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5271) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5284 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5286 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5284 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5286)] (_inst_4 : α) {a : α}, Iff (LT.lt.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) _inst_4 a) _inst_4) (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) a)
Case conversion may be inaccurate. Consider using '#align div_lt_self_iff div_lt_self_iffₓ'. -/
@[simp, to_additive]
theorem div_lt_self_iff (a : α) {b : α} : a / b < a ↔ 1 < b := by simp [div_eq_mul_inv]
#align div_lt_self_iff div_lt_self_iff

alias sub_lt_self_iff ↔ _ sub_lt_self

end TypeclassesLeftRightLt

section PreOrder

variable [Preorder α]

section LeftLe

variable [CovariantClass α α (· * ·) (· ≤ ·)] {a : α}

/- warning: left.inv_le_self -> Left.inv_le_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5435 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5437 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5435 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5437) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5450 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5452 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5450 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5452)] {a : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) a)
Case conversion may be inaccurate. Consider using '#align left.inv_le_self Left.inv_le_selfₓ'. -/
@[to_additive]
theorem Left.inv_le_self (h : 1 ≤ a) : a⁻¹ ≤ a :=
  le_trans (Left.inv_le_one_iff.mpr h) h
#align left.inv_le_self Left.inv_le_self

alias Left.neg_le_self ← neg_le_self

/- warning: left.self_le_inv -> Left.self_le_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5504 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5506 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5504 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5506) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5519 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5521 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5519 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5521)] {a : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1))))))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a))
Case conversion may be inaccurate. Consider using '#align left.self_le_inv Left.self_le_invₓ'. -/
@[to_additive]
theorem Left.self_le_inv (h : a ≤ 1) : a ≤ a⁻¹ :=
  le_trans h (Left.one_le_inv_iff.mpr h)
#align left.self_le_inv Left.self_le_inv

end LeftLe

section LeftLt

variable [CovariantClass α α (· * ·) (· < ·)] {a : α}

/- warning: left.inv_lt_self -> Left.inv_lt_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] {a : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5619 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5621 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5619 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5621) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5634 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5636 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5634 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5636)] {a : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) a)
Case conversion may be inaccurate. Consider using '#align left.inv_lt_self Left.inv_lt_selfₓ'. -/
@[to_additive]
theorem Left.inv_lt_self (h : 1 < a) : a⁻¹ < a :=
  (Left.inv_lt_one_iff.mpr h).trans h
#align left.inv_lt_self Left.inv_lt_self

alias Left.neg_lt_self ← neg_lt_self

/- warning: left.self_lt_inv -> Left.self_lt_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] {a : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5688 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5690 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5688 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5690) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5703 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5705 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5703 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5705)] {a : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1))))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a))
Case conversion may be inaccurate. Consider using '#align left.self_lt_inv Left.self_lt_invₓ'. -/
@[to_additive]
theorem Left.self_lt_inv (h : a < 1) : a < a⁻¹ :=
  lt_trans h (Left.one_lt_inv_iff.mpr h)
#align left.self_lt_inv Left.self_lt_inv

end LeftLt

section RightLe

variable [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a : α}

/- warning: right.inv_le_self -> Right.inv_le_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5809 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5811 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5809 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5811)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5824 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5826 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5824 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5826)] {a : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) a)
Case conversion may be inaccurate. Consider using '#align right.inv_le_self Right.inv_le_selfₓ'. -/
@[to_additive]
theorem Right.inv_le_self (h : 1 ≤ a) : a⁻¹ ≤ a :=
  le_trans (Right.inv_le_one_iff.mpr h) h
#align right.inv_le_self Right.inv_le_self

/- warning: right.self_le_inv -> Right.self_le_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5880 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5882 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5880 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5882)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5895 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5897 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5895 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5897)] {a : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1))))))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a))
Case conversion may be inaccurate. Consider using '#align right.self_le_inv Right.self_le_invₓ'. -/
@[to_additive]
theorem Right.self_le_inv (h : a ≤ 1) : a ≤ a⁻¹ :=
  le_trans h (Right.one_le_inv_iff.mpr h)
#align right.self_le_inv Right.self_le_inv

end RightLe

section RightLt

variable [CovariantClass α α (swap (· * ·)) (· < ·)] {a : α}

/- warning: right.inv_lt_self -> Right.inv_lt_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] {a : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6001 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6003 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6001 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6003)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6016 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6018 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6016 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6018)] {a : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) a)
Case conversion may be inaccurate. Consider using '#align right.inv_lt_self Right.inv_lt_selfₓ'. -/
@[to_additive]
theorem Right.inv_lt_self (h : 1 < a) : a⁻¹ < a :=
  (Right.inv_lt_one_iff.mpr h).trans h
#align right.inv_lt_self Right.inv_lt_self

/- warning: right.self_lt_inv -> Right.self_lt_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] {a : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6072 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6074 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6072 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6074)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6087 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6089 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6087 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6089)] {a : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1))))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a))
Case conversion may be inaccurate. Consider using '#align right.self_lt_inv Right.self_lt_invₓ'. -/
@[to_additive]
theorem Right.self_lt_inv (h : a < 1) : a < a⁻¹ :=
  lt_trans h (Right.one_lt_inv_iff.mpr h)
#align right.self_lt_inv Right.self_lt_inv

end RightLt

end PreOrder

end Group

section CommGroup

variable [CommGroup α]

section LE

variable [LE α] [CovariantClass α α (· * ·) (· ≤ ·)] {a b c d : α}

/- warning: inv_mul_le_iff_le_mul' -> inv_mul_le_iff_le_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))) c) a) b) (LE.le.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6200 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6202 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6200 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6202) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6215 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6217 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6215 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6217)] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_1))))) c) a) b) (LE.le.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) b c))
Case conversion may be inaccurate. Consider using '#align inv_mul_le_iff_le_mul' inv_mul_le_iff_le_mul'ₓ'. -/
@[to_additive]
theorem inv_mul_le_iff_le_mul' : c⁻¹ * a ≤ b ↔ a ≤ b * c := by rw [inv_mul_le_iff_le_mul, mul_comm]
#align inv_mul_le_iff_le_mul' inv_mul_le_iff_le_mul'

/- warning: mul_inv_le_iff_le_mul' -> mul_inv_le_iff_le_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) a (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))) b)) c) (LE.le.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6297 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6299 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6297 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6299) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6312 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6314 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6312 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6314)] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) a (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_1))))) b)) c) (LE.le.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) b c))
Case conversion may be inaccurate. Consider using '#align mul_inv_le_iff_le_mul' mul_inv_le_iff_le_mul'ₓ'. -/
@[simp, to_additive]
theorem mul_inv_le_iff_le_mul' : a * b⁻¹ ≤ c ↔ a ≤ b * c := by
  rw [← inv_mul_le_iff_le_mul, mul_comm]
#align mul_inv_le_iff_le_mul' mul_inv_le_iff_le_mul'

/- warning: mul_inv_le_mul_inv_iff' -> mul_inv_le_mul_inv_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α} {c : α} {d : α}, Iff (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) a (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))) b)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) c (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))) d))) (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) a d) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) c b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6394 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6396 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6394 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6396) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6409 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6411 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6409 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6411)] {a : α} {b : α} {c : α} {d : α}, Iff (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) a (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_1))))) b)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) c (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_1))))) d))) (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) a d) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) c b))
Case conversion may be inaccurate. Consider using '#align mul_inv_le_mul_inv_iff' mul_inv_le_mul_inv_iff'ₓ'. -/
@[to_additive add_neg_le_add_neg_iff]
theorem mul_inv_le_mul_inv_iff' : a * b⁻¹ ≤ c * d⁻¹ ↔ a * d ≤ c * b := by
  rw [mul_comm c, mul_inv_le_inv_mul_iff, mul_comm]
#align mul_inv_le_mul_inv_iff' mul_inv_le_mul_inv_iff'

end LE

section LT

variable [LT α] [CovariantClass α α (· * ·) (· < ·)] {a b c d : α}

/- warning: inv_mul_lt_iff_lt_mul' -> inv_mul_lt_iff_lt_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α} {c : α}, Iff (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))) c) a) b) (LT.lt.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6555 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6557 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6555 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6557) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6570 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6572 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6570 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6572)] {a : α} {b : α} {c : α}, Iff (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_1))))) c) a) b) (LT.lt.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) b c))
Case conversion may be inaccurate. Consider using '#align inv_mul_lt_iff_lt_mul' inv_mul_lt_iff_lt_mul'ₓ'. -/
@[to_additive]
theorem inv_mul_lt_iff_lt_mul' : c⁻¹ * a < b ↔ a < b * c := by rw [inv_mul_lt_iff_lt_mul, mul_comm]
#align inv_mul_lt_iff_lt_mul' inv_mul_lt_iff_lt_mul'

/- warning: mul_inv_lt_iff_le_mul' -> mul_inv_lt_iff_le_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α} {c : α}, Iff (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) a (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))) b)) c) (LT.lt.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6652 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6654 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6652 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6654) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6667 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6669 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6667 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6669)] {a : α} {b : α} {c : α}, Iff (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) a (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_1))))) b)) c) (LT.lt.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) b c))
Case conversion may be inaccurate. Consider using '#align mul_inv_lt_iff_le_mul' mul_inv_lt_iff_le_mul'ₓ'. -/
@[simp, to_additive]
theorem mul_inv_lt_iff_le_mul' : a * b⁻¹ < c ↔ a < b * c := by
  rw [← inv_mul_lt_iff_lt_mul, mul_comm]
#align mul_inv_lt_iff_le_mul' mul_inv_lt_iff_le_mul'

/- warning: mul_inv_lt_mul_inv_iff' -> mul_inv_lt_mul_inv_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α} {c : α} {d : α}, Iff (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) a (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))) b)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) c (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))) d))) (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) a d) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) c b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6749 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6751 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6749 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6751) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6764 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6766 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6764 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6766)] {a : α} {b : α} {c : α} {d : α}, Iff (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) a (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_1))))) b)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) c (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_1))))) d))) (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) a d) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) c b))
Case conversion may be inaccurate. Consider using '#align mul_inv_lt_mul_inv_iff' mul_inv_lt_mul_inv_iff'ₓ'. -/
@[to_additive add_neg_lt_add_neg_iff]
theorem mul_inv_lt_mul_inv_iff' : a * b⁻¹ < c * d⁻¹ ↔ a * d < c * b := by
  rw [mul_comm c, mul_inv_lt_inv_mul_iff, mul_comm]
#align mul_inv_lt_mul_inv_iff' mul_inv_lt_mul_inv_iff'

end LT

end CommGroup

alias Left.inv_le_one_iff ↔ one_le_of_inv_le_one _

attribute [to_additive] one_le_of_inv_le_one

alias Left.one_le_inv_iff ↔ le_one_of_one_le_inv _

attribute [to_additive nonpos_of_neg_nonneg] le_one_of_one_le_inv

alias inv_lt_inv_iff ↔ lt_of_inv_lt_inv _

attribute [to_additive] lt_of_inv_lt_inv

alias Left.inv_lt_one_iff ↔ one_lt_of_inv_lt_one _

attribute [to_additive] one_lt_of_inv_lt_one

alias Left.inv_lt_one_iff ← inv_lt_one_iff_one_lt

attribute [to_additive] inv_lt_one_iff_one_lt

alias Left.inv_lt_one_iff ← inv_lt_one'

attribute [to_additive neg_lt_zero] inv_lt_one'

alias Left.one_lt_inv_iff ↔ inv_of_one_lt_inv _

attribute [to_additive neg_of_neg_pos] inv_of_one_lt_inv

alias Left.one_lt_inv_iff ↔ _ one_lt_inv_of_inv

attribute [to_additive neg_pos_of_neg] one_lt_inv_of_inv

alias le_inv_mul_iff_mul_le ↔ mul_le_of_le_inv_mul _

attribute [to_additive] mul_le_of_le_inv_mul

alias le_inv_mul_iff_mul_le ↔ _ le_inv_mul_of_mul_le

attribute [to_additive] le_inv_mul_of_mul_le

alias inv_mul_le_iff_le_mul ↔ _ inv_mul_le_of_le_mul

attribute [to_additive] inv_mul_le_iff_le_mul

alias lt_inv_mul_iff_mul_lt ↔ mul_lt_of_lt_inv_mul _

attribute [to_additive] mul_lt_of_lt_inv_mul

alias lt_inv_mul_iff_mul_lt ↔ _ lt_inv_mul_of_mul_lt

attribute [to_additive] lt_inv_mul_of_mul_lt

alias inv_mul_lt_iff_lt_mul ↔ lt_mul_of_inv_mul_lt inv_mul_lt_of_lt_mul

attribute [to_additive] lt_mul_of_inv_mul_lt

attribute [to_additive] inv_mul_lt_of_lt_mul

alias lt_mul_of_inv_mul_lt ← lt_mul_of_inv_mul_lt_left

attribute [to_additive] lt_mul_of_inv_mul_lt_left

alias Left.inv_le_one_iff ← inv_le_one'

attribute [to_additive neg_nonpos] inv_le_one'

alias Left.one_le_inv_iff ← one_le_inv'

attribute [to_additive neg_nonneg] one_le_inv'

alias Left.one_lt_inv_iff ← one_lt_inv'

attribute [to_additive neg_pos] one_lt_inv'

alias mul_lt_mul_left' ← OrderedCommGroup.mul_lt_mul_left'

attribute [to_additive OrderedAddCommGroup.add_lt_add_left] OrderedCommGroup.mul_lt_mul_left'

alias le_of_mul_le_mul_left' ← OrderedCommGroup.le_of_mul_le_mul_left

attribute [to_additive OrderedAddCommGroup.le_of_add_le_add_left]
  OrderedCommGroup.le_of_mul_le_mul_left

alias lt_of_mul_lt_mul_left' ← OrderedCommGroup.lt_of_mul_lt_mul_left

attribute [to_additive OrderedAddCommGroup.lt_of_add_lt_add_left]
  OrderedCommGroup.lt_of_mul_lt_mul_left

--  Most of the lemmas that are primed in this section appear in ordered_field. 
--  I (DT) did not try to minimise the assumptions.
section Group

variable [Group α] [LE α]

section Right

variable [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c d : α}

/- warning: div_le_div_iff_right -> div_le_div_iff_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α} (c : α), Iff (LE.le.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a c) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) b c)) (LE.le.{u1} α _inst_2 a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6970 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6972 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6970 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6972)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6985 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6987 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6985 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6987)] {a : α} {b : α} (c : α), Iff (LE.le.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a c) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) b c)) (LE.le.{u1} α _inst_2 a b)
Case conversion may be inaccurate. Consider using '#align div_le_div_iff_right div_le_div_iff_rightₓ'. -/
@[simp, to_additive]
theorem div_le_div_iff_right (c : α) : a / c ≤ b / c ↔ a ≤ b := by
  simpa only [div_eq_mul_inv] using mul_le_mul_iff_right _
#align div_le_div_iff_right div_le_div_iff_right

/- warning: div_le_div_right' -> div_le_div_right' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 a b) -> (forall (c : α), LE.le.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a c) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7047 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7049 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7047 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7049)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7062 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7064 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7062 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7064)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 a b) -> (forall (c : α), LE.le.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a c) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) b c))
Case conversion may be inaccurate. Consider using '#align div_le_div_right' div_le_div_right'ₓ'. -/
@[to_additive sub_le_sub_right]
theorem div_le_div_right' (h : a ≤ b) (c : α) : a / c ≤ b / c :=
  (div_le_div_iff_right c).2 h
#align div_le_div_right' div_le_div_right'

/- warning: one_le_div' -> one_le_div' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a b)) (LE.le.{u1} α _inst_2 b a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7118 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7120 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7118 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7120)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7133 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7135 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7133 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7135)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a b)) (LE.le.{u1} α _inst_2 b a)
Case conversion may be inaccurate. Consider using '#align one_le_div' one_le_div'ₓ'. -/
@[simp, to_additive sub_nonneg]
theorem one_le_div' : 1 ≤ a / b ↔ b ≤ a := by
  rw [← mul_le_mul_iff_right b, one_mul, div_eq_mul_inv, inv_mul_cancel_right]
#align one_le_div' one_le_div'

alias sub_nonneg ↔ le_of_sub_nonneg sub_nonneg_of_le

/- warning: div_le_one' -> div_le_one' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))))) (LE.le.{u1} α _inst_2 a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7216 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7218 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7216 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7218)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7231 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7233 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7231 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7233)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2 a b)
Case conversion may be inaccurate. Consider using '#align div_le_one' div_le_one'ₓ'. -/
@[simp, to_additive sub_nonpos]
theorem div_le_one' : a / b ≤ 1 ↔ a ≤ b := by
  rw [← mul_le_mul_iff_right b, one_mul, div_eq_mul_inv, inv_mul_cancel_right]
#align div_le_one' div_le_one'

alias sub_nonpos ↔ le_of_sub_nonpos sub_nonpos_of_le

/- warning: le_div_iff_mul_le -> le_div_iff_mul_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α _inst_2 a (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) c b)) (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a b) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7314 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7316 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7314 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7316)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7329 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7331 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7329 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7331)] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α _inst_2 a (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) c b)) (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a b) c)
Case conversion may be inaccurate. Consider using '#align le_div_iff_mul_le le_div_iff_mul_leₓ'. -/
@[to_additive]
theorem le_div_iff_mul_le : a ≤ c / b ↔ a * b ≤ c := by
  rw [← mul_le_mul_iff_right b, div_eq_mul_inv, inv_mul_cancel_right]
#align le_div_iff_mul_le le_div_iff_mul_le

alias le_sub_iff_add_le ↔ add_le_of_le_sub_right le_sub_right_of_add_le

/- warning: div_le_iff_le_mul -> div_le_iff_le_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a c) b) (LE.le.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7413 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7415 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7413 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7415)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7428 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7430 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7428 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7430)] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a c) b) (LE.le.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b c))
Case conversion may be inaccurate. Consider using '#align div_le_iff_le_mul div_le_iff_le_mulₓ'. -/
@[to_additive]
theorem div_le_iff_le_mul : a / c ≤ b ↔ a ≤ b * c := by
  rw [← mul_le_mul_iff_right c, div_eq_mul_inv, inv_mul_cancel_right]
#align div_le_iff_le_mul div_le_iff_le_mul

/- warning: add_group.to_has_ordered_sub -> AddGroup.toHasOrderedSub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_4 : AddGroup.{u1} α] [_inst_5 : LE.{u1} α] [_inst_6 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_4))))))) (LE.le.{u1} α _inst_5)], OrderedSub.{u1} α _inst_5 (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_4)))) (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_4))
but is expected to have type
  forall {α : Type.{u1}} [_inst_4 : AddGroup.{u1} α] [_inst_5 : LE.{u1} α] [_inst_6 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7562 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7564 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_4))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7562 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7564)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7577 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7579 : α) => LE.le.{u1} α _inst_5 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7577 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7579)], OrderedSub.{u1} α _inst_5 (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_4)))) (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_4))
Case conversion may be inaccurate. Consider using '#align add_group.to_has_ordered_sub AddGroup.toHasOrderedSubₓ'. -/
-- TODO: Should we get rid of `sub_le_iff_le_add` in favor of
-- (a renamed version of) `tsub_le_iff_right`?
-- see Note [lower instance priority]
instance (priority := 100) AddGroup.toHasOrderedSub {α : Type _} [AddGroup α] [LE α]
    [CovariantClass α α (swap (· + ·)) (· ≤ ·)] : OrderedSub α :=
  ⟨fun a b c => sub_le_iff_le_add⟩
#align add_group.to_has_ordered_sub AddGroup.toHasOrderedSub

end Right

section Left

variable [CovariantClass α α (· * ·) (· ≤ ·)]

variable [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α}

/- warning: div_le_div_iff_left -> div_le_div_iff_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α _inst_2)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {b : α} {c : α} (a : α), Iff (LE.le.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a b) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a c)) (LE.le.{u1} α _inst_2 c b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7750 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7752 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7750 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7752) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7765 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7767 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7765 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7767)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7787 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7789 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7787 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7789)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7802 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7804 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7802 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7804)] {b : α} {c : α} (a : α), Iff (LE.le.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a b) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a c)) (LE.le.{u1} α _inst_2 c b)
Case conversion may be inaccurate. Consider using '#align div_le_div_iff_left div_le_div_iff_leftₓ'. -/
@[simp, to_additive]
theorem div_le_div_iff_left (a : α) : a / b ≤ a / c ↔ c ≤ b := by
  rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_le_mul_iff_left a⁻¹, inv_mul_cancel_left,
    inv_mul_cancel_left, inv_le_inv_iff]
#align div_le_div_iff_left div_le_div_iff_left

/- warning: div_le_div_left' -> div_le_div_left' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α _inst_2)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 a b) -> (forall (c : α), LE.le.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) c b) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) c a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7888 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7890 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7888 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7890) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7903 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7905 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7903 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7905)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7925 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7927 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7925 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7927)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7940 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7942 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7940 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7942)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 a b) -> (forall (c : α), LE.le.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) c b) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) c a))
Case conversion may be inaccurate. Consider using '#align div_le_div_left' div_le_div_left'ₓ'. -/
@[to_additive sub_le_sub_left]
theorem div_le_div_left' (h : a ≤ b) (c : α) : c / b ≤ c / a :=
  (div_le_div_iff_left c).2 h
#align div_le_div_left' div_le_div_left'

end Left

end Group

section CommGroup

variable [CommGroup α]

section LE

variable [LE α] [CovariantClass α α (· * ·) (· ≤ ·)] {a b c d : α}

/- warning: div_le_div_iff' -> div_le_div_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α} {c : α} {d : α}, Iff (LE.le.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) a b) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) c d)) (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) a d) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) c b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8054 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8056 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8054 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8056) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8069 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8071 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8069 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8071)] {a : α} {b : α} {c : α} {d : α}, Iff (LE.le.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) a b) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) c d)) (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) a d) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) c b))
Case conversion may be inaccurate. Consider using '#align div_le_div_iff' div_le_div_iff'ₓ'. -/
@[to_additive sub_le_sub_iff]
theorem div_le_div_iff' : a / b ≤ c / d ↔ a * d ≤ c * b := by
  simpa only [div_eq_mul_inv] using mul_inv_le_mul_inv_iff'
#align div_le_div_iff' div_le_div_iff'

/- warning: le_div_iff_mul_le' -> le_div_iff_mul_le' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α _inst_2 b (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) c a)) (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) a b) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8130 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8132 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8130 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8132) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8145 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8147 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8145 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8147)] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α _inst_2 b (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) c a)) (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) a b) c)
Case conversion may be inaccurate. Consider using '#align le_div_iff_mul_le' le_div_iff_mul_le'ₓ'. -/
@[to_additive]
theorem le_div_iff_mul_le' : b ≤ c / a ↔ a * b ≤ c := by rw [le_div_iff_mul_le, mul_comm]
#align le_div_iff_mul_le' le_div_iff_mul_le'

alias le_sub_iff_add_le' ↔ add_le_of_le_sub_left le_sub_left_of_add_le

/- warning: div_le_iff_le_mul' -> div_le_iff_le_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) a b) c) (LE.le.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8224 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8226 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8224 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8226) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8239 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8241 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8239 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8241)] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) a b) c) (LE.le.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) b c))
Case conversion may be inaccurate. Consider using '#align div_le_iff_le_mul' div_le_iff_le_mul'ₓ'. -/
@[to_additive]
theorem div_le_iff_le_mul' : a / b ≤ c ↔ a ≤ b * c := by rw [div_le_iff_le_mul, mul_comm]
#align div_le_iff_le_mul' div_le_iff_le_mul'

alias sub_le_iff_le_add' ↔ le_add_of_sub_left_le sub_left_le_of_le_add

/- warning: inv_le_div_iff_le_mul -> inv_le_div_iff_le_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α _inst_2 (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))) b) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) a c)) (LE.le.{u1} α _inst_2 c (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8318 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8320 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8318 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8320) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8333 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8335 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8333 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8335)] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α _inst_2 (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_1))))) b) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) a c)) (LE.le.{u1} α _inst_2 c (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) a b))
Case conversion may be inaccurate. Consider using '#align inv_le_div_iff_le_mul inv_le_div_iff_le_mulₓ'. -/
@[simp, to_additive]
theorem inv_le_div_iff_le_mul : b⁻¹ ≤ a / c ↔ c ≤ a * b :=
  le_div_iff_mul_le.trans inv_mul_le_iff_le_mul'
#align inv_le_div_iff_le_mul inv_le_div_iff_le_mul

/- warning: inv_le_div_iff_le_mul' -> inv_le_div_iff_le_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α _inst_2 (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))) a) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) b c)) (LE.le.{u1} α _inst_2 c (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8388 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8390 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8388 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8390) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8403 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8405 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8403 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8405)] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α _inst_2 (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_1))))) a) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) b c)) (LE.le.{u1} α _inst_2 c (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) a b))
Case conversion may be inaccurate. Consider using '#align inv_le_div_iff_le_mul' inv_le_div_iff_le_mul'ₓ'. -/
@[to_additive]
theorem inv_le_div_iff_le_mul' : a⁻¹ ≤ b / c ↔ c ≤ a * b := by rw [inv_le_div_iff_le_mul, mul_comm]
#align inv_le_div_iff_le_mul' inv_le_div_iff_le_mul'

/- warning: div_le_comm -> div_le_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) a b) c) (LE.le.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) a c) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8485 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8487 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8485 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8487) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8500 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8502 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8500 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8502)] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) a b) c) (LE.le.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) a c) b)
Case conversion may be inaccurate. Consider using '#align div_le_comm div_le_commₓ'. -/
@[to_additive]
theorem div_le_comm : a / b ≤ c ↔ a / c ≤ b :=
  div_le_iff_le_mul'.trans div_le_iff_le_mul.symm
#align div_le_comm div_le_comm

/- warning: le_div_comm -> le_div_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α _inst_2 a (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) b c)) (LE.le.{u1} α _inst_2 c (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) b a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8551 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8553 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8551 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8553) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8566 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8568 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8566 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8568)] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α _inst_2 a (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) b c)) (LE.le.{u1} α _inst_2 c (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) b a))
Case conversion may be inaccurate. Consider using '#align le_div_comm le_div_commₓ'. -/
@[to_additive]
theorem le_div_comm : a ≤ b / c ↔ c ≤ b / a :=
  le_div_iff_mul_le'.trans le_div_iff_mul_le.symm
#align le_div_comm le_div_comm

end LE

section Preorder

variable [Preorder α] [CovariantClass α α (· * ·) (· ≤ ·)] {a b c d : α}

/- warning: div_le_div'' -> div_le_div'' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α} {c : α} {d : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) c d) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) a d) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8671 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8673 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8671 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8673) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8686 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8688 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8686 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8688)] {a : α} {b : α} {c : α} {d : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) c d) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) a d) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) b c))
Case conversion may be inaccurate. Consider using '#align div_le_div'' div_le_div''ₓ'. -/
@[to_additive sub_le_sub]
theorem div_le_div'' (hab : a ≤ b) (hcd : c ≤ d) : a / d ≤ b / c :=
  by
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_comm b, mul_inv_le_inv_mul_iff, mul_comm]
  exact mul_le_mul' hab hcd
#align div_le_div'' div_le_div''

end Preorder

end CommGroup

--  Most of the lemmas that are primed in this section appear in ordered_field. 
--  I (DT) did not try to minimise the assumptions.
section Group

variable [Group α] [LT α]

section Right

variable [CovariantClass α α (swap (· * ·)) (· < ·)] {a b c d : α}

/- warning: div_lt_div_iff_right -> div_lt_div_iff_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α} (c : α), Iff (LT.lt.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a c) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) b c)) (LT.lt.{u1} α _inst_2 a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8849 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8851 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8849 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8851)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8864 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8866 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8864 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8866)] {a : α} {b : α} (c : α), Iff (LT.lt.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a c) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) b c)) (LT.lt.{u1} α _inst_2 a b)
Case conversion may be inaccurate. Consider using '#align div_lt_div_iff_right div_lt_div_iff_rightₓ'. -/
@[simp, to_additive]
theorem div_lt_div_iff_right (c : α) : a / c < b / c ↔ a < b := by
  simpa only [div_eq_mul_inv] using mul_lt_mul_iff_right _
#align div_lt_div_iff_right div_lt_div_iff_right

/- warning: div_lt_div_right' -> div_lt_div_right' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α}, (LT.lt.{u1} α _inst_2 a b) -> (forall (c : α), LT.lt.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a c) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8926 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8928 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8926 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8928)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8941 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8943 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8941 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8943)] {a : α} {b : α}, (LT.lt.{u1} α _inst_2 a b) -> (forall (c : α), LT.lt.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a c) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) b c))
Case conversion may be inaccurate. Consider using '#align div_lt_div_right' div_lt_div_right'ₓ'. -/
@[to_additive sub_lt_sub_right]
theorem div_lt_div_right' (h : a < b) (c : α) : a / c < b / c :=
  (div_lt_div_iff_right c).2 h
#align div_lt_div_right' div_lt_div_right'

/- warning: one_lt_div' -> one_lt_div' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a b)) (LT.lt.{u1} α _inst_2 b a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8997 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8999 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8997 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8999)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9012 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9014 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9012 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9014)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a b)) (LT.lt.{u1} α _inst_2 b a)
Case conversion may be inaccurate. Consider using '#align one_lt_div' one_lt_div'ₓ'. -/
@[simp, to_additive sub_pos]
theorem one_lt_div' : 1 < a / b ↔ b < a := by
  rw [← mul_lt_mul_iff_right b, one_mul, div_eq_mul_inv, inv_mul_cancel_right]
#align one_lt_div' one_lt_div'

alias sub_pos ↔ lt_of_sub_pos sub_pos_of_lt

/- warning: div_lt_one' -> div_lt_one' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))))) (LT.lt.{u1} α _inst_2 a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9095 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9097 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9095 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9097)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9110 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9112 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9110 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9112)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2 a b)
Case conversion may be inaccurate. Consider using '#align div_lt_one' div_lt_one'ₓ'. -/
@[simp, to_additive sub_neg]
theorem div_lt_one' : a / b < 1 ↔ a < b := by
  rw [← mul_lt_mul_iff_right b, one_mul, div_eq_mul_inv, inv_mul_cancel_right]
#align div_lt_one' div_lt_one'

alias sub_neg ↔ lt_of_sub_neg sub_neg_of_lt

alias sub_neg ← sub_lt_zero

/- warning: lt_div_iff_mul_lt -> lt_div_iff_mul_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α} {c : α}, Iff (LT.lt.{u1} α _inst_2 a (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) c b)) (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a b) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9194 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9196 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9194 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9196)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9209 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9211 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9209 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9211)] {a : α} {b : α} {c : α}, Iff (LT.lt.{u1} α _inst_2 a (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) c b)) (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a b) c)
Case conversion may be inaccurate. Consider using '#align lt_div_iff_mul_lt lt_div_iff_mul_ltₓ'. -/
@[to_additive]
theorem lt_div_iff_mul_lt : a < c / b ↔ a * b < c := by
  rw [← mul_lt_mul_iff_right b, div_eq_mul_inv, inv_mul_cancel_right]
#align lt_div_iff_mul_lt lt_div_iff_mul_lt

alias lt_sub_iff_add_lt ↔ add_lt_of_lt_sub_right lt_sub_right_of_add_lt

/- warning: div_lt_iff_lt_mul -> div_lt_iff_lt_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α} {c : α}, Iff (LT.lt.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a c) b) (LT.lt.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9293 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9295 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9293 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9295)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9308 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9310 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9308 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9310)] {a : α} {b : α} {c : α}, Iff (LT.lt.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a c) b) (LT.lt.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b c))
Case conversion may be inaccurate. Consider using '#align div_lt_iff_lt_mul div_lt_iff_lt_mulₓ'. -/
@[to_additive]
theorem div_lt_iff_lt_mul : a / c < b ↔ a < b * c := by
  rw [← mul_lt_mul_iff_right c, div_eq_mul_inv, inv_mul_cancel_right]
#align div_lt_iff_lt_mul div_lt_iff_lt_mul

alias sub_lt_iff_lt_add ↔ lt_add_of_sub_right_lt sub_right_lt_of_lt_add

end Right

section Left

variable [CovariantClass α α (· * ·) (· < ·)] [CovariantClass α α (swap (· * ·)) (· < ·)]
  {a b c : α}

/- warning: div_lt_div_iff_left -> div_lt_div_iff_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α _inst_2)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {b : α} {c : α} (a : α), Iff (LT.lt.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a b) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a c)) (LT.lt.{u1} α _inst_2 c b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9478 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9480 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9478 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9480) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9493 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9495 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9493 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9495)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9515 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9517 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9515 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9517)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9530 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9532 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9530 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9532)] {b : α} {c : α} (a : α), Iff (LT.lt.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a b) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a c)) (LT.lt.{u1} α _inst_2 c b)
Case conversion may be inaccurate. Consider using '#align div_lt_div_iff_left div_lt_div_iff_leftₓ'. -/
@[simp, to_additive]
theorem div_lt_div_iff_left (a : α) : a / b < a / c ↔ c < b := by
  rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_lt_mul_iff_left a⁻¹, inv_mul_cancel_left,
    inv_mul_cancel_left, inv_lt_inv_iff]
#align div_lt_div_iff_left div_lt_div_iff_left

/- warning: inv_lt_div_iff_lt_mul -> inv_lt_div_iff_lt_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α _inst_2)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α} {c : α}, Iff (LT.lt.{u1} α _inst_2 (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) b c)) (LT.lt.{u1} α _inst_2 c (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9616 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9618 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9616 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9618) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9631 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9633 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9631 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9633)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9653 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9655 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9653 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9655)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9668 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9670 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9668 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9670)] {a : α} {b : α} {c : α}, Iff (LT.lt.{u1} α _inst_2 (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) b c)) (LT.lt.{u1} α _inst_2 c (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a b))
Case conversion may be inaccurate. Consider using '#align inv_lt_div_iff_lt_mul inv_lt_div_iff_lt_mulₓ'. -/
@[simp, to_additive]
theorem inv_lt_div_iff_lt_mul : a⁻¹ < b / c ↔ c < a * b := by
  rw [div_eq_mul_inv, lt_mul_inv_iff_mul_lt, inv_mul_lt_iff_lt_mul]
#align inv_lt_div_iff_lt_mul inv_lt_div_iff_lt_mul

/- warning: div_lt_div_left' -> div_lt_div_left' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α _inst_2)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α}, (LT.lt.{u1} α _inst_2 a b) -> (forall (c : α), LT.lt.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) c b) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) c a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9750 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9752 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9750 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9752) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9765 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9767 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9765 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9767)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9787 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9789 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9787 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9789)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9802 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9804 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9802 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9804)] {a : α} {b : α}, (LT.lt.{u1} α _inst_2 a b) -> (forall (c : α), LT.lt.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) c b) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) c a))
Case conversion may be inaccurate. Consider using '#align div_lt_div_left' div_lt_div_left'ₓ'. -/
@[to_additive sub_lt_sub_left]
theorem div_lt_div_left' (h : a < b) (c : α) : c / b < c / a :=
  (div_lt_div_iff_left c).2 h
#align div_lt_div_left' div_lt_div_left'

end Left

end Group

section CommGroup

variable [CommGroup α]

section LT

variable [LT α] [CovariantClass α α (· * ·) (· < ·)] {a b c d : α}

/- warning: div_lt_div_iff' -> div_lt_div_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α} {c : α} {d : α}, Iff (LT.lt.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) a b) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) c d)) (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) a d) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) c b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9916 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9918 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9916 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9918) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9931 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9933 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9931 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9933)] {a : α} {b : α} {c : α} {d : α}, Iff (LT.lt.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) a b) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) c d)) (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) a d) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) c b))
Case conversion may be inaccurate. Consider using '#align div_lt_div_iff' div_lt_div_iff'ₓ'. -/
@[to_additive sub_lt_sub_iff]
theorem div_lt_div_iff' : a / b < c / d ↔ a * d < c * b := by
  simpa only [div_eq_mul_inv] using mul_inv_lt_mul_inv_iff'
#align div_lt_div_iff' div_lt_div_iff'

/- warning: lt_div_iff_mul_lt' -> lt_div_iff_mul_lt' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α} {c : α}, Iff (LT.lt.{u1} α _inst_2 b (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) c a)) (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) a b) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9992 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9994 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9992 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9994) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10007 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10009 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10007 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10009)] {a : α} {b : α} {c : α}, Iff (LT.lt.{u1} α _inst_2 b (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) c a)) (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) a b) c)
Case conversion may be inaccurate. Consider using '#align lt_div_iff_mul_lt' lt_div_iff_mul_lt'ₓ'. -/
@[to_additive]
theorem lt_div_iff_mul_lt' : b < c / a ↔ a * b < c := by rw [lt_div_iff_mul_lt, mul_comm]
#align lt_div_iff_mul_lt' lt_div_iff_mul_lt'

alias lt_sub_iff_add_lt' ↔ add_lt_of_lt_sub_left lt_sub_left_of_add_lt

/- warning: div_lt_iff_lt_mul' -> div_lt_iff_lt_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α} {c : α}, Iff (LT.lt.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) a b) c) (LT.lt.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10086 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10088 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10086 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10088) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10101 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10103 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10101 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10103)] {a : α} {b : α} {c : α}, Iff (LT.lt.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) a b) c) (LT.lt.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) b c))
Case conversion may be inaccurate. Consider using '#align div_lt_iff_lt_mul' div_lt_iff_lt_mul'ₓ'. -/
@[to_additive]
theorem div_lt_iff_lt_mul' : a / b < c ↔ a < b * c := by rw [div_lt_iff_lt_mul, mul_comm]
#align div_lt_iff_lt_mul' div_lt_iff_lt_mul'

alias sub_lt_iff_lt_add' ↔ lt_add_of_sub_left_lt sub_left_lt_of_lt_add

/- warning: inv_lt_div_iff_lt_mul' -> inv_lt_div_iff_lt_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α} {c : α}, Iff (LT.lt.{u1} α _inst_2 (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))) b) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) a c)) (LT.lt.{u1} α _inst_2 c (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10180 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10182 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10180 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10182) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10195 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10197 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10195 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10197)] {a : α} {b : α} {c : α}, Iff (LT.lt.{u1} α _inst_2 (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_1))))) b) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) a c)) (LT.lt.{u1} α _inst_2 c (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) a b))
Case conversion may be inaccurate. Consider using '#align inv_lt_div_iff_lt_mul' inv_lt_div_iff_lt_mul'ₓ'. -/
@[to_additive]
theorem inv_lt_div_iff_lt_mul' : b⁻¹ < a / c ↔ c < a * b :=
  lt_div_iff_mul_lt.trans inv_mul_lt_iff_lt_mul'
#align inv_lt_div_iff_lt_mul' inv_lt_div_iff_lt_mul'

/- warning: div_lt_comm -> div_lt_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α} {c : α}, Iff (LT.lt.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) a b) c) (LT.lt.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) a c) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10250 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10252 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10250 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10252) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10265 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10267 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10265 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10267)] {a : α} {b : α} {c : α}, Iff (LT.lt.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) a b) c) (LT.lt.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) a c) b)
Case conversion may be inaccurate. Consider using '#align div_lt_comm div_lt_commₓ'. -/
@[to_additive]
theorem div_lt_comm : a / b < c ↔ a / c < b :=
  div_lt_iff_lt_mul'.trans div_lt_iff_lt_mul.symm
#align div_lt_comm div_lt_comm

/- warning: lt_div_comm -> lt_div_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α} {c : α}, Iff (LT.lt.{u1} α _inst_2 a (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) b c)) (LT.lt.{u1} α _inst_2 c (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) b a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10316 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10318 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10316 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10318) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10331 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10333 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10331 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10333)] {a : α} {b : α} {c : α}, Iff (LT.lt.{u1} α _inst_2 a (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) b c)) (LT.lt.{u1} α _inst_2 c (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) b a))
Case conversion may be inaccurate. Consider using '#align lt_div_comm lt_div_commₓ'. -/
@[to_additive]
theorem lt_div_comm : a < b / c ↔ c < b / a :=
  lt_div_iff_mul_lt'.trans lt_div_iff_mul_lt.symm
#align lt_div_comm lt_div_comm

end LT

section Preorder

variable [Preorder α] [CovariantClass α α (· * ·) (· < ·)] {a b c d : α}

/- warning: div_lt_div'' -> div_lt_div'' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] {a : α} {b : α} {c : α} {d : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) c d) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) a d) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10436 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10438 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10436 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10438) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10451 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10453 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10451 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10453)] {a : α} {b : α} {c : α} {d : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) c d) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) a d) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) b c))
Case conversion may be inaccurate. Consider using '#align div_lt_div'' div_lt_div''ₓ'. -/
@[to_additive sub_lt_sub]
theorem div_lt_div'' (hab : a < b) (hcd : c < d) : a / d < b / c :=
  by
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_comm b, mul_inv_lt_inv_mul_iff, mul_comm]
  exact mul_lt_mul_of_lt_of_lt hab hcd
#align div_lt_div'' div_lt_div''

end Preorder

end CommGroup

section LinearOrder

variable [Group α] [LinearOrder α]

/- warning: cmp_div_one' -> cmp_div_one' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LinearOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2))))))] (a : α) (b : α), Eq.{1} Ordering (cmp.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2))))) (fun (a : α) (b : α) => LT.lt.decidable.{u1} α _inst_2 a b) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))))) (cmp.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2))))) (fun (a : α) (b : α) => LT.lt.decidable.{u1} α _inst_2 a b) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LinearOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10559 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10561 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10559 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10561)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10574 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10576 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10574 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10576)] (a : α) (b : α), Eq.{1} Ordering (cmp.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_2)))))) (fun (a : α) (b : α) => instDecidableLtToLTToPreorderToPartialOrder.{u1} α _inst_2 a b) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1))))))) (cmp.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_2)))))) (fun (a : α) (b : α) => instDecidableLtToLTToPreorderToPartialOrder.{u1} α _inst_2 a b) a b)
Case conversion may be inaccurate. Consider using '#align cmp_div_one' cmp_div_one'ₓ'. -/
@[simp, to_additive cmp_sub_zero]
theorem cmp_div_one' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] (a b : α) :
    cmp (a / b) 1 = cmp a b := by rw [← cmp_mul_right' _ _ b, one_mul, div_mul_cancel']
#align cmp_div_one' cmp_div_one'

variable [CovariantClass α α (· * ·) (· ≤ ·)]

section VariableNames

variable {a b c : α}

/- warning: le_of_forall_one_lt_lt_mul -> le_of_forall_one_lt_lt_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LinearOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2))))))] {a : α} {b : α}, (forall (ε : α), (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2))))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) ε) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2))))) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b ε))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2))))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LinearOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10745 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10747 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10745 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10747) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10760 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10762 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10760 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10762)] {a : α} {b : α}, (forall (ε : α), (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_2)))))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) ε) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_2)))))) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b ε))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_2)))))) a b)
Case conversion may be inaccurate. Consider using '#align le_of_forall_one_lt_lt_mul le_of_forall_one_lt_lt_mulₓ'. -/
@[to_additive]
theorem le_of_forall_one_lt_lt_mul (h : ∀ ε : α, 1 < ε → a < b * ε) : a ≤ b :=
  le_of_not_lt fun h₁ => lt_irrefl a (by simpa using h _ (lt_inv_mul_iff_lt.mpr h₁))
#align le_of_forall_one_lt_lt_mul le_of_forall_one_lt_lt_mul

/- warning: le_iff_forall_one_lt_lt_mul -> le_iff_forall_one_lt_lt_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LinearOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2))))))] {a : α} {b : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2))))) a b) (forall (ε : α), (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2))))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) ε) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2))))) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b ε)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LinearOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10833 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10835 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10833 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10835) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10848 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10850 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10848 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10850)] {a : α} {b : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_2)))))) a b) (forall (ε : α), (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_2)))))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) ε) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_2)))))) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b ε)))
Case conversion may be inaccurate. Consider using '#align le_iff_forall_one_lt_lt_mul le_iff_forall_one_lt_lt_mulₓ'. -/
@[to_additive]
theorem le_iff_forall_one_lt_lt_mul : a ≤ b ↔ ∀ ε, 1 < ε → a < b * ε :=
  ⟨fun h ε => lt_mul_of_le_of_one_lt h, le_of_forall_one_lt_lt_mul⟩
#align le_iff_forall_one_lt_lt_mul le_iff_forall_one_lt_lt_mul

/- warning: div_le_inv_mul_iff -> div_le_inv_mul_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LinearOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2))))))] {a : α} {b : α} [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2))))))], Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2))))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) b)) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2))))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LinearOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10913 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10915 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10913 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10915) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10928 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10930 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10928 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10930)] {a : α} {b : α} [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10953 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10955 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10953 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10955)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10968 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10970 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10968 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10970)], Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_2)))))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) b)) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_2)))))) a b)
Case conversion may be inaccurate. Consider using '#align div_le_inv_mul_iff div_le_inv_mul_iffₓ'. -/
/-  I (DT) introduced this lemma to prove (the additive version `sub_le_sub_flip` of)
`div_le_div_flip` below.  Now I wonder what is the point of either of these lemmas... -/
@[to_additive]
theorem div_le_inv_mul_iff [CovariantClass α α (swap (· * ·)) (· ≤ ·)] : a / b ≤ a⁻¹ * b ↔ a ≤ b :=
  by
  rw [div_eq_mul_inv, mul_inv_le_inv_mul_iff]
  exact
    ⟨fun h => not_lt.mp fun k => not_lt.mpr h (mul_lt_mul_of_lt_of_lt k k), fun h =>
      mul_le_mul' h h⟩
#align div_le_inv_mul_iff div_le_inv_mul_iff

/- warning: div_le_div_flip -> div_le_div_flip is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_4 : CommGroup.{u1} α] [_inst_5 : LinearOrder.{u1} α] [_inst_6 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_4))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_5))))))] {a : α} {b : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_5))))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_4)))) a b) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_4)))) b a)) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_5))))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_4 : CommGroup.{u1} α] [_inst_5 : LinearOrder.{u1} α] [_inst_6 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.11117 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.11119 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_4)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.11117 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.11119) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.11132 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.11134 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_5)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.11132 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.11134)] {a : α} {b : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_5)))))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_4)))) a b) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_4)))) b a)) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_5)))))) a b)
Case conversion may be inaccurate. Consider using '#align div_le_div_flip div_le_div_flipₓ'. -/
--  What is the point of this lemma?  See comment about `div_le_inv_mul_iff` above.
@[simp, to_additive]
theorem div_le_div_flip {α : Type _} [CommGroup α] [LinearOrder α]
    [CovariantClass α α (· * ·) (· ≤ ·)] {a b : α} : a / b ≤ b / a ↔ a ≤ b :=
  by
  rw [div_eq_mul_inv b, mul_comm]
  exact div_le_inv_mul_iff
#align div_le_div_flip div_le_div_flip

end VariableNames

end LinearOrder

/-!
### Linearly ordered commutative groups
-/


#print LinearOrderedAddCommGroup /-
/-- A linearly ordered additive commutative group is an
additive commutative group with a linear order in which
addition is monotone. -/
@[protect_proj]
class LinearOrderedAddCommGroup (α : Type u) extends OrderedAddCommGroup α, LinearOrder α
#align linear_ordered_add_comm_group LinearOrderedAddCommGroup
-/

#print LinearOrderedAddCommGroupWithTop /-
/-- A linearly ordered commutative monoid with an additively absorbing `⊤` element.
  Instances should include number systems with an infinite element adjoined.` -/
@[protect_proj]
class LinearOrderedAddCommGroupWithTop (α : Type _) extends LinearOrderedAddCommMonoidWithTop α,
  SubNegMonoid α, Nontrivial α where
  neg_top : -(⊤ : α) = ⊤
  add_neg_cancel : ∀ a : α, a ≠ ⊤ → a + -a = 0
#align linear_ordered_add_comm_group_with_top LinearOrderedAddCommGroupWithTop
-/

#print LinearOrderedCommGroup /-
/-- A linearly ordered commutative group is a
commutative group with a linear order in which
multiplication is monotone. -/
@[protect_proj, to_additive]
class LinearOrderedCommGroup (α : Type u) extends OrderedCommGroup α, LinearOrder α
#align linear_ordered_comm_group LinearOrderedCommGroup
-/

section LinearOrderedCommGroup

variable [LinearOrderedCommGroup α] {a b c : α}

/- warning: linear_ordered_comm_group.mul_lt_mul_left' -> LinearOrderedCommGroup.mul_lt_mul_left' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedCommGroup.{u1} α] (a : α) (b : α), (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α (LinearOrderedCommGroup.toOrderedCommGroup.{u1} α _inst_1)))) a b) -> (forall (c : α), LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α (LinearOrderedCommGroup.toOrderedCommGroup.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α (LinearOrderedCommGroup.toOrderedCommGroup.{u1} α _inst_1)))))))) c a) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α (LinearOrderedCommGroup.toOrderedCommGroup.{u1} α _inst_1)))))))) c b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedCommGroup.{u1} α] (a : α) (b : α), (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α (LinearOrderedCommGroup.toOrderedCommGroup.{u1} α _inst_1)))) a b) -> (forall (c : α), LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α (LinearOrderedCommGroup.toOrderedCommGroup.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α (LinearOrderedCommGroup.toOrderedCommGroup.{u1} α _inst_1)))))))) c a) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α (LinearOrderedCommGroup.toOrderedCommGroup.{u1} α _inst_1)))))))) c b))
Case conversion may be inaccurate. Consider using '#align linear_ordered_comm_group.mul_lt_mul_left' LinearOrderedCommGroup.mul_lt_mul_left'ₓ'. -/
@[to_additive LinearOrderedAddCommGroup.add_lt_add_left]
theorem LinearOrderedCommGroup.mul_lt_mul_left' (a b : α) (h : a < b) (c : α) : c * a < c * b :=
  mul_lt_mul_left' h c
#align linear_ordered_comm_group.mul_lt_mul_left' LinearOrderedCommGroup.mul_lt_mul_left'

/- warning: eq_one_of_inv_eq' -> eq_one_of_inv_eq' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedCommGroup.{u1} α] {a : α}, (Eq.{succ u1} α (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α (LinearOrderedCommGroup.toOrderedCommGroup.{u1} α _inst_1))))) a) a) -> (Eq.{succ u1} α a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α (LinearOrderedCommGroup.toOrderedCommGroup.{u1} α _inst_1)))))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedCommGroup.{u1} α] {a : α}, (Eq.{succ u1} α (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α (OrderedCommGroup.toCommGroup.{u1} α (LinearOrderedCommGroup.toOrderedCommGroup.{u1} α _inst_1))))))) a) a) -> (Eq.{succ u1} α a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α (OrderedCommGroup.toCommGroup.{u1} α (LinearOrderedCommGroup.toOrderedCommGroup.{u1} α _inst_1))))))))))
Case conversion may be inaccurate. Consider using '#align eq_one_of_inv_eq' eq_one_of_inv_eq'ₓ'. -/
@[to_additive eq_zero_of_neg_eq]
theorem eq_one_of_inv_eq' (h : a⁻¹ = a) : a = 1 :=
  match lt_trichotomy a 1 with
  | Or.inl h₁ =>
    have : 1 < a := h ▸ one_lt_inv_of_inv h₁
    absurd h₁ this.asymm
  | Or.inr (Or.inl h₁) => h₁
  | Or.inr (Or.inr h₁) =>
    have : a < 1 := h ▸ inv_lt_one'.mpr h₁
    absurd h₁ this.asymm
#align eq_one_of_inv_eq' eq_one_of_inv_eq'

/- warning: exists_one_lt' -> exists_one_lt' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedCommGroup.{u1} α] [_inst_2 : Nontrivial.{u1} α], Exists.{succ u1} α (fun (a : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α (LinearOrderedCommGroup.toOrderedCommGroup.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α (LinearOrderedCommGroup.toOrderedCommGroup.{u1} α _inst_1)))))))))) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedCommGroup.{u1} α] [_inst_2 : Nontrivial.{u1} α], Exists.{succ u1} α (fun (a : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α (LinearOrderedCommGroup.toOrderedCommGroup.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α (OrderedCommGroup.toCommGroup.{u1} α (LinearOrderedCommGroup.toOrderedCommGroup.{u1} α _inst_1))))))))) a)
Case conversion may be inaccurate. Consider using '#align exists_one_lt' exists_one_lt'ₓ'. -/
@[to_additive exists_zero_lt]
theorem exists_one_lt' [Nontrivial α] : ∃ a : α, 1 < a :=
  by
  obtain ⟨y, hy⟩ := Decidable.exists_ne (1 : α)
  cases hy.lt_or_lt
  · exact ⟨y⁻¹, one_lt_inv'.mpr h⟩
  · exact ⟨y, h⟩
#align exists_one_lt' exists_one_lt'

#print LinearOrderedCommGroup.to_no_max_order /-
-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) LinearOrderedCommGroup.to_no_max_order [Nontrivial α] : NoMaxOrder α :=
  ⟨by
    obtain ⟨y, hy⟩ : ∃ a : α, 1 < a := exists_one_lt'
    exact fun a => ⟨a * y, lt_mul_of_one_lt_right' a hy⟩⟩
#align linear_ordered_comm_group.to_no_max_order LinearOrderedCommGroup.to_no_max_order
-/

#print LinearOrderedCommGroup.to_no_min_order /-
-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) LinearOrderedCommGroup.to_no_min_order [Nontrivial α] : NoMinOrder α :=
  ⟨by
    obtain ⟨y, hy⟩ : ∃ a : α, 1 < a := exists_one_lt'
    exact fun a => ⟨a / y, (div_lt_self_iff a).mpr hy⟩⟩
#align linear_ordered_comm_group.to_no_min_order LinearOrderedCommGroup.to_no_min_order
-/

#print LinearOrderedCommGroup.to_LinearOrderedCancelCommMonoid /-
-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) LinearOrderedCommGroup.to_LinearOrderedCancelCommMonoid :
    LinearOrderedCancelCommMonoid α :=
  { ‹LinearOrderedCommGroup α›, OrderedCommGroup.to_OrderedCancelCommMonoid with }
#align
  linear_ordered_comm_group.to_linear_ordered_cancel_comm_monoid LinearOrderedCommGroup.to_LinearOrderedCancelCommMonoid
-/

end LinearOrderedCommGroup

namespace AddCommGroup

#print AddCommGroup.PositiveCone /-
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic order_laws_tac -/
/-- A collection of elements in an `add_comm_group` designated as "non-negative".
This is useful for constructing an `ordered_add_commm_group`
by choosing a positive cone in an exisiting `add_comm_group`. -/
@[nolint has_nonempty_instance]
structure PositiveCone (α : Type _) [AddCommGroup α] where
  Nonneg : α → Prop
  Pos : α → Prop := fun a => nonneg a ∧ ¬nonneg (-a)
  pos_iff : ∀ a, Pos a ↔ nonneg a ∧ ¬nonneg (-a) := by
    run_tac
      order_laws_tac
  zero_nonneg : nonneg 0
  add_nonneg : ∀ {a b}, nonneg a → nonneg b → nonneg (a + b)
  nonneg_antisymm : ∀ {a}, nonneg a → nonneg (-a) → a = 0
#align add_comm_group.positive_cone AddCommGroup.PositiveCone
-/

#print AddCommGroup.TotalPositiveCone /-
/-- A positive cone in an `add_comm_group` induces a linear order if
for every `a`, either `a` or `-a` is non-negative. -/
@[nolint has_nonempty_instance]
structure TotalPositiveCone (α : Type _) [AddCommGroup α] extends PositiveCone α where
  nonnegDecidable : DecidablePred nonneg
  nonneg_total : ∀ a : α, nonneg a ∨ nonneg (-a)
#align add_comm_group.total_positive_cone AddCommGroup.TotalPositiveCone
-/

/-- Forget that a `total_positive_cone` is total. -/
add_decl_doc total_positive_cone.to_positive_cone

end AddCommGroup

namespace OrderedAddCommGroup

open AddCommGroup

#print OrderedAddCommGroup.mkOfPositiveCone /-
/-- Construct an `ordered_add_comm_group` by
designating a positive cone in an existing `add_comm_group`. -/
def mkOfPositiveCone {α : Type _} [AddCommGroup α] (C : PositiveCone α) : OrderedAddCommGroup α :=
  { ‹AddCommGroup α› with
    le := fun a b => C.Nonneg (b - a)
    lt := fun a b => C.Pos (b - a)
    lt_iff_le_not_le := fun a b => by simp <;> rw [C.pos_iff] <;> simp
    le_refl := fun a => by simp [C.zero_nonneg]
    le_trans := fun a b c nab nbc => by
      simp [-sub_eq_add_neg] <;> rw [← sub_add_sub_cancel] <;> exact C.add_nonneg nbc nab
    le_antisymm := fun a b nab nba =>
      eq_of_sub_eq_zero <| C.nonneg_antisymm nba (by rw [neg_sub] <;> exact nab)
    add_le_add_left := fun a b nab c => by simpa [(· ≤ ·), Preorder.Le] using nab }
#align ordered_add_comm_group.mk_of_positive_cone OrderedAddCommGroup.mkOfPositiveCone
-/

end OrderedAddCommGroup

namespace LinearOrderedAddCommGroup

open AddCommGroup

#print LinearOrderedAddCommGroup.mkOfPositiveCone /-
/-- Construct a `linear_ordered_add_comm_group` by
designating a positive cone in an existing `add_comm_group`
such that for every `a`, either `a` or `-a` is non-negative. -/
def mkOfPositiveCone {α : Type _} [AddCommGroup α] (C : TotalPositiveCone α) :
    LinearOrderedAddCommGroup α :=
  {
    OrderedAddCommGroup.mkOfPositiveCone
      C.toPositiveCone with
    le_total := fun a b => by
      convert C.nonneg_total (b - a)
      change C.nonneg _ = _
      congr
      simp
    decidableLe := fun a b => C.nonnegDecidable _ }
#align linear_ordered_add_comm_group.mk_of_positive_cone LinearOrderedAddCommGroup.mkOfPositiveCone
-/

end LinearOrderedAddCommGroup

section NormNumLemmas

/- The following lemmas are stated so that the `norm_num` tactic can use them with the
expected signatures.  -/
variable [OrderedCommGroup α] {a b : α}

/- warning: inv_le_inv' -> inv_le_inv' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) a b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))) b) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) a b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))) b) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))) a))
Case conversion may be inaccurate. Consider using '#align inv_le_inv' inv_le_inv'ₓ'. -/
@[to_additive neg_le_neg]
theorem inv_le_inv' : a ≤ b → b⁻¹ ≤ a⁻¹ :=
  inv_le_inv_iff.mpr
#align inv_le_inv' inv_le_inv'

/- warning: inv_lt_inv' -> inv_lt_inv' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) a b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))) b) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) a b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))) b) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))) a))
Case conversion may be inaccurate. Consider using '#align inv_lt_inv' inv_lt_inv'ₓ'. -/
@[to_additive neg_lt_neg]
theorem inv_lt_inv' : a < b → b⁻¹ < a⁻¹ :=
  inv_lt_inv_iff.mpr
#align inv_lt_inv' inv_lt_inv'

/- warning: inv_lt_one_of_one_lt -> inv_lt_one_of_one_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] {a : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1))))))))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))) a) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1))))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] {a : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))) a) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))))))
Case conversion may be inaccurate. Consider using '#align inv_lt_one_of_one_lt inv_lt_one_of_one_ltₓ'. -/
--  The additive version is also a `linarith` lemma.
@[to_additive]
theorem inv_lt_one_of_one_lt : 1 < a → a⁻¹ < 1 :=
  inv_lt_one_iff_one_lt.mpr
#align inv_lt_one_of_one_lt inv_lt_one_of_one_lt

/- warning: inv_le_one_of_one_le -> inv_le_one_of_one_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] {a : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1))))))))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))) a) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1))))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] {a : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))) a) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))))))
Case conversion may be inaccurate. Consider using '#align inv_le_one_of_one_le inv_le_one_of_one_leₓ'. -/
--  The additive version is also a `linarith` lemma.
@[to_additive]
theorem inv_le_one_of_one_le : 1 ≤ a → a⁻¹ ≤ 1 :=
  inv_le_one'.mpr
#align inv_le_one_of_one_le inv_le_one_of_one_le

/- warning: one_le_inv_of_le_one -> one_le_inv_of_le_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] {a : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))))))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1))))))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] {a : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1))))))))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))) a))
Case conversion may be inaccurate. Consider using '#align one_le_inv_of_le_one one_le_inv_of_le_oneₓ'. -/
@[to_additive neg_nonneg_of_nonpos]
theorem one_le_inv_of_le_one : a ≤ 1 → 1 ≤ a⁻¹ :=
  one_le_inv'.mpr
#align one_le_inv_of_le_one one_le_inv_of_le_one

end NormNumLemmas

section

variable {β : Type _} [Group α] [Preorder α] [CovariantClass α α (· * ·) (· ≤ ·)]
  [CovariantClass α α (swap (· * ·)) (· ≤ ·)] [Preorder β] {f : β → α} {s : Set β}

/- warning: monotone.inv -> Monotone.inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] [_inst_5 : Preorder.{u2} β] {f : β -> α}, (Monotone.{u2, u1} β α _inst_5 _inst_2 f) -> (Antitone.{u2, u1} β α _inst_5 _inst_2 (fun (x : β) => Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) (f x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Group.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12508 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12510 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12508 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12510) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12523 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12525 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12523 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12525)] [_inst_4 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12545 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12547 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12545 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12547)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12560 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12562 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12560 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12562)] [_inst_5 : Preorder.{u1} β] {f : β -> α}, (Monotone.{u1, u2} β α _inst_5 _inst_2 f) -> (Antitone.{u1, u2} β α _inst_5 _inst_2 (fun (x : β) => Inv.inv.{u2} α (InvOneClass.toInv.{u2} α (DivInvOneMonoid.toInvOneClass.{u2} α (DivisionMonoid.toDivInvOneMonoid.{u2} α (Group.toDivisionMonoid.{u2} α _inst_1)))) (f x)))
Case conversion may be inaccurate. Consider using '#align monotone.inv Monotone.invₓ'. -/
@[to_additive]
theorem Monotone.inv (hf : Monotone f) : Antitone fun x => (f x)⁻¹ := fun x y hxy =>
  inv_le_inv_iff.2 (hf hxy)
#align monotone.inv Monotone.inv

/- warning: antitone.inv -> Antitone.inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] [_inst_5 : Preorder.{u2} β] {f : β -> α}, (Antitone.{u2, u1} β α _inst_5 _inst_2 f) -> (Monotone.{u2, u1} β α _inst_5 _inst_2 (fun (x : β) => Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) (f x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Group.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12626 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12628 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12626 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12628) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12641 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12643 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12641 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12643)] [_inst_4 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12663 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12665 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12663 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12665)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12678 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12680 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12678 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12680)] [_inst_5 : Preorder.{u1} β] {f : β -> α}, (Antitone.{u1, u2} β α _inst_5 _inst_2 f) -> (Monotone.{u1, u2} β α _inst_5 _inst_2 (fun (x : β) => Inv.inv.{u2} α (InvOneClass.toInv.{u2} α (DivInvOneMonoid.toInvOneClass.{u2} α (DivisionMonoid.toDivInvOneMonoid.{u2} α (Group.toDivisionMonoid.{u2} α _inst_1)))) (f x)))
Case conversion may be inaccurate. Consider using '#align antitone.inv Antitone.invₓ'. -/
@[to_additive]
theorem Antitone.inv (hf : Antitone f) : Monotone fun x => (f x)⁻¹ := fun x y hxy =>
  inv_le_inv_iff.2 (hf hxy)
#align antitone.inv Antitone.inv

/- warning: monotone_on.inv -> MonotoneOn.inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] [_inst_5 : Preorder.{u2} β] {f : β -> α} {s : Set.{u2} β}, (MonotoneOn.{u2, u1} β α _inst_5 _inst_2 f s) -> (AntitoneOn.{u2, u1} β α _inst_5 _inst_2 (fun (x : β) => Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) (f x)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Group.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12744 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12746 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12744 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12746) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12759 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12761 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12759 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12761)] [_inst_4 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12781 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12783 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12781 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12783)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12796 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12798 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12796 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12798)] [_inst_5 : Preorder.{u1} β] {f : β -> α} {s : Set.{u1} β}, (MonotoneOn.{u1, u2} β α _inst_5 _inst_2 f s) -> (AntitoneOn.{u1, u2} β α _inst_5 _inst_2 (fun (x : β) => Inv.inv.{u2} α (InvOneClass.toInv.{u2} α (DivInvOneMonoid.toInvOneClass.{u2} α (DivisionMonoid.toDivInvOneMonoid.{u2} α (Group.toDivisionMonoid.{u2} α _inst_1)))) (f x)) s)
Case conversion may be inaccurate. Consider using '#align monotone_on.inv MonotoneOn.invₓ'. -/
@[to_additive]
theorem MonotoneOn.inv (hf : MonotoneOn f s) : AntitoneOn (fun x => (f x)⁻¹) s :=
  fun x hx y hy hxy => inv_le_inv_iff.2 (hf hx hy hxy)
#align monotone_on.inv MonotoneOn.inv

/- warning: antitone_on.inv -> AntitoneOn.inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] [_inst_5 : Preorder.{u2} β] {f : β -> α} {s : Set.{u2} β}, (AntitoneOn.{u2, u1} β α _inst_5 _inst_2 f s) -> (MonotoneOn.{u2, u1} β α _inst_5 _inst_2 (fun (x : β) => Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) (f x)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Group.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12870 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12872 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12870 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12872) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12885 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12887 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12885 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12887)] [_inst_4 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12907 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12909 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12907 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12909)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12922 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12924 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12922 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12924)] [_inst_5 : Preorder.{u1} β] {f : β -> α} {s : Set.{u1} β}, (AntitoneOn.{u1, u2} β α _inst_5 _inst_2 f s) -> (MonotoneOn.{u1, u2} β α _inst_5 _inst_2 (fun (x : β) => Inv.inv.{u2} α (InvOneClass.toInv.{u2} α (DivInvOneMonoid.toInvOneClass.{u2} α (DivisionMonoid.toDivInvOneMonoid.{u2} α (Group.toDivisionMonoid.{u2} α _inst_1)))) (f x)) s)
Case conversion may be inaccurate. Consider using '#align antitone_on.inv AntitoneOn.invₓ'. -/
@[to_additive]
theorem AntitoneOn.inv (hf : AntitoneOn f s) : MonotoneOn (fun x => (f x)⁻¹) s :=
  fun x hx y hy hxy => inv_le_inv_iff.2 (hf hx hy hxy)
#align antitone_on.inv AntitoneOn.inv

end

section

variable {β : Type _} [Group α] [Preorder α] [CovariantClass α α (· * ·) (· < ·)]
  [CovariantClass α α (swap (· * ·)) (· < ·)] [Preorder β] {f : β → α} {s : Set β}

/- warning: strict_mono.inv -> StrictMono.inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] [_inst_5 : Preorder.{u2} β] {f : β -> α}, (StrictMono.{u2, u1} β α _inst_5 _inst_2 f) -> (StrictAnti.{u2, u1} β α _inst_5 _inst_2 (fun (x : β) => Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) (f x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Group.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13094 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13096 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13094 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13096) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13109 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13111 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13109 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13111)] [_inst_4 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13131 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13133 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13131 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13133)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13146 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13148 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13146 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13148)] [_inst_5 : Preorder.{u1} β] {f : β -> α}, (StrictMono.{u1, u2} β α _inst_5 _inst_2 f) -> (StrictAnti.{u1, u2} β α _inst_5 _inst_2 (fun (x : β) => Inv.inv.{u2} α (InvOneClass.toInv.{u2} α (DivInvOneMonoid.toInvOneClass.{u2} α (DivisionMonoid.toDivInvOneMonoid.{u2} α (Group.toDivisionMonoid.{u2} α _inst_1)))) (f x)))
Case conversion may be inaccurate. Consider using '#align strict_mono.inv StrictMono.invₓ'. -/
@[to_additive]
theorem StrictMono.inv (hf : StrictMono f) : StrictAnti fun x => (f x)⁻¹ := fun x y hxy =>
  inv_lt_inv_iff.2 (hf hxy)
#align strict_mono.inv StrictMono.inv

/- warning: strict_anti.inv -> StrictAnti.inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] [_inst_5 : Preorder.{u2} β] {f : β -> α}, (StrictAnti.{u2, u1} β α _inst_5 _inst_2 f) -> (StrictMono.{u2, u1} β α _inst_5 _inst_2 (fun (x : β) => Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) (f x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Group.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13212 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13214 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13212 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13214) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13227 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13229 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13227 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13229)] [_inst_4 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13249 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13251 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13249 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13251)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13264 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13266 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13264 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13266)] [_inst_5 : Preorder.{u1} β] {f : β -> α}, (StrictAnti.{u1, u2} β α _inst_5 _inst_2 f) -> (StrictMono.{u1, u2} β α _inst_5 _inst_2 (fun (x : β) => Inv.inv.{u2} α (InvOneClass.toInv.{u2} α (DivInvOneMonoid.toInvOneClass.{u2} α (DivisionMonoid.toDivInvOneMonoid.{u2} α (Group.toDivisionMonoid.{u2} α _inst_1)))) (f x)))
Case conversion may be inaccurate. Consider using '#align strict_anti.inv StrictAnti.invₓ'. -/
@[to_additive]
theorem StrictAnti.inv (hf : StrictAnti f) : StrictMono fun x => (f x)⁻¹ := fun x y hxy =>
  inv_lt_inv_iff.2 (hf hxy)
#align strict_anti.inv StrictAnti.inv

/- warning: strict_mono_on.inv -> StrictMonoOn.inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] [_inst_5 : Preorder.{u2} β] {f : β -> α} {s : Set.{u2} β}, (StrictMonoOn.{u2, u1} β α _inst_5 _inst_2 f s) -> (StrictAntiOn.{u2, u1} β α _inst_5 _inst_2 (fun (x : β) => Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) (f x)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Group.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13330 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13332 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13330 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13332) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13345 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13347 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13345 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13347)] [_inst_4 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13367 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13369 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13367 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13369)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13382 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13384 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13382 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13384)] [_inst_5 : Preorder.{u1} β] {f : β -> α} {s : Set.{u1} β}, (StrictMonoOn.{u1, u2} β α _inst_5 _inst_2 f s) -> (StrictAntiOn.{u1, u2} β α _inst_5 _inst_2 (fun (x : β) => Inv.inv.{u2} α (InvOneClass.toInv.{u2} α (DivInvOneMonoid.toInvOneClass.{u2} α (DivisionMonoid.toDivInvOneMonoid.{u2} α (Group.toDivisionMonoid.{u2} α _inst_1)))) (f x)) s)
Case conversion may be inaccurate. Consider using '#align strict_mono_on.inv StrictMonoOn.invₓ'. -/
@[to_additive]
theorem StrictMonoOn.inv (hf : StrictMonoOn f s) : StrictAntiOn (fun x => (f x)⁻¹) s :=
  fun x hx y hy hxy => inv_lt_inv_iff.2 (hf hx hy hxy)
#align strict_mono_on.inv StrictMonoOn.inv

/- warning: strict_anti_on.inv -> StrictAntiOn.inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] [_inst_5 : Preorder.{u2} β] {f : β -> α} {s : Set.{u2} β}, (StrictAntiOn.{u2, u1} β α _inst_5 _inst_2 f s) -> (StrictMonoOn.{u2, u1} β α _inst_5 _inst_2 (fun (x : β) => Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) (f x)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Group.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13456 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13458 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13456 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13458) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13471 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13473 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13471 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13473)] [_inst_4 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13493 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13495 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13493 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13495)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13508 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13510 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13508 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13510)] [_inst_5 : Preorder.{u1} β] {f : β -> α} {s : Set.{u1} β}, (StrictAntiOn.{u1, u2} β α _inst_5 _inst_2 f s) -> (StrictMonoOn.{u1, u2} β α _inst_5 _inst_2 (fun (x : β) => Inv.inv.{u2} α (InvOneClass.toInv.{u2} α (DivInvOneMonoid.toInvOneClass.{u2} α (DivisionMonoid.toDivInvOneMonoid.{u2} α (Group.toDivisionMonoid.{u2} α _inst_1)))) (f x)) s)
Case conversion may be inaccurate. Consider using '#align strict_anti_on.inv StrictAntiOn.invₓ'. -/
@[to_additive]
theorem StrictAntiOn.inv (hf : StrictAntiOn f s) : StrictMonoOn (fun x => (f x)⁻¹) s :=
  fun x hx y hy hxy => inv_lt_inv_iff.2 (hf hx hy hxy)
#align strict_anti_on.inv StrictAntiOn.inv

end

